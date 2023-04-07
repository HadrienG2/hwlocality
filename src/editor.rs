//! Facilities for modifying a loaded Topology
//!
//! hwloc employs lazy evaluation patterns that are thread-unsafe and violate
//! Rust's aliasing rules. It is possible to force eager evaluation of the lazy
//! caches to return to a normal state, but as a result of this design, topology
//! modifications must be carried out through a proxy object that does not
//! permit shared references to unevaluated caches to escape.

#[cfg(doc)]
use crate::builder::{BuildFlags, TopologyBuilder, TypeFilter};
use crate::{
    bitmaps::{BitmapKind, CpuSet, NodeSet, SpecializedBitmap},
    cpu::kinds::CpuEfficiency,
    depth::Depth,
    distances::{Distances, DistancesKind},
    errors::{self, NulError, RawIntError, RawNullError},
    ffi::{self, LibcString},
    memory::attributes::{
        MemoryAttributeFlags, MemoryAttributeID, MemoryAttributeLocation, RawLocation,
    },
    objects::{types::ObjectType, TopologyObject},
    RawTopology, Topology,
};
use bitflags::bitflags;
use derive_more::Display;
use errno::Errno;
use libc::{c_void, EBUSY, EINVAL, ENOMEM};
use std::{
    ffi::{c_int, c_uint, c_ulong},
    fmt, ptr,
};
use thiserror::Error;

/// Proxy for modifying a `Topology`
///
/// This proxy object is carefully crafted to only allow operations that are
/// safe while modifying a topology and minimize the number of times the hwloc
/// lazy caches will need to be refreshed.
#[derive(Debug)]
pub struct TopologyEditor<'topology>(&'topology mut Topology);

/// # General-purpose utilities
impl<'topology> TopologyEditor<'topology> {
    /// Wrap an `&mut Topology` into a topology editor
    pub(crate) fn new(topology: &'topology mut Topology) -> Self {
        Self(topology)
    }

    /// Get a shared reference to the inner Topology
    ///
    /// This requires rebuilding inner caches, which can be costly. Prefer
    /// accessing the topology before or after editing it if possible.
    pub fn topology(&mut self) -> &Topology {
        self.topology_mut().refresh();
        self.topology_mut()
    }

    /// Get a mutable reference to the inner Topology
    fn topology_mut(&mut self) -> &mut Topology {
        self.0
    }

    /// Returns the contained hwloc topology pointer for interaction with hwloc
    fn topology_mut_ptr(&mut self) -> *mut RawTopology {
        self.topology_mut().as_mut_ptr()
    }
}

/// # Basic modifications
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__tinker.html
impl TopologyEditor<'_> {
    /// Restrict the topology to the given CPU set or nodeset
    ///
    /// The topology is modified so as to remove all objects that are not
    /// included (or partially included) in the specified CPU or NUMANode set.
    /// All objects CPU and node sets are restricted accordingly.
    ///
    /// This call may not be reverted by restricting back to a larger set. Once
    /// dropped during restriction, objects may not be brought back, except by
    /// loading another topology with [`Topology::new()`] or [`TopologyBuilder`].
    ///
    /// # Errors
    ///
    /// Err([`InvalidParameter`]) will be returned if the input set is invalid.
    /// The topology is not modified in this case.
    ///
    /// # Aborts
    ///
    /// Failure to allocate internal data will lead to a process abort, because
    /// the topology gets corrupted in this case and must not be touched again,
    /// but we have no way to prevent this in a safe API.
    #[doc(alias = "hwloc_topology_restrict")]
    pub fn restrict<Set: SpecializedBitmap>(
        &mut self,
        set: &Set,
        mut flags: RestrictFlags,
    ) -> Result<(), InvalidParameter> {
        // Configure restrict flags correctly depending on the node set type
        match Set::BITMAP_KIND {
            BitmapKind::CpuSet => flags.remove(RestrictFlags::BY_NODE_SET),
            BitmapKind::NodeSet => flags.insert(RestrictFlags::BY_NODE_SET),
        }
        if flags.contains(RestrictFlags::REMOVE_EMPTIED) {
            flags.remove(RestrictFlags::REMOVE_EMPTIED);
            match Set::BITMAP_KIND {
                BitmapKind::CpuSet => flags.insert(RestrictFlags::REMOVE_CPULESS),
                BitmapKind::NodeSet => flags.insert(RestrictFlags::REMOVE_MEMLESS),
            }
        }

        // Apply requested restriction
        let result = unsafe {
            errors::call_hwloc_int("hwloc_topology_restrict", || {
                ffi::hwloc_topology_restrict(
                    self.topology_mut_ptr(),
                    set.as_ref().as_ptr(),
                    flags.bits(),
                )
            })
        };
        match result {
            Ok(0) => Ok(()),
            Err(RawIntError::Errno {
                api: _,
                errno: Some(errno),
            }) => match errno.0 {
                EINVAL => Err(InvalidParameter),
                ENOMEM => {
                    eprintln!("Topology stuck in an invalid state, must abort");
                    std::process::abort()
                }
                _ => panic!("Unexpected errno {errno} from hwloc_topology_restrict"),
            },
            other => panic!("Unexpected result {other:?} from hwloc_topology_restrict"),
        }
    }

    /// Change the sets of allowed PUs and NUMA nodes in the topology
    ///
    /// This function only works if [`BuildFlags::INCLUDE_DISALLOWED`] was set
    /// during topology building. It does not modify any object, it only changes
    /// the sets returned by [`Topology::allowed_cpuset()`] and
    /// [`Topology::allowed_nodeset()`].
    ///
    /// It is notably useful when importing a topology from another process
    /// running in a different Linux Cgroup.
    ///
    /// Removing objects from a topology should rather be performed with
    /// [`TopologyEditor::restrict()`].
    #[doc(alias = "hwloc_topology_allow")]
    pub fn allow(&mut self, allow_set: AllowSet) -> Result<(), RawIntError> {
        // Convert AllowSet into a valid `hwloc_topology_allow` configuration
        let (cpuset, nodeset, flags) = match allow_set {
            AllowSet::All => (ptr::null(), ptr::null(), 1 << 0),
            AllowSet::LocalRestrictions => (ptr::null(), ptr::null(), 1 << 1),
            AllowSet::Custom { cpuset, nodeset } => {
                let cpuset = cpuset.map(|cpuset| cpuset.as_ptr()).unwrap_or(ptr::null());
                let nodeset = nodeset
                    .map(|nodeset| nodeset.as_ptr())
                    .unwrap_or(ptr::null());
                assert!(!(cpuset.is_null() && nodeset.is_null()));
                (cpuset, nodeset, 1 << 2)
            }
        };

        // Call hwloc
        unsafe {
            errors::call_hwloc_int("hwloc_topology_allow", || {
                ffi::hwloc_topology_allow(self.topology_mut_ptr(), cpuset, nodeset, flags)
            })
        }
        .map(|_| ())
    }

    /// Add more structure to the topology by adding an intermediate Group
    ///
    /// Use the `find_children` callback to specify which [`TopologyObject`]s
    /// should be made children of the newly created Group object. The cpuset
    /// and nodeset of the final Group object will be the union of the cpuset
    /// and nodeset of all children respectively. Empty groups are not allowed,
    /// so at least one of these sets must be non-empty, or no Group object
    /// will be created.
    ///
    /// Use the `merge` option to control hwloc's propension to merge groups
    /// with hierarchically-identical topology objects.
    //
    // NOTE: In the future, find_children will be an
    //       impl FnOnce(&Topology) -> impl IntoIterator<Item = &TopologyObject>
    //       but impl Trait is not yet allowed on function return types.
    #[doc(alias = "hwloc_topology_alloc_group_object")]
    #[doc(alias = "hwloc_obj_add_other_obj_sets")]
    #[doc(alias = "hwloc_topology_insert_group_object")]
    pub fn insert_group_object(
        &mut self,
        merge: Option<GroupMerge>,
        find_children: impl FnOnce(&Topology) -> Vec<&TopologyObject>,
    ) -> GroupInsertResult {
        // Allocate group object
        let group = unsafe {
            errors::call_hwloc_ptr_mut("hwloc_topology_alloc_group_object", || {
                ffi::hwloc_topology_alloc_group_object(self.topology_mut_ptr())
            })
        };
        let mut group = match group {
            Ok(group) => group,
            Err(e) => return GroupInsertResult::Failed(GroupInsertError::AllocFailed(e)),
        };

        // Expand cpu sets and node sets to cover designated children
        // NOTE: This function may panic, in which case an allocation will be
        //       leaked, but hwloc does not provide a way to liberate it...
        let children = find_children(self.topology());
        for child in children {
            let result = unsafe {
                errors::call_hwloc_int("hwloc_obj_add_other_obj_sets", || {
                    ffi::hwloc_obj_add_other_obj_sets(group.as_ptr(), child)
                })
            };
            if let Err(e) = result {
                return GroupInsertResult::Failed(e.into());
            }
        }

        // Adjust hwloc's propension to merge groups if instructed to do so
        if let Some(merge) = merge {
            let mut group_attributes = unsafe {
                group
                    .as_mut()
                    .raw_attributes()
                    .expect("Expected group attributes")
                    .group
            };
            match merge {
                GroupMerge::Never => group_attributes.prevent_merging(),
                GroupMerge::Always => group_attributes.favor_merging(),
            }
        }

        // Insert the group object into the topology
        let result = unsafe {
            errors::call_hwloc_ptr_mut("hwloc_topology_insert_group_object", || {
                ffi::hwloc_topology_insert_group_object(self.topology_mut_ptr(), group.as_ptr())
            })
        };
        match result {
            Ok(result) if result == group => GroupInsertResult::New(unsafe { group.as_mut() }),
            Ok(mut other) => GroupInsertResult::Existing(unsafe { other.as_mut() }),
            Err(e) => GroupInsertResult::Failed(GroupInsertError::InsertFailed(e)),
        }
    }

    /// Add a Misc object as a leaf of the topology
    ///
    /// A new Misc object will be created and inserted into the topology as
    /// a child of the node selected by `find_parent`. It is appended to the
    /// list of existing Misc children, without ever adding any intermediate
    /// hierarchy level. This is useful for annotating the topology without
    /// actually changing the hierarchy.
    ///
    /// `name` is supposed to be unique across all Misc objects in the topology.
    /// It will be duplicated to setup the new object attributes. If it contains
    /// some non-printable characters, then they will be dropped when exporting
    /// to XML.
    ///
    /// The new leaf object will not have any cpuset.
    ///
    /// # Errors
    ///
    /// None will be returned if an error occurs or if Misc objects are
    /// filtered out of the topology via [`TypeFilter::KeepNone`].
    #[doc(alias = "hwloc_topology_insert_misc_object")]
    pub fn insert_misc_object(
        &mut self,
        name: &str,
        find_parent: impl FnOnce(&Topology) -> &TopologyObject,
    ) -> Result<&mut TopologyObject, MiscInsertError> {
        // This is on the edge of violating Rust's aliasing rules, but I think
        // it should work out because...
        //
        // - We discard the original parent reference before handing over the
        //   *mut derived from it to hwloc, and thus we should not be able to
        //   trigger UB consequences linked to the fact that we modified
        //   something that we accessed via &T while the compiler is allowed to
        //   assume that what's behind said &T doesn't change.
        // - We hand over to hwloc a honestly acquired *mut RawTopology that
        //   legally allows it to modify anything behind it, including the
        //   *mut TopologyObject that `parent` points to.
        //
        // On the other hand, I think even with interior mutability it would be
        // impossible to devise a safe API that directly takes an
        // &TopologyObject to the `parent`, because unless we filled the entire
        // TopologyStruct with interior mutability (which we don't want to do
        // just to support this minor hwloc feature), the compiler would then be
        // allowed to assume that nothing changed behind that shared reference.
        // So letting the client keep hold of it would be highly problematic.
        //
        let parent = find_parent(self.topology()) as *const TopologyObject as *mut TopologyObject;
        let name = LibcString::new(name)?;
        unsafe {
            let mut ptr = errors::call_hwloc_ptr_mut("hwloc_topology_insert_misc_object", || {
                ffi::hwloc_topology_insert_misc_object(
                    self.topology_mut_ptr(),
                    parent,
                    name.borrow(),
                )
            })?;
            Ok(ptr.as_mut())
        }
    }
}

bitflags! {
    /// Flags to be given to [`TopologyEditor::restrict()`]
    #[repr(C)]
    pub struct RestrictFlags: c_ulong {
        /// Remove all objects that lost all resources of the target type
        ///
        /// By default, only objects that contain no PU and no memory are
        /// removed. This flag allows you to remove all objects that...
        ///
        /// - Do not have access to any CPU anymore when restricting by CpuSet
        /// - Do not have access to any memory anymore when restricting by NodeSet
        //
        // NOTE: This is a virtual flag that is cleared and mapped into
        //       `REMOVE_CPULESS` or `REMOVE_MEMLESS` as appropriate.
        const REMOVE_EMPTIED = c_ulong::MAX;

        /// Remove all objects that became CPU-less
        ///
        /// This is what `REMOVE_EMPTIED` maps into when restricting by `CpuSet`.
        #[doc(hidden)]
        const REMOVE_CPULESS = (1<<0);

        /// Restrict by NodeSet insted of by `CpuSet`
        ///
        /// This flag is automatically set when restricting by `NodeSet`.
        #[doc(hidden)]
        const BY_NODE_SET = (1<<3);

        /// Remove all objects that became memory-less
        ///
        /// This is what `REMOVE_EMPTIED` maps into when restricting by `NodeSet`.
        #[doc(hidden)]
        const REMOVE_MEMLESS = (1<<4);

        /// Move Misc objects to ancestors if their parents are removed during
        /// restriction
        ///
        /// If this flag is not set, Misc objects are removed when their parents
        /// are removed.
        const ADAPT_MISC = (1<<1);

        /// Move I/O objects to ancestors if their parents are removed
        /// during restriction
        ///
        /// If this flag is not set, I/O devices and bridges are removed when
        /// their parents are removed.
        const ADAPT_IO = (1<<2);
    }
}
//
impl Default for RestrictFlags {
    fn default() -> Self {
        Self::empty()
    }
}

/// Requested adjustment to the allowed set of PUs and NUMA nodes
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum AllowSet<'set> {
    /// Mark all objects as allowed in the topology
    All,

    /// Only allow objects that are available to the current process
    ///
    /// Requires [`BuildFlags::ASSUME_THIS_SYSTEM`] so that the set of available
    /// resources can actually be retrieved from the operating system.
    LocalRestrictions,

    /// Allow a custom set of objects
    ///
    /// You should provide at least one of `cpuset` and `memset`.
    Custom {
        cpuset: Option<&'set CpuSet>,
        nodeset: Option<&'set NodeSet>,
    },
}
//
impl fmt::Display for AllowSet<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AllowSet::Custom { cpuset, nodeset } => {
                write!(f, "Custom(")?;
                if let Some(cpuset) = cpuset {
                    write!(f, "{cpuset}")?;
                    if nodeset.is_some() {
                        write!(f, ", ")?;
                    }
                }
                if let Some(nodeset) = nodeset {
                    write!(f, "{nodeset}")?;
                }
                write!(f, ")")
            }
            other => write!(f, "{other:?}"),
        }
    }
}

/// Control merging of newly inserted groups with existing objects
#[derive(Copy, Clone, Debug, Display, Eq, Hash, PartialEq)]
pub enum GroupMerge {
    /// Prevent the hwloc core from ever merging this Group with another
    /// hierarchically-identical object
    ///
    /// This is useful when the Group itself describes an important feature that
    /// cannot be exposed anywhere else in the hierarchy.
    Never,

    /// Always discard this new group in favor of any existing Group with the
    /// same locality
    Always,
}

/// Result of inserting a Group object
#[derive(Debug)]
#[must_use]
pub enum GroupInsertResult<'topology> {
    /// New Group that was properly inserted
    New(&'topology mut TopologyObject),

    /// Existing object that already fulfilled the role of the proposed Group
    ///
    /// If the Group adds no hierarchy information, hwloc may merge or discard
    /// it in favor of existing topology object at the same location.
    Existing(&'topology mut TopologyObject),

    /// One hwloc API call failed
    Failed(GroupInsertError),
}

/// Error while inserting a Group object
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum GroupInsertError {
    /// `hwloc_topology_alloc_group_object` failed in an unspecified manner
    #[error(transparent)]
    AllocFailed(RawNullError),

    /// `hwloc_obj_add_other_obj_sets` failed in an unspecified manner
    #[error(transparent)]
    AddObjectsFailed(#[from] RawIntError),

    /// `hwloc_topology_insert_group_object` failed
    ///
    /// There are several documented reasons why this may happen
    ///
    /// - There are conflicting sets in the topology tree
    /// - Group objects are filtered out of the topology with
    ///   [`TypeFilter::KeepNone`]
    /// - The union of the cpusets and nodeset of all proposed children of the
    ///   Group object is empty.
    #[error(transparent)]
    InsertFailed(RawNullError),
}

/// Error while inserting a Misc object
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum MiscInsertError {
    /// Object name contains the NUL char, and is thus not compatible with C
    #[error("provided name contains the NUL char")]
    NameContainsNul,

    /// Insertion failed for another reason
    ///
    /// One documented reason for Misc object insertion failure is when Misc
    /// objects are filtered out of the topology via
    /// [`TypeFilter::KeepNone`]. However, the hwloc doc suggests that this
    /// process can fail for other reasons, without detailing them.
    #[error("{0}, maybe Misc objects are filtered out of the topology?")]
    HwlocError(#[from] RawNullError),
}
//
impl From<NulError> for MiscInsertError {
    fn from(_: NulError) -> Self {
        Self::NameContainsNul
    }
}

/// A method was passed an invalid parameter
#[derive(Copy, Clone, Debug, Default, Eq, Error, Hash, PartialEq)]
#[error("invalid parameter specified")]
pub struct InvalidParameter;

/// # Add distances between objects
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__add.html
impl TopologyEditor<'_> {
    /// Create a new object distances matrix
    ///
    /// `kind` specifies the kind of distance. Kind
    /// [`DistancesKind::HETEROGENEOUS_TYPES`] will be automatically set
    /// according to objects having different types, so you do not need to set
    /// it and should not do so.
    ///
    /// `flags` can be used to request the grouping of existing objects based on
    /// distance.
    ///
    /// The `collect_objects_and_distances` callback should query the geometry
    /// to collect references to the objects of interest, and produce the
    /// corresponding distance matrix. If there are N output objects, then there
    /// should be N.pow(2) output distances.
    ///
    /// Distances must be provided in sender-major order: the distance from
    /// object 0 to object 1, then object 0 to object 2, ... all the way to
    /// object N, and then from object 1 to object 0, and so on.
    ///
    /// # Errors
    ///
    /// - [`NameContainsNul`](AddDistancesError::NameContainsNul) if the
    ///   provided `name` contains NUL chars
    /// - [`BadKind`](AddDistancesError::BadKind) if the provided `kind`
    ///   contains [`HETEROGENEOUS_TYPES`](DistancesKind::HETEROGENEOUS_TYPES).
    /// - [`BadObjectsCount`](AddDistancesError::BadObjectsCount) if less
    ///   than 2 or more than `u32::MAX` objects are returned by the callback
    ///   (hwloc does not support such configurations).
    /// - [`BadDistancesCount`](AddDistancesError::BadDistancesCount) if
    ///   the number of distances returned by the callback is not compatible
    ///   with the number of objects (it should be the square of it).
    /// - [`CreateFailed`](AddDistancesError::CreateFailed),
    ///   [`AddValuesFailed`](AddDistancesError::AddValuesFailed) or
    ///   [`CommitFailed`](AddDistancesError::CommitFailed) if hwloc failed
    ///   for another (undocumented) reason.
    #[doc(alias = "hwloc_distances_add_create")]
    #[doc(alias = "hwloc_distances_add_values")]
    #[doc(alias = "hwloc_distances_add_commit")]
    pub fn add_distances(
        &mut self,
        name: Option<&str>,
        kind: DistancesKind,
        flags: AddDistancesFlags,
        collect_objects_and_distances: impl FnOnce(
            &Topology,
        ) -> (Vec<Option<&TopologyObject>>, Vec<u64>),
    ) -> Result<(), AddDistancesError> {
        // Prepare arguments for C consumption and validate them
        let name = name.map(LibcString::new).transpose()?;
        let name = name.map(|lcs| lcs.borrow()).unwrap_or(ptr::null());
        //
        if kind.contains(DistancesKind::HETEROGENEOUS_TYPES) {
            return Err(AddDistancesError::BadKind);
        }
        let kind = kind.bits();
        //
        let create_add_flags = 0;
        let commit_flags = flags.bits();
        //
        let (objects, distances) = collect_objects_and_distances(self.topology());
        if objects.len() < 2 {
            return Err(AddDistancesError::BadObjectsCount(objects.len()));
        }
        let Ok(nbobjs) = c_uint::try_from(objects.len()) else {
            return Err(AddDistancesError::BadObjectsCount(objects.len()))
        };
        let expected_distances_len = objects.len().pow(2);
        if distances.len() != expected_distances_len {
            return Err(AddDistancesError::BadDistancesCount {
                expected_distances_len,
                actual_distances_len: distances.len(),
            });
        }
        let objs = objects.as_ptr() as *const *const TopologyObject;
        let values = distances.as_ptr() as *const u64;

        // Create new empty distances structure
        let handle = unsafe {
            errors::call_hwloc_ptr_mut("hwloc_distances_add_create", || {
                ffi::hwloc_distances_add_create(
                    self.topology_mut_ptr(),
                    name,
                    kind,
                    create_add_flags,
                )
            })?
        };

        // Add objects to the distance structure
        let result = unsafe {
            errors::call_hwloc_int("hwloc_distances_add_values", || {
                ffi::hwloc_distances_add_values(
                    self.topology_mut_ptr(),
                    handle.as_ptr(),
                    nbobjs,
                    objs,
                    values,
                    create_add_flags,
                )
            })
        };
        match result {
            Ok(0) => {}
            // Per hwloc documentation, handle is auto-freed on failure
            Err(e) => return Err(AddDistancesError::AddValuesFailed(e)),
            Ok(other) => panic!("Unexpected result from hwloc_distances_add_values: {other}"),
        }

        // Finalize the distance structure and insert it into the topology
        let result = unsafe {
            errors::call_hwloc_int("hwloc_distances_add_commit", || {
                ffi::hwloc_distances_add_commit(
                    self.topology_mut_ptr(),
                    handle.as_ptr(),
                    commit_flags,
                )
            })
        };
        match result {
            Ok(0) => Ok(()),
            // Per hwloc documentation, handle is auto-freed on failure
            Err(e) => Err(AddDistancesError::CommitFailed(e)),
            Ok(other) => panic!("Unexpected result from hwloc_distances_add_commit: {other}"),
        }
    }
}

bitflags! {
    /// Flags to be given to [`TopologyEditor::add_distances()`]
    #[repr(C)]
    pub struct AddDistancesFlags: c_ulong {
        /// Try to group objects based on the newly provided distance information
        ///
        /// This is ignored for distances between objects of different types.
        #[doc(alias = "HWLOC_DISTANCES_ADD_FLAG_GROUP")]
        const GROUP = (1<<0);

        /// Like Group, but consider the distance values as inaccurate and relax
        /// the comparisons during the grouping algorithms. The actual accuracy
        /// may be modified through the HWLOC_GROUPING_ACCURACY environment
        /// variable (see
        /// [Environment Variables](https://hwloc.readthedocs.io/en/v2.9/envvar.html)).
        #[doc(alias = "HWLOC_DISTANCES_ADD_FLAG_GROUP_INACCURATE")]
        const GROUP_INACCURATE = (1<<0) | (1<<1);
    }
}

impl Default for AddDistancesFlags {
    fn default() -> Self {
        Self::empty()
    }
}

/// Failed to add a new distance matrix to the topology
#[derive(Copy, Clone, Debug, Eq, Error, Hash, PartialEq)]
pub enum AddDistancesError {
    /// Provided `name` contains NUL chars
    #[error("provided name contains NUL chars")]
    NameContainsNul,

    /// Provided `kind` contains [`DistancesKind::HETEROGENEOUS_TYPES`]
    ///
    /// You should not set this kind yourself, it will be automatically set by
    /// hwloc through scanning of the provided object list.
    #[error("provided kind contains HETEROGENEOUS_TYPES")]
    BadKind,

    /// Provided callback returned too many or too few objects
    ///
    /// hwloc only supports distances matrices with 2 to `u32::MAX` objects.
    #[error("callback emitted <2 or >u32::MAX objects: {0}")]
    BadObjectsCount(usize),

    /// Provided callback returned incompatible objects and distances arrays
    ///
    /// If we denote N the length of the objects array, the distances array
    /// should contain N.pow(2) elements.
    #[error("callback emitted an invalid amount of distances (expected {expected_distances_len}, got {actual_distances_len})")]
    BadDistancesCount {
        expected_distances_len: usize,
        actual_distances_len: usize,
    },

    /// `hwloc_distances_add_create` failed in an unspecified manner
    #[error(transparent)]
    CreateFailed(#[from] RawNullError),

    /// `hwloc_distances_add_values` failed in an unspecified manner
    #[error(transparent)]
    AddValuesFailed(RawIntError),

    /// `hwloc_distances_add_commit` failed in an unspecified manner
    #[error(transparent)]
    CommitFailed(RawIntError),
}
//
impl From<NulError> for AddDistancesError {
    fn from(_: NulError) -> Self {
        Self::NameContainsNul
    }
}

/// Handle to a new distances structure during its addition to the topology
pub(crate) type DistancesAddHandle = *mut c_void;

/// # Remove distances between objects
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__remove.html
impl TopologyEditor<'_> {
    /// Remove a single distances matrix from the topology
    ///
    /// The distances matrix to be removed can be selected using the
    /// `find_distances` callback.
    #[doc(alias = "hwloc_distances_release_remove")]
    pub fn remove_distances(
        &mut self,
        find_distances: impl FnOnce(&Topology) -> Distances,
    ) -> Result<(), RawIntError> {
        let distances = find_distances(self.topology()).into_inner();
        unsafe {
            errors::call_hwloc_int("hwloc_distances_release_remove", || {
                ffi::hwloc_distances_release_remove(self.topology_mut_ptr(), distances)
            })
        }
        .map(|_| ())
    }

    /// Remove all distance matrices from a topology
    ///
    /// If these distances were used to group objects, these additional Group
    /// objects are not removed from the topology.
    #[doc(alias = "hwloc_distances_remove")]
    pub fn remove_all_distances(&mut self) -> Result<(), RawIntError> {
        unsafe {
            errors::call_hwloc_int("hwloc_distances_remove", || {
                ffi::hwloc_distances_remove(self.topology_mut_ptr())
            })
        }
        .map(|_| ())
    }

    /// Remove distance matrices for objects at a specific depth in the topology
    ///
    /// See also [`TopologyEditor::remove_all_distances()`].
    #[doc(alias = "hwloc_distances_remove_by_depth")]
    pub fn remove_distances_at_depth(
        &mut self,
        depth: impl Into<Depth>,
    ) -> Result<(), RawIntError> {
        unsafe {
            errors::call_hwloc_int("hwloc_distances_remove_by_depth", || {
                ffi::hwloc_distances_remove_by_depth(self.topology_mut_ptr(), depth.into().into())
            })
        }
        .map(|_| ())
    }

    /// Remove distance matrices for objects of a specific type in the topology
    ///
    /// See also [`TopologyEditor::remove_all_distances()`].
    #[doc(alias = "hwloc_distances_remove_by_type")]
    pub fn remove_distances_with_type(&mut self, ty: ObjectType) -> Result<(), RawIntError> {
        let topology = self.topology();
        if let Ok(depth) = topology.depth_for_type(ty) {
            self.remove_distances_at_depth(depth)?;
        } else {
            let depths = (0..topology.depth())
                .map(Depth::from)
                .filter_map(|depth| {
                    let depth_ty = topology
                        .type_at_depth(depth)
                        .expect("A type should be present at this depth");
                    (depth_ty == ty).then_some(depth)
                })
                .collect::<Vec<_>>();
            for depth in depths {
                self.remove_distances_at_depth(depth)?;
            }
        }
        Ok(())
    }
}

/// # Managing memory attributes
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs__manage.html
impl<'topology> TopologyEditor<'topology> {
    /// Register a new memory attribute
    ///
    /// # Panics
    ///
    /// - `name` contains NUL chars
    #[doc(alias = "hwloc_memattr_register")]
    pub fn register_memory_attribute<'name>(
        &mut self,
        name: &'name str,
        flags: MemoryAttributeFlags,
    ) -> Result<MemoryAttributeBuilder<'_, 'topology>, MemoryAttributeRegisterError> {
        if !flags.is_valid() {
            return Err(MemoryAttributeRegisterError::BadFlags(flags));
        }
        let name = LibcString::new(name)?;
        let mut id = MemoryAttributeID::default();
        let result = unsafe {
            errors::call_hwloc_int("hwloc_memattr_register", || {
                ffi::hwloc_memattr_register(
                    self.topology_mut_ptr(),
                    name.borrow(),
                    flags.bits(),
                    &mut id,
                )
            })
        };
        match result {
            Ok(_) => Ok(MemoryAttributeBuilder {
                editor: self,
                flags,
                id,
            }),
            Err(RawIntError::Errno {
                api: _,
                errno: Some(Errno(EBUSY)),
            }) => Err(MemoryAttributeRegisterError::AlreadyExists),
            Err(e) => Err(MemoryAttributeRegisterError::HwlocError(e)),
        }
    }
}

/// Error returned when trying to create an memory attribute
#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
pub enum MemoryAttributeRegisterError {
    /// Specified flags are not correct
    ///
    /// You must specify exactly one of [`MemoryAttributeFlags::HIGHER_IS_BEST`]
    /// and [`MemoryAttributeFlags::LOWER_IS_BEST`].
    #[error("flags {0:?} do not contain exactly one of the _IS_BEST flags")]
    BadFlags(MemoryAttributeFlags),

    /// Provided `name` contains NUL chars
    #[error("provided name contains NUL chars")]
    NameContainsNul,

    /// A memory attribute with this name already exists
    #[error("a memory attribute with this name already exists")]
    AlreadyExists,

    /// An unkown hwloc error has occured
    #[error(transparent)]
    HwlocError(#[from] RawIntError),
}
//
impl From<NulError> for MemoryAttributeRegisterError {
    fn from(_: NulError) -> Self {
        Self::NameContainsNul
    }
}

/// Mechanism to configure a memory attribute
pub struct MemoryAttributeBuilder<'editor, 'topology> {
    editor: &'editor mut TopologyEditor<'topology>,
    flags: MemoryAttributeFlags,
    id: MemoryAttributeID,
}
//
impl MemoryAttributeBuilder<'_, '_> {
    /// Set attribute values for (initiator, target node) pairs
    ///
    /// Initiators should be provided if and only if this memory attribute has
    /// an initiator (flag [`MemoryAttributeFlags::NEED_INITIATOR`] was set at
    /// registration time. In that case, there should be as many initiators as
    /// there are targets and attribute values.
    ///
    /// # Errors
    ///
    /// - [`BadInitiators`] if initiators are specified for attributes that
    ///   don't have them, are not specified for attributes that have them, or
    ///   if there are more or less initiators than (target, value) pairs.
    ///
    /// [`BadInitiators`]: MemoryAttributeSetValuesError::BadInitiators
    #[doc(alias = "hwloc_memattr_set_value")]
    pub fn set_values(
        &mut self,
        find_values: impl FnOnce(
            &Topology,
        ) -> (
            Option<Vec<MemoryAttributeLocation>>,
            Vec<(&TopologyObject, u64)>,
        ),
    ) -> Result<(), MemoryAttributeSetValuesError> {
        // Run user callback, validate results for correctness
        let (initiators, targets_and_values) = find_values(self.editor.topology());
        if !(self.flags.contains(MemoryAttributeFlags::NEED_INITIATOR) ^ initiators.is_some()) {
            return Err(MemoryAttributeSetValuesError::BadInitiators);
        }
        let size_ok = match (&initiators, &targets_and_values) {
            (Some(initiators), targets_and_values)
                if initiators.len() == targets_and_values.len() =>
            {
                true
            }
            (None, _) => true,
            _ => false,
        };
        if !size_ok {
            return Err(MemoryAttributeSetValuesError::BadInitiators);
        }

        // Post-process results to fit hwloc and borrow checker expectations
        let initiators = initiators.map(|vec| {
            vec.into_iter()
                .map(MemoryAttributeLocation::into_raw)
                .collect::<Vec<_>>()
        });
        let initiator_ptrs = initiators
            .iter()
            .flatten()
            .map(|initiator_ref| initiator_ref as *const RawLocation)
            .chain(std::iter::repeat_with(ptr::null));
        let target_ptrs_and_values = targets_and_values
            .into_iter()
            .map(|(target_ref, value)| (target_ref as *const TopologyObject, value))
            .collect::<Vec<_>>();

        // Set memory attribute values
        for (initiator_ptr, (target_ptr, value)) in
            initiator_ptrs.zip(target_ptrs_and_values.into_iter())
        {
            unsafe {
                errors::call_hwloc_int("hwloc_memattr_set_value", || {
                    ffi::hwloc_memattr_set_value(
                        self.editor.topology_mut_ptr(),
                        self.id,
                        target_ptr,
                        initiator_ptr,
                        0,
                        value,
                    )
                })?;
            }
        }
        Ok(())
    }
}

/// Error returned when trying to create an memory attribute
#[derive(Copy, Clone, Debug, Error)]
pub enum MemoryAttributeSetValuesError {
    /// Incorrect initiators were emitted
    ///
    /// Either an initiator had to be specified and was not specified, or the
    /// requested attribute has no notion of initiator (e.g. Capacity) but an
    /// initiator was specified nonetheless.
    ///
    /// This error is also emitted if the array of initiators is not sized like
    /// the main (target, value) array.
    #[error("incorrect initiators")]
    BadInitiators,

    /// Unexpected hwloc API result
    #[error(transparent)]
    UnexpectedResult(#[from] RawIntError),
}

/// # Kinds of CPU cores
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpukinds.html
impl<'topology> TopologyEditor<'topology> {
    /// Register a kind of CPU in the topology.
    ///
    /// Mark the PUs listed in `cpuset` as being of the same kind with respect
    /// to the given attributes.
    ///
    /// `forced_efficiency` should be `None` if unknown. Otherwise it is an
    /// abstracted efficiency value to enforce the ranking of all kinds if all
    /// of them have valid (and different) efficiencies.
    ///
    /// Note that the efficiency reported later by [`Topology::cpu_kinds()`] may
    /// differ because hwloc will scale efficiency values down to between 0 and
    /// the number of kinds minus 1.
    ///
    /// If `cpuset` overlaps with some existing kinds, those might get modified
    /// or split. For instance if existing kind A contains PUs 0 and 1, and one
    /// registers another kind for PU 1 and 2, there will be 3 resulting kinds:
    /// existing kind A is restricted to only PU 0; new kind B contains only PU
    /// 1 and combines information from A and from the newly-registered kind;
    /// new kind C contains only PU 2 and only gets information from the
    /// newly-registered kind.
    //
    // NOTE: Not exposing info setting at the moment because I don't know how to
    //       make it safe with respect to string allocation/liberation.
    #[doc(alias = "hwloc_cpukinds_register")]
    pub fn register_cpu_kind(
        &mut self,
        cpuset: &CpuSet,
        forced_efficiency: Option<CpuEfficiency>,
    ) -> Result<(), RawIntError> {
        errors::call_hwloc_int("hwloc_cpukinds_register", || unsafe {
            let forced_efficiency = forced_efficiency
                .map(|eff| c_int::try_from(eff).unwrap_or(c_int::MAX))
                .unwrap_or(-1);
            ffi::hwloc_cpukinds_register(
                self.topology_mut_ptr(),
                cpuset.as_ptr(),
                forced_efficiency,
                0,
                ptr::null(),
                0,
            )
        })
        .map(|_| ())
    }
}

// NOTE: Do not implement traits like AsRef/Deref/Borrow, that would be unsafe
//       as it would expose &Topology with unevaluated lazy hwloc caches.
