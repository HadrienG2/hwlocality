//! Modifying a loaded Topology

use super::RawTopology;
use crate::{
    bitmap::{BitmapKind, SpecializedBitmap},
    cpu::cpuset::CpuSet,
    errors::{self, HybridError, NulError, ParameterError, RawHwlocError},
    ffi::{self, LibcString},
    memory::nodeset::NodeSet,
    objects::TopologyObject,
    topology::Topology,
};
#[cfg(doc)]
use crate::{
    objects::types::ObjectType,
    topology::builder::{BuildFlags, TopologyBuilder, TypeFilter},
};
use bitflags::bitflags;
use derive_more::Display;
use libc::{EINVAL, ENOMEM};
use std::{
    ffi::c_ulong,
    fmt::{self, Write},
    panic::{AssertUnwindSafe, UnwindSafe},
    ptr,
};
use thiserror::Error;

/// # Modifying a loaded `Topology`
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__tinker.html
impl Topology {
    /// Modify this topology
    ///
    /// hwloc employs lazy caching patterns that do not interact well with
    /// Rust's shared XOR mutable aliasing model. This API lets you safely
    /// modify the active `Topology` through a [`TopologyEditor`] proxy object,
    /// with the guarantee that by the time `Topology::edit()` returns, the
    /// `Topology` will be back in a state where it is safe to use `&self` again.
    ///
    /// In general, the hwlocality binding optimizes the ergonomics and
    /// performance of reading and using topologies at the expense of making
    /// them harder and slower to edit. If there were a strong need for more
    /// efficient topology editing, the right thing to do would be to set up an
    /// alternate hwloc Rust binding optimized for that, with some code sharing
    /// with respect to hwlocality.
    #[doc(alias = "hwloc_topology_refresh")]
    pub fn edit<R>(&mut self, edit: impl UnwindSafe + FnOnce(&mut TopologyEditor) -> R) -> R {
        // Set up topology editing
        let mut editor = TopologyEditor::new(self);
        let mut editor = AssertUnwindSafe(&mut editor);

        // Run the user-provided edit callback, catching panics
        let result = std::panic::catch_unwind(move || edit(&mut editor));

        // Force eager evaluation of all caches
        self.refresh();

        // Return user callback result or resume unwinding as appropriate
        match result {
            Ok(result) => result,
            Err(e) => std::panic::resume_unwind(e),
        }
    }

    /// Force eager evaluation of all lazily evaluated caches in preparation for
    /// using or exposing &self
    ///
    /// # Aborts
    ///
    /// A process abort will occur if this fails as we must not let an invalid
    /// `Topology` state escape, not even via unwinding, as that would result in
    /// undefined behavior (mutation which the compiler assumes will not happen).
    pub(crate) fn refresh(&mut self) {
        let result = errors::call_hwloc_int_normal("hwloc_topology_refresh", || unsafe {
            ffi::hwloc_topology_refresh(self.as_mut_ptr())
        });
        if let Err(e) = result {
            eprintln!("Failed to refresh topology ({e}), so it's stuck in a state that violates Rust aliasing rules, aborting...");
            std::process::abort()
        }
        if cfg!(debug_assertions) {
            unsafe { ffi::hwloc_topology_check(self.as_ptr()) }
        }
    }
}

/// Proxy for modifying a `Topology`
///
/// This proxy object is carefully crafted to only allow operations that are
/// safe while modifying a topology and minimize the number of times the hwloc
/// lazy caches will need to be refreshed.
///
/// The API is broken down into sections roughly following the structure of the
/// upstream hwloc documentation:
///
/// - [General-purpose utilities](#general-purpose-utilities)
/// - [Basic modifications](#basic-modifications)
#[cfg_attr(
    feature = "hwloc-2_5_0",
    doc = "- [Add distances between objects](#add-distances-between-objects) (hwloc 2.5+)"
)]
/// - [Remove distances between objects](#remove-distances-between-objects)
/// - [Managing memory attributes](#managing-memory-attributes)
#[cfg_attr(
    feature = "hwloc-2_4_0",
    doc = "- [Kinds of CPU cores](#kinds-of-cpu-cores) (hwloc 2.4+)"
)]
//
// NOTE: Not all of the TopologyEditor API is implemented in the core editor.rs
//       module. Instead, functionality which is very strongly related to
//       one other code module is implemented in that module, leaving the editor
//       module focused on basic lifecycle and cross-cutting issues.
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
    pub(crate) fn topology_mut(&mut self) -> &mut Topology {
        self.0
    }

    /// Contained hwloc topology pointer (for interaction with hwloc)
    pub(crate) fn topology_mut_ptr(&mut self) -> *mut RawTopology {
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
    /// Restricting the topology removes some locality information, hence the
    /// remaining objects may get reordered (including PUs and NUMA nodes), and
    /// their logical indices may change.
    ///
    /// This call may not be reverted by restricting back to a larger set. Once
    /// dropped during restriction, objects may not be brought back, except by
    /// loading another topology with [`Topology::new()`] or [`TopologyBuilder`].
    ///
    /// # Errors
    ///
    /// Err([`ParameterError`]) will be returned if the input set is
    /// invalid. The topology is not modified in this case.
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
    ) -> Result<(), ParameterError<Set::Owned>> {
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
        let result = errors::call_hwloc_int_normal("hwloc_topology_restrict", || unsafe {
            ffi::hwloc_topology_restrict(
                self.topology_mut_ptr(),
                set.as_ref().as_ptr(),
                flags.bits(),
            )
        });
        match result {
            Ok(_) => Ok(()),
            Err(
                raw_err @ RawHwlocError {
                    api: _,
                    errno: Some(errno),
                },
            ) => match errno.0 {
                EINVAL => Err(ParameterError::from(set.to_owned())),
                ENOMEM => {
                    eprintln!("Topology stuck in an invalid state, must abort");
                    std::process::abort()
                }
                _ => unreachable!("{raw_err}"),
            },
            Err(raw_err) => unreachable!("{raw_err}"),
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
    ///
    /// # Errors
    ///
    /// - [`BadAllowSet`] if an `AllowSet` with neither a `cpuset` nor a
    ///   `nodeset` is passed in.
    #[doc(alias = "hwloc_topology_allow")]
    pub fn allow(&mut self, allow_set: AllowSet) -> Result<(), HybridError<BadAllowSet>> {
        // Convert AllowSet into a valid `hwloc_topology_allow` configuration
        let (cpuset, nodeset, flags) = match allow_set {
            AllowSet::All => (ptr::null(), ptr::null(), 1 << 0),
            AllowSet::LocalRestrictions => (ptr::null(), ptr::null(), 1 << 1),
            AllowSet::Custom { cpuset, nodeset } => {
                let cpuset = cpuset.map(|cpuset| cpuset.as_ptr()).unwrap_or(ptr::null());
                let nodeset = nodeset
                    .map(|nodeset| nodeset.as_ptr())
                    .unwrap_or(ptr::null());
                if cpuset.is_null() && nodeset.is_null() {
                    return Err(BadAllowSet.into());
                }
                (cpuset, nodeset, 1 << 2)
            }
        };

        // Call hwloc
        errors::call_hwloc_int_normal("hwloc_topology_allow", || unsafe {
            ffi::hwloc_topology_allow(self.topology_mut_ptr(), cpuset, nodeset, flags)
        })
        .map(std::mem::drop)
        .map_err(HybridError::Hwloc)
    }

    /// Add more structure to the topology by adding an intermediate [`Group`]
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
    ///
    /// After insertion, [`TopologyObject::set_subtype()`] can be used to
    /// display something other than "Group" as the type name for this object in
    /// `lstopo`, and custom name/value info pairs may be added using
    /// [`TopologyObject::add_info()`].
    ///
    /// [`Group`]: ObjectType::Group
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
        let group = errors::call_hwloc_ptr_mut("hwloc_topology_alloc_group_object", || unsafe {
            ffi::hwloc_topology_alloc_group_object(self.topology_mut_ptr())
        });
        let mut group = match group {
            Ok(group) => group,
            Err(e) => return GroupInsertResult::Failed(e),
        };

        // Expand cpu sets and node sets to cover designated children
        // NOTE: This function may panic, in which case an allocation will be
        //       leaked, but hwloc does not provide a way to liberate it...
        let children = find_children(self.topology());
        for child in children {
            let result = errors::call_hwloc_int_normal("hwloc_obj_add_other_obj_sets", || unsafe {
                ffi::hwloc_obj_add_other_obj_sets(group.as_ptr(), child)
            });
            if let Err(e) = result {
                return GroupInsertResult::Failed(e);
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
        let result = errors::call_hwloc_ptr_mut("hwloc_topology_insert_group_object", || unsafe {
            ffi::hwloc_topology_insert_group_object(self.topology_mut_ptr(), group.as_ptr())
        });
        match result {
            Ok(result) if result == group => GroupInsertResult::New(unsafe { group.as_mut() }),
            Ok(mut other) => GroupInsertResult::Existing(unsafe { other.as_mut() }),
            Err(e) => GroupInsertResult::Failed(e),
        }
    }

    /// Add a [`Misc`] object as a leaf of the topology
    ///
    /// A new [`Misc`] object will be created and inserted into the topology as
    /// a child of the node selected by `find_parent`. It is appended to the
    /// list of existing Misc children, without ever adding any intermediate
    /// hierarchy level. This is useful for annotating the topology without
    /// actually changing the hierarchy.
    ///
    /// `name` is supposed to be unique across all [`Misc`] objects in the
    /// topology. If it contains some non-printable characters, then they will
    /// be dropped when exporting to XML.
    ///
    /// The new leaf object will not have any cpuset.
    ///
    /// # Errors
    ///
    /// This method will fail with an unspecified hwloc error if Misc objects
    /// are filtered out of the topology via [`TypeFilter::KeepNone`].
    ///
    /// [`Misc`]: ObjectType::Misc
    #[doc(alias = "hwloc_topology_insert_misc_object")]
    pub fn insert_misc_object(
        &mut self,
        name: &str,
        find_parent: impl FnOnce(&Topology) -> &TopologyObject,
    ) -> Result<&mut TopologyObject, HybridError<NulError>> {
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
        let parent: *const TopologyObject = find_parent(self.topology());
        let parent = parent.cast_mut();
        let name = LibcString::new(name)?;
        let mut ptr = errors::call_hwloc_ptr_mut("hwloc_topology_insert_misc_object", || unsafe {
            ffi::hwloc_topology_insert_misc_object(self.topology_mut_ptr(), parent, name.borrow())
        })
        .map_err(HybridError::Hwloc)?;
        Ok(unsafe { ptr.as_mut() })
    }
}

bitflags! {
    /// Flags to be given to [`TopologyEditor::restrict()`]
    #[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
    #[doc(alias = "hwloc_restrict_flags_e")]
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
        #[doc(alias = "HWLOC_RESTRICT_FLAG_REMOVE_CPULESS")]
        #[doc(alias = "HWLOC_RESTRICT_FLAG_REMOVE_MEMLESS")]
        const REMOVE_EMPTIED = c_ulong::MAX;

        /// Remove all objects that became CPU-less
        //
        // NOTE: This is what `REMOVE_EMPTIED` maps into when restricting by `CpuSet`.
        #[doc(hidden)]
        const REMOVE_CPULESS = (1<<0);

        /// Restrict by NodeSet insted of by `CpuSet`
        //
        // NOTE: This flag is automatically set when restricting by `NodeSet`.
        #[doc(hidden)]
        const BY_NODE_SET = (1<<3);

        /// Remove all objects that became memory-less
        //
        // NOTE: This is what `REMOVE_EMPTIED` maps into when restricting by `NodeSet`.
        #[doc(hidden)]
        const REMOVE_MEMLESS = (1<<4);

        /// Move Misc objects to ancestors if their parents are removed during
        /// restriction
        ///
        /// If this flag is not set, Misc objects are removed when their parents
        /// are removed.
        #[doc(alias = "HWLOC_RESTRICT_FLAG_ADAPT_MISC")]
        const ADAPT_MISC = (1<<1);

        /// Move I/O objects to ancestors if their parents are removed
        /// during restriction
        ///
        /// If this flag is not set, I/O devices and bridges are removed when
        /// their parents are removed.
        #[doc(alias = "HWLOC_RESTRICT_FLAG_ADAPT_IO")]
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
#[doc(alias = "hwloc_allow_flags_e")]
pub enum AllowSet<'set> {
    /// Mark all objects as allowed in the topology
    #[doc(alias = "HWLOC_ALLOW_FLAG_ALL")]
    All,

    /// Only allow objects that are available to the current process
    ///
    /// Requires [`BuildFlags::ASSUME_THIS_SYSTEM`] so that the set of available
    /// resources can actually be retrieved from the operating system.
    #[doc(alias = "HWLOC_ALLOW_FLAG_LOCAL_RESTRICTIONS")]
    LocalRestrictions,

    /// Allow a custom set of objects
    ///
    /// You should provide at least one of `cpuset` and `memset`.
    #[doc(alias = "HWLOC_ALLOW_FLAG_CUSTOM")]
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
                let mut s = String::from("Custom(");
                if let Some(cpuset) = cpuset {
                    write!(s, "{cpuset}")?;
                    if nodeset.is_some() {
                        s.push_str(", ");
                    }
                }
                if let Some(nodeset) = nodeset {
                    write!(s, "{nodeset}")?;
                }
                s.push(')');
                f.pad(&s)
            }
            other => <Self as fmt::Debug>::fmt(other, f),
        }
    }
}

/// Attempted to change the allowed set of PUs and NUMA nodes without saying how
#[derive(Copy, Clone, Debug, Default, Eq, Error, Hash, PartialEq)]
#[error("AllowSet::Custom cannot have both empty cpuset AND nodeset members")]
pub struct BadAllowSet;

/// Control merging of newly inserted groups with existing objects
#[derive(Copy, Clone, Debug, Display, Eq, Hash, PartialEq)]
pub enum GroupMerge {
    /// Prevent the hwloc core from ever merging this Group with another
    /// hierarchically-identical object
    ///
    /// This is useful when the Group itself describes an important feature that
    /// cannot be exposed anywhere else in the hierarchy.
    #[doc(alias = "hwloc_group_attr_s::dont_merge")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_group_attr_s::dont_merge")]
    Never,

    /// Always discard this new group in favor of any existing Group with the
    /// same locality
    #[doc(alias = "hwloc_group_attr_s::kind")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_group_attr_s::kind")]
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
    ///
    /// This can happen if there are conflicting sets in the topology tree,
    /// if [`Group`](ObjectType::Group) objects are filtered out of the
    /// topology through [`TypeFilter::KeepNone`], or if the effective CPU set
    /// or NUMA node set ends up being empty.
    Failed(RawHwlocError),
}

// NOTE: Do not implement traits like AsRef/Deref/Borrow, that would be unsafe
//       as it would expose &Topology with unevaluated lazy hwloc caches.
