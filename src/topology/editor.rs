//! Modifying a loaded Topology
// TODO: Long-form description

use crate::{
    bitmap::{BitmapKind, SpecializedBitmap},
    cpu::cpuset::CpuSet,
    errors::{self, ForeignObject, HybridError, ParameterError, RawHwlocError},
    ffi::{self, string::LibcString},
    memory::nodeset::NodeSet,
    object::{attributes::GroupAttributes, TopologyObject},
    topology::Topology,
};
#[cfg(doc)]
use crate::{
    object::types::ObjectType,
    topology::builder::{BuildFlags, TopologyBuilder, TypeFilter},
};
use bitflags::bitflags;
use derive_more::Display;
use hwlocality_sys::{
    hwloc_obj, hwloc_restrict_flags_e, hwloc_topology, HWLOC_ALLOW_FLAG_ALL,
    HWLOC_ALLOW_FLAG_CUSTOM, HWLOC_ALLOW_FLAG_LOCAL_RESTRICTIONS, HWLOC_RESTRICT_FLAG_ADAPT_IO,
    HWLOC_RESTRICT_FLAG_ADAPT_MISC, HWLOC_RESTRICT_FLAG_BYNODESET,
    HWLOC_RESTRICT_FLAG_REMOVE_CPULESS, HWLOC_RESTRICT_FLAG_REMOVE_MEMLESS,
};
use libc::{EINVAL, ENOMEM};
use std::{
    ffi::c_ulong,
    fmt::{self, Write},
    panic::{AssertUnwindSafe, UnwindSafe},
    ptr::{self, NonNull},
};
use thiserror::Error;

/// # Modifying a loaded `Topology`
//
// --- Implementation details ---
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
    /// them harder and slower to edit. If a strong need for easier or more
    /// efficient topology editing emerged, the right thing to do would
    /// probably be to set up an alternate hwloc Rust binding optimized for
    /// that, sharing as much code as possible with hwlocality.
    #[doc(alias = "hwloc_topology_refresh")]
    pub fn edit<R>(&mut self, edit: impl UnwindSafe + FnOnce(&mut TopologyEditor<'_>) -> R) -> R {
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
            hwlocality_sys::hwloc_topology_refresh(self.as_mut_ptr())
        });
        if let Err(e) = result {
            eprintln!("Failed to refresh topology ({e}), so it's stuck in a state that violates Rust aliasing rules, aborting...");
            std::process::abort()
        }
        if cfg!(debug_assertions) {
            unsafe { hwlocality_sys::hwloc_topology_check(self.as_ptr()) }
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
// --- Implementation details
//
// Not all of the TopologyEditor API is implemented in the core editor.rs
// module. Instead, functionality which is very strongly related to one other
// code module is implemented in that module, leaving the editor module focused
// on basic lifecycle and cross-cutting issues.
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
    pub(crate) fn topology_mut_ptr(&mut self) -> *mut hwloc_topology {
        self.topology_mut().as_mut_ptr()
    }
}

/// # Basic modifications
//
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__tinker.html
impl<'topology> TopologyEditor<'topology> {
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
            hwlocality_sys::hwloc_topology_restrict(
                self.topology_mut_ptr(),
                set.as_ref().as_ptr(),
                flags.bits(),
            )
        });
        match result {
            Ok(_) => Ok(()),
            Err(
                raw_err @ RawHwlocError {
                    errno: Some(errno), ..
                },
            ) => match errno.0 {
                EINVAL => Err(ParameterError::from(set.to_owned())),
                ENOMEM => {
                    eprintln!("Topology stuck in an invalid state, must abort");
                    std::process::abort()
                }
                _ => unreachable!("Unexpected hwloc error: {raw_err}"),
            },
            Err(raw_err) => unreachable!("Unexpected hwloc error: {raw_err}"),
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
    pub fn allow(&mut self, allow_set: AllowSet<'_>) -> Result<(), HybridError<BadAllowSet>> {
        // Convert AllowSet into a valid `hwloc_topology_allow` configuration
        let (cpuset, nodeset, flags) = match allow_set {
            AllowSet::All => (ptr::null(), ptr::null(), HWLOC_ALLOW_FLAG_ALL),
            AllowSet::LocalRestrictions => (
                ptr::null(),
                ptr::null(),
                HWLOC_ALLOW_FLAG_LOCAL_RESTRICTIONS,
            ),
            AllowSet::Custom { cpuset, nodeset } => {
                let cpuset = cpuset.map(CpuSet::as_ptr).unwrap_or(ptr::null());
                let nodeset = nodeset.map(NodeSet::as_ptr).unwrap_or(ptr::null());
                if cpuset.is_null() && nodeset.is_null() {
                    return Err(BadAllowSet.into());
                }
                (cpuset, nodeset, HWLOC_ALLOW_FLAG_CUSTOM)
            }
        };

        // Call hwloc
        errors::call_hwloc_int_normal("hwloc_topology_allow", || unsafe {
            hwlocality_sys::hwloc_topology_allow(self.topology_mut_ptr(), cpuset, nodeset, flags)
        })
        .map(std::mem::drop)
        .map_err(HybridError::Hwloc)
    }

    /// Add more structure to the topology by adding an intermediate [`Group`]
    ///
    /// Use the `find_children` callback to specify which [`TopologyObject`]s of
    /// this topology should be made children of the newly created Group
    /// object. The cpuset and nodeset of the final Group object will be the
    /// union of the cpuset and nodeset of all children respectively. Empty
    /// groups are not allowed, so at least one of these sets must be
    /// non-empty, or no Group object will be created.
    ///
    /// Use the `merge` option to control hwloc's propension to merge groups
    /// with hierarchically-identical topology objects.
    ///
    /// After a successful insertion, [`TopologyObject::set_subtype()`] can be
    /// used to display something other than "Group" as the type name for this
    /// object in `lstopo`, and custom name/value info pairs may be added using
    /// [`TopologyObject::add_info()`].
    ///
    /// # Errors
    ///
    /// - [`ForeignObject`] if some of the child `&TopologyObject`s specified
    ///   by the `find_children` callback do not belong to this [`Topology`].
    /// - [`RawHwlocError`]s are documented to happen if...
    ///     - There are conflicting sets in the topology tree
    ///     - [`Group`] objects are filtered out of the topology through
    ///       [`TypeFilter::KeepNone`]
    ///     - The effective CPU set or NUMA node set ends up being empty.
    ///
    /// [`Group`]: ObjectType::Group
    //
    // --- Implementation details ---
    //
    // In the future, find_children will be an impl FnOnce(&Topology) -> impl
    // IntoIterator<Item = &TopologyObject>, but impl Trait inside of impl
    // Trait is not allowed yet.
    #[doc(alias = "hwloc_topology_alloc_group_object")]
    #[doc(alias = "hwloc_obj_add_other_obj_sets")]
    #[doc(alias = "hwloc_topology_insert_group_object")]
    pub fn insert_group_object(
        &mut self,
        merge: Option<GroupMerge>,
        find_children: impl FnOnce(&Topology) -> Vec<&TopologyObject>,
    ) -> Result<InsertedGroup<'topology>, HybridError<ForeignObject>> {
        let mut group = AllocatedGroup::new(self).map_err(HybridError::Hwloc)?;
        group.add_children(find_children)?;
        if let Some(merge) = merge {
            group.set_merge_policy(merge);
        }
        group.insert().map_err(HybridError::Hwloc)
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
    /// topology. It must not contain any NUL chars. If it contains any other
    /// non-printable characters, then they will be dropped when exporting to
    /// XML.
    ///
    /// The new leaf object will not have any cpuset.
    ///
    /// # Errors
    ///
    /// - [`ForeignParent`] if the parent `&TopologyObject` returned by
    ///   `find_parent` does not belong to this [`Topology`].
    /// - [`NameContainsNul`] if `name` contains NUL chars.
    /// - An unspecified [`RawHwlocError`] if Misc objects are filtered out of
    ///   the topology via [`TypeFilter::KeepNone`].
    ///
    /// [`ForeignParent`]: InsertMiscError::ForeignParent
    /// [`Misc`]: ObjectType::Misc
    /// [`NameContainsNul`]: InsertMiscError::NameContainsNul
    #[doc(alias = "hwloc_topology_insert_misc_object")]
    pub fn insert_misc_object(
        &mut self,
        name: &str,
        find_parent: impl FnOnce(&Topology) -> &TopologyObject,
    ) -> Result<&'topology mut TopologyObject, HybridError<InsertMiscError>> {
        // Find parent object
        let raw_parent_mut: *mut hwloc_obj = {
            let topology = self.topology();
            let parent = find_parent(topology);
            if !topology.contains(parent) {
                return Err(HybridError::Rust(InsertMiscError::ForeignParent));
            }
            let raw_parent: *const hwloc_obj = &parent.0;
            raw_parent.cast_mut()
        };

        // Convert object name to a C string
        let name = LibcString::new(name)
            .map_err(|_| HybridError::Rust(InsertMiscError::NameContainsNul))?;

        // Call hwloc entry point
        //
        // This is on the edge of violating Rust's aliasing rules, but I think
        // it should work out because...
        //
        // - We discard the original parent reference before handing over the
        //   *mut derived from it to hwloc, and thus we should not be able to
        //   trigger UB consequences linked to the fact that we modified
        //   something that we accessed via &T while the compiler is allowed to
        //   assume that what's behind said &T doesn't change.
        // - We hand over to hwloc a honestly acquired *mut hwloc_topology that
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
        let mut ptr = errors::call_hwloc_ptr_mut("hwloc_topology_insert_misc_object", || unsafe {
            hwlocality_sys::hwloc_topology_insert_misc_object(
                self.topology_mut_ptr(),
                raw_parent_mut,
                name.borrow(),
            )
        })
        .map_err(HybridError::Hwloc)?;
        // SAFETY: - If hwloc succeeded, the output pointer is assumed valid
        //         - Output lifetime is bound to the topology that it comes from
        //         - TopologyObject is a repr(transparent) newtype of hwloc_obj
        Ok(unsafe { ffi::as_newtype_mut(ptr.as_mut()) })
    }
}

bitflags! {
    /// Flags to be given to [`TopologyEditor::restrict()`]
    #[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
    #[doc(alias = "hwloc_restrict_flags_e")]
    #[repr(transparent)]
    pub struct RestrictFlags: hwloc_restrict_flags_e {
        /// Remove all objects that lost all resources of the target type
        ///
        /// By default, only objects that contain no PU and no memory are
        /// removed. This flag allows you to remove all objects that...
        ///
        /// - Do not have access to any CPU anymore when restricting by CpuSet
        /// - Do not have access to any memory anymore when restricting by NodeSet
        //
        // --- Implementation details ---
        //
        // This is a virtual flag that is cleared and mapped into
        // `REMOVE_CPULESS` or `REMOVE_MEMLESS` as appropriate.
        #[doc(alias = "HWLOC_RESTRICT_FLAG_REMOVE_CPULESS")]
        #[doc(alias = "HWLOC_RESTRICT_FLAG_REMOVE_MEMLESS")]
        const REMOVE_EMPTIED = c_ulong::MAX;

        /// Remove all objects that became CPU-less
        //
        // --- Implementation details ---
        //
        // This is what `REMOVE_EMPTIED` maps into when restricting by `CpuSet`.
        #[doc(hidden)]
        const REMOVE_CPULESS = HWLOC_RESTRICT_FLAG_REMOVE_CPULESS;

        /// Restrict by NodeSet insted of by `CpuSet`
        //
        // --- Implementation details ---
        //
        // This flag is automatically set when restricting by `NodeSet`.
        #[doc(hidden)]
        const BY_NODE_SET = HWLOC_RESTRICT_FLAG_BYNODESET;

        /// Remove all objects that became memory-less
        //
        // --- Implementation details ---
        //
        // This is what `REMOVE_EMPTIED` maps into when restricting by `NodeSet`.
        #[doc(hidden)]
        const REMOVE_MEMLESS = HWLOC_RESTRICT_FLAG_REMOVE_MEMLESS;

        /// Move Misc objects to ancestors if their parents are removed during
        /// restriction
        ///
        /// If this flag is not set, Misc objects are removed when their parents
        /// are removed.
        #[doc(alias = "HWLOC_RESTRICT_FLAG_ADAPT_MISC")]
        const ADAPT_MISC = HWLOC_RESTRICT_FLAG_ADAPT_MISC;

        /// Move I/O objects to ancestors if their parents are removed
        /// during restriction
        ///
        /// If this flag is not set, I/O devices and bridges are removed when
        /// their parents are removed.
        #[doc(alias = "HWLOC_RESTRICT_FLAG_ADAPT_IO")]
        const ADAPT_IO = HWLOC_RESTRICT_FLAG_ADAPT_IO;
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
    /// You should provide at least one of `cpuset` and `nodeset`.
    #[doc(alias = "HWLOC_ALLOW_FLAG_CUSTOM")]
    Custom {
        /// New value of [`Topology::allowed_cpuset()`]
        cpuset: Option<&'set CpuSet>,

        /// New value of [`Topology::allowed_nodeset()`]
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

/// RAII guard for `Group` objects that have been allocated, but not inserted
///
/// Ensures that these groups are auto-deleted if not inserted for any reason
/// (typically as a result of erroring out).
///
/// # Safety
///
/// `group` must be a newly allocated, not-yet-inserted `Group` object that is
/// bound to topology editor `editor`. It would be an `&mut TopologyObject` if
/// this didn't break the Rust aliasing rules.
struct AllocatedGroup<'editor, 'topology> {
    /// Group object
    group: NonNull<TopologyObject>,

    /// Underlying TopologyEditor the Group is allocated from
    editor: &'editor mut TopologyEditor<'topology>,
}
//
impl<'editor, 'topology> AllocatedGroup<'editor, 'topology> {
    /// Allocate a new Group object
    pub(self) fn new(
        editor: &'editor mut TopologyEditor<'topology>,
    ) -> Result<Self, RawHwlocError> {
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted to keep *mut parameters in a valid state
        errors::call_hwloc_ptr_mut("hwloc_topology_alloc_group_object", || unsafe {
            hwlocality_sys::hwloc_topology_alloc_group_object(editor.topology_mut_ptr())
        })
        // SAFETY: - hwloc is trusted to produce a valid, non-inserted group
        //           object pointer
        //         - TopologyObject is a repr(transparent) newtype of hwloc_obj
        .map(|group| Self {
            group: group.cast::<TopologyObject>(),
            editor,
        })
    }

    /// Expand cpu sets and node sets to cover designated children
    ///
    /// # Errors
    ///
    /// [`ForeignObject`] if some of the designated children do not come from
    /// the same topology as this group.
    pub(self) fn add_children(
        &mut self,
        find_children: impl FnOnce(&Topology) -> Vec<&TopologyObject>,
    ) -> Result<(), ForeignObject> {
        // Enumerate children, check they belong to this topology
        let topology = self.editor.topology();
        let children = find_children(topology);
        if children.iter().any(|child| !topology.contains(child)) {
            return Err(ForeignObject);
        }

        // Add children to this group
        for child in children {
            // SAFETY: - group is assumed to be valid as a type invariant
            //         - hwloc ops are trusted not to modify *const parameters
            //         - child was checked to belong to the same topology as group
            //         - TopologyObject is a repr(transparent) newtype of hwloc_obj
            let result = errors::call_hwloc_int_normal("hwloc_obj_add_other_obj_sets", || unsafe {
                hwlocality_sys::hwloc_obj_add_other_obj_sets(
                    self.group.cast::<hwloc_obj>().as_ptr(),
                    &child.0,
                )
            });
            match result {
                Ok(_) => {}
                Err(
                    raw_err @ RawHwlocError {
                        errno: Some(errno::Errno(ENOMEM)),
                        ..
                    },
                ) => panic!("Internal reallocation failed: {raw_err}"),
                Err(raw_err) => unreachable!("Unexpected hwloc error: {raw_err}"),
            }
        }
        Ok(())
    }

    /// Configure hwloc's group merging policy
    ///
    /// By default, hwloc may or may not merge identical groups covering the
    /// same objects. You can encourage or inhibit this tendency with this method.
    pub(self) fn set_merge_policy(&mut self, merge: GroupMerge) {
        // SAFETY: - We know this is a group object as a type invariant, so
        //           accessing the group raw attribute is safe
        //         - We are not changing the raw attributes variant
        //         - GroupAttributes is a repr(transparent) newtype of hwloc_group_attr_s
        let group_attributes: &mut GroupAttributes =
            unsafe { ffi::as_newtype_mut(&mut (*self.group.as_mut().0.attr).group) };
        match merge {
            GroupMerge::Never => group_attributes.prevent_merging(),
            GroupMerge::Always => group_attributes.favor_merging(),
        }
    }

    /// Insert this Group object into the underlying topology
    ///
    /// # Errors
    ///
    /// Will return an unspecified error if any of the following happens:
    ///
    /// - Insertion failed because of conflicting sets in the topology tree
    /// - Group objects are filtered out of the topology via
    ///   [`TypeFilter::KeepNone`]
    /// - The object was discarded because no set was initialized in the Group,
    ///   or they were all empty.
    pub(self) fn insert(mut self) -> Result<InsertedGroup<'topology>, RawHwlocError> {
        // SAFETY: self is forgotten after this, so no drop or reuse will occur
        let res = unsafe { self.insert_impl() };
        std::mem::forget(self);
        res
    }

    /// Implementation of `insert()` with an `&mut self` argument
    ///
    /// # Errors
    ///
    /// Will return an unspecified error if any of the following happens:
    ///
    /// - Insertion failed because of conflicting sets in the topology tree
    /// - Group objects are filtered out of the topology via
    ///   [`TypeFilter::KeepNone`]
    /// - The object was discarded because no set was initialized in the Group,
    ///   or they were all empty.
    ///
    /// # Safety
    ///
    /// After calling this method, `self` is in an invalid state and should not
    /// be used in any way anymore. In particular, care should be taken to
    /// ensure that its Drop destructor is not called.
    unsafe fn insert_impl(&mut self) -> Result<InsertedGroup<'topology>, RawHwlocError> {
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - Inner group pointer is assumed valid as a type invariant
        //         - hwloc ops are trusted not to modify *const parameters
        //         - hwloc ops are trusted to keep *mut parameters in a valid state
        //         - We break the AllocatedGroup type invariant by inserting the
        //           group object, but a precondition warns the user about it
        //         - TopologyObject is a repr(transparent) newtype of hwloc_obj
        errors::call_hwloc_ptr_mut("hwloc_topology_insert_group_object", || unsafe {
            hwlocality_sys::hwloc_topology_insert_group_object(
                self.editor.topology_mut_ptr(),
                self.group.cast::<hwloc_obj>().as_ptr(),
            )
        })
        .map(|mut result| {
            if result == self.group.cast::<hwloc_obj>() {
                // SAFETY: - We know this is a group object as a type invariant
                //         - Output lifetime is bound to the topology it comes from
                //         - Group has been successfully inserted, can expose &mut
                InsertedGroup::New(unsafe { self.group.as_mut() })
            } else {
                // SAFETY: - Successful result is trusted to point to an
                //           existing group
                //         - Output lifetime is bound to the topology it comes from
                //         - TopologyObject is a repr(transparent) newtype of hwloc_obj
                InsertedGroup::Existing(unsafe { ffi::as_newtype_mut(result.as_mut()) })
            }
        })
    }
}
//
impl Drop for AllocatedGroup<'_, '_> {
    fn drop(&mut self) {
        // FIXME: As of hwloc v2.9.4, there is no API to delete a previously
        //        allocated Group object without attempting to insert it into
        //        the topology. An always-failing insertion is the officially
        //        recommended workaround until such an API is added:
        //        https://github.com/open-mpi/hwloc/issues/619
        // SAFETY: - Inner group pointer is assumed valid as a type invariant
        //         - The state where this invariant is invalidated, produced by
        //           insert_impl(), is never exposed to Drop
        unsafe {
            TopologyObject::delete_all_sets(self.group);
        }
        // SAFETY: - AllocatedGroup will not be droppable again after Drop
        unsafe {
            self.insert_impl()
                .expect_err("Group insertion with NULL sets should fail and deallocate the group");
        }
    }
}

/// Result of inserting a Group object
#[derive(Debug)]
#[must_use]
pub enum InsertedGroup<'topology> {
    /// New Group that was properly inserted
    New(&'topology mut TopologyObject),

    /// Existing object that already fulfilled the role of the proposed Group
    ///
    /// If the Group adds no hierarchy information, hwloc may merge or discard
    /// it in favor of existing topology object at the same location.
    Existing(&'topology mut TopologyObject),
}

/// Attempted to create a group with invalid children
///
/// The `find_children` callback that was passed to
/// [`TopologyEditor::insert_group_object()`] returned "children" which don't
/// actually belong to the topology that is being edited.
#[derive(Copy, Clone, Debug, Default, Eq, Error, Hash, PartialEq)]
#[error("Provided find_children callback returned invalid (foreign) children")]
pub struct BadGroupChildren;

/// Error returned by [`TopologyEditor::insert_misc_object()`]
#[derive(Copy, Clone, Debug, Eq, Error, Hash, PartialEq)]
pub enum InsertMiscError {
    /// Specified parent does not belong to this topology
    #[error("the specified parent does not belong to this topology")]
    ForeignParent,

    /// Object name contains NUL chars, which hwloc can't handle
    #[error("requested object name contains NUL chars")]
    NameContainsNul,
}

// NOTE: Do not implement traits like AsRef/Deref/Borrow for TopologyEditor,
//       that would be unsafe as it would expose &Topology with unevaluated lazy
//       hwloc caches, and calling their methods could violates Rust's aliasing
//       model via mutation through &Topology.
