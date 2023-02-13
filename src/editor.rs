//! Facilities for modifying a loaded Topology
//!
//! hwloc employs lazy evaluation patterns that are thread-unsafe and violate
//! Rust's aliasing rules. It is possible to force eager evaluation of the lazy
//! caches to return to a normal state, but as a result of this design, topology
//! modifications must be carried out through a proxy object that does not
//! permit shared references to unevaluated caches to escape.

use crate::{
    bitmap::{BitmapKind, SpecializedBitmap},
    ffi,
    objects::TopologyObject,
    RawTopology, Topology,
};
use bitflags::bitflags;
use errno::errno;
use libc::{c_ulong, EINVAL, ENOMEM};
use std::ffi::CString;
use thiserror::Error;

/// Proxy for modifying a `Topology`
pub struct TopologyEditor<'topology>(&'topology mut Topology);

impl<'topology> TopologyEditor<'topology> {
    // === General-purpose internal utilities ===

    /// Wrap an `&mut Topology` into a topology editor
    pub(crate) fn new(topology: &'topology mut Topology) -> Self {
        Self(topology)
    }

    /// Get a shared reference to the inner Topology that follows Rust invariants
    ///
    /// This operation may be costly, you may want to consider doing it before
    /// or after starting the topology editing process if possible.
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

    // === Modifying a loaded Topology: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__tinker.html ===

    /// Restrict the topology to the given CPU set or nodeset
    ///
    /// The topology is modified so as to remove all objects that are not
    /// included (or partially included) in the specified CPU or NUMANode set.
    /// All objects CPU and node sets are restricted accordingly.
    ///
    /// This call may not be reverted by restricting back to a larger set. Once
    /// dropped during restriction, objects may not be brought back, except by
    /// loading another topology with `Topology::new()` or `TopologyBuilder`.
    ///
    /// # Errors
    ///
    /// `Err(InvalidParameter)` will be returned if the input set is invalid.
    /// The topology is not modified in this case.
    ///
    /// # Panics
    ///
    /// Failure to allocate internal data will lead to a panic. The topology is
    /// reinitialized in this case and should not be used again.
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
        let result =
            unsafe { ffi::hwloc_topology_restrict(self.topology_mut_ptr(), set.as_ptr(), flags) };
        match result {
            0 => Ok(()),
            -1 => {
                let errno = errno();
                match errno.0 {
                    EINVAL => Err(InvalidParameter),
                    ENOMEM => panic!("Topology was reinitialized and must be dropped"),
                    _ => panic!("Unexpected errno {errno}"),
                }
            }
            other => panic!("Unexpected result {other} with errno {}", errno()),
        }
    }

    /// Add a `Misc` object as a leaf of the topology
    ///
    /// A new `Misc` object will be created and inserted into the topology as
    /// a child of the node selected by `find_parent`. It is appended to the
    /// list of existing `Misc` children, without ever adding any intermediate
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
    /// None will be returned if an error occurs or if `Misc` objects are
    /// filtered out of the topology via `TypeFilter::KeepNone`.
    pub fn insert_misc_object(
        &mut self,
        find_parent: impl FnOnce(&Topology) -> &TopologyObject,
        name: &str,
    ) -> Option<&mut TopologyObject> {
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
        let name = CString::new(name).ok()?;
        unsafe {
            let ptr = ffi::hwloc_topology_insert_misc_object(
                self.topology_mut_ptr(),
                parent,
                name.as_ptr(),
            );
            (!ptr.is_null()).then(|| &mut *ptr)
        }
    }

    // TODO: insert_xyz_objects will require weird tricks because by design they
    //       violate Rust's shared XOR mutability rules.
}

// NOTE: Do not implement traits like AsRef/Deref/Borrow, that would be unsafe
//       as it would expose &Topology with unevaluated lazy hwloc caches.

bitflags! {
    /// Flags to be given to `TopologyEditor::restrict()`
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
        /// This is automatically set when restricting by `NodeSet`.
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

#[derive(Copy, Clone, Debug, Default, Eq, Error, PartialEq)]
#[error("invalid parameter specified")]
pub struct InvalidParameter;
