//! Facilities for modifying a loaded Topology
//!
//! hwloc employs thread-unsafe lazy evaluation patterns. It is possible to
//! avoid the thread-unsafety and keep `impl Sync for Topology` by forcing eager
//! evaluation of the lazy caches at the end of editing, but as a result of this
//! design, topology modifications must be carried out through a proxy object
//! that does not permit shared references to unevaluated caches to escape.

use crate::{RawTopology, Topology};

/// Proxy for modifying a `Topology`
pub struct TopologyEditor<'topology>(&'topology mut Topology);

impl<'topology> TopologyEditor<'topology> {
    // === Modifying a loaded Topology: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__tinker.html ===

    // TODO: insert_xyz_objects will require weird tricks because by design they
    //       violate Rust's shared XOR mutability rules.

    // === General-purpose internal utilities ===

    /// Wrap an `&mut Topology` into a topology editor
    pub(crate) fn new(topology: &'topology mut Topology) -> Self {
        Self(topology)
    }

    /// Returns the contained hwloc topology pointer for interaction with hwloc
    fn as_mut_ptr(&mut self) -> *mut RawTopology {
        self.0.as_mut_ptr()
    }
}
