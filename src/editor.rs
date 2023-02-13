//! Facilities for modifying a loaded Topology
//!
//! hwloc employs thread-unsafe lazy evaluation patterns. It is possible to
//! avoid the thread-unsafety and keep `impl Sync for Topology` by forcing eager
//! evaluation of the lazy caches at the end of editing, but as a result of this
//! design, topology modifications must be carried out through a proxy object
//! that does not permit unevaluated caches to escape.

use std::panic::UnwindSafe;

use crate::Topology;

/// Proxy for modifying a `Topology`
pub struct TopologyEditor<'topology>(&'topology mut Topology);

impl<'topology> TopologyEditor<'topology> {
    /// Wrap an `&mut Topology` into a topology editor
    pub(crate) fn new(topology: &'topology mut Topology) -> Self {
        Self(topology)
    }
}
