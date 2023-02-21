//! Synthetic topologies

// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__syntheticexport.html

use bitflags::bitflags;
use std::ffi::c_ulong;

bitflags! {
    /// Flags to be given to [`Topology::export_synthetic()`]
    #[repr(C)]
    pub struct SyntheticExportFlags: c_ulong {
        /// Export extended types such as L2dcache as basic types such as Cache
        ///
        /// This is required if loading the synthetic description with hwloc
        /// < 1.9.
        const NO_EXTENDED_TYPES = (1<<0);

        /// Do not export level attributes
        ///
        /// Ignore level attributes such as memory/cache sizes or PU indexes.
        ///
        /// This is required if loading the synthetic description with hwloc
        /// < 1.10.
        const NO_ATTRIBUTES = (1<<1);

        /// Export the memory hierarchy as expected in hwloc 1.x
        ///
        /// Instead of attaching memory children to levels, export single NUMA
        /// node children as normal intermediate levels, when possible.
        ///
        /// This is required if loading the synthetic description with hwloc
        /// 1.x. However this may fail if some objects have multiple local NUMA
        /// nodes.
        const V1 = (1<<2);

        /// Do not export memory information
        ///
        /// Only export the actual hierarchy of normal CPU-side objects and
        /// ignore where memory is attached.
        ///
        /// This is useful for when the hierarchy of CPUs is what really matters,
        /// but it behaves as if there was a single machine-wide NUMA node.
        const IGNORE_MEMORY = (1<<3);
    }
}

impl Default for SyntheticExportFlags {
    fn default() -> Self {
        Self::empty()
    }
}
