//! NUMA node sets

#[cfg(doc)]
use crate::{bitmap::Bitmap, topology::support::DiscoverySupport};
use crate::{cpu::cpuset::CpuSet, impl_bitmap_newtype, object::depth::Depth, topology::Topology};
use std::borrow::Borrow;

/// # NodeSet-specific API
//
// --- Implementation details ---
//
// This goes before the main impl_bitmap_newtype macro so that it appears before
// the bitmap API reexport in rustdoc.
impl NodeSet {
    /// Convert a CPU set into a NUMA node set
    ///
    /// For each PU included in the input `cpuset`, set the corresponding local
    /// NUMA node(s) in the output nodeset.
    ///
    /// If some NUMA nodes have no CPUs at all, this function never sets their
    /// indices in the output node set, even if a full CPU set is given in input.
    ///
    /// Hence the entire topology CPU set, that one can query via
    /// [`Topology::cpuset()`], would be converted by this function into the
    /// set of all nodes that have some local CPUs.
    #[doc(alias = "hwloc_cpuset_to_nodeset")]
    pub fn from_cpuset(topology: &Topology, cpuset: impl Borrow<CpuSet>) -> NodeSet {
        let mut nodeset = NodeSet::new();
        for obj in topology.objects_covering_cpuset_at_depth(cpuset, Depth::NUMANode) {
            nodeset.set(obj.os_index().expect("NUMA nodes should have OS indices"));
        }
        nodeset
    }
}

impl_bitmap_newtype!(
    /// A `NodeSet` is a [`Bitmap`] whose bits are set according to NUMA memory
    /// node physical OS indexes.
    ///
    /// Each bit may be converted into a NUMA node object using
    /// [`Topology::node_with_os_index()`].
    ///
    /// When binding memory on a system without any NUMA node, the single main
    /// memory bank is considered as NUMA node #0.
    #[doc(alias = "hwloc_nodeset_t")]
    #[doc(alias = "hwloc_const_nodeset_t")]
    NodeSet
);
