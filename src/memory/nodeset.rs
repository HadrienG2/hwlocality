//! NUMA node sets
//!
//! These specialized bitmaps represent sets of NUMA nodes, as exposed by the
//! underlying operating system.

#[cfg(doc)]
use crate::{bitmap::Bitmap, topology::support::DiscoverySupport};
use crate::{cpu::cpuset::CpuSet, impl_bitmap_newtype, topology::Topology};
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::ops::Deref;

/// # NodeSet-specific API
//
// --- Implementation details ---
//
// This goes before the main impl_bitmap_newtype macro so that it appears before
// the bitmap API reexport in rustdoc.
impl NodeSet {
    /// Convert a CPU set into a NUMA node set
    ///
    /// `cpuset` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`.
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
    pub fn from_cpuset(topology: &Topology, cpuset: impl Deref<Target = CpuSet>) -> Self {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized(topology: &Topology, cpuset: &CpuSet) -> NodeSet {
            topology
                .pus_from_cpuset(cpuset)
                .fold(NodeSet::new(), |mut nodeset, pu| {
                    nodeset |= pu.nodeset().expect("processing units should have nodesets");
                    nodeset
                })
        }
        polymorphized(topology, &cpuset)
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::strategies::topology_related_set;
    use proptest::prelude::*;

    proptest! {
        /// Test for [`NodeSet::from_cpuset()`]
        #[test]
        fn nodeset_from_cpuset(
            cpuset in topology_related_set(Topology::cpuset),
        ) {
            let topology = Topology::test_instance();
            prop_assert_eq!(
                NodeSet::from_cpuset(topology, &cpuset),
                topology.pus_from_cpuset(&cpuset)
                        .map(|pu| pu.nodeset().unwrap().clone_target())
                        .reduce(|set1, set2| set1 | set2)
                        .unwrap_or_default()
            )
        }
    }
}
