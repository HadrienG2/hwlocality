//! CPU sets

#[cfg(doc)]
use crate::{bitmaps::Bitmap, topology::support::DiscoverySupport};
use crate::{
    impl_bitmap_newtype,
    memory::nodesets::NodeSet,
    objects::{depth::Depth, types::ObjectType, TopologyObject},
    topology::Topology,
};
use std::{clone::Clone, fmt::Debug, iter::FusedIterator, ptr};

/// # Finding objects inside a CPU set
//
// This is inspired by the upstream functionality described at
// https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__find__inside.html
// but the code had to be ported to Rust as most C code is inline and thus
// cannot be called from Rust, and the only function that's not inline does not
// fit Rust's design (assumes caller has allocated large enough storage with no
// way to tell what is large enough)
impl Topology {
    /// Enumerate the largest objects included in the given cpuset `set`
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set).
    ///
    /// In the common case where `set` is a subset of the root cpuset, this
    /// operation can be more efficiently performed by using
    /// `coarsest_cpuset_partition()`.
    #[doc(alias = "hwloc_get_first_largest_obj_inside_cpuset")]
    pub fn largest_objects_inside_cpuset(
        &self,
        set: CpuSet,
    ) -> impl Iterator<Item = &TopologyObject> + FusedIterator {
        LargestObjectsInsideCpuSet {
            topology: self,
            set,
        }
    }

    /// Get the largest objects exactly covering the given cpuset `set`
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set).
    ///
    /// # Panics
    ///
    /// If the requested cpuset is not a subset of the root cpuset, we can't
    /// find children covering the indices outside of the root cpuset
    #[doc(alias = "hwloc_get_largest_objs_inside_cpuset")]
    pub fn coarsest_cpuset_partition(&self, set: &CpuSet) -> Vec<&TopologyObject> {
        // Make sure each set index actually maps into a hardware PU
        let root = self.root_object();
        assert!(
            set.includes(root.cpuset().expect("Root should have a CPU set")),
            "Requested set has indices outside the root cpuset"
        );

        // Start recursion
        let mut result = Vec::new();
        let mut cpusets = Vec::new();
        fn process_object<'a>(
            parent: &'a TopologyObject,
            set: &CpuSet,
            result: &mut Vec<&'a TopologyObject>,
            cpusets: &mut Vec<CpuSet>,
        ) {
            // If the current object does not have a cpuset, ignore it
            let Some(parent_cpuset) = parent.cpuset() else { return };

            // If it exactly covers the target cpuset, we're done
            if parent_cpuset == set {
                result.push(parent);
                return;
            }

            // Otherwise, look for children that cover the target cpuset
            let mut subset = cpusets.pop().unwrap_or_default();
            for child in parent.normal_children() {
                // Ignore children without a cpuset, or with a cpuset that
                // doesn't intersect the target cpuset
                let Some(child_cpuset) = child.cpuset() else { continue };
                if !child_cpuset.intersects(set) {
                    continue;
                }

                // Split out the cpuset part corresponding to this child and recurse
                subset.copy_from(set);
                subset &= child_cpuset;
                process_object(child, &subset, result, cpusets);
            }
            cpusets.push(subset);
        }
        process_object(root, set, &mut result, &mut cpusets);
        result
    }

    /// Enumerate objects included in the given cpuset `set` at a certain depth
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set). Therefore, an empty iterator will
    /// always be returned for I/O or Misc depths as those objects have no cpusets.
    #[doc(alias = "hwloc_get_obj_inside_cpuset_by_depth")]
    #[doc(alias = "hwloc_get_next_obj_inside_cpuset_by_depth")]
    #[doc(alias = "hwloc_get_nbobjs_inside_cpuset_by_depth")]
    pub fn objects_inside_cpuset_at_depth<'result>(
        &'result self,
        set: &'result CpuSet,
        depth: impl Into<Depth>,
    ) -> impl Iterator<Item = &TopologyObject> + Clone + DoubleEndedIterator + FusedIterator + 'result
    {
        let depth = depth.into();
        self.objects_at_depth(depth)
            .filter(|object| object.is_inside_cpuset(set))
    }

    /// Get objects included in the given cpuset `set` with a certain type
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set). Therefore, an empty Vec will
    /// always be returned for I/O or Misc objects as they don't have cpusets.
    #[doc(alias = "hwloc_get_obj_inside_cpuset_by_type")]
    #[doc(alias = "hwloc_get_next_obj_inside_cpuset_by_type")]
    #[doc(alias = "hwloc_get_nbobjs_inside_cpuset_by_type")]
    pub fn objects_inside_cpuset_with_type<'result>(
        &'result self,
        set: &'result CpuSet,
        object_type: ObjectType,
    ) -> impl Iterator<Item = &TopologyObject> + Clone + DoubleEndedIterator + FusedIterator + 'result
    {
        self.objects_with_type(object_type)
            .filter(|object| object.is_inside_cpuset(set))
    }

    /// Get the first largest object included in the given cpuset `set`
    ///
    /// Returns the first object that is included in `set` and whose parent is
    /// not, in descending depth and children iteration order.
    ///
    /// This is convenient for iterating over all largest objects within a CPU
    /// set by doing a loop getting the first largest object and clearing its
    /// CPU set from the remaining CPU set. This very pattern is exposed by
    /// the `largest_objects_inside_cpuset` method, which is why this method is
    /// not publicly exposed.
    ///
    /// That being said, if the cpuset is a strict subset of the root cpuset of
    /// this `Topology`, the work may be more efficiently done by
    /// `largest_cpuset_partition()`, which only needs to walk the topology
    /// tree once.
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set).
    fn first_largest_object_inside_cpuset(&self, set: &CpuSet) -> Option<&TopologyObject> {
        // If root object doesn't intersect this CPU set then no child will
        let root = self.root_object();
        let root_cpuset = root.cpuset().expect("Root should have a CPU set");
        if !root_cpuset.intersects(set) {
            return None;
        }

        // Walk the topology tree until we find an object included into set
        let mut parent = root;
        let mut parent_cpuset = root_cpuset;
        while !set.includes(parent_cpuset) {
            // While the object intersects without being included, look at children
            let old_parent = parent;
            for child in parent.normal_children() {
                if let Some(child_cpuset) = child.cpuset() {
                    // This child intersects, make it the new parent and recurse
                    if set.intersects(child_cpuset) {
                        parent = child;
                        parent_cpuset = child_cpuset;
                    }
                }
            }
            assert!(
                !ptr::eq(parent, old_parent),
                "This should not happen because...\n\
                - The root intersects, so it has at least one index from the set\n\
                - The lowest-level children are PUs, which have only one index set,\
                  so one of them should pass the includes() test"
            );
        }
        Some(parent)
    }
}

/// Iterator over largest objects inside a cpuset
#[derive(Clone, Debug)]
struct LargestObjectsInsideCpuSet<'topology> {
    topology: &'topology Topology,
    set: CpuSet,
}
//
impl<'topology> Iterator for LargestObjectsInsideCpuSet<'topology> {
    type Item = &'topology TopologyObject;

    fn next(&mut self) -> Option<Self::Item> {
        let object = self
            .topology
            .first_largest_object_inside_cpuset(&self.set)?;
        let object_cpuset = object
            .cpuset()
            .expect("Output of first_largest_object_inside_cpuset should have a cpuset");
        self.set.and_not_assign(object_cpuset);
        Some(object)
    }
}
//
impl FusedIterator for LargestObjectsInsideCpuSet<'_> {}

/// # Finding objects covering at least a CPU set
//
// This is inspired by the upstream functionality described at
// https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__find__covering.html
// but the code had to be ported to Rust because it's inline
impl Topology {
    /// Get the lowest object covering at least the given cpuset `set`
    ///
    /// No object is considered to cover the empty cpuset, therefore such a
    /// request will always return None, as if a set going outside of the root
    /// cpuset were passed as input.
    #[doc(alias = "hwloc_get_obj_covering_cpuset")]
    pub fn smallest_object_covering_cpuset(&self, set: &CpuSet) -> Option<&TopologyObject> {
        let root = self.root_object();
        if !root.covers_cpuset(set) || set.is_empty() {
            return None;
        }
        let mut parent = root;
        while let Some(child) = parent.normal_child_covering_cpuset(set) {
            parent = child;
        }
        Some(parent)
    }

    /// Get the first data (or unified) cache covering the given cpuset
    #[doc(alias = "hwloc_get_cache_covering_cpuset")]
    pub fn first_cache_covering_cpuset(&self, set: &CpuSet) -> Option<&TopologyObject> {
        let first_obj = self.smallest_object_covering_cpuset(set)?;
        std::iter::once(first_obj)
            .chain(first_obj.ancestors())
            .find(|obj| obj.object_type().is_cpu_data_cache())
    }

    /// Enumerate objects covering the given cpuset `set` at a certain depth
    ///
    /// Objects are not considered to cover the empty CPU set (otherwise a list
    /// of all objects would be returned). Therefore, an empty iterator will
    /// always be returned for I/O or Misc depths as those objects have no cpusets.
    #[doc(alias = "hwloc_get_next_obj_covering_cpuset_by_depth")]
    pub fn objects_covering_cpuset_at_depth<'result>(
        &'result self,
        set: &'result CpuSet,
        depth: impl Into<Depth>,
    ) -> impl Iterator<Item = &TopologyObject> + Clone + DoubleEndedIterator + FusedIterator + 'result
    {
        let depth = depth.into();
        self.objects_at_depth(depth)
            .filter(|object| object.covers_cpuset(set))
    }

    /// Get objects covering the given cpuset `set` with a certain type
    ///
    /// Objects are not considered to cover the empty CPU set (otherwise a list
    /// of all objects would be returned). Therefore, an empty iterator will
    /// always be returned for I/O or Misc depths as those objects have no cpusets.
    #[doc(alias = "hwloc_get_next_obj_covering_cpuset_by_type")]
    pub fn objects_covering_cpuset_with_type<'result>(
        &'result self,
        set: &'result CpuSet,
        object_type: ObjectType,
    ) -> impl Iterator<Item = &TopologyObject> + Clone + DoubleEndedIterator + FusedIterator + 'result
    {
        self.objects_with_type(object_type)
            .filter(|object| object.covers_cpuset(set))
    }
}

/// # CpuSet-specific API
//
// NOTE: This goes before the main impl_bitmap_newtype macro so that it appears
//       before the bitmap API reexport in rustdoc.
impl CpuSet {
    /// Remove simultaneous multithreading PUs from a CPU set
    ///
    /// For each core in `topology`, if this cpuset contains several PUs of that
    /// core, modify it to only keep a single PU for that core.
    ///
    /// `which` specifies which PU will be kept, in physical index order. If it
    /// is set to 0, for each core, the function keeps the first PU that was
    /// originally set in `cpuset`. If it is larger than the number of PUs in a
    /// core there were originally set in `cpuset`, no PU is kept for that core.
    ///
    /// PUs that are not below a Core object (for instance if the topology does
    /// not contain any Core object) are kept in the cpuset.
    #[cfg(feature = "hwloc-2_2_0")]
    #[doc(alias = "hwloc_bitmap_singlify_per_core")]
    pub fn singlify_per_core(&mut self, topology: &Topology, which: u32) {
        let result = unsafe {
            crate::ffi::hwloc_bitmap_singlify_per_core(topology.as_ptr(), self.as_mut_ptr(), which)
        };
        assert!(
            result >= 0,
            "Unexpected result from hwloc_bitmap_singlify_per_core"
        )
    }

    /// Convert a NUMA node set into a CPU set
    ///
    /// For each NUMA node included in the input `nodeset`, set the
    /// corresponding local PUs in the output cpuset.
    ///
    /// If some CPUs have no local NUMA nodes, this function never sets their
    /// indexes in the output CPU set, even if a full node set is given in input.
    ///
    /// Hence the entire topology node set, that one can query via
    /// [`Topology::nodeset()`], would be converted by this function into the
    /// set of all CPUs that have some local NUMA nodes.
    ///
    /// Requires [`DiscoverySupport::numa_count()`].
    pub fn from_nodeset(topology: &Topology, nodeset: &NodeSet) -> CpuSet {
        let mut cpuset = CpuSet::new();
        for obj in topology.objects_at_depth(Depth::NUMANode) {
            if nodeset.is_set(obj.os_index().expect("NUMA nodes should have OS indices")) {
                cpuset |= obj.cpuset().expect("NUMA nodes should have cpusets");
            }
        }
        cpuset
    }
}

impl_bitmap_newtype!(
    /// A `CpuSet` is a [`Bitmap`] whose bits are set according to CPU physical
    /// OS indexes
    ///
    /// Each bit may be converted into a PU object using
    /// [`Topology::pu_with_os_index()`].
    #[doc(alias = "hwloc_cpuset_t")]
    #[doc(alias = "hwloc_const_cpuset_t")]
    CpuSet
);