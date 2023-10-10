//! CPU sets
//!
//! These specialized bitmaps represent sets of logical CPU cores, as exposed by
//! the underlying operating system. The logical cores may map into either
//! full-blown hardware CPU cores or SMT threads thereof
//! (aka "hyper-threads") depending on the underlying hardware and OS
//! configuration.

#[cfg(feature = "hwloc-2_2_0")]
use crate::errors;
#[cfg(doc)]
use crate::{bitmap::Bitmap, topology::support::DiscoverySupport};
use crate::{
    impl_bitmap_newtype,
    memory::nodeset::NodeSet,
    object::{
        depth::{Depth, NormalDepth},
        types::ObjectType,
        TopologyObject,
    },
    topology::Topology,
};
#[allow(unused)]
#[cfg(test)]
use pretty_assertions::{assert_eq, assert_ne};
#[cfg(feature = "hwloc-2_2_0")]
use std::ffi::c_uint;
use std::{borrow::Borrow, fmt::Debug, iter::FusedIterator, ptr};
use thiserror::Error;

/// # Finding objects inside a CPU set
//
// --- Implementation details ---
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
    /// iteration can be more efficiently performed by using
    /// [`coarsest_cpuset_partition()`].
    ///
    /// [`coarsest_cpuset_partition()`]: Topology::coarsest_cpuset_partition()
    #[doc(alias = "hwloc_get_first_largest_obj_inside_cpuset")]
    pub fn largest_objects_inside_cpuset(
        &self,
        set: CpuSet,
    ) -> impl FusedIterator<Item = &TopologyObject> {
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
    /// # Errors
    ///
    /// - [`CoarsestPartitionError`] if `set` covers more indices than the
    ///   topology's root cpuset
    #[doc(alias = "hwloc_get_largest_objs_inside_cpuset")]
    pub fn coarsest_cpuset_partition(
        &self,
        set: impl Borrow<CpuSet>,
    ) -> Result<Vec<&TopologyObject>, CoarsestPartitionError> {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized<'self_>(
            self_: &'self_ Topology,
            set: &CpuSet,
        ) -> Result<Vec<&'self_ TopologyObject>, CoarsestPartitionError> {
            // Make sure each set index actually maps into a hardware PU
            let root = self_.root_object();
            let root_cpuset = root.cpuset().expect("Root should have a CPU set");
            if !root_cpuset.includes(set) {
                return Err(CoarsestPartitionError {
                    query: set.clone(),
                    root: root_cpuset.clone_target(),
                });
            }

            /// Recursive implementation of the partitioning algorithm
            fn process_object<'a>(
                parent: &'a TopologyObject,
                set: &CpuSet,
                result: &mut Vec<&'a TopologyObject>,
                cpusets: &mut Vec<CpuSet>,
            ) {
                // If the current object does not have a cpuset, ignore it
                let Some(parent_cpuset) = parent.cpuset() else {
                    return;
                };

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
                    let Some(child_cpuset) = child.cpuset() else {
                        continue;
                    };
                    if !child_cpuset.intersects(set) {
                        continue;
                    }

                    // Split out cpu subset corresponding to this child, recurse
                    subset.copy_from(set);
                    subset &= child_cpuset;
                    process_object(child, &subset, result, cpusets);
                }
                cpusets.push(subset);
            }
            let mut result = Vec::new();
            let mut cpusets = Vec::new();
            process_object(root, set, &mut result, &mut cpusets);
            Ok(result)
        }
        polymorphized(self, set.borrow())
    }

    /// Enumerate objects included in the given cpuset `set` at a certain depth
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set). Therefore, an empty iterator will
    /// always be returned for I/O or Misc depths as those objects have no cpusets.
    #[doc(alias = "hwloc_get_obj_inside_cpuset_by_depth")]
    #[doc(alias = "hwloc_get_next_obj_inside_cpuset_by_depth")]
    #[doc(alias = "hwloc_get_nbobjs_inside_cpuset_by_depth")]
    pub fn objects_inside_cpuset_at_depth<'result, DepthLike>(
        &'result self,
        set: impl Borrow<CpuSet> + 'result,
        depth: DepthLike,
    ) -> impl DoubleEndedIterator<Item = &TopologyObject> + FusedIterator + 'result
    where
        DepthLike: TryInto<Depth>,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        // This little hack works because hwloc topologies never get anywhere
        // close the maximum possible depth, which is c_int::MAX, so there will
        // never be any object at that depth. We need it because impl Trait
        // needs homogeneous return types.
        let depth = depth.try_into().unwrap_or(Depth::Normal(NormalDepth::MAX));
        self.objects_at_depth(depth)
            .filter(move |object| object.is_inside_cpuset(set.borrow()))
    }

    /// Logical index among the objects included in CPU set `set`
    ///
    /// Consult all objects in the same level as `obj` and inside CPU set `set`
    /// in the logical order, and return the index of `obj` within them. If
    /// `set` covers the entire topology, this is the logical index of `obj`.
    /// Otherwise, this is similar to a logical index within the part of the
    /// topology defined by CPU set `set`.
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set). Therefore, `None` will always be
    /// returned for I/O or Misc depths as those objects have no cpusets.
    ///
    /// This method will also return `None` if called with an `obj` that does
    /// not belong to this [`Topology`].
    #[doc(alias = "hwloc_get_obj_index_inside_cpuset")]
    pub fn object_index_inside_cpuset<'result>(
        &'result self,
        set: impl Borrow<CpuSet> + 'result,
        obj: &TopologyObject,
    ) -> Option<usize> {
        // obj may not belong to this topology, but the current implementation
        // is fine with that and will just return None.
        self.objects_inside_cpuset_at_depth(set, obj.depth())
            .position(|candidate| std::ptr::eq(candidate, obj))
    }

    /// Get objects included in the given cpuset `set` with a certain type
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set). Therefore, an empty iterator will
    /// always be returned for I/O or Misc objects as they don't have cpusets.
    #[doc(alias = "hwloc_get_obj_inside_cpuset_by_type")]
    #[doc(alias = "hwloc_get_next_obj_inside_cpuset_by_type")]
    #[doc(alias = "hwloc_get_nbobjs_inside_cpuset_by_type")]
    pub fn objects_inside_cpuset_with_type<'result>(
        &'result self,
        set: impl Borrow<CpuSet> + 'result,
        object_type: ObjectType,
    ) -> impl DoubleEndedIterator<Item = &TopologyObject> + FusedIterator + 'result {
        self.objects_with_type(object_type)
            .filter(move |object| object.is_inside_cpuset(set.borrow()))
    }

    /// First largest object included in the given cpuset `set`
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
    fn first_largest_object_inside_cpuset(
        &self,
        set: impl Borrow<CpuSet>,
    ) -> Option<&TopologyObject> {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized<'self_>(
            self_: &'self_ Topology,
            set: &CpuSet,
        ) -> Option<&'self_ TopologyObject> {
            // If root object doesn't intersect this CPU set then no child will
            let root = self_.root_object();
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
                'iterate_children: for child in parent.normal_children() {
                    if let Some(child_cpuset) = child.cpuset() {
                        // This child intersects, make it the new parent and recurse
                        if set.intersects(child_cpuset) {
                            parent = child;
                            parent_cpuset = child_cpuset;
                            break 'iterate_children;
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
        polymorphized(self, set.borrow())
    }
}

/// Iterator over largest objects inside a cpuset
#[derive(Clone, Debug)]
struct LargestObjectsInsideCpuSet<'topology> {
    /// Topology which is being interrogated
    topology: &'topology Topology,

    /// Share of the input [`CpuSet`] that hasn't been covered yet
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
        self.set -= object_cpuset;
        Some(object)
    }
}
//
impl FusedIterator for LargestObjectsInsideCpuSet<'_> {}

/// [`Topology::coarsest_cpuset_partition()`] was called for an invalid `cpuset`
///
/// This error is returned when the input `cpuset` is not a subset of the root
/// (topology-wide) cpuset. In that case, it is impossible to find topology
/// objects covering all of the input cpuset.
#[derive(Clone, Debug, Default, Eq, Error, PartialEq)]
#[error("can't partition {query} that isn't included in topology root {root}")]
pub struct CoarsestPartitionError {
    /// Requested cpuset
    pub query: CpuSet,

    /// Root cpuset covering all CPUs in the topology
    pub root: CpuSet,
}

/// # Finding objects covering at least a CPU set
//
// --- Implementation details ---
//
// This is inspired by the upstream functionality described at
// https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__find__covering.html
// and https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__find__cache.html
// but the code had to be ported to Rust because it's inline
impl Topology {
    /// Get the lowest object covering at least the given cpuset `set`, if any
    ///
    /// No object is considered to cover the empty cpuset, therefore such a
    /// request will always return None, as if a set going outside of the root
    /// cpuset were passed as input.
    #[doc(alias = "hwloc_get_obj_covering_cpuset")]
    pub fn smallest_object_covering_cpuset(
        &self,
        set: impl Borrow<CpuSet>,
    ) -> Option<&TopologyObject> {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized<'self_>(
            self_: &'self_ Topology,
            set: &CpuSet,
        ) -> Option<&'self_ TopologyObject> {
            let root = self_.root_object();
            if !root.covers_cpuset(set) || set.is_empty() {
                return None;
            }
            let mut parent = root;
            while let Some(child) = parent.normal_child_covering_cpuset(set) {
                parent = child;
            }
            Some(parent)
        }
        polymorphized(self, set.borrow())
    }

    /// Get the first data (or unified) cache covering the given cpuset
    #[doc(alias = "hwloc_get_cache_covering_cpuset")]
    pub fn first_cache_covering_cpuset(&self, set: impl Borrow<CpuSet>) -> Option<&TopologyObject> {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized<'self_>(
            self_: &'self_ Topology,
            set: &CpuSet,
        ) -> Option<&'self_ TopologyObject> {
            let first_obj = self_.smallest_object_covering_cpuset(set)?;
            std::iter::once(first_obj)
                .chain(first_obj.ancestors())
                .find(|obj| obj.object_type().is_cpu_data_cache())
        }
        polymorphized(self, set.borrow())
    }

    /// Enumerate objects covering the given cpuset `set` at a certain depth
    ///
    /// Objects are not considered to cover the empty CPU set (otherwise a list
    /// of all objects would be returned). An empty iterator will always be
    /// returned for I/O or Misc depths as those objects have no cpusets.
    #[doc(alias = "hwloc_get_next_obj_covering_cpuset_by_depth")]
    pub fn objects_covering_cpuset_at_depth<'result, DepthLike>(
        &'result self,
        set: impl Borrow<CpuSet> + 'result,
        depth: DepthLike,
    ) -> impl DoubleEndedIterator<Item = &TopologyObject> + FusedIterator + 'result
    where
        DepthLike: TryInto<Depth>,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        // This little hack works because hwloc topologies never get anywhere
        // close the maximum possible depth, which is c_int::MAX, so there will
        // never be any object at that depth. We need it because impl Trait
        // needs homogeneous return types.
        let depth = depth.try_into().unwrap_or(Depth::Normal(NormalDepth::MAX));
        self.objects_at_depth(depth)
            .filter(move |object| object.covers_cpuset(set.borrow()))
    }

    /// Get objects covering the given cpuset `set` with a certain type
    ///
    /// Objects are not considered to cover the empty CPU set (otherwise a list
    /// of all objects would be returned). An empty iterator will always be
    /// returned for I/O or Misc depths as those objects have no cpusets.
    #[doc(alias = "hwloc_get_next_obj_covering_cpuset_by_type")]
    pub fn objects_covering_cpuset_with_type<'result>(
        &'result self,
        set: impl Borrow<CpuSet> + 'result,
        object_type: ObjectType,
    ) -> impl DoubleEndedIterator<Item = &TopologyObject> + FusedIterator + 'result {
        self.objects_with_type(object_type)
            .filter(move |object| object.covers_cpuset(set.borrow()))
    }
}

/// # CpuSet-specific API
//
// --- Implementation details ---
//
// This goes before the main impl_bitmap_newtype macro so that it appears before
// the bitmap API reexport in rustdoc.
impl CpuSet {
    /// Remove simultaneous multithreading PUs from a CPU set
    ///
    /// For each [`Core`] in `topology`, if this cpuset contains several PUs of
    /// that core, modify it to only keep a single PU for that core.
    ///
    /// `which` specifies which PU will be kept, in physical index order. If it
    /// is set to 0, for each core, the function keeps the first PU that was
    /// originally set in `cpuset`. If it is larger than the number of PUs in a
    /// core that were originally set in `cpuset`, no PU is kept for that core.
    ///
    /// PUs that are not below a [`Core`] object (for instance if the topology
    /// does not contain any [`Core`] object) are kept in the cpuset.
    ///
    /// [`Core`]: ObjectType::Core
    #[cfg(feature = "hwloc-2_2_0")]
    #[doc(alias = "hwloc_bitmap_singlify_per_core")]
    pub fn singlify_per_core(&mut self, topology: &Topology, which: usize) {
        let Ok(which) = c_uint::try_from(which) else {
            self.clear();
            return;
        };
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - Bitmap is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted not to modify *const parameters
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - Per documentation, hwloc should handle arbitrarily large which values
        errors::call_hwloc_int_normal("hwloc_bitmap_singlify_per_core", || unsafe {
            hwlocality_sys::hwloc_bitmap_singlify_per_core(
                topology.as_ptr(),
                self.as_mut_ptr(),
                which,
            )
        })
        .expect("Per hwloc documentation, this function should not fail");
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
    #[doc(alias = "hwloc_cpuset_from_nodeset")]
    pub fn from_nodeset(topology: &Topology, nodeset: impl Borrow<NodeSet>) -> Self {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized(topology: &Topology, nodeset: &NodeSet) -> CpuSet {
            let mut cpuset = CpuSet::new();
            for obj in topology.objects_at_depth(Depth::NUMANode) {
                if nodeset.is_set(obj.os_index().expect("NUMA nodes should have OS indices")) {
                    cpuset |= obj.cpuset().expect("NUMA nodes should have cpusets");
                }
            }
            cpuset
        }
        polymorphized(topology, nodeset.borrow())
    }
}

impl_bitmap_newtype!(
    /// [`Bitmap`] whose bits are set according to CPU physical OS indexes
    ///
    /// A `CpuSet` represents a set of logical CPU cores, as exposed by the
    /// underlying operating system. These logical cores may map into either
    /// complete hardware CPU cores or SMT threads thereof
    /// (aka "hyper-threads") depending on the underlying hardware and OS
    /// configuration.
    ///
    /// Each bit may be converted into a PU object using
    /// [`Topology::pu_with_os_index()`].
    #[doc(alias = "hwloc_cpuset_t")]
    #[doc(alias = "hwloc_const_cpuset_t")]
    CpuSet
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::impl_bitmap_newtype_tests;

    impl_bitmap_newtype_tests!(CpuSet);
}
