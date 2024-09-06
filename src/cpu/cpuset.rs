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
use similar_asserts::assert_eq;
#[cfg(feature = "hwloc-2_2_0")]
use std::ffi::c_uint;
use std::{debug_assert, fmt::Debug, iter::FusedIterator, ops::Deref, ptr};
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
    /// `set` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`.
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
        set: impl Deref<Target = CpuSet>,
    ) -> Result<Vec<&TopologyObject>, CoarsestPartitionError> {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized<'self_>(
            self_: &'self_ Topology,
            set: &CpuSet,
        ) -> Result<Vec<&'self_ TopologyObject>, CoarsestPartitionError> {
            // Handle empty set edge case
            if set.is_empty() {
                return Ok(Vec::new());
            }

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
            fn process_object<'self_>(
                parent: &'self_ TopologyObject,
                set: &CpuSet,
                result: &mut Vec<&'self_ TopologyObject>,
                cpusets: &mut Vec<CpuSet>,
            ) {
                // If the current object matches the target cpuset, we're done
                let parent_cpuset = parent
                    .cpuset()
                    .expect("normal objects should have a cpuset");
                debug_assert!(
                    parent_cpuset.intersects(set),
                    "shouldn't recurse into objects with an unrelated cpuset"
                );
                if parent_cpuset == set {
                    result.push(parent);
                    return;
                }

                // Otherwise, look for children that cover the target cpuset
                let mut subset = cpusets.pop().unwrap_or_default();
                for child in parent.normal_children() {
                    // Ignore children that don't intersect the target cpuset
                    let child_cpuset = child.cpuset().expect("normal objects should have a cpuset");
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
        polymorphized(self, &set)
    }

    /// Enumerate objects included in the given cpuset `set` at a certain depth
    ///
    /// Accepted operand types are as follows:
    ///
    /// - `set` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`
    /// - `depth` can be a [`Depth`], a [`NormalDepth`] or an [`usize`]
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set). Therefore, an empty iterator will
    /// always be returned for I/O or Misc depths as those objects have no cpusets.
    #[doc(alias = "hwloc_get_obj_inside_cpuset_by_depth")]
    #[doc(alias = "hwloc_get_next_obj_inside_cpuset_by_depth")]
    #[doc(alias = "hwloc_get_nbobjs_inside_cpuset_by_depth")]
    pub fn objects_inside_cpuset_at_depth<'iterator, 'self_: 'iterator, DepthLike>(
        &'self_ self,
        set: impl Deref<Target = CpuSet> + 'iterator,
        depth: DepthLike,
    ) -> impl DoubleEndedIterator<Item = &'self_ TopologyObject> + FusedIterator + 'iterator
    where
        DepthLike: TryInto<Depth>,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        // This little hack works because hwloc topologies never get anywhere
        // close the maximum possible depth, which is c_int::MAX, so there will
        // never be any object at that depth. We need it because impl Trait
        // needs homogeneous return types.
        let depth = depth.try_into().unwrap_or(Depth::Normal(NormalDepth::MAX));
        self.objects_at_depth(depth).filter(move |object| {
            let set: &CpuSet = &set;
            object.is_inside_cpuset(set)
        })
    }

    /// Logical index among the objects included in CPU set `set`
    ///
    /// Consult all objects in the same level as `obj` and inside CPU set `set`
    /// in the logical order, and return the index of `obj` within them. If
    /// `set` covers the entire topology, this is the logical index of `obj`.
    /// Otherwise, this is similar to a logical index within the part of the
    /// topology defined by CPU set `set`.
    ///
    /// `set` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`.
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set). Therefore, `None` will always be
    /// returned for I/O or Misc depths as those objects have no cpusets.
    ///
    /// This method will also return `None` if called with an `obj` that does
    /// not belong to this [`Topology`].
    #[doc(alias = "hwloc_get_obj_index_inside_cpuset")]
    pub fn object_index_inside_cpuset<'self_>(
        &'self_ self,
        set: impl Deref<Target = CpuSet>,
        obj: &'self_ TopologyObject,
    ) -> Option<usize> {
        // obj may not belong to this topology, but the current implementation
        // is fine with that and will just return None.
        self.objects_inside_cpuset_at_depth(set, obj.depth())
            .position(|candidate| std::ptr::eq(candidate, obj))
    }

    /// Get objects included in the given cpuset `set` with a certain type
    ///
    /// `set` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`.
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set). Therefore, an empty iterator will
    /// always be returned for I/O or Misc objects as they don't have cpusets.
    #[doc(alias = "hwloc_get_obj_inside_cpuset_by_type")]
    #[doc(alias = "hwloc_get_next_obj_inside_cpuset_by_type")]
    #[doc(alias = "hwloc_get_nbobjs_inside_cpuset_by_type")]
    pub fn objects_inside_cpuset_with_type<'iterator, 'self_: 'iterator>(
        &'self_ self,
        set: impl Deref<Target = CpuSet> + 'iterator,
        object_type: ObjectType,
    ) -> impl DoubleEndedIterator<Item = &'self_ TopologyObject> + FusedIterator + 'iterator {
        self.objects_with_type(object_type).filter(move |object| {
            let set: &CpuSet = &set;
            object.is_inside_cpuset(set)
        })
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
    /// `set` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`.
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set).
    fn first_largest_object_inside_cpuset(
        &self,
        set: impl Deref<Target = CpuSet>,
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
        polymorphized(self, &set)
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
    /// `set` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`.
    ///
    /// No object is considered to cover the empty cpuset, therefore such a
    /// request will always return None, as if a set going outside of the root
    /// cpuset were passed as input.
    #[doc(alias = "hwloc_get_obj_covering_cpuset")]
    pub fn smallest_object_covering_cpuset(
        &self,
        set: impl Deref<Target = CpuSet>,
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
        polymorphized(self, &set)
    }

    /// Get the first data (or unified) cache covering the given cpuset
    ///
    /// `set` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`.
    #[doc(alias = "hwloc_get_cache_covering_cpuset")]
    pub fn first_cache_covering_cpuset(
        &self,
        set: impl Deref<Target = CpuSet>,
    ) -> Option<&TopologyObject> {
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
        polymorphized(self, &set)
    }

    /// Enumerate objects covering the given cpuset `set` at a certain depth
    ///
    /// Accepted operand types are as follows:
    ///
    /// - `set` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`
    /// - `depth` can be a [`Depth`], a [`NormalDepth`] or an [`usize`]
    ///
    /// Objects are not considered to cover the empty CPU set (otherwise a list
    /// of all objects would be returned). An empty iterator will always be
    /// returned for I/O or Misc depths as those objects have no cpusets.
    #[doc(alias = "hwloc_get_next_obj_covering_cpuset_by_depth")]
    pub fn objects_covering_cpuset_at_depth<'iterator, 'self_: 'iterator, DepthLike>(
        &'self_ self,
        set: impl Deref<Target = CpuSet> + 'iterator,
        depth: DepthLike,
    ) -> impl DoubleEndedIterator<Item = &'self_ TopologyObject> + FusedIterator + 'iterator
    where
        DepthLike: TryInto<Depth>,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        // This little hack works because hwloc topologies never get anywhere
        // close the maximum possible depth, which is c_int::MAX, so there will
        // never be any object at that depth. We need it because impl Trait
        // needs homogeneous return types.
        let depth = depth.try_into().unwrap_or(Depth::Normal(NormalDepth::MAX));
        self.objects_at_depth(depth).filter(move |object| {
            let set: &CpuSet = &set;
            object.covers_cpuset(set)
        })
    }

    /// Get objects covering the given cpuset `set` with a certain type
    ///
    /// `set` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`.
    ///
    /// Objects are not considered to cover the empty CPU set (otherwise a list
    /// of all objects would be returned). An empty iterator will always be
    /// returned for I/O or Misc depths as those objects have no cpusets.
    #[doc(alias = "hwloc_get_next_obj_covering_cpuset_by_type")]
    pub fn objects_covering_cpuset_with_type<'iterator, 'self_: 'iterator>(
        &'self_ self,
        set: impl Deref<Target = CpuSet> + 'iterator,
        object_type: ObjectType,
    ) -> impl DoubleEndedIterator<Item = &'self_ TopologyObject> + FusedIterator + 'iterator {
        self.objects_with_type(object_type).filter(move |object| {
            let set: &CpuSet = &set;
            object.covers_cpuset(set)
        })
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
                c_uint::try_from(which).unwrap_or(c_uint::MAX),
            )
        })
        .expect("Per hwloc documentation, this function should not fail");
    }

    /// Convert a NUMA node set into a CPU set
    ///
    /// `nodeset` can be a `&'_ NodeSet` or a `BitmapRef<'_, NodeSet>`.
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
    pub fn from_nodeset(topology: &Topology, nodeset: impl Deref<Target = NodeSet>) -> Self {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized(topology: &Topology, nodeset: &NodeSet) -> CpuSet {
            topology
                .nodes_from_nodeset(nodeset)
                .fold(CpuSet::new(), |mut cpuset, node| {
                    cpuset |= node.cpuset().expect("NUMA nodes should have cpusets");
                    cpuset
                })
        }
        polymorphized(topology, &nodeset)
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
    use crate::{
        object::{
            hierarchy::tests::{any_hwloc_depth, any_normal_depth, any_usize_depth},
            lists::tests::compare_object_sets,
            tests::object_and_related_cpuset,
        },
        strategies::topology_related_set,
    };
    use proptest::prelude::*;
    use std::collections::HashSet;

    proptest! {
        /// Test for [`Topology::largest_objects_inside_cpuset()`]
        #[test]
        fn largest_objects_inside_cpuset(set in topology_related_set(Topology::cpuset)) {
            // Compute direct result
            let topology = Topology::test_instance();
            let mut result = topology.largest_objects_inside_cpuset(set.clone());

            // Figure out which objects we should get by iterating in order of
            // increasing depth, noting which objects match...
            let mut remaining_set = set;
            let mut expected = HashSet::new();
            'depths: for depth in NormalDepth::iter_range(NormalDepth::MIN, topology.depth()) {
                for obj in topology.objects_at_depth(depth) {
                    if obj.is_inside_cpuset(&remaining_set) {
                        prop_assert!(expected.insert(obj.global_persistent_index()));
                        // ...and updating the search cpuset as we go in order
                        // to avoid double-counting children of these objects
                        remaining_set -= obj.cpuset().unwrap();
                        if remaining_set.is_empty() {
                            break 'depths;
                        }
                    }
                }
            }

            // Check that the iterator yields all expected objects and only them
            for _ in 0..expected.len() {
                let out_obj = result.next().unwrap();
                prop_assert!(expected.remove(&out_obj.global_persistent_index()));
            }
            prop_assert!(result.next().is_none());
        }

        /// Test for [`Topology::coarsest_cpuset_partition()`]
        #[test]
        fn coarsest_cpuset_partition(set in topology_related_set(Topology::cpuset)) {
            // Compute direct result
            let topology = Topology::test_instance();
            let result = topology.coarsest_cpuset_partition(&set);

            // This function should only succeed when the input set is a subset
            // of the topology cpuset
            if !topology.cpuset().includes(&set) {
                let expected_error = CoarsestPartitionError {
                    query: set,
                    root: topology.cpuset().clone_target()
                };
                prop_assert!(matches!(result, Err(e) if e == expected_error));
                return Ok(());
            }
            let result = result.unwrap();

            // When it does succeed, it should produce the same output as
            // largest_objects_inside_cpuset
            let mut expected = topology
                .largest_objects_inside_cpuset(set)
                .map(TopologyObject::global_persistent_index)
                .collect::<HashSet<_>>();
            for obj in result {
                prop_assert!(expected.remove(&obj.global_persistent_index()));
            }
            prop_assert_eq!(expected, HashSet::new());
        }

        /// Test for [`Topology::objects_covering_cpuset_with_type()`]
        #[test]
        fn objects_covering_cpuset_with_type(
            set in topology_related_set(Topology::cpuset),
            object_type: ObjectType
        ) {
            let topology = Topology::test_instance();
            compare_object_sets(
                topology.objects_covering_cpuset_with_type(&set, object_type),
                topology.objects_with_type(object_type).filter(|obj| obj.covers_cpuset(&set))
            )?;
        }

        /// Test for [`Topology::object_index_inside_cpuset()`]
        #[test]
        fn object_index_inside_cpuset((obj, set) in object_and_related_cpuset()) {
            let topology = Topology::test_instance();
            prop_assert_eq!(
                topology.object_index_inside_cpuset(&set, obj),
                topology.objects_inside_cpuset_at_depth(&set, obj.depth())
                        .position(|candidate| ptr::eq(candidate, obj))
            );
        }

        /// Test for [`CpuSet::from_nodeset()`]
        #[test]
        fn cpuset_from_nodeset(
            nodeset in topology_related_set(Topology::nodeset),
        ) {
            let topology = Topology::test_instance();
            prop_assert_eq!(
                CpuSet::from_nodeset(topology, &nodeset),
                topology.nodes_from_nodeset(&nodeset)
                        .map(|node| node.cpuset().unwrap().clone_target())
                        .reduce(|set1, set2| set1 | set2)
                        .unwrap_or_default()
            )
        }
    }

    /// Find the smallest object covering a cpuset whose type matches some
    /// conditions, using a naive algorithm
    fn smallest_obj_above_cpuset_with_type_filter(
        set: &CpuSet,
        mut type_filter: impl FnMut(ObjectType) -> bool,
    ) -> Option<&'static TopologyObject> {
        let topology = Topology::test_instance();
        'depths: for depth in NormalDepth::iter_range(NormalDepth::MIN, topology.depth()).rev() {
            if !type_filter(topology.type_at_depth(depth).unwrap()) {
                continue 'depths;
            }
            for obj in topology.objects_at_depth(depth) {
                if obj.covers_cpuset(set) {
                    return Some(obj);
                }
            }
        }
        None
    }

    proptest! {
        /// Test for [`Topology::smallest_object_covering_cpuset()`]
        #[test]
        fn smallest_object_covering_cpuset(set in topology_related_set(Topology::cpuset)) {
            // Compute direct result
            let topology = Topology::test_instance();
            let result = topology.smallest_object_covering_cpuset(&set);

            // Check against output of naive algorithm
            if let Some(obj) = smallest_obj_above_cpuset_with_type_filter(&set, |_| true) {
                prop_assert!(ptr::eq(result.unwrap(), obj));
            } else {
                prop_assert!(result.is_none());
            }
        }

        /// Test for [`Topology::first_cache_covering_cpuset()`]
        #[test]
        fn first_cache_covering_cpuset(set in topology_related_set(Topology::cpuset)) {
            // Compute direct result
            let topology = Topology::test_instance();
            let result = topology.first_cache_covering_cpuset(&set);

            // Check against output of naive algorithm
            if let Some(obj) = smallest_obj_above_cpuset_with_type_filter(&set, ObjectType::is_cpu_data_cache) {
                prop_assert!(ptr::eq(result.unwrap(), obj));
            } else {
                prop_assert!(result.is_none());
            }
        }
    }

    // === Test singlify_per_core ===

    #[cfg(feature = "hwloc-2_2_0")]
    mod singlify_per_core {
        use super::*;
        use std::collections::HashMap;

        /// Generate a `which` input that is usually sensible, but can be anything
        fn any_core_pu_idx() -> impl Strategy<Value = usize> {
            let topology = Topology::test_instance();
            let max_pus_per_core = topology
                .objects_with_type(ObjectType::Core)
                .map(|core| core.cpuset().unwrap().weight().unwrap())
                .max()
                .unwrap_or(1);
            prop_oneof![
                4 => 0..max_pus_per_core,
                1 => max_pus_per_core..=usize::MAX
            ]
        }

        proptest! {
            /// Test for [`Topology::singlify_per_core()`]
            #[test]
            fn singlify_per_core(
                mut set in topology_related_set(Topology::cpuset),
                which in any_core_pu_idx(),
            ) {
                // Start by computing the expected result
                let topology = Topology::test_instance();

                // Do a pass over PUs in the cpuset, directly adding PUs that don't
                // have a core parent, and keeping track of which PUs are below each
                // core in OS index order.
                let mut expected_result = &set - topology.cpuset();
                let mut core_to_cpu_indices = HashMap::<_, CpuSet>::new();
                for pu in topology.pus_from_cpuset(&set) {
                    let cpu_idx = pu.os_index().unwrap();
                    #[allow(clippy::option_if_let_else)]
                    if let Some(core) = pu.ancestors().find(|obj| obj.object_type() == ObjectType::Core) {
                        core_to_cpu_indices.entry(core.global_persistent_index()).or_default().set(cpu_idx)
                    } else {
                        expected_result.set(cpu_idx);
                    }
                }

                // Pick the requested PU below each core, if any
                for (_core_id, cpus_below_core) in core_to_cpu_indices {
                    if let Some(cpu_idx) = cpus_below_core.iter_set().nth(which) {
                        expected_result.set(cpu_idx);
                    }
                }

                // Check if the output matches our expectation
                set.singlify_per_core(topology, which);
                prop_assert_eq!(set, expected_result);
            }
        }
    }

    // === Test methods that need a (set, depth) tuple ===

    /// Test for [`Topology::objects_inside_cpuset_at_depth()`]
    fn check_objects_inside_cpuset_at_depth<DepthLike>(
        set: &CpuSet,
        depth: DepthLike,
    ) -> Result<(), TestCaseError>
    where
        DepthLike: TryInto<Depth> + Copy + Debug + Eq,
        Depth: PartialEq<DepthLike>,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        let topology = Topology::test_instance();
        compare_object_sets(
            topology.objects_inside_cpuset_at_depth(set, depth),
            topology
                .objects_at_depth(depth)
                .filter(|obj| obj.is_inside_cpuset(set)),
        )
    }

    /// Test for [`Topology::objects_covering_cpuset_at_depth()`]
    fn check_objects_covering_cpuset_at_depth<DepthLike>(
        set: &CpuSet,
        depth: DepthLike,
    ) -> Result<(), TestCaseError>
    where
        DepthLike: TryInto<Depth> + Copy + Debug + Eq,
        Depth: PartialEq<DepthLike>,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        let topology = Topology::test_instance();
        compare_object_sets(
            topology.objects_covering_cpuset_at_depth(set, depth),
            topology
                .objects_at_depth(depth)
                .filter(|obj| obj.covers_cpuset(set)),
        )
    }

    proptest! {
        // Test all of the above for all depth types
        #[test]
        fn check_objects_inside_cpuset_at_hwloc_depth(
            set in topology_related_set(Topology::cpuset),
            depth in any_hwloc_depth()
        ) {
            check_objects_inside_cpuset_at_depth(&set, depth)?;
            check_objects_covering_cpuset_at_depth(&set, depth)?;
        }
        //
        #[test]
        fn check_objects_inside_cpuset_at_normal_depth(
            set in topology_related_set(Topology::cpuset),
            depth in any_normal_depth()
        ) {
            check_objects_inside_cpuset_at_depth(&set, depth)?;
            check_objects_covering_cpuset_at_depth(&set, depth)?;
        }
        //
        #[test]
        fn check_objects_inside_cpuset_at_usize_depth(
            set in topology_related_set(Topology::cpuset),
            depth in any_usize_depth()
        ) {
            check_objects_inside_cpuset_at_depth(&set, depth)?;
            check_objects_covering_cpuset_at_depth(&set, depth)?;
        }
    }
}
