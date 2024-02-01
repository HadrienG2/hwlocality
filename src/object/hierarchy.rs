//! Queries against the depth- and type-based hierarchy of objects

use super::{
    attributes::ObjectAttributes,
    depth::{Depth, NormalDepth, TypeToDepthError},
    types::{CacheType, ObjectType},
    TopologyObject,
};
use crate::{
    ffi::{int, transparent::AsNewtype},
    object::TopologyObjectID,
    topology::Topology,
};
use hwlocality_sys::hwloc_obj_type_t;
use num_enum::TryFromPrimitiveError;
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::{collections::HashMap, ffi::c_uint, fmt::Debug, iter::FusedIterator};

/// # Object levels, depths and types
///
/// Be sure to see read through the
/// [Terms and Definitions](https://hwloc.readthedocs.io/en/v2.9/termsanddefs.html)
/// section of the upstream hwloc documentation to avoid any confusion about
/// depths, child/sibling/cousin relationships, and see an example of an
/// asymmetric topology where one package has fewer caches than its peers.
//
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__levels.html
// Also includes https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__find__cache.html,
// which had to be reimplemented because it's static.
impl Topology {
    /// Depth of the hierarchical tree of objects
    ///
    /// This is the depth of [`ObjectType::PU`] plus one. NUMA nodes, I/O and
    /// Misc objects are ignored when computing the depth of the tree (they are
    /// placed at special depths).
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::{object::types::ObjectType, Topology};
    /// # let topology = hwlocality::Topology::test_instance();
    /// let depth = topology.depth();
    /// assert!(depth >= 2, "Machine and PU are always present");
    /// assert_eq!(
    ///     depth,
    ///     topology.depth_for_type(ObjectType::PU)?.expect_normal() + 1
    /// );
    /// # Ok::<(), eyre::Report>(())
    /// ```
    #[doc(alias = "hwloc_topology_get_depth")]
    pub fn depth(&self) -> NormalDepth {
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted not to modify *const parameters
        NormalDepth::try_from_c_int(unsafe {
            hwlocality_sys::hwloc_topology_get_depth(self.as_ptr())
        })
        .expect("Got unexpected depth from hwloc_topology_get_depth")
    }

    /// Depth of normal parents where memory objects are attached
    ///
    /// # Errors
    ///
    /// - [`TypeToDepthError::Multiple`] if memory objects are attached at multiple
    ///   depths, e.g. some to [`Package`]s and some to [`Group`]s
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::object::TopologyObject;
    /// # let topology = hwlocality::Topology::test_instance();
    /// if let Ok(depth) = topology.memory_parents_depth() {
    ///     let num_memory_objects =
    ///         topology.objects_at_depth(depth)
    ///                 .flat_map(TopologyObject::memory_children)
    ///                 .count();
    ///     assert!(num_memory_objects > 0);
    /// }
    /// # Ok::<(), eyre::Report>(())
    /// ```
    ///
    /// [`Package`]: ObjectType::Package
    /// [`Group`]: ObjectType::Group
    #[doc(alias = "hwloc_get_memory_parents_depth")]
    pub fn memory_parents_depth(&self) -> Result<NormalDepth, TypeToDepthError> {
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted not to modify *const parameters
        Depth::from_raw(unsafe { hwlocality_sys::hwloc_get_memory_parents_depth(self.as_ptr()) })
            .map(Depth::expect_normal)
    }

    /// Depth for the given [`ObjectType`]
    ///
    /// # Errors
    ///
    /// - [`TypeToDepthError::Nonexistent`] if no object of this type is present or
    ///   if the OS doesn't provide this kind of information. If a similar type
    ///   is acceptable, consider using [`depth_or_below_for_type()`] or
    ///   [`depth_or_above_for_type()`] instead.
    /// - [`TypeToDepthError::Multiple`] if objects of this type exist at multiple
    ///   depths (can happen when `object_type` is [`Group`]).
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::object::types::ObjectType;
    /// #
    /// # let topology = hwlocality::Topology::test_instance();
    /// #
    /// let machine_depth = topology.depth_for_type(ObjectType::Machine)?;
    /// let pu_depth = topology.depth_for_type(ObjectType::PU)?;
    ///
    /// assert_eq!(machine_depth.expect_normal(), 0);
    /// assert!(machine_depth.expect_normal() < pu_depth.expect_normal());
    /// #
    /// # Ok::<(), eyre::Report>(())
    /// ```
    ///
    /// [`depth_or_below_for_type()`]: Self::depth_or_below_for_type()
    /// [`depth_or_above_for_type()`]: Self::depth_or_above_for_type()
    /// [`Group`]: ObjectType::Group
    #[doc(alias = "hwloc_get_type_depth")]
    pub fn depth_for_type(&self, object_type: ObjectType) -> Result<Depth, TypeToDepthError> {
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted not to modify *const parameters
        //         - By construction, ObjectType only exposes values that map into
        //           hwloc_obj_type_t values understood by the configured version
        //           of hwloc, and build.rs checks that the active version of
        //           hwloc is not older than that, so into() may only generate
        //           valid hwloc_obj_type_t values for current hwloc
        Depth::from_raw(unsafe {
            hwlocality_sys::hwloc_get_type_depth(self.as_ptr(), object_type.into())
        })
    }

    /// Depth for the given [`ObjectType`] or below
    ///
    /// If no object of this type is present on the underlying architecture, the
    /// function returns the depth of the first present object typically found
    /// inside `object_type`.
    ///
    /// This function is only meaningful for normal object types. Passing in a
    /// memory, I/O or Misc object type will result in a panic.
    ///
    /// # Errors
    ///
    /// [`TypeToDepthError::Multiple`] if objects of this type exist at multiple
    /// depths (can happen when `object_type` is [`Group`]).
    ///
    /// # Panics
    ///
    /// If `object_type` is not a normal object type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::{object::types::ObjectType};
    /// #
    /// # let topology = hwlocality::Topology::test_instance();
    /// #
    /// let machine_depth = topology.depth_for_type(ObjectType::Machine)?;
    /// let package_or_below = topology.depth_or_below_for_type(ObjectType::Package)?;
    ///
    /// assert!(machine_depth.expect_normal() < package_or_below.expect_normal());
    /// #
    /// # Ok::<(), eyre::Report>(())
    /// ```
    ///
    /// [`Group`]: ObjectType::Group
    #[doc(alias = "hwloc_get_type_or_below_depth")]
    pub fn depth_or_below_for_type(
        &self,
        object_type: ObjectType,
    ) -> Result<Depth, TypeToDepthError> {
        // Virtual object type special case
        assert!(
            object_type.is_normal(),
            "this function only makes sense for normal object types"
        );

        // Normal object type case
        match self.depth_for_type(object_type) {
            Ok(d) => Ok(d),
            Err(TypeToDepthError::Nonexistent) => {
                let first_depth_above = NormalDepth::iter_range(NormalDepth::ZERO, self.depth())
                    // Can't use binary search due to group objects
                    .rfind(|&depth| {
                        self.type_at_depth(depth)
                            .expect("only valid depths are being iterated over")
                            < object_type
                    })
                    .expect("shouldn't fail since PUs are always present and at the bottom");
                // First depth above + 1 is first depth below
                Ok(Depth::from(first_depth_above + 1))
            }
            other_err => other_err,
        }
    }

    /// Depth for the given [`ObjectType`] or above
    ///
    /// If no object of this type is present on the underlying architecture, the
    /// function returns the depth of the first present object typically
    /// containing `object_type`.
    ///
    /// This function is only meaningful for normal object types. Passing in a
    /// memory, I/O or Misc object type will result in a panic.
    ///
    /// # Errors
    ///
    /// [`TypeToDepthError::Multiple`] if objects of this type exist at multiple
    /// depths (can happen when `object_type` is [`Group`]).
    ///
    /// # Panics
    ///
    /// If `object_type` is not a normal object type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::object::types::ObjectType;
    /// #
    /// # let topology = hwlocality::Topology::test_instance();
    /// #
    /// let pu_depth = topology.depth_for_type(ObjectType::PU)?;
    /// let core_or_above = topology.depth_or_below_for_type(ObjectType::Core)?;
    ///
    /// assert!(core_or_above.expect_normal() < pu_depth.expect_normal());
    /// #
    /// # Ok::<(), eyre::Report>(())
    /// ```
    ///
    /// [`Group`]: ObjectType::Group
    #[doc(alias = "hwloc_get_type_or_above_depth")]
    pub fn depth_or_above_for_type(
        &self,
        object_type: ObjectType,
    ) -> Result<Depth, TypeToDepthError> {
        // Virtual object type special case
        assert!(
            object_type.is_normal(),
            "this function only makes sense for normal object types"
        );

        // Normal object type case
        match self.depth_for_type(object_type) {
            Ok(d) => Ok(d),
            Err(TypeToDepthError::Nonexistent) => {
                let first_depth_below = NormalDepth::iter_range(NormalDepth::ZERO, self.depth())
                    // Can't use binary search due to group objects
                    .find(|&depth| {
                        self.type_at_depth(depth)
                            .expect("only valid depths are being iterated over")
                            > object_type
                    })
                    .expect("shouldn't fail since Machine is always present and at the top");
                // First depth below - 1 is first depth above
                Ok(Depth::from(first_depth_below - 1))
            }
            other_err => other_err,
        }
    }

    /// Depth for the given cache type and level
    ///
    /// Returns the depth of the topology level that contains cache objects whose
    /// attributes match `cache_level` and `cache_type`.
    ///
    /// This function is similar to calling [`depth_for_type()`] with
    /// the corresponding type such as [`ObjectType::L1ICache`], except that it
    /// may also return a unified cache when looking for an instruction cache.
    ///
    /// Please note that following hardware nomenclature, cache levels normally
    /// start at 1 (corresponding to the hardware L1 cache), not 0.
    ///
    /// If `cache_type` is `None`, it is ignored and multiple levels may match.
    /// The function returns either the depth of a uniquely matching level or
    /// Err([`TypeToDepthError::Multiple`]).
    ///
    /// If `cache_type` is Some([`CacheType::Unified`]), the depth of the unique
    /// matching unified cache level (if any) is returned.
    ///
    /// If `cache_type` is Some([`CacheType::Data`]) or
    /// Some([`CacheType::Instruction`]), either a matching cache or a
    /// unified cache is returned.
    ///
    /// # Errors
    ///
    /// - [`TypeToDepthError::Nonexistent`] if no cache level matches
    /// - [`TypeToDepthError::Multiple`] if multiple cache depths match (this can only
    ///   happen if `cache_type` is `None`).
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::object::types::CacheType;
    /// # let topology = hwlocality::Topology::test_instance();
    /// let l1d_depth = topology.depth_for_cache(1, Some(CacheType::Data));
    /// assert!(l1d_depth.is_ok());
    /// # Ok::<(), eyre::Report>(())
    /// ```
    ///
    /// [`depth_for_type()`]: Self::depth_for_type()
    #[doc(alias = "hwloc_get_cache_type_depth")]
    pub fn depth_for_cache(
        &self,
        cache_level: usize,
        cache_type: Option<CacheType>,
    ) -> Result<Depth, TypeToDepthError> {
        // Otherwise, need to actually look it up
        let mut result = Err(TypeToDepthError::Nonexistent);
        for depth in NormalDepth::iter_range(NormalDepth::MIN, self.depth()) {
            // Cache level and type are homogeneous across a depth level so we
            // only need to look at one object
            let obj = self
                .objects_at_depth(depth)
                .next()
                .expect("valid depths should contain objects");

            // Is this a cache?
            if let Some(ObjectAttributes::Cache(cache)) = obj.attributes() {
                // Check cache level
                if cache.depth() != cache_level {
                    continue;
                }

                // Check cache type if instructed to do so
                if let Some(cache_type) = cache_type {
                    if cache.cache_type() == cache_type || cache.cache_type() == CacheType::Unified
                    {
                        // If both cache type + level are specified, then
                        // multiple matches cannot occur: stop here.
                        return Ok(depth.into());
                    } else {
                        continue;
                    }
                } else {
                    // Without a cache type check, multiple matches may
                    // occur, so we need to check all other depths.
                    match result {
                        Err(TypeToDepthError::Nonexistent) => result = Ok(depth.into()),
                        Ok(_) => {
                            return Err(TypeToDepthError::Multiple);
                        }
                        Err(TypeToDepthError::Multiple) => {
                            unreachable!("setting this value triggers a loop break")
                        }
                        Err(TypeToDepthError::Unexpected(_)) => {
                            unreachable!("this value is never set")
                        }
                    }
                }
            }
        }
        result
    }

    /// Type of objects at the given `depth`, if any
    ///
    /// `depth` can be a [`Depth`], a [`NormalDepth`] or an [`usize`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::object::{depth::Depth, types::ObjectType};
    /// # let topology = hwlocality::Topology::test_instance();
    /// let numa_type = topology.type_at_depth(Depth::NUMANode);
    /// assert_eq!(numa_type, Some(ObjectType::NUMANode));
    /// # Ok::<(), eyre::Report>(())
    /// ```
    #[doc(alias = "hwloc_get_depth_type")]
    pub fn type_at_depth<DepthLike>(&self, depth: DepthLike) -> Option<ObjectType>
    where
        DepthLike: TryInto<Depth>,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized(self_: &Topology, depth: Depth) -> Option<ObjectType> {
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - hwloc ops are trusted not to modify *const parameters
            //         - By construction, Depth only exposes values that map into
            //           hwloc_get_depth_type_e values understood by the configured
            //           version of hwloc, and build.rs checks that the active
            //           version of hwloc is not older than that, so into() may only
            //           generate valid hwloc_get_depth_type_e values for current hwloc
            match unsafe { hwlocality_sys::hwloc_get_depth_type(self_.as_ptr(), depth.to_raw()) }
                .try_into()
            {
                Ok(depth) => Some(depth),
                Err(TryFromPrimitiveError {
                    number: hwloc_obj_type_t::MAX,
                }) => None,
                Err(unknown) => {
                    unreachable!("Got unknown object type from hwloc_get_depth_type: {unknown}")
                }
            }
        }

        // There cannot be any object at a depth below the hwloc-supported max
        let depth = depth.try_into().ok()?;
        polymorphized(self, depth)
    }

    /// Number of objects at the given `depth`
    ///
    /// `depth` can be a [`Depth`], a [`NormalDepth`] or an [`usize`].
    ///
    /// # Examples
    ///
    /// ```
    /// # let topology = hwlocality::Topology::test_instance();
    /// #
    /// let num_roots = topology.num_objects_at_depth(0);
    /// assert_eq!(num_roots, 1);
    ///
    /// let num_root_children = topology.num_objects_at_depth(1);
    /// assert!(num_root_children > 0);
    /// #
    /// # Ok::<(), eyre::Report>(())
    /// ```
    #[doc(alias = "hwloc_get_nbobjs_by_depth")]
    pub fn num_objects_at_depth<DepthLike>(&self, depth: DepthLike) -> usize
    where
        DepthLike: TryInto<Depth>,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        // There cannot be any object at a depth below the hwloc-supported max
        let Ok(depth) = depth.try_into() else {
            return 0;
        };
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted not to modify *const parameters
        //         - By construction, Depth only exposes values that map into
        //           hwloc_get_depth_type_e values understood by the configured
        //           version of hwloc, and build.rs checks that the active
        //           version of hwloc is not older than that, so into() may only
        //           generate valid hwloc_get_depth_type_e values for current hwloc
        int::expect_usize(unsafe {
            hwlocality_sys::hwloc_get_nbobjs_by_depth(self.as_ptr(), depth.to_raw())
        })
    }

    /// [`TopologyObject`]s at the given `depth`
    ///
    /// `depth` can be a [`Depth`], a [`NormalDepth`] or an [`usize`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::object::{depth::Depth, types::ObjectType};
    /// # let topology = hwlocality::Topology::test_instance();
    /// #
    /// use eyre::eyre;
    ///
    /// let root = topology.root_object();
    ///
    /// for node in topology.objects_at_depth(Depth::NUMANode) {
    ///     assert_eq!(node.object_type(), ObjectType::NUMANode);
    ///     assert!(node.is_in_subtree(root));
    ///     assert_eq!(node.normal_arity(), 0);
    ///     assert_eq!(node.memory_arity(), 0);
    ///     let num_nodes =
    ///         node.nodeset()
    ///             .ok_or_else(|| eyre!("a NUMANode should have a NodeSet"))?
    ///             .weight()
    ///             .ok_or_else(|| {
    ///                 eyre!("a NUMANode's NodeSet should be finite")
    ///             })?;
    ///     assert_eq!(num_nodes, 1);
    /// }
    /// #
    /// # Ok::<(), eyre::Report>(())
    /// ```
    #[doc(alias = "hwloc_get_obj_by_depth")]
    #[doc(alias = "hwloc_get_next_obj_by_depth")]
    pub fn objects_at_depth<DepthLike>(
        &self,
        depth: DepthLike,
    ) -> impl DoubleEndedIterator<Item = &TopologyObject> + Clone + ExactSizeIterator + FusedIterator
    where
        DepthLike: TryInto<Depth>,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized(
            self_: &Topology,
            depth: Depth,
        ) -> impl DoubleEndedIterator<Item = &TopologyObject> + Clone + ExactSizeIterator + FusedIterator
        {
            let size = self_.num_objects_at_depth(depth);
            let depth = depth.to_raw();
            (0..size).map(move |idx| {
                let idx = c_uint::try_from(idx).expect("Can't happen, size comes from hwloc");
                let ptr =
                    // SAFETY: - Topology is trusted to contain a valid ptr
                    //           (type invariant)
                    //         - hwloc ops are trusted not to modify *const
                    //           parameters
                    //         - By construction, Depth only exposes values that
                    //           map into hwloc_get_depth_type_e values
                    //           understood by the configured version of hwloc,
                    //           and build.rs checks that the active version of
                    //           hwloc is not older than that, so into() may
                    //           only generate valid hwloc_get_depth_type_e
                    //           values for current hwloc
                    //         - idx is in bounds by construction
                    unsafe { hwlocality_sys::hwloc_get_obj_by_depth(self_.as_ptr(), depth, idx) };
                assert!(
                    !ptr.is_null(),
                    "Got null pointer from hwloc_get_obj_by_depth"
                );
                // SAFETY: If hwloc_get_obj_by_depth returns a non-null pointer,
                //         it's assumed to be successful and thus that the
                //         output pointer and its target are valid
                unsafe { (&*ptr).as_newtype() }
            })
        }

        // This little hack works because hwloc topologies never get anywhere
        // close the maximum possible depth, which is c_int::MAX, so there will
        // never be any object at that depth. We need it because impl Trait
        // needs homogeneous return types.
        let depth = depth.try_into().unwrap_or(Depth::Normal(NormalDepth::MAX));
        polymorphized(self, depth)
    }

    /// [`TopologyObject`] at the root of the topology
    ///
    /// Its type is [`ObjectType::Machine`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::object::{
    /// #     depth::{Depth, NormalDepth},
    /// #     types::ObjectType
    /// # };
    /// # let topology = hwlocality::Topology::test_instance();
    /// let root = topology.root_object();
    ///
    /// assert_eq!(root.object_type(), ObjectType::Machine);
    ///
    /// assert_eq!(root.depth(), NormalDepth::MIN);
    /// assert!(root.parent().is_none());
    ///
    /// assert!(root.cpuset().is_some());
    /// assert!(root.nodeset().is_some());
    ///
    /// println!("{root:#}");
    /// # Ok::<(), eyre::Report>(())
    /// ```
    #[doc(alias = "hwloc_get_root_obj")]
    pub fn root_object(&self) -> &TopologyObject {
        self.objects_at_depth(NormalDepth::MIN)
            .next()
            .expect("Root object should exist")
    }

    /// [`TopologyObject`]s with the given [`ObjectType`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::object::types::ObjectType;
    /// # let topology = hwlocality::Topology::test_instance();
    /// #
    /// use eyre::eyre;
    ///
    /// let root = topology.root_object();
    ///
    /// for pu in topology.objects_with_type(ObjectType::PU) {
    ///     assert_eq!(pu.object_type(), ObjectType::PU);
    ///     assert!(pu.is_in_subtree(root));
    ///     assert_eq!(pu.normal_arity(), 0);
    ///     let num_cpus =
    ///         pu
    ///             .cpuset()
    ///             .ok_or_else(|| eyre!("a PU should have a CpuSet"))?
    ///             .weight()
    ///             .ok_or_else(|| {
    ///                 eyre!("a PU's CpuSet should be finite")
    ///             })?;
    ///     assert_eq!(num_cpus, 1);
    /// }
    /// #
    /// # Ok::<(), eyre::Report>(())
    /// ```
    #[doc(alias = "hwloc_get_obj_by_type")]
    #[doc(alias = "hwloc_get_nbobjs_by_type")]
    #[doc(alias = "hwloc_get_next_obj_by_type")]
    pub fn objects_with_type(
        &self,
        object_type: ObjectType,
    ) -> impl DoubleEndedIterator<Item = &TopologyObject> + Clone + ExactSizeIterator + FusedIterator
    {
        let type_depth = self.depth_for_type(object_type);
        let depth_iter = NormalDepth::iter_range(NormalDepth::MIN, self.depth())
            .map(Depth::from)
            .chain(Depth::VIRTUAL_DEPTHS.iter().copied())
            .filter(move |&depth| {
                type_depth.map_or_else(
                    |_| self.type_at_depth(depth).expect("Depth should exist") == object_type,
                    |type_depth| depth == type_depth,
                )
            });
        let size = depth_iter
            .clone()
            .map(move |depth| self.num_objects_at_depth(depth))
            .sum();
        ObjectsWithType {
            size,
            inner: depth_iter.flat_map(move |depth| self.objects_at_depth(depth)),
        }
    }

    /// Truth that this topology has the same object hierarchy as another, where
    /// our equality criterion includes global persistent indices
    pub(crate) fn has_same_object_hierarchy(&self, other: &Self) -> bool {
        /// Extract all object properties in a clone-agnostic form
        fn object_properties(topology: &Topology) -> impl PartialEq + '_ {
            /// Translate a neighbor into its global persistent index
            fn neighbor(obj: Option<&TopologyObject>) -> Option<TopologyObjectID> {
                obj.map(TopologyObject::global_persistent_index)
            }
            /// Translate children into their global persistent indices
            fn children<'a>(
                iter: impl Iterator<Item = &'a TopologyObject>,
            ) -> Vec<TopologyObjectID> {
                iter.map(TopologyObject::global_persistent_index).collect()
            }
            topology
                .objects()
                .map(|obj| {
                    (
                        obj.global_persistent_index(),
                        (
                            (
                                obj.object_type(),
                                obj.subtype(),
                                obj.name(),
                                obj.attributes(),
                                obj.os_index(),
                            ),
                            (obj.depth(), neighbor(obj.parent())),
                            (
                                obj.logical_index(),
                                neighbor(obj.next_cousin()),
                                neighbor(obj.prev_cousin()),
                                obj.sibling_rank(),
                                neighbor(obj.next_sibling()),
                                neighbor(obj.prev_sibling()),
                            ),
                            (
                                obj.normal_arity(),
                                children(obj.normal_children()),
                                obj.is_symmetric_subtree(),
                                obj.memory_arity(),
                                children(obj.memory_children()),
                                obj.total_memory(),
                                obj.io_arity(),
                                children(obj.io_children()),
                                obj.misc_arity(),
                                children(obj.misc_children()),
                            ),
                            (
                                obj.cpuset(),
                                obj.complete_cpuset(),
                                obj.nodeset(),
                                obj.complete_nodeset(),
                            ),
                            obj.infos(),
                        ),
                    )
                })
                .collect::<HashMap<_, _>>()
        }
        object_properties(self) == object_properties(other)
    }
}

/// Iterator emitted by [`TopologyObject::objects_with_type()`]
///
/// Needed because iterator combinator chains don't implement all desired
/// [`Iterator`] subtraits.
#[derive(Copy, Clone)]
struct ObjectsWithType<Inner> {
    /// Number of items that this iterator will yield
    size: usize,

    /// Inner iterator
    inner: Inner,
}
//
impl<'topology, Inner: Iterator<Item = &'topology TopologyObject>> Iterator
    for ObjectsWithType<Inner>
{
    type Item = &'topology TopologyObject;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.inner.next()?;
        self.size -= 1;
        Some(next)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.size, Some(self.size))
    }

    fn count(self) -> usize {
        self.size
    }
}
//
impl<'topology, Inner: DoubleEndedIterator<Item = &'topology TopologyObject>> DoubleEndedIterator
    for ObjectsWithType<Inner>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        let next = self.inner.next_back()?;
        self.size -= 1;
        Some(next)
    }
}
//
impl<'topology, Inner: Iterator<Item = &'topology TopologyObject>> ExactSizeIterator
    for ObjectsWithType<Inner>
{
}
//
impl<'topology, Inner: FusedIterator<Item = &'topology TopologyObject>> FusedIterator
    for ObjectsWithType<Inner>
{
}

#[allow(clippy::cognitive_complexity)]
#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::tests::assert_panics;
    use proptest::prelude::*;
    use similar_asserts::assert_eq;
    use std::{collections::HashMap, collections::HashSet, ptr, sync::OnceLock};

    /// Check that reported topology depth matches hwloc rule that PUs are the
    /// deepest kind of normal object
    #[test]
    fn topology_depth() {
        let topology = Topology::test_instance();
        assert_eq!(
            topology.depth(),
            topology
                .depth_for_type(ObjectType::PU)
                .unwrap()
                .expect_normal()
                + 1
        );
    }

    /// Check that memory parent depth reporting is correct
    #[test]
    fn memory_parents_depth() {
        let topology = Topology::test_instance();

        let depths_with_memory_parents =
            NormalDepth::iter_range(NormalDepth::MIN, topology.depth())
                .filter(|&depth| {
                    topology
                        .objects_at_depth(depth)
                        .any(|obj| obj.memory_arity() > 0)
                })
                .collect::<Vec<_>>();

        match topology.memory_parents_depth() {
            Ok(memory_parents_depth) => {
                assert_eq!(depths_with_memory_parents, vec![memory_parents_depth])
            }
            Err(TypeToDepthError::Multiple) => assert!(depths_with_memory_parents.len() > 1),
            Err(_) => unreachable!(),
        }
    }

    /// List of valid depths in the topology
    fn valid_depths() -> impl Iterator<Item = Depth> {
        let topology = Topology::test_instance();
        NormalDepth::iter_range(NormalDepth::MIN, topology.depth())
            .map(Depth::from)
            .chain(Depth::VIRTUAL_DEPTHS.iter().copied())
    }

    /// Check the mapping from types to depths
    fn type_to_depths() -> HashMap<ObjectType, Vec<Depth>> {
        let topology = Topology::test_instance();
        let mut result = HashMap::<ObjectType, Vec<Depth>>::new();
        for depth in valid_depths() {
            let ty = topology.type_at_depth(depth).unwrap();
            result.entry(ty).or_default().push(depth);
        }
        result
    }

    /// Check that type -> depth translation is correct
    #[test]
    fn depth_for_type() -> Result<(), TestCaseError> {
        let topology = Topology::test_instance();

        // Probe the type -> depths mapping for all types using type_at_depth
        let type_to_depths = type_to_depths();

        // Check that depth_for_type-like methods produce expected results for
        // all types + also check depth_or_(above|below) for present types
        let mut absent_normal_types = Vec::new();
        #[allow(clippy::option_if_let_else)]
        for ty in enum_iterator::all::<ObjectType>() {
            if let Some(depths) = type_to_depths.get(&ty) {
                let expected = if depths.len() == 1 {
                    Ok(depths[0])
                } else {
                    Err(TypeToDepthError::Multiple)
                };
                assert_eq!(topology.depth_for_type(ty), expected);
                if ty.is_normal() {
                    assert_eq!(topology.depth_or_above_for_type(ty), expected);
                    assert_eq!(topology.depth_or_below_for_type(ty), expected);
                } else {
                    assert_panics(|| topology.depth_or_above_for_type(ty))?;
                    assert_panics(|| topology.depth_or_below_for_type(ty))?;
                }
            } else {
                assert_eq!(
                    topology.depth_for_type(ty),
                    Err(TypeToDepthError::Nonexistent)
                );
                if ty.is_normal() {
                    absent_normal_types.push(ty);
                }
            }
        }

        // Enumerate present types in depth order, use that to check that
        // depth_or_(above|below) works for nonexistent types.
        let normal_types_by_depth = NormalDepth::iter_range(NormalDepth::MIN, topology.depth())
            .map(|depth| topology.type_at_depth(depth).unwrap())
            .collect::<Vec<_>>();
        let above_below = absent_normal_types
            .iter()
            .map(|ty| {
                let below_idx = normal_types_by_depth
                    .iter()
                    .position(|probe| probe > ty)
                    .unwrap();
                let above_idx = below_idx - 1;
                let to_depth = |us| Depth::try_from(us).unwrap();
                (to_depth(above_idx), to_depth(below_idx))
            })
            .collect::<Vec<_>>();
        for (ty, (above, below)) in absent_normal_types.into_iter().zip(above_below) {
            assert_eq!(topology.depth_or_above_for_type(ty), Ok(above));
            assert_eq!(topology.depth_or_below_for_type(ty), Ok(below));
        }
        Ok(())
    }

    /// Check the root object
    ///
    /// It's the top of the topology, so we know a lot about it.
    #[test]
    fn root_object() {
        let topology = Topology::test_instance();

        let root = topology.root_object();

        assert_eq!(topology.objects_with_type(ObjectType::Machine).count(), 1);
        assert_eq!(root.object_type(), ObjectType::Machine);
        assert!(root.attributes().is_none());

        assert_eq!(root.depth(), NormalDepth::MIN);
        assert!(root.first_shared_cache().is_none());
        assert!(root.first_non_io_ancestor().is_none());

        assert_eq!(root.logical_index(), 0);
        assert!(root.next_cousin().is_none());
        assert!(root.prev_cousin().is_none());
        assert_eq!(root.sibling_rank(), 0);
        assert!(root.next_sibling().is_none());
        assert!(root.prev_sibling().is_none());

        assert_ne!(root.normal_arity(), 0);

        assert_eq!(root.cpuset(), Some(topology.cpuset()));
        assert!(root.is_inside_cpuset(topology.cpuset()));
        assert!(root.covers_cpuset(topology.cpuset()));
        assert_eq!(root.complete_cpuset(), Some(topology.complete_cpuset()));
        assert_eq!(root.nodeset(), Some(topology.nodeset()));
        assert_eq!(root.complete_nodeset(), Some(topology.complete_nodeset()));

        for depth in valid_depths() {
            assert!(root.ancestor_at_depth(depth).is_none());
        }

        for ty in type_to_depths().into_keys() {
            assert!(root.first_ancestor_with_type(ty).is_none());
        }

        for obj in topology.objects() {
            assert!(root.first_common_ancestor(obj).is_none());
            assert!(!root.is_in_subtree(obj));
            assert_eq!(obj.is_in_subtree(root), !ptr::eq(obj, root));
        }
    }

    /// Check the PU objects
    ///
    /// They're the leaves of the normal topology, so we know a lot about them.
    #[test]
    fn processing_units() {
        let topology = Topology::test_instance();

        assert_eq!(
            topology.objects_with_type(ObjectType::PU).count(),
            topology.cpuset().weight().unwrap()
        );

        for (idx, pu) in topology.objects_with_type(ObjectType::PU).enumerate() {
            assert_eq!(pu.object_type(), ObjectType::PU);
            assert!(pu.attributes().is_none());

            assert_eq!(pu.depth(), topology.depth() - 1);
            assert_eq!(pu.logical_index(), idx);
            assert!(pu.first_non_io_ancestor().is_some());

            assert_eq!(pu.normal_arity(), 0);
            assert!(pu.is_symmetric_subtree());

            assert_eq!(pu.cpuset().unwrap().weight().unwrap(), 1);
            assert_eq!(pu.nodeset().unwrap().weight().unwrap(), 1);
        }
    }

    /// Check the NUMA node objects
    ///
    /// They're the leaves of the memory hierarchy, so we know a lot about them
    #[test]
    fn numa_nodes() {
        let topology = Topology::test_instance();

        assert_eq!(
            topology.objects_with_type(ObjectType::NUMANode).count(),
            topology.nodeset().weight().unwrap()
        );

        for (idx, numa) in topology.objects_with_type(ObjectType::NUMANode).enumerate() {
            assert_eq!(numa.object_type(), ObjectType::NUMANode);
            assert!(matches!(
                numa.attributes(),
                Some(ObjectAttributes::NUMANode(_))
            ));

            assert_eq!(numa.depth(), Depth::NUMANode);
            assert_eq!(numa.logical_index(), idx);
            assert!(numa.first_non_io_ancestor().is_some());

            assert_eq!(numa.normal_arity(), 0);
            assert!(!numa.is_symmetric_subtree());
            assert_eq!(numa.memory_arity(), 0);

            assert_eq!(numa.nodeset().unwrap().weight().unwrap(), 1);
        }
    }

    /// Check that [`Topology::objects_with_type()`] is correct
    #[test]
    fn objects_with_type() {
        let topology = Topology::test_instance();

        let type_to_depths = type_to_depths();

        for ty in enum_iterator::all::<ObjectType>() {
            // Does it only expose objects of the right type?
            for obj in topology.objects_with_type(ty) {
                assert_eq!(obj.object_type(), ty);
            }

            // Does it expose every object of the right type?
            let num_objects = type_to_depths.get(&ty).map_or(0, |depths| {
                depths
                    .iter()
                    .map(|depth| topology.objects_at_depth(*depth).count())
                    .sum::<usize>()
            });
            assert_eq!(topology.objects_with_type(ty).count(), num_objects);

            // Does the custom iterator logic work as expected ?
            let mut iter = topology.objects_with_type(ty);
            fn check_size_hint<'a>(
                iter: &(impl DoubleEndedIterator<Item = &'a TopologyObject> + ExactSizeIterator),
            ) {
                assert_eq!(iter.size_hint(), (iter.len(), Some(iter.len())));
            }
            assert_eq!(iter.len(), num_objects);
            check_size_hint(&iter);
            iter.next();
            assert_eq!(iter.len(), num_objects.saturating_sub(1));
            check_size_hint(&iter);
            iter = topology.objects_with_type(ty);
            match (iter.next_back(), topology.objects_with_type(ty).last()) {
                (Some(obj1), Some(obj2)) if ptr::eq(obj1, obj2) => {}
                (None, None) => {}
                other => panic!("next_back doesn't match last: {other:?}"),
            }
            assert_eq!(iter.len(), num_objects.saturating_sub(1));
            check_size_hint(&iter);
        }
    }

    // --- Check that cache search is correct ---

    /// Kinds of caches present on the system, ordered by depth
    fn cache_kinds() -> &'static [CacheKind] {
        static KINDS: OnceLock<Box<[CacheKind]>> = OnceLock::new();
        &KINDS.get_or_init(|| {
            let topology = Topology::test_instance();
            NormalDepth::iter_range(NormalDepth::MIN, topology.depth())
                .filter_map(|depth| {
                    let obj = topology.objects_at_depth(depth).next()?;
                    let Some(ObjectAttributes::Cache(attr)) = obj.attributes() else {
                        return None;
                    };
                    Some(CacheKind {
                        depth,
                        level: attr.depth(),
                        ty: attr.cache_type(),
                    })
                })
                .collect()
        })[..]
    }
    //
    /// Data about a single cache level
    struct CacheKind {
        depth: NormalDepth,
        level: usize,
        ty: CacheType,
    }

    /// Parameters for [`Topology::depth_for_cache()`], random but with a bias
    /// towards generating valid inputs more often
    fn depth_for_cache_params() -> impl Strategy<Value = (usize, Option<CacheType>)> {
        // Probe the system's cache configuration
        let cache_kinds = cache_kinds();

        // If no cache was detected, all parameters are equally (in)valid
        if cache_kinds.is_empty() {
            return (any::<usize>(), any::<Option<CacheType>>()).boxed();
        }

        // Otherwise, find the valid cache levels and the last valid one...
        let cache_levels = cache_kinds
            .iter()
            .map(|kind| kind.level)
            .collect::<HashSet<_>>();
        let last_level = cache_levels.iter().copied().max().unwrap();

        // ...and find the valid and invalid cache types too
        let valid_cache_types = cache_kinds
            .iter()
            .map(|kind| Some(kind.ty))
            .chain(std::iter::once(None))
            .collect::<HashSet<_>>();
        let invalid_cache_types = enum_iterator::all::<CacheType>()
            .map(Some)
            .filter(|ty| !valid_cache_types.contains(ty))
            .collect::<Vec<_>>();

        // Use this to build valid strategies that cover the full possible range
        // of inputs with a bias towards valid inputs
        fn to_vec<T>(hs: HashSet<T>) -> Vec<T> {
            hs.into_iter().collect()
        }
        let level = prop_oneof![
            1 => Just(0),
            3 => prop::sample::select(to_vec(cache_levels)),
            1 => (last_level+1)..
        ];
        let ty = if invalid_cache_types.is_empty() {
            prop::sample::select(to_vec(valid_cache_types)).boxed()
        } else {
            prop_oneof![
                4 => prop::sample::select(to_vec(valid_cache_types)),
                1 => prop::sample::select(invalid_cache_types),
            ]
            .boxed()
        };
        (level, ty).boxed()
    }

    proptest! {
        /// Check that cache search is correct
        #[test]
        fn depth_for_cache((cache_level, cache_type) in depth_for_cache_params()) {
            let matches = cache_kinds()
                .iter()
                .filter(|kind| {
                    let level_ok = kind.level == cache_level;
                    let type_ok = cache_type.map_or(true, |ty| {
                        kind.ty == ty || kind.ty == CacheType::Unified
                    });
                    level_ok && type_ok
                })
                .map(|kind| Depth::from(kind.depth))
                .collect::<Vec<_>>();

            let topology = Topology::test_instance();
            match topology.depth_for_cache(cache_level, cache_type) {
                Ok(depth) => prop_assert_eq!(matches, &[depth]),
                Err(TypeToDepthError::Nonexistent) => prop_assert!(matches.is_empty()),
                Err(TypeToDepthError::Multiple) => {
                    prop_assert!(cache_type.is_none());
                    prop_assert!(matches.len() >= 2);
                },
                Err(TypeToDepthError::Unexpected(e)) => panic!("got unexpected error {e}"),
            }
        }
    }

    // --- Test operations with a depth parameter ---

    /// Depths that are mostly valid, but may be invalid too
    pub(crate) fn any_hwloc_depth() -> impl Strategy<Value = Depth> {
        let valid_depths = valid_depths().collect::<Vec<_>>();
        prop_oneof![
            4 => prop::sample::select(valid_depths),
            1 => any::<Depth>()
        ]
    }

    /// Like `any_depth()` but restricted to normal depths
    pub(crate) fn any_normal_depth() -> impl Strategy<Value = NormalDepth> {
        let topology = Topology::test_instance();
        let normal_depths =
            NormalDepth::iter_range(NormalDepth::MIN, topology.depth()).collect::<Vec<_>>();
        prop_oneof![
            4 => prop::sample::select(normal_depths),
            1 => any::<NormalDepth>()
        ]
    }

    /// Like `any_depth()` but covers full `usize` range
    pub(crate) fn any_usize_depth() -> impl Strategy<Value = usize> {
        prop_oneof![
            4 => any_normal_depth().prop_map(usize::from),
            1 => any::<usize>(),
        ]
    }

    /// Test [`Topology::type_at_depth()`] at a certain depth
    fn check_type_at_depth<DepthLike>(depth: DepthLike) -> Result<(), TestCaseError>
    where
        DepthLike: TryInto<Depth> + Copy,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        let topology = Topology::test_instance();
        let result = topology.type_at_depth(depth);
        let depth: Result<Depth, _> = depth.try_into();
        match depth {
            Ok(Depth::Normal(depth)) => {
                if depth < topology.depth() {
                    let ty = result.unwrap();
                    #[allow(clippy::option_if_let_else)]
                    if let Ok(expected) = topology.depth_for_type(ty) {
                        prop_assert_eq!(depth, expected);
                    } else {
                        prop_assert_eq!(ty, ObjectType::Group);
                    }
                } else {
                    prop_assert_eq!(result, None);
                }
            }
            Ok(Depth::NUMANode) => prop_assert_eq!(result, Some(ObjectType::NUMANode)),
            Ok(Depth::Bridge) => prop_assert_eq!(result, Some(ObjectType::Bridge)),
            Ok(Depth::PCIDevice) => prop_assert_eq!(result, Some(ObjectType::PCIDevice)),
            Ok(Depth::OSDevice) => prop_assert_eq!(result, Some(ObjectType::OSDevice)),
            Ok(Depth::Misc) => prop_assert_eq!(result, Some(ObjectType::Misc)),
            #[cfg(feature = "hwloc-2_1_0")]
            Ok(Depth::MemCache) => prop_assert_eq!(result, Some(ObjectType::MemCache)),
            Err(_) => prop_assert_eq!(result, None),
        }
        Ok(())
    }

    /// Test [`Topology::num_objects_at_depth()`] at a certain depth
    fn check_num_objects_at_depth<DepthLike>(depth: DepthLike) -> Result<(), TestCaseError>
    where
        DepthLike: TryInto<Depth> + Copy,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        let topology = Topology::test_instance();
        prop_assert_eq!(
            topology.num_objects_at_depth(depth),
            topology.objects_at_depth(depth).count()
        );
        Ok(())
    }

    /// Test [`Topology::objects_at_depth()`] at a certain depth
    fn check_objects_at_depth<DepthLike>(depth: DepthLike) -> Result<(), TestCaseError>
    where
        DepthLike: TryInto<Depth> + Copy + Debug + Eq,
        Depth: PartialEq<DepthLike>,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        let topology = Topology::test_instance();

        let Some(ty) = topology.type_at_depth(depth) else {
            prop_assert_eq!(topology.objects_at_depth(depth).count(), 0);
            return Ok(());
        };

        for obj in topology.objects_at_depth(depth) {
            prop_assert_eq!(obj.depth(), depth);
            prop_assert_eq!(obj.object_type(), ty);
            if let Ok(Depth::Normal(depth)) = depth.try_into() {
                prop_assert_eq!(obj.ancestors().count(), depth);
            }
        }
        Ok(())
    }

    proptest! {
        // Test above operations at valid and invalid depths
        #[test]
        fn operations_at_any_hwloc_depth(depth in any_hwloc_depth()) {
            check_type_at_depth(depth)?;
            check_num_objects_at_depth(depth)?;
            check_objects_at_depth(depth)?;
        }
        //
        #[test]
        fn operations_at_any_normal_depth(depth in any_normal_depth()) {
            check_type_at_depth(depth)?;
            check_num_objects_at_depth(depth)?;
            check_objects_at_depth(depth)?;
        }
        //
        #[test]
        fn operations_at_any_usize_depth(depth in any_usize_depth()) {
            check_type_at_depth(depth)?;
            check_num_objects_at_depth(depth)?;
            check_objects_at_depth(depth)?;
        }
    }
}
