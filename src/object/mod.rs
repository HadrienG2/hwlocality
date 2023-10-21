//! Objects within a hardware topology
//!
//! A [`Topology`] is first and foremost a tree of [`TopologyObject`] which
//! represents resource sharing relationships in hardware: an object is
//! considered the parent of all other objects that share the
//! most direct/fastest/lowest-latency route to it. For example, on x86, an L3
//! cache is the parent of a number of L2 caches, each the parent of one L1
//! cache, which is in turn the parent of a CPU core that may or may not be
//! shared by multiple hyperthreads (PUs in hwloc's vocabulary).
//!
//! This module defines the (very extensive) API through which one can query
//! various properties of topology objects and jump from them to other elements
//! of the surrounding topology.

pub mod attributes;
pub mod depth;
pub mod distance;
pub mod types;

use self::{
    attributes::{DownstreamAttributes, ObjectAttributes, PCIDomain},
    depth::{Depth, NormalDepth, TypeToDepthError},
    types::{CacheType, ObjectType},
};
#[cfg(doc)]
use crate::topology::{builder::BuildFlags, support::DiscoverySupport};
use crate::{
    bitmap::BitmapRef,
    cpu::cpuset::CpuSet,
    errors::{self, ForeignObjectError, HybridError, NulError, ParameterError},
    ffi::{
        self, int,
        string::LibcString,
        transparent::{AsNewtype, TransparentNewtype},
    },
    info::TextualInfo,
    memory::nodeset::NodeSet,
    topology::Topology,
};
use hwlocality_sys::{hwloc_obj, hwloc_obj_type_t, HWLOC_UNKNOWN_INDEX};
use num_enum::TryFromPrimitiveError;
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
#[cfg(test)]
use std::sync::OnceLock;
use std::{
    ffi::{c_char, c_uint, CStr},
    fmt::{self, Debug, Display},
    iter::FusedIterator,
    num::NonZeroUsize,
    ops::Deref,
    ptr,
};
use thiserror::Error;

/// # Full object list
///
/// For some use cases, especially testing, it is convenient to have a full list
/// of all objects contained within a topology. There methods provide just that.
///
/// This functionality is unique to the Rust hwloc bindings
impl Topology {
    /// Full list of objects in the topology, first normal objects ordered by
    /// increasing depth then virtual objects ordered by type
    pub fn objects(&self) -> impl FusedIterator<Item = &TopologyObject> + Clone {
        self.normal_objects().chain(self.virtual_objects())
    }

    /// Pre-computed list of objects from the test instance
    #[cfg(test)]
    pub(crate) fn test_objects() -> &'static [&'static TopologyObject] {
        static OBJECTS: OnceLock<Box<[&'static TopologyObject]>> = OnceLock::new();
        &OBJECTS.get_or_init(|| Self::test_instance().objects().collect())[..]
    }

    /// Full list of objects contains in the normal hierarchy of the topology,
    /// ordered by increasing depth
    pub fn normal_objects(&self) -> impl FusedIterator<Item = &TopologyObject> + Clone {
        NormalDepth::iter_range(NormalDepth::MIN, self.depth())
            .flat_map(|depth| self.objects_at_depth(depth))
    }

    /// Full list of virtual bjects in the topology, ordered by type
    pub fn virtual_objects(&self) -> impl FusedIterator<Item = &TopologyObject> + Clone {
        Depth::VIRTUAL_DEPTHS
            .iter()
            .flat_map(|&depth| self.objects_at_depth(depth))
    }

    /// Full list of memory objects in the topology, ordered by type
    pub fn memory_objects(&self) -> impl FusedIterator<Item = &TopologyObject> + Clone {
        Depth::MEMORY_DEPTHS
            .iter()
            .flat_map(|&depth| self.objects_at_depth(depth))
    }

    /// Full list of I/O objects in the topology, ordered by type
    pub fn io_objects(&self) -> impl FusedIterator<Item = &TopologyObject> + Clone {
        Depth::IO_DEPTHS
            .iter()
            .flat_map(|&depth| self.objects_at_depth(depth))
    }
}

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
    /// placed on special levels).
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
    ///     topology.depth_for_type(ObjectType::PU)?.assume_normal() + 1
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
            .map(Depth::assume_normal)
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
    /// assert_eq!(machine_depth.assume_normal(), 0);
    /// assert!(machine_depth.assume_normal() < pu_depth.assume_normal());
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
    /// This function is only meaningful for normal object types. If a memory,
    /// I/O or Misc object type is given, the corresponding virtual depth is
    /// always returned.
    ///
    /// # Errors
    ///
    /// - [`TypeToDepthError::Nonexistent`] if no object typically found inside
    ///   `object_type` is present.
    /// - [`TypeToDepthError::Multiple`] if objects of this type exist at multiple
    ///   depths (can happen when `object_type` is [`Group`]).
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
    /// assert!(machine_depth.assume_normal() < package_or_below.assume_normal());
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
        assert!(
            object_type.is_normal(),
            "This is only meaningful for normal objects"
        );
        match self.depth_for_type(object_type) {
            Ok(d) => Ok(d),
            Err(TypeToDepthError::Nonexistent) => {
                let pu_depth = self
                    .depth_for_type(ObjectType::PU)
                    .expect("PU objects should be present")
                    .assume_normal();
                for depth in NormalDepth::iter_range(NormalDepth::MIN, pu_depth).rev() {
                    if self
                        .type_at_depth(depth)
                        .expect("Depths above PU depth should exist")
                        < object_type
                    {
                        return Ok((depth + 1).into());
                    }
                }
                Err(TypeToDepthError::Nonexistent)
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
    /// This function is only meaningful for normal object types. If a memory,
    /// I/O or Misc object type is given, the corresponding virtual depth is
    /// always returned.
    ///
    /// # Errors
    ///
    /// - [`TypeToDepthError::Nonexistent`] if no object typically containing
    ///   `object_type` is present.
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
    /// let pu_depth = topology.depth_for_type(ObjectType::PU)?;
    /// let core_or_above = topology.depth_or_below_for_type(ObjectType::Core)?;
    ///
    /// assert!(core_or_above.assume_normal() < pu_depth.assume_normal());
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
        assert!(
            object_type.is_normal(),
            "This is only meaningful for normal objects"
        );
        match self.depth_for_type(object_type) {
            Ok(d) => Ok(d),
            Err(TypeToDepthError::Nonexistent) => {
                for depth in NormalDepth::iter_range(NormalDepth::MIN, self.depth()).rev() {
                    if self
                        .type_at_depth(depth)
                        .expect("Depths above bottom depth should exist")
                        > object_type
                    {
                        return Ok((depth - 1).into());
                    }
                }
                Err(TypeToDepthError::Nonexistent)
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
        // There is no cache level 0, it starts at L1
        let Some(cache_level) = NonZeroUsize::new(cache_level) else {
            return Err(TypeToDepthError::Nonexistent);
        };

        // Otherwise, need to actually look it up
        let mut result = Err(TypeToDepthError::Nonexistent);
        for depth in NormalDepth::iter_range(NormalDepth::MIN, self.depth()) {
            // Cache level and type are homogeneous across a depth level so we
            // only need to look at one object
            for obj in self.objects_at_depth(depth).take(1) {
                // Is this a cache?
                if let Some(ObjectAttributes::Cache(cache)) = obj.attributes() {
                    // Check cache level
                    if cache.depth() != cache_level {
                        continue;
                    }

                    // Check cache type if instructed to do so
                    if let Some(cache_type) = cache_type {
                        if cache.cache_type() == cache_type
                            || cache.cache_type() == CacheType::Unified
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
                                unreachable!("Setting this value triggers a loop break")
                            }
                            Err(TypeToDepthError::Unexpected(_)) => {
                                unreachable!("This value is never set")
                            }
                        }
                    }
                }
            }
        }
        result
    }

    /// Type of objects at the given `depth`, if any
    ///
    /// Accepts [`Depth`], [`NormalDepth`] and [`usize`] operands. Use the
    /// former two for type-safety (they are guaranteed to be in range as a type
    /// invariant) or the latter for convenience (it is more tightly integrated
    /// with Rust's built-in integer support, for example it supports integer
    /// literals).
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
            // There cannot be any normal object at a depth below the topology depth
            if let Depth::Normal(depth) = depth {
                if depth >= self_.depth() {
                    return None;
                }
            }

            // Otherwise, ask hwloc
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
    /// Accepts [`Depth`], [`NormalDepth`] and [`usize`] operands. Use the
    /// former two for type-safety (they are guaranteed to be in range as a type
    /// invariant) or the latter for convenience (it is more tightly integrated
    /// with Rust's built-in integer support, for example it supports integer
    /// literals).
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
    /// Accepts [`Depth`], [`NormalDepth`] and [`usize`] operands. Use the
    /// former two for type-safety (they are guaranteed to be in range as a type
    /// invariant) or the latter for convenience (it is more tightly integrated
    /// with Rust's built-in integer support, for example it supports integer
    /// literals).
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
    /// assert_eq!(root.depth(), Depth::from(NormalDepth::MIN));
    /// assert!(root.parent().is_none());
    /// assert_eq!(root.logical_index(), 0);
    /// assert_ne!(root.normal_arity(), 0);
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
        self.inner.next()
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
        self.inner.next_back()
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

/// # Finding other objects
//
// --- Implementation details ---
//
// This is inspired by the upstream functionality described at
// https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__find__misc.html
// but the code had to be ported to Rust because it's inline
impl Topology {
    /// Get the object of type [`ObjectType::PU`] with the specified OS index
    ///
    /// If you want to convert an entire CPU set into the PU objects it
    /// contains, using [`pus_from_cpuset()`] will be more efficient than
    /// repeatedly calling this function with every OS index from the [`CpuSet`].
    ///
    /// Requires [`DiscoverySupport::pu_count()`].
    ///
    /// [`pus_from_cpuset()`]: Self::pus_from_cpuset()
    #[doc(alias = "hwloc_get_pu_obj_by_os_index")]
    pub fn pu_with_os_index(&self, os_index: usize) -> Option<&TopologyObject> {
        self.objs_and_os_indices(ObjectType::PU)
            .find_map(|(pu, pu_os_index)| (pu_os_index == os_index).then_some(pu))
    }

    /// Get the objects of type [`ObjectType::PU`] covered by the specified cpuset
    ///
    /// Accepts both `&'_ CpuSet` and `BitmapRef<'_, CpuSet>` operands.
    ///
    /// Requires [`DiscoverySupport::pu_count()`].
    ///
    /// This functionality is specific to the Rust bindings.
    pub fn pus_from_cpuset<'result>(
        &'result self,
        cpuset: impl Deref<Target = CpuSet> + 'result,
    ) -> impl DoubleEndedIterator<Item = &TopologyObject> + FusedIterator + 'result {
        self.objs_and_os_indices(ObjectType::PU)
            .filter_map(move |(pu, os_index)| cpuset.is_set(os_index).then_some(pu))
    }

    /// Get the object of type [`NUMANode`] with the specified OS index
    ///
    /// If you want to convert an entire [`NodeSet` into the [`NUMANode`]
    /// objects it contains, using [`nodes_from_nodeset()`] will be more
    /// efficient than repeatedly calling this function with every OS index from
    /// the [`NodeSet`].
    ///
    /// Requires [`DiscoverySupport::numa_count()`].
    ///
    /// [`nodes_from_nodeset()`]: Self::nodes_from_nodeset()
    /// [`NUMANode`]: ObjectType::NUMANode
    #[doc(alias = "hwloc_get_numanode_obj_by_os_index")]
    pub fn node_with_os_index(&self, os_index: usize) -> Option<&TopologyObject> {
        self.objs_and_os_indices(ObjectType::NUMANode)
            .find_map(|(node, node_os_index)| (node_os_index == os_index).then_some(node))
    }

    /// Get the objects of type [`ObjectType::NUMANode`] covered by the
    /// specified nodeset
    ///
    /// Accepts both `&'_ NodeSet` and `BitmapRef<'_, NodeSet>` operands.
    ///
    /// Requires [`DiscoverySupport::numa_count()`].
    ///
    /// This functionality is specific to the Rust bindings.
    pub fn nodes_from_nodeset<'result>(
        &'result self,
        nodeset: impl Deref<Target = NodeSet> + 'result,
    ) -> impl DoubleEndedIterator<Item = &TopologyObject> + FusedIterator + 'result {
        self.objs_and_os_indices(ObjectType::NUMANode)
            .filter_map(move |(node, os_index)| nodeset.is_set(os_index).then_some(node))
    }

    /// Get a list of `(&TopologyObject, OS index)` tuples for an `ObjectType`
    /// that is guaranteed to appear only at one depth of the topology and to
    /// have an OS index.
    ///
    /// # Panics
    ///
    /// Will panic if the object type appears at more than one depth or do not
    /// have an OS index. As this method is an implementation detail of other
    /// methods above, the caller should be able to ensure it never happens.
    fn objs_and_os_indices(
        &self,
        ty: ObjectType,
    ) -> impl DoubleEndedIterator<Item = (&TopologyObject, usize)>
           + Clone
           + ExactSizeIterator
           + FusedIterator {
        self.objects_at_depth(
            self.depth_for_type(ty)
                .expect("These objects should only appear at a single depth"),
        )
        .map(|obj| {
            (
                obj,
                obj.os_index()
                    .expect("These objects should have an OS index"),
            )
        })
    }

    /// Enumerate objects at the same depth as `obj`, but with increasing
    /// physical distance (i.e. from increasingly higher common ancestors in the
    /// topology tree).
    ///
    /// This search may only be applied to objects that have a cpuset (normal
    /// and memory objects) and belong to this topology.
    ///
    /// # Errors
    ///
    /// - [`ForeignObject`] if `obj` does not belong to this topology.
    /// - [`MissingCpuSet`] if `obj` does not have a cpuset.
    ///
    /// [`ForeignObject`]: ClosestObjectsError::ForeignObject
    /// [`MissingCpuSet`]: ClosestObjectsError::MissingCpuSet
    #[doc(alias = "hwloc_get_closest_objs")]
    pub fn objects_closest_to<'result>(
        &'result self,
        obj: &'result TopologyObject,
    ) -> Result<impl Iterator<Item = &TopologyObject> + 'result, ClosestObjectsError> {
        // Validate input object
        if !self.contains(obj) {
            return Err(ClosestObjectsError::ForeignObject(obj.into()));
        }
        let obj_cpuset = obj
            .cpuset()
            .ok_or_else(|| ClosestObjectsError::MissingCpuSet(obj.into()))?;

        /// Assert that an object has a cpuset, return both
        fn obj_and_cpuset<'obj>(
            obj: &'obj TopologyObject,
            error: &str,
        ) -> (&'obj TopologyObject, BitmapRef<'obj, CpuSet>) {
            (obj, obj.cpuset().expect(error))
        }

        /// Find the first ancestor of an object that knows about more objects
        /// than that object (if any), and return it along with its cpuset
        fn find_larger_parent<'obj>(
            known_obj: &'obj TopologyObject,
            known_cpuset: &CpuSet,
        ) -> Option<(&'obj TopologyObject, BitmapRef<'obj, CpuSet>)> {
            known_obj
                .ancestors()
                .map(|ancestor| {
                    obj_and_cpuset(
                        ancestor,
                        "Ancestors of an object with a cpuset should have a cpuset",
                    )
                })
                .find(|(_ancestor, ancestor_cpuset)| ancestor_cpuset != known_cpuset)
        }
        let mut ancestor_and_cpuset = find_larger_parent(obj, &obj_cpuset);

        // Prepare to jointly iterate over cousins and their cpusets
        // On each pass, we're going to find which cousins are covered by the
        // current ancestor, keeping the other cousins around to iterate over
        // them again during the next pass with a higher-level ancestor.
        let mut cousins_and_cpusets = self
            .objects_at_depth(obj.depth())
            .filter(|cousin_or_obj| !ptr::eq(*cousin_or_obj, obj))
            .map(|cousin| {
                obj_and_cpuset(
                    cousin,
                    "Cousins of an object with a cpuset should have a cpuset",
                )
            })
            .collect::<Vec<_>>();
        let mut next_cousins_and_cpusets = Vec::new();

        // Emit the final iterator
        Ok(std::iter::from_fn(move || {
            loop {
                // Look for a cousin that is covered by the current ancestor
                let (ancestor, ancestor_cpuset) = ancestor_and_cpuset.take()?;
                while let Some((cousin, cousin_cpuset)) = cousins_and_cpusets.pop() {
                    if ancestor_cpuset.includes(cousin_cpuset) {
                        return Some(cousin);
                    } else {
                        next_cousins_and_cpusets.push((cousin, cousin_cpuset));
                    }
                }

                // We ran out of cousins, go to a higher-level ancestor or end
                // iteration if we reached the top of the tree.
                let (ancestor, ancestor_cpuset) = find_larger_parent(ancestor, &ancestor_cpuset)?;
                ancestor_and_cpuset = Some((ancestor, ancestor_cpuset));
                std::mem::swap(&mut cousins_and_cpusets, &mut next_cousins_and_cpusets);
            }
        }))
    }

    /// Find an object via a parent->child chain specified by types and indices
    ///
    /// For example, if called with `&[(NUMANode, 0), (Package, 1), (Core, 2)]`,
    /// this will return the third core object below the second package below
    /// the first NUMA node.
    ///
    /// This search may only be applied to object types that have a cpuset
    /// (normal and memory objects).
    ///
    /// # Errors
    ///
    /// - [`MissingCpuSetError`] if one of the specified object types does not
    ///   have a cpuset.
    #[doc(alias = "hwloc_get_obj_below_array_by_type")]
    #[doc(alias = "hwloc_get_obj_below_by_type")]
    pub fn object_by_type_index_path(
        &self,
        path: &[(ObjectType, usize)],
    ) -> Result<Option<&TopologyObject>, MissingCpuSetError> {
        let mut obj = self.root_object();
        for &(ty, idx) in path {
            let cpuset = obj.cpuset().ok_or_else(|| MissingCpuSetError::from(obj))?;
            if let Some(next_obj) = self.objects_inside_cpuset_with_type(cpuset, ty).nth(idx) {
                obj = next_obj;
            } else {
                return Ok(None);
            }
        }
        Ok(Some(obj))
    }

    /// Find an object of a different type with the same locality
    ///
    /// The source object `src` must belong to this topology, otherwise a
    /// [`ForeignSource`] error will be returned.
    ///
    /// If the source object is a normal or memory type, this function returns
    /// an object of type `ty` with the same CPU and node sets, either below or
    /// above in the hierarchy.
    ///
    /// If the source object is a PCI or an OS device within a PCI device, the
    /// function may either return that PCI device, or another OS device in the
    /// same PCI parent. This may for instance be useful for converting between
    /// OS devices such as "nvml0" or "rsmi1" used in distance structures into
    /// the the PCI device, or the CUDA or OpenCL OS device that correspond to
    /// the same physical card.
    ///
    /// If specified, parameter `subtype` restricts the search to objects whose
    /// [`TopologyObject::subtype()`] attribute exists and is equal to `subtype`
    /// (case-insensitively), for instance "OpenCL" or "CUDA".
    ///
    /// If specified, parameter `name_prefix` restricts the search to objects
    /// whose [`TopologyObject::name()`] attribute exists and starts with
    /// `name_prefix` (case-insensitively), for instance "rsmi" for matching
    /// "rsmi0".
    ///
    /// If multiple objects match, the first one is returned.
    ///
    /// This function will not walk the hierarchy across bridges since the PCI
    /// locality may become different. This function cannot also convert between
    /// normal/memory objects and I/O or Misc objects.
    ///
    /// If no matching object could be found, or if the source object and target
    /// type are incompatible, `None` will be returned.
    ///
    /// # Errors
    ///
    /// - [`ForeignSource`] if `src` does not belong to this topology.
    /// - [`StringContainsNul`] if `subtype` or `name_prefix` contains NUL chars.
    ///
    /// [`ForeignSource`]: LocalObjectError::ForeignSource
    /// [`StringContainsNul`]: LocalObjectError::StringContainsNul
    #[cfg(feature = "hwloc-2_5_0")]
    #[doc(alias = "hwloc_get_obj_with_same_locality")]
    pub fn object_with_same_locality(
        &self,
        src: &TopologyObject,
        ty: ObjectType,
        subtype: Option<&str>,
        name_prefix: Option<&str>,
    ) -> Result<Option<&TopologyObject>, LocalObjectError> {
        if !self.contains(src) {
            return Err(src.into());
        }
        let subtype = subtype.map(LibcString::new).transpose()?;
        let name_prefix = name_prefix.map(LibcString::new).transpose()?;
        let borrow_pchar = |opt: &Option<LibcString>| -> *const c_char {
            opt.as_ref().map_or(ptr::null(), LibcString::borrow)
        };
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - src was checked to belong to the active topology
        //         - LibcStrings are trusted to be valid C strings and not used
        //           after the end of their lifetime
        //         - hwloc ops are trusted not to modify *const parameters
        //         - By construction, ObjectType only exposes values that map into
        //           hwloc_obj_type_t values understood by the configured version
        //           of hwloc, and build.rs checks that the active version of
        //           hwloc is not older than that, so into() may only generate
        //           valid hwloc_obj_type_t values for current hwloc
        //         - Per documentation, flags must be zero
        let ptr = unsafe {
            hwlocality_sys::hwloc_get_obj_with_same_locality(
                self.as_ptr(),
                &src.0,
                ty.into(),
                borrow_pchar(&subtype),
                borrow_pchar(&name_prefix),
                0,
            )
        };
        // SAFETY: - If hwloc succeeds, the output pointer and its target are
        //           both assumed to be valid
        //         - Output is bound to the lifetime of the topology it comes from
        Ok((!ptr.is_null()).then(|| unsafe { (&*ptr).as_newtype() }))
    }
}

/// Error returned by [`Topology::objects_closest_to()`]
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum ClosestObjectsError {
    /// Target object does not belong to this topology
    #[error(transparent)]
    ForeignObject(#[from] ForeignObjectError),

    /// Target object does not have a cpuset and this search requires one
    #[error(transparent)]
    MissingCpuSet(#[from] MissingCpuSetError),
}

/// Error returned when a search algorithm that requires a cpuset is applied to
/// an object that doesn't have one.
///
/// The presence of a cpuset greatly simplifies some search algorithms as it
/// allows asserting that an object is a child of another with simple bitmap
/// operations, rather than requiring topology tree traversal. Therefore,
/// relatively complex search operations may only be applied to objects with a
/// cpuset (i.e. normal and memory objects) and will fail with this error if
/// applied to other object types.
//
// --- Implementation notes ---
//
// Not implementing Copy at this point because I want to leave options open for
// switching to another way to describe objects (Debug string, etc).
#[allow(missing_copy_implementations)]
#[derive(Clone, Debug, Default, Eq, Error, PartialEq)]
#[error("object #{0} doesn't have a cpuset but we need one for this search")]
pub struct MissingCpuSetError(TopologyObjectID);
//
impl<'topology> From<&'topology TopologyObject> for MissingCpuSetError {
    fn from(object: &'topology TopologyObject) -> Self {
        Self(object.global_persistent_index())
    }
}

/// Error returned by [`Topology::object_with_same_locality()`]
#[cfg(feature = "hwloc-2_5_0")]
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum LocalObjectError {
    /// Target object does not belong to this topology
    #[error(transparent)]
    ForeignSource(#[from] ForeignObjectError),

    /// Subtype or name prefix string contains a NUL char
    #[error("local object query string can't contain NUL chars")]
    StringContainsNul,
}
//
#[cfg(feature = "hwloc-2_5_0")]
impl From<NulError> for LocalObjectError {
    fn from(_: NulError) -> Self {
        Self::StringContainsNul
    }
}
//
#[cfg(feature = "hwloc-2_5_0")]
impl<'topology> From<&'topology TopologyObject> for LocalObjectError {
    fn from(object: &'topology TopologyObject) -> Self {
        Self::ForeignSource(object.into())
    }
}

/// # Finding I/O objects
//
// --- Implementation details ---
//
// Inspired by https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__advanced__io.html
// but inline functions had to be reimplemented in Rust. Further, queries
// pertaining to ancestors and children were moved to the corresponding sections.
impl Topology {
    /// Enumerate PCI devices in the system
    #[doc(alias = "hwloc_get_next_pcidev")]
    pub fn pci_devices(
        &self,
    ) -> impl DoubleEndedIterator<Item = &TopologyObject> + Clone + ExactSizeIterator + FusedIterator
    {
        self.objects_at_depth(Depth::PCIDevice)
    }

    /// Find the PCI device object matching the PCI bus id given domain, bus
    /// device and function PCI bus id
    #[doc(alias = "hwloc_get_pcidev_by_busid")]
    pub fn pci_device_by_bus_id(
        &self,
        domain: PCIDomain,
        bus_id: u8,
        bus_device: u8,
        function: u8,
    ) -> Option<&TopologyObject> {
        self.pci_devices().find(|obj| {
            let Some(ObjectAttributes::PCIDevice(pci)) = obj.attributes() else {
                unreachable!("All PCI devices should have PCI attributes")
            };
            pci.domain() == domain
                && pci.bus_id() == bus_id
                && pci.bus_device() == bus_device
                && pci.function() == function
        })
    }

    /// Find the PCI device object matching the PCI bus id given as a string
    /// of format "xxxx:yy:zz.t" (with domain) or "yy:zz.t" (without domain)
    ///
    /// # Errors
    ///
    /// - [`ParameterError`] if the given string does not match the PCI bus id
    ///   format given above
    #[doc(alias = "hwloc_get_pcidev_by_busidstring")]
    pub fn pci_device_by_bus_id_string(
        &self,
        bus_id: &str,
    ) -> Result<Option<&TopologyObject>, ParameterError<String>> {
        // Package `bus_id` into an error if need be
        let make_error = || ParameterError(bus_id.to_owned());

        // Assume well-formatted string
        let parse_domain = |s| PCIDomain::from_str_radix(s, 16).map_err(|_| make_error());
        let parse_u8 = |s| u8::from_str_radix(s, 16).map_err(|_| make_error());

        // Extract initial hex (whose semantics are ambiguous at this stage)
        let (int1, mut rest) = bus_id.split_once(':').ok_or_else(make_error)?;

        // From presence/absence of second ':', deduce if int1 was a domain or
        // a bus id in the default 0 domain.
        let (domain, bus) = if let Some((bus, next_rest)) = rest.split_once(':') {
            rest = next_rest;
            (parse_domain(int1)?, parse_u8(bus)?)
        } else {
            (0, parse_u8(int1)?)
        };

        // Parse device and function IDs, and forward to non-textual lookup
        let (dev, func) = rest.split_once('.').ok_or_else(make_error)?;
        Ok(self.pci_device_by_bus_id(domain, bus, parse_u8(dev)?, parse_u8(func)?))
    }

    /// Enumerate OS devices in the system
    #[doc(alias = "hwloc_get_next_osdev")]
    pub fn os_devices(
        &self,
    ) -> impl DoubleEndedIterator<Item = &TopologyObject> + Clone + ExactSizeIterator + FusedIterator
    {
        self.objects_at_depth(Depth::OSDevice)
    }

    /// Enumerate bridges in the system
    #[doc(alias = "hwloc_get_next_bridge")]
    pub fn bridges(
        &self,
    ) -> impl DoubleEndedIterator<Item = &TopologyObject> + Clone + ExactSizeIterator + FusedIterator
    {
        self.objects_at_depth(Depth::Bridge)
    }
}

/// Hardware topology object
///
/// Like `Topology`, this is a pretty big struct, so the documentation is
/// sliced into smaller parts:
///
/// - [Basic identity](#basic-identity)
/// - [Depth and ancestors](#depth-and-ancestors)
/// - [Cousins and siblings](#cousins-and-siblings)
/// - [Children](#children)
/// - [CPU set](#cpu-set)
/// - [NUMA node set](#numa-node-set)
/// - [Key-value information](#key-value-information)
///
/// You cannot create an owned object of this type, it belongs to the topology.
//
// --- Implementation details ---
//
// Upstream docs:
// - https://hwloc.readthedocs.io/en/v2.9/structhwloc__obj.html
// - https://hwloc.readthedocs.io/en/v2.9/attributes.html
//
// See the matching accessor methods and hwloc documentation for more details on
// field semantics, the struct member documentation will only be focused on
// allowed interactions from methods.
//
// # Safety
//
// As a type invariant, all inner pointers are assumed to be safe to dereference
// and devoid of mutable aliases if the TopologyObject is reachable at all.
//
// This is enforced through the following precautions:
//
// - No API exposes an owned TopologyObjects, only references to it bound by
//   the source topology's lifetime are exposed.
// - APIs for interacting with topologies and topology objects honor Rust's
//   shared XOR mutable aliasing rules, with no internal mutability.
//
// Provided that objects do not link to other objects outside of the topology
// they originate from, which is minimally sane expectation from hwloc, this
// should be enough.
//
// The hwloc_obj has very complex consistency invariants that are not fully
// documented by upstream. We assume the following:
//
// - If any pointer is non-null, its target can be assumed to be valid
// - Anything that is not explicitly listed as okay to modify below should be
//   considered unsafe to modify unless proven otherwise
// - object_type is assumed to be in sync with attr
// - It is okay to change attr inner data as long as no union is switched
//   from one variant to another
// - subtype may be replaced with another C string allocated by malloc(),
//   which hwloc will automatically free() on topology destruction (source:
//   documentation of hwloc_topology_insert_group_object() encourages it)
// - depth is in sync with parent
// - logical_index is in sync with (next|prev)_cousin
// - sibling_rank is in sync with (next|prev)_sibling
// - arity is in sync with (children|(first|last)_child)
// - symmetric_subtree is in sync with child pointers
// - memory_arity is in sync with memory_first_child
// - io_arity is in sync with io_first_child
// - misc_arity is in sync with misc_first_child
// - infos_count is in sync with infos
// - userdata should not be touched as topology duplication aliases it
// - gp_index is stable by API contract
#[allow(clippy::non_send_fields_in_send_ty, missing_copy_implementations)]
#[doc(alias = "hwloc_obj")]
#[doc(alias = "hwloc_obj_t")]
#[repr(transparent)]
pub struct TopologyObject(hwloc_obj);

/// # Basic identity
impl TopologyObject {
    /// Type of object
    #[doc(alias = "hwloc_obj::type")]
    pub fn object_type(&self) -> ObjectType {
        self.0.ty.try_into().expect("Got unexpected object type")
    }

    /// Subtype string to better describe the type field
    ///
    /// See <https://hwloc.readthedocs.io/en/v2.9/attributes.html#attributes_normal>
    /// for a list of subtype strings that hwloc can emit.
    #[doc(alias = "hwloc_obj::subtype")]
    pub fn subtype(&self) -> Option<&CStr> {
        // SAFETY: - Pointer validity is assumed as a type invariant
        //         - Rust aliasing rules are enforced by deriving the reference
        //           from &self, which itself is derived from &Topology
        unsafe { ffi::deref_str(&self.0.subtype) }
    }

    /// Set the subtype string
    ///
    /// This is something you'll often want to do when creating Group or Misc
    /// objects in order to make them more descriptive.
    ///
    /// # Errors
    ///
    /// - [`NulError`] if `subtype` contains NUL chars.
    pub fn set_subtype(&mut self, subtype: &str) -> Result<(), NulError> {
        self.0.subtype = LibcString::new(subtype)?.into_raw();
        Ok(())
    }

    /// Object-specific name, if any
    ///
    /// Mostly used for identifying OS devices and Misc objects where a name
    /// string is more useful than numerical indices.
    #[doc(alias = "hwloc_obj::name")]
    pub fn name(&self) -> Option<&CStr> {
        // SAFETY: - Pointer validity is assumed as a type invariant
        //         - Rust aliasing rules are enforced by deriving the reference
        //           from &self, which itself is derived from &Topology
        unsafe { ffi::deref_str(&self.0.name) }
    }

    /// Object type-specific attributes, if any
    #[doc(alias = "hwloc_obj::attr")]
    pub fn attributes(&self) -> Option<ObjectAttributes<'_>> {
        // SAFETY: Per type invariant
        unsafe { ObjectAttributes::new(self.object_type(), &self.0.attr) }
    }

    /// The OS-provided physical index number
    ///
    /// It is not guaranteed unique across the entire machine,
    /// except for PUs and NUMA nodes.
    ///
    /// Not specified if unknown or irrelevant for this object.
    #[doc(alias = "hwloc_obj::os_index")]
    pub fn os_index(&self) -> Option<usize> {
        (self.0.os_index != HWLOC_UNKNOWN_INDEX).then(|| int::expect_usize(self.0.os_index))
    }

    /// Global persistent index
    ///
    /// Generated by hwloc, unique across the topology (contrary to
    /// [`os_index()`]) and persistent across topology changes (contrary to
    /// [`logical_index()`]).
    ///
    /// All this means you can safely use this index as a cheap key representing
    /// the object in a Set or a Map, as long as that Set or Map only refers to
    /// [`TopologyObject`]s originating from a single [`Topology`].
    ///
    /// [`logical_index()`]: Self::logical_index()
    /// [`os_index()`]: Self::os_index()
    #[doc(alias = "hwloc_obj::gp_index")]
    pub fn global_persistent_index(&self) -> TopologyObjectID {
        self.0.gp_index
    }
}

/// Global persistent [`TopologyObject`] ID
///
/// Generated by hwloc, unique across a given topology and persistent across
/// topology changes. Basically, the only collisions you can expect are between
/// objects from different topologies, which you normally shouldn't mix.
pub type TopologyObjectID = u64;

/// # Depth and ancestors
//
// --- Implementation details ---
//
// Includes functionality inspired by https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__ancestors.html
impl TopologyObject {
    /// Vertical index in the hierarchy
    ///
    /// For normal objects, this is the depth of the horizontal level that
    /// contains this object and its cousins of the same type. If the topology
    /// is symmetric, this is equal to the parent depth plus one, and also equal
    /// to the number of parent/child links from the root object to here.
    ///
    /// For special objects (NUMA nodes, I/O and Misc) that are not in the main
    /// tree, this is a special value that is unique to their type.
    #[doc(alias = "hwloc_obj::depth")]
    pub fn depth(&self) -> Depth {
        Depth::from_raw(self.0.depth).expect("Got unexpected depth value")
    }

    /// Parent object
    ///
    /// Only `None` for the root `Machine` object.
    #[doc(alias = "hwloc_obj::parent")]
    pub fn parent(&self) -> Option<&Self> {
        // SAFETY: - Pointer & target validity are assumed as a type invariant
        //         - Rust aliasing rules are enforced by deriving the reference
        //           from &self, which itself is derived from &Topology
        unsafe { ffi::deref_ptr_mut(&self.0.parent).map(|raw| raw.as_newtype()) }
    }

    /// Chain of parent objects up to the topology root
    pub fn ancestors(&self) -> impl ExactSizeIterator<Item = &Self> + Clone + FusedIterator {
        Ancestors(self)
    }

    /// Search for an ancestor at a certain depth
    ///
    /// Accepts [`Depth`], [`NormalDepth`] and [`usize`] operands. Use the
    /// former two for type-safety (they are guaranteed to be in range as a type
    /// invariant) or the latter for convenience (it is more tightly integrated
    /// with Rust's built-in integer support, for example it supports integer
    /// literals).
    ///
    /// Will return `None` if the requested depth is deeper than the depth of
    /// the current object.
    #[doc(alias = "hwloc_get_ancestor_obj_by_depth")]
    pub fn ancestor_at_depth<DepthLike>(&self, depth: DepthLike) -> Option<&Self>
    where
        DepthLike: TryInto<Depth>,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized(self_: &TopologyObject, depth: Depth) -> Option<&TopologyObject> {
            // Fast failure path when depth is comparable
            let self_depth = self_.depth();
            if let (Ok(self_depth), Ok(depth)) = (
                NormalDepth::try_from(self_depth),
                NormalDepth::try_from(depth),
            ) {
                if self_depth <= depth {
                    return None;
                }
            }

            // Otherwise, walk parents looking for the right depth
            self_.ancestors().find(|ancestor| ancestor.depth() == depth)
        }

        // There cannot be any ancestor at a depth below the hwloc-supported max
        let depth = depth.try_into().ok()?;
        polymorphized(self, depth)
    }

    /// Search for the first ancestor with a certain type in ascending order
    ///
    /// If multiple matching ancestors exist (which can happen with [`Group`]
    /// ancestors), the lowest ancestor is returned.
    ///
    /// Will return `None` if the requested type appears deeper than the
    /// current object or doesn't appear in the topology.
    ///
    /// [`Group`]: ObjectType::Group
    #[doc(alias = "hwloc_get_ancestor_obj_by_type")]
    pub fn first_ancestor_with_type(&self, ty: ObjectType) -> Option<&Self> {
        self.ancestors()
            .find(|ancestor| ancestor.object_type() == ty)
    }

    /// Search for the first ancestor that is shared with another object
    ///
    /// The search will always succeed unless...
    /// - One of `self` and `other` is the root [`Machine`](ObjectType::Machine)
    ///   object, which has no ancestors.
    /// - `self` and `other` do not belong to the same topology, and thus have
    ///   no shared ancestor.
    #[doc(alias = "hwloc_get_common_ancestor_obj")]
    pub fn common_ancestor(&self, other: &Self) -> Option<&Self> {
        // Handle degenerate case
        if ptr::eq(self, other) {
            return self.parent();
        }

        /// Collect ancestors with virtual depths on both sides
        /// Returns the list of ancestors with virtual depths together with the
        /// first ancestor with a normal depth, if any
        fn collect_virtual_ancestors(
            obj: &TopologyObject,
        ) -> (Vec<&TopologyObject>, Option<&TopologyObject>) {
            let mut ancestors = Vec::new();
            let mut current = obj;
            loop {
                if let Some(parent) = current.parent() {
                    if let Depth::Normal(_) = parent.depth() {
                        return (ancestors, Some(parent));
                    } else {
                        ancestors.push(parent);
                        current = parent;
                    }
                } else {
                    return (ancestors, None);
                }
            }
        }
        let (virtual_ancestors_1, parent1) = collect_virtual_ancestors(self);
        let (virtual_ancestors_2, parent2) = collect_virtual_ancestors(other);

        // Make sure there is no common ancestor at some virtual depth
        // (can't avoid O(N²) alg here as virtual depths cannot be compared)
        for ancestor1 in virtual_ancestors_1 {
            for ancestor2 in &virtual_ancestors_2 {
                if ptr::eq(ancestor1, *ancestor2) {
                    return Some(ancestor1);
                }
            }
        }

        // Now that we have virtual depths taken care of, we can enter a fast
        // path for parents with normal depths (if any)
        let mut parent1 = parent1?;
        let mut parent2 = parent2?;
        loop {
            // Walk up ancestors, try to reach the same depth.
            // Only normal depths should be observed all the way through the
            // ancestor chain, since the parent of a normal object is normal.
            let normal_depth = |obj: &Self| {
                NormalDepth::try_from(obj.depth()).expect("Should only observe normal depth here")
            };
            let depth2 = normal_depth(parent2);
            while normal_depth(parent1) > depth2 {
                parent1 = parent1.parent()?;
            }
            let depth1 = normal_depth(parent1);
            while normal_depth(parent2) > depth1 {
                parent2 = parent2.parent()?;
            }

            // If we reached the same parent, we're done
            if ptr::eq(parent1, parent2) {
                return Some(parent1);
            }

            // Otherwise, either parent2 jumped above parent1 (which can happen
            // as hwloc topology may "skip" depths on hybrid plaforms like
            // Adler Lake or in the presence of complicated allowed cpusets), or
            // we reached cousin objects and must go up one level.
            if parent1.depth() == parent2.depth() {
                parent1 = parent1.parent()?;
                parent2 = parent2.parent()?;
            }
        }
    }

    /// Truth that this object is in the subtree beginning with ancestor
    /// object `subtree_root`
    ///
    /// This will return `false` if `self` and `subtree_root` do not belong to
    /// the same topology.
    #[doc(alias = "hwloc_obj_is_in_subtree")]
    pub fn is_in_subtree(&self, subtree_root: &Self) -> bool {
        // NOTE: Not reusing the cpuset-based optimization of hwloc as it is
        //       invalid in the presence of objects that do not belong to the
        //       same topology and there is no way to detect whether this is the
        //       case or not without... walking the ancestors ;)
        self.ancestors()
            .any(|ancestor| ptr::eq(ancestor, subtree_root))
    }

    /// Get the first data (or unified) CPU cache shared between this object and
    /// another object, if any.
    ///
    /// Will always return `None` if called on an I/O or Misc object that does
    /// not contain CPUs.
    #[doc(alias = "hwloc_get_shared_cache_covering_obj")]
    pub fn first_shared_cache(&self) -> Option<&Self> {
        let cpuset = self.cpuset()?;
        self.ancestors()
            .skip_while(|ancestor| {
                ancestor
                    .cpuset()
                    .map_or(false, |ancestor_set| ancestor_set == cpuset)
            })
            .find(|ancestor| ancestor.object_type().is_cpu_data_cache())
    }

    /// Get the first non-I/O ancestor object
    ///
    /// Find the smallest non-I/O ancestor object. This object (normal or
    /// memory) may then be used for binding because it has CPU and node sets
    /// and because its locality is the same as this object.
    #[doc(alias = "hwloc_get_non_io_ancestor_obj")]
    pub fn non_io_ancestor(&self) -> &Self {
        self.ancestors()
            .find(|obj| obj.cpuset().is_some())
            .expect("Per hwloc documentation, there has to be one non-I/O ancestor")
    }
}

/// Iterator over ancestors of a topology object
#[derive(Copy, Clone, Debug)]
struct Ancestors<'object>(&'object TopologyObject);
//
impl<'object> Iterator for Ancestors<'object> {
    type Item = &'object TopologyObject;

    fn next(&mut self) -> Option<Self::Item> {
        self.0 = self.0.parent()?;
        Some(self.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let depth_res = usize::try_from(self.0.depth());
        (depth_res.unwrap_or(0), depth_res.ok())
    }
}
//
impl ExactSizeIterator for Ancestors<'_> {}
//
impl FusedIterator for Ancestors<'_> {}

/// # Cousins and siblings
impl TopologyObject {
    /// Horizontal index in the whole list of similar objects, hence guaranteed
    /// unique across the entire machine
    ///
    /// Could be a "cousin rank" since it's the rank within the "cousin" list.
    ///
    /// Note that this index may change when restricting the topology
    /// or when inserting a group.
    #[doc(alias = "hwloc_obj::logical_index")]
    pub fn logical_index(&self) -> usize {
        int::expect_usize(self.0.logical_index)
    }

    /// Next object of same type and depth
    #[doc(alias = "hwloc_obj::next_cousin")]
    pub fn next_cousin(&self) -> Option<&Self> {
        // SAFETY: - Pointer and target validity are assumed as a type invariant
        //         - Rust aliasing rules are enforced by deriving the reference
        //           from &self, which itself is derived from &Topology
        unsafe { ffi::deref_ptr_mut(&self.0.next_cousin).map(|raw| raw.as_newtype()) }
    }

    /// Previous object of same type and depth
    #[doc(alias = "hwloc_obj::prev_cousin")]
    pub fn prev_cousin(&self) -> Option<&Self> {
        // SAFETY: - Pointer and target validity are assumed as a type invariant
        //         - Rust aliasing rules are enforced by deriving the reference
        //           from &self, which itself is derived from &Topology
        unsafe { ffi::deref_ptr_mut(&self.0.prev_cousin).map(|raw| raw.as_newtype()) }
    }

    /// Index in the parent's relevant child list for this object type
    #[doc(alias = "hwloc_obj::sibling_rank")]
    pub fn sibling_rank(&self) -> usize {
        int::expect_usize(self.0.sibling_rank)
    }

    /// Next object below the same parent, in the same child list
    #[doc(alias = "hwloc_obj::next_sibling")]
    pub fn next_sibling(&self) -> Option<&Self> {
        // SAFETY: - Pointer and target validity are assumed as a type invariant
        //         - Rust aliasing rules are enforced by deriving the reference
        //           from &self, which itself is derived from &Topology
        unsafe { ffi::deref_ptr_mut(&self.0.next_sibling).map(|raw| raw.as_newtype()) }
    }

    /// Previous object below the same parent, in the same child list
    #[doc(alias = "hwloc_obj::prev_sibling")]
    pub fn prev_sibling(&self) -> Option<&Self> {
        // SAFETY: - Pointer and target validity are assumed as a type invariant
        //         - Rust aliasing rules are enforced by deriving the reference
        //           from &self, which itself is derived from &Topology
        unsafe { ffi::deref_ptr_mut(&self.0.prev_sibling).map(|raw| raw.as_newtype()) }
    }
}

/// # Children
impl TopologyObject {
    /// Number of normal children (excluding Memory, Misc and I/O)
    #[doc(alias = "hwloc_obj::arity")]
    pub fn normal_arity(&self) -> usize {
        int::expect_usize(self.0.arity)
    }

    /// Normal children of this object
    #[doc(alias = "hwloc_obj::children")]
    #[doc(alias = "hwloc_obj::first_child")]
    #[doc(alias = "hwloc_obj::last_child")]
    pub fn normal_children(
        &self,
    ) -> impl DoubleEndedIterator<Item = &Self> + Clone + ExactSizeIterator + FusedIterator {
        if self.0.children.is_null() {
            assert_eq!(
                self.normal_arity(),
                0,
                "Got null children pointer with nonzero arity"
            );
        }
        (0..self.normal_arity()).map(move |offset| {
            // SAFETY: Pointer is in bounds by construction
            let child = unsafe { *self.0.children.add(offset) };
            assert!(!child.is_null(), "Got null child pointer");
            // SAFETY: - We checked that the pointer isn't null
            //         - Pointer & target validity assumed as a type invariant
            //         - Rust aliasing rules are enforced by deriving the reference
            //           from &self, which itself is derived from &Topology
            unsafe { (&*child).as_newtype() }
        })
    }

    // NOTE: Not exposing first_/last_child accessors for now as in the presence
    //       of the normal_children iterator, they feel very redundant, and I
    //       can't think of a usage situation where avoiding one pointer
    //       indirection by exposing them would be worth the API inconsistency.
    //       If you do, please submit an issue to the repository!

    /// Truth that this object is symmetric, which means all normal children and
    /// their children have identical subtrees
    ///
    /// Memory, I/O and Misc children are ignored.
    ///
    /// If this is true of the root object, then the topology may be [exported
    /// as a synthetic string](Topology::export_synthetic()).
    #[doc(alias = "hwloc_obj::symmetric_subtree")]
    pub fn symmetric_subtree(&self) -> bool {
        self.0.symmetric_subtree != 0
    }

    /// Get the child covering at least the given cpuset `set`
    ///
    /// Accepts both `&'_ CpuSet` and `BitmapRef<'_, CpuSet>` operands.
    ///
    /// This function will always return `None` if the given set is empty or
    /// this topology object doesn't have a cpuset (I/O or Misc objects), as
    /// no object is considered to cover the empty cpuset.
    #[doc(alias = "hwloc_get_child_covering_cpuset")]
    pub fn normal_child_covering_cpuset(&self, set: impl Deref<Target = CpuSet>) -> Option<&Self> {
        let set: &CpuSet = &set;
        self.normal_children()
            .find(|child| child.covers_cpuset(set))
    }

    /// Number of memory children
    #[doc(alias = "hwloc_obj::memory_arity")]
    pub fn memory_arity(&self) -> usize {
        int::expect_usize(self.0.memory_arity)
    }

    /// Memory children of this object
    ///
    /// NUMA nodes and Memory-side caches are listed here instead of in the
    /// [`TopologyObject::normal_children()`] list. See also
    /// [`ObjectType::is_memory()`].
    ///
    /// A memory hierarchy starts from a normal CPU-side object (e.g.
    /// [`Package`]) and ends with NUMA nodes as leaves. There might exist some
    /// memory-side caches between them in the middle of the memory subtree.
    ///
    /// [`Package`]: ObjectType::Package
    #[doc(alias = "hwloc_obj::memory_first_child")]
    pub fn memory_children(&self) -> impl ExactSizeIterator<Item = &Self> + Clone + FusedIterator {
        // SAFETY: - memory_first_child is a valid first-child of this object
        //         - memory_arity is assumed in sync as a type invariant
        unsafe { self.singly_linked_children(self.0.memory_first_child, self.memory_arity()) }
    }

    /// Total memory (in bytes) in NUMA nodes below this object
    ///
    /// Requires [`DiscoverySupport::numa_memory()`].
    #[doc(alias = "hwloc_obj::total_memory")]
    pub fn total_memory(&self) -> u64 {
        self.0.total_memory
    }

    /// Number of I/O children
    #[doc(alias = "hwloc_obj::io_arity")]
    pub fn io_arity(&self) -> usize {
        int::expect_usize(self.0.io_arity)
    }

    /// I/O children of this object
    ///
    /// Bridges, PCI and OS devices are listed here instead of in the
    /// [`TopologyObject::normal_children()`] list. See also
    /// [`ObjectType::is_io()`].
    #[doc(alias = "hwloc_obj::io_first_child")]
    pub fn io_children(&self) -> impl ExactSizeIterator<Item = &Self> + Clone + FusedIterator {
        // SAFETY: - io_first_child is a valid first-child of this object
        //         - io_arity is assumed in sync as a type invariant
        unsafe { self.singly_linked_children(self.0.io_first_child, self.io_arity()) }
    }

    /// Truth that this is a bridge covering the specified PCI bus
    #[doc(alias = "hwloc_bridge_covers_pcibus")]
    pub fn is_bridge_covering_pci_bus(&self, domain: PCIDomain, bus_id: u8) -> bool {
        let Some(ObjectAttributes::Bridge(bridge)) = self.attributes() else {
            return false;
        };
        let Some(DownstreamAttributes::PCI(pci)) = bridge.downstream_attributes() else {
            return false;
        };
        pci.domain() == domain && pci.secondary_bus() <= bus_id && pci.subordinate_bus() >= bus_id
    }

    /// Number of Misc children
    #[doc(alias = "hwloc_obj::misc_arity")]
    pub fn misc_arity(&self) -> usize {
        int::expect_usize(self.0.misc_arity)
    }

    /// Misc children of this object
    ///
    /// Misc objects are listed here instead of in the
    /// [`TopologyObject::normal_children()`] list.
    #[doc(alias = "hwloc_obj::misc_first_child")]
    pub fn misc_children(&self) -> impl ExactSizeIterator<Item = &Self> + Clone + FusedIterator {
        // SAFETY: - misc_first_child is a valid first-child of this object
        //         - misc_arity is assumed in sync as a type invariant
        unsafe { self.singly_linked_children(self.0.misc_first_child, self.misc_arity()) }
    }

    /// Full list of children (normal, then memory, then I/O, then Misc)
    #[doc(alias = "hwloc_get_next_child")]
    pub fn all_children(&self) -> impl FusedIterator<Item = &Self> + Clone {
        self.normal_children()
            .chain(self.memory_children())
            .chain(self.io_children())
            .chain(self.misc_children())
    }

    /// Iterator over singly linked lists of child objects with known arity
    ///
    /// # Safety
    ///
    /// - `first` must be one of the `xyz_first_child` pointers of this object
    /// - `arity` must be the matching `xyz_arity` child count variable
    unsafe fn singly_linked_children(
        &self,
        first: *mut hwloc_obj,
        arity: usize,
    ) -> impl ExactSizeIterator<Item = &Self> + Clone + FusedIterator {
        let mut current = first;
        (0..arity).map(move |_| {
            assert!(!current.is_null(), "Got null child before expected arity");
            // SAFETY: - We checked that the pointer isn't null
            //         - Pointer & target validity assumed as a type invariant
            //         - Rust aliasing rules are enforced by deriving the reference
            //           from &self, which itself is derived from &Topology
            let result: &Self = unsafe { (&*current).as_newtype() };
            current = result.0.next_sibling;
            result
        })
    }
}

/// # CPU set
impl TopologyObject {
    /// CPUs covered by this object
    ///
    /// This is the set of CPUs for which there are PU objects in the
    /// topology under this object, i.e. which are known to be physically
    /// contained in this object and known how (the children path between this
    /// object and the PU objects).
    ///
    /// If the [`BuildFlags::INCLUDE_DISALLOWED`] topology building
    /// configuration flag is set, some of these CPUs may be online but not
    /// allowed for binding, see [`Topology::allowed_cpuset()`].
    ///
    /// All objects have CPU and node sets except Misc and I/O objects, so if
    /// you know this object to be a normal or Memory object, you can safely
    /// unwrap this Option.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use hwlocality::Topology;
    /// # let topology = Topology::test_instance();
    /// println!(
    ///     "Visible CPUs attached to the root object: {:?}",
    ///     topology.root_object().cpuset()
    /// );
    /// # Ok::<_, eyre::Report>(())
    /// ```
    #[doc(alias = "hwloc_obj::cpuset")]
    pub fn cpuset(&self) -> Option<BitmapRef<'_, CpuSet>> {
        // SAFETY: Per type invariant
        unsafe { CpuSet::borrow_from_raw_mut(self.0.cpuset) }
    }

    /// Truth that this object is inside of the given cpuset `set`
    ///
    /// Accepts both `&'_ CpuSet` and `BitmapRef<'_, CpuSet>` operands.
    ///
    /// Objects are considered to be inside `set` if they have a non-empty
    /// cpuset which verifies `set.includes(object_cpuset)`.
    pub fn is_inside_cpuset(&self, set: impl Deref<Target = CpuSet>) -> bool {
        let Some(object_cpuset) = self.cpuset() else {
            return false;
        };
        set.includes(object_cpuset) && !object_cpuset.is_empty()
    }

    /// Truth that this object covers the given cpuset `set`
    ///
    /// Accepts both `&'_ CpuSet` and `BitmapRef<'_, CpuSet>` operands.
    ///
    /// Objects are considered to cover `set` if it is non-empty and the object
    /// has a cpuset which verifies `object_cpuset.includes(set)`.
    pub fn covers_cpuset(&self, set: impl Deref<Target = CpuSet>) -> bool {
        let Some(object_cpuset) = self.cpuset() else {
            return false;
        };
        let set: &CpuSet = &set;
        object_cpuset.includes(set) && !set.is_empty()
    }

    /// The complete CPU set of this object
    ///
    /// To the CPUs listed by [`cpuset()`], this adds CPUs for which topology
    /// information is unknown or incomplete, some offline CPUs, and CPUs that
    /// are ignored when the [`BuildFlags::INCLUDE_DISALLOWED`] topology
    /// building configuration flag is not set.
    ///
    /// Thus no corresponding PU object may be found in the topology, because
    /// the precise position is undefined. It is however known that it would be
    /// somewhere under this object.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use hwlocality::Topology;
    /// # let topology = Topology::test_instance();
    /// println!(
    ///     "Overall CPUs attached to the root object: {:?}",
    ///     topology.root_object().complete_cpuset()
    /// );
    /// # Ok::<_, eyre::Report>(())
    /// ```
    ///
    /// [`cpuset()`]: Self::cpuset()
    #[doc(alias = "hwloc_obj::complete_cpuset")]
    pub fn complete_cpuset(&self) -> Option<BitmapRef<'_, CpuSet>> {
        // SAFETY: Per type invariant
        unsafe { CpuSet::borrow_from_raw_mut(self.0.complete_cpuset) }
    }
}

/// # NUMA node set
impl TopologyObject {
    /// NUMA nodes covered by this object or containing this object.
    ///
    /// This is the set of NUMA nodes for which there are NUMA node objects in
    /// the topology under or above this object, i.e. which are known to be
    /// physically contained in this object or containing it and known how
    /// (the children path between this object and the NUMA node objects). In
    /// the end, these nodes are those that are close to the current object.
    ///
    #[cfg_attr(
        feature = "hwloc-2_3_0",
        doc = "With hwloc 2.3+, [`Topology::local_numa_nodes()`] may be used to"
    )]
    #[cfg_attr(feature = "hwloc-2_3_0", doc = "list those NUMA nodes more precisely.")]
    ///
    /// If the [`BuildFlags::INCLUDE_DISALLOWED`] topology building
    /// configuration flag is set, some of these nodes may not be allowed for
    /// allocation, see [`Topology::allowed_nodeset()`].
    ///
    /// If there are no NUMA nodes in the machine, all the memory is close to
    /// this object, so the nodeset is full.
    ///
    /// All objects have CPU and node sets except Misc and I/O objects, so if
    /// you know this object to be a normal or Memory object, you can safely
    /// unwrap this Option.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use hwlocality::Topology;
    /// # let topology = Topology::test_instance();
    /// println!(
    ///     "Visible NUMA nodes attached to the root object: {:?}",
    ///     topology.root_object().nodeset()
    /// );
    /// # Ok::<_, eyre::Report>(())
    /// ```
    #[doc(alias = "hwloc_obj::nodeset")]
    pub fn nodeset(&self) -> Option<BitmapRef<'_, NodeSet>> {
        // SAFETY: Per type invariant
        unsafe { NodeSet::borrow_from_raw_mut(self.0.nodeset) }
    }

    /// The complete NUMA node set of this object
    ///
    /// To the nodes listed by [`nodeset()`], this adds nodes for which topology
    /// information is unknown or incomplete, some offline nodes, and nodes
    /// that are ignored when the [`BuildFlags::INCLUDE_DISALLOWED`] topology
    /// building configuration flag is not set.
    ///
    /// Thus no corresponding [`NUMANode`] object may be found in the topology,
    /// because the precise position is undefined. It is however known that it
    /// would be somewhere under this object.
    ///
    /// If there are no NUMA nodes in the machine, all the memory is close to
    /// this object, so the complete nodeset is full.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use hwlocality::Topology;
    /// # let topology = Topology::test_instance();
    /// println!(
    ///     "Overall NUMA nodes attached to the root object: {:?}",
    ///     topology.root_object().complete_nodeset()
    /// );
    /// # Ok::<_, eyre::Report>(())
    /// ```
    ///
    /// [`nodeset()`]: Self::nodeset()
    /// [`NUMANode`]: ObjectType::NUMANode
    #[doc(alias = "hwloc_obj::complete_nodeset")]
    pub fn complete_nodeset(&self) -> Option<BitmapRef<'_, NodeSet>> {
        // SAFETY: Per type invariant
        unsafe { NodeSet::borrow_from_raw_mut(self.0.complete_nodeset) }
    }
}

/// # Key-value information
impl TopologyObject {
    /// Complete list of (key, value) textual info pairs
    ///
    /// hwloc defines [a number of standard object info attribute names with
    /// associated semantics](https://hwloc.readthedocs.io/en/v2.9/attributes.html#attributes_info).
    ///
    /// Beware that hwloc allows multiple informations with the same key to
    /// exist, although sane users should not leverage this possibility.
    #[doc(alias = "hwloc_obj::infos")]
    pub fn infos(&self) -> &[TextualInfo] {
        if self.0.children.is_null() {
            assert_eq!(
                self.0.infos_count, 0,
                "Got null infos pointer with nonzero info count"
            );
            return &[];
        }
        // SAFETY: - infos and count are assumed in sync per type invariant
        //         - infos are assumed to be valid per type invariant
        //         - AsNewtype is trusted to be implemented correctly
        unsafe {
            std::slice::from_raw_parts(
                self.0.infos.as_newtype(),
                int::expect_usize(self.0.infos_count),
            )
        }
    }

    /// Search the given key name in object infos and return the corresponding value
    ///
    /// Beware that hwloc allows multiple informations with the same key to
    /// exist, although no sane programs should leverage this possibility.
    /// If multiple keys match the given name, only the first one is returned.
    ///
    /// Calling this operation multiple times will result in duplicate work. If
    /// you need to do this sort of search many times, consider collecting
    /// `infos()` into a `HashMap` or `BTreeMap` for increased lookup efficiency.
    #[doc(alias = "hwloc_obj_get_info_by_name")]
    pub fn info(&self, key: &str) -> Option<&CStr> {
        self.infos().iter().find_map(|info| {
            let Ok(info_name) = info.name().to_str() else {
                return None;
            };
            (info_name == key).then_some(info.value())
        })
    }

    /// Add the given info name and value pair to the given object
    ///
    /// The info is appended to the existing info array even if another key with
    /// the same name already exists.
    ///
    /// This function may be used to enforce object colors in the lstopo
    /// graphical output by using "lstopoStyle" as a name and "Background=#rrggbb"
    /// as a value. See `CUSTOM COLORS` in the `lstopo(1)` manpage for details.
    ///
    /// If value contains some non-printable characters, they will be dropped
    /// when exporting to XML.
    ///
    /// # Errors
    ///
    /// - [`NulError`] if `name` or `value` contains NUL chars.
    #[doc(alias = "hwloc_obj_add_info")]
    pub fn add_info(&mut self, name: &str, value: &str) -> Result<(), HybridError<NulError>> {
        let name = LibcString::new(name)?;
        let value = LibcString::new(value)?;
        // SAFETY: - An &mut TopologyObject may only be obtained from &mut Topology
        //         - Object validity trusted by type invariant
        //         - hwloc is trusted not to make object invalid
        //         - LibcStrings are valid C strings by construction, and not
        //           used after the end of their lifetimes
        errors::call_hwloc_int_normal("hwloc_obj_add_info", || unsafe {
            hwlocality_sys::hwloc_obj_add_info(&mut self.0, name.borrow(), value.borrow())
        })
        .map(std::mem::drop)
        .map_err(HybridError::Hwloc)
    }
}

// # Internal utilities
impl TopologyObject {
    /// Display this object's type and attributes
    fn display(&self, f: &mut fmt::Formatter<'_>, verbose: bool) -> fmt::Result {
        // SAFETY: - These are indeed snprintf-like APIs
        //         - Object validity trusted by type invariant
        //         - verbose translates nicely into a C-style boolean
        //         - separators are valid C strings
        let (type_chars, attr_chars) = unsafe {
            let type_chars = ffi::call_snprintf(|buf, len| {
                hwlocality_sys::hwloc_obj_type_snprintf(buf, len, &self.0, verbose.into())
            });

            let separator = if f.alternate() {
                b",\n  \0".as_ptr()
            } else {
                b", \0".as_ptr()
            }
            .cast::<c_char>();
            let attr_chars = ffi::call_snprintf(|buf, len| {
                hwlocality_sys::hwloc_obj_attr_snprintf(
                    buf,
                    len,
                    &self.0,
                    separator,
                    verbose.into(),
                )
            });
            (type_chars, attr_chars)
        };

        let cpuset_str = self.cpuset().map_or_else(
            || " without a CpuSet".to_owned(),
            |cpuset| format!(" with {cpuset}"),
        );

        // SAFETY: - Output of call_snprintf should be valid C strings
        //         - We're not touching type_chars and attr_chars while type_str
        //           and attr_str are live.
        unsafe {
            let type_str = CStr::from_ptr(type_chars.as_ptr()).to_string_lossy();
            let attr_str = CStr::from_ptr(attr_chars.as_ptr()).to_string_lossy();
            let type_and_cpuset = format!("{type_str}{cpuset_str}");
            if attr_str.is_empty() {
                f.pad(&type_and_cpuset)
            } else if f.alternate() {
                let s = format!("{type_and_cpuset} (\n  {attr_str}\n)");
                f.pad(&s)
            } else {
                let s = format!("{type_and_cpuset} ({attr_str})");
                f.pad(&s)
            }
        }
    }

    /// Delete all cpusets and nodesets from a non-inserted `Group` object
    ///
    /// This is needed as part of a dirty topology editing workaround that will
    /// hopefully not be needed anymore after hwloc v2.10.
    ///
    /// # (Absence of) Panics
    ///
    /// This method is called inside of destructors, it should never panic.
    ///
    /// # Safety
    ///
    /// `self_` must designate a valid `Group` object that has been allocated
    /// with `hwloc_topology_alloc_group_object()` but not yet inserted into a
    /// topology with `hwloc_topology_insert_group_object()`.
    #[cfg(feature = "hwloc-2_3_0")]
    pub(crate) unsafe fn delete_all_sets(self_: ptr::NonNull<Self>) {
        use ptr::addr_of_mut;

        let self_ = self_.as_ptr();
        for set_ptr in [
            addr_of_mut!((*self_).0.cpuset),
            addr_of_mut!((*self_).0.nodeset),
            addr_of_mut!((*self_).0.complete_cpuset),
            addr_of_mut!((*self_).0.complete_nodeset),
        ] {
            // SAFETY: This is safe per the input precondition that `self_` is a
            //         valid `TopologyObject` (which includes valid bitmap
            //         pointers), and it's not part of a `Topology` yet so we
            //         assume complete ownership of it delete its cpu/node-sets
            //         without worrying about unintended consequences.
            unsafe {
                let set = set_ptr.read();
                if !set.is_null() {
                    hwlocality_sys::hwloc_bitmap_free(set);
                    set_ptr.write(ptr::null_mut())
                }
            }
        }
    }
}

impl Debug for TopologyObject {
    /// Verbose display of the object's type and attributes
    ///
    /// See the [`Display`] implementation if you want a more concise display.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use hwlocality::Topology;
    /// # let topology = Topology::test_instance();
    /// println!("Root object: {:#?}", topology.root_object());
    /// # Ok::<_, eyre::Report>(())
    /// ```
    #[doc(alias = "hwloc_obj_attr_snprintf")]
    #[doc(alias = "hwloc_obj_type_snprintf")]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.display(f, true)
    }
}

impl Display for TopologyObject {
    #[allow(clippy::doc_markdown)]
    /// Display of the type and attributes that is more concise than [`Debug`]
    ///
    /// - Shorter type names are used, e.g. "L1Cache" becomes "L1"
    /// - Only the major object attributes are printed
    ///
    /// # Example
    ///
    /// ```rust
    /// # use hwlocality::Topology;
    /// # let topology = Topology::test_instance();
    /// println!("Root object: {}", topology.root_object());
    /// # Ok::<_, eyre::Report>(())
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.display(f, false)
    }
}

// SAFETY: No internal mutability
unsafe impl Send for TopologyObject {}

// SAFETY: No internal mutability
unsafe impl Sync for TopologyObject {}

// SAFETY: TopologyObject is a repr(transparent) newtype of hwloc_obj
unsafe impl TransparentNewtype for TopologyObject {
    type Inner = hwloc_obj;
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use proptest::prelude::*;
    use similar_asserts::assert_eq;
    use std::collections::{HashMap, HashSet};

    /// Pick a random object from the test instance
    pub(crate) fn test_object() -> impl Strategy<Value = &'static TopologyObject> {
        prop::sample::select(Topology::test_objects())
    }

    /// Check that the various object lists match their definitions
    #[test]
    fn object_lists() {
        let topology = Topology::test_instance();

        fn checked_object_set<'a>(
            it: impl Iterator<Item = &'a TopologyObject>,
        ) -> HashMap<u64, &'a TopologyObject> {
            let mut set = HashMap::new();
            for obj in it {
                assert!(
                    set.insert(obj.global_persistent_index(), obj).is_none(),
                    "global_persistent_index should be unique across the topology"
                );
            }
            set
        }
        let key_set = |map: &HashMap<u64, _>| -> HashSet<u64> { map.keys().copied().collect() };

        let objects = checked_object_set(topology.objects());
        let keys = key_set(&objects);

        let normal_objects = checked_object_set(topology.normal_objects());
        assert!(normal_objects
            .values()
            .all(|obj| obj.object_type().is_normal()));
        let normal_keys = key_set(&normal_objects);

        let virtual_objects = checked_object_set(topology.virtual_objects());
        assert!(virtual_objects
            .values()
            .all(|obj| !obj.object_type().is_normal()));
        let virtual_keys = key_set(&virtual_objects);

        assert_eq!(keys, &normal_keys | &virtual_keys);
        assert_eq!(normal_keys, &keys - &virtual_keys);
        assert_eq!(virtual_keys, &keys - &normal_keys);

        let memory_objects = checked_object_set(topology.memory_objects());
        assert!(memory_objects
            .values()
            .all(|obj| obj.object_type().is_memory()));
        let memory_keys = key_set(&memory_objects);

        let io_objects = checked_object_set(topology.io_objects());
        assert!(io_objects.values().all(|obj| obj.object_type().is_io()));
        let io_keys = key_set(&io_objects);

        let misc_objects = checked_object_set(topology.objects_with_type(ObjectType::Misc));
        assert!(misc_objects
            .values()
            .all(|obj| obj.object_type() == ObjectType::Misc));
        let misc_keys = key_set(&misc_objects);

        assert_eq!(virtual_keys, &(&memory_keys | &io_keys) | &misc_keys);
        assert_eq!(memory_keys, &(&virtual_keys - &io_keys) - &misc_keys);
        assert_eq!(io_keys, &(&virtual_keys - &memory_keys) - &misc_keys);
        assert_eq!(misc_keys, &(&virtual_keys - &memory_keys) - &io_keys);
    }
}
