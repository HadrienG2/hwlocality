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
    errors::{ForeignObjectError, ParameterError},
    ffi::{
        self, int,
        transparent::{AsNewtype, TransparentNewtype},
    },
    info::TextualInfo,
    memory::nodeset::NodeSet,
    topology::Topology,
};
#[cfg(feature = "hwloc-2_3_0")]
use crate::{
    errors::{self, HybridError, NulError},
    ffi::string::LibcString,
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

    /// Like [`Topology::test_objects()`], but for the foreign instance
    #[cfg(test)]
    pub(crate) fn foreign_objects() -> &'static [&'static TopologyObject] {
        static OBJECTS: OnceLock<Box<[&'static TopologyObject]>> = OnceLock::new();
        &OBJECTS.get_or_init(|| Self::foreign_instance().objects().collect())[..]
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
    /// Please note that following hardware nomenclature, hardware cache levels
    /// start at 1 (L1 cache), not 0.
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
    /// `cpuset` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`.
    ///
    /// Requires [`DiscoverySupport::pu_count()`].
    ///
    /// This functionality is specific to the Rust bindings.
    pub fn pus_from_cpuset<'result>(
        &'result self,
        cpuset: impl Deref<Target = CpuSet> + Clone + 'result,
    ) -> impl DoubleEndedIterator<Item = &TopologyObject> + Clone + FusedIterator + 'result {
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
    /// `nodeset` can be a `&'_ NodeSet` or a `BitmapRef<'_, NodeSet>`.
    ///
    /// Requires [`DiscoverySupport::numa_count()`].
    ///
    /// This functionality is specific to the Rust bindings.
    pub fn nodes_from_nodeset<'result>(
        &'result self,
        nodeset: impl Deref<Target = NodeSet> + Clone + 'result,
    ) -> impl DoubleEndedIterator<Item = &TopologyObject> + Clone + FusedIterator + 'result {
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
    ) -> Result<impl Iterator<Item = &TopologyObject> + Clone + 'result, ClosestObjectsError> {
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
                        ancestor_and_cpuset = Some((ancestor, ancestor_cpuset));
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
    /// The first object is indexed relative to the topology's root Machine
    /// object and searched amongst its children. As a consequence, the root
    /// Machine object cannot be found using this method.
    ///
    /// This search may only be applied to object types that have a cpuset
    /// (normal and memory objects).
    ///
    /// # Errors
    ///
    /// - [`ParameterError`] if one of the specified object types does not have
    ///   a cpuset.
    #[doc(alias = "hwloc_get_obj_below_array_by_type")]
    #[doc(alias = "hwloc_get_obj_below_by_type")]
    pub fn object_by_type_index_path(
        &self,
        path: &[(ObjectType, usize)],
    ) -> Result<Option<&TopologyObject>, ParameterError<ObjectType>> {
        // Make sure the path only includes object types with cpusets
        if let Some(&(bad_ty, _idx)) = path.iter().find(|(ty, _idx)| !ty.has_sets()) {
            return Err(ParameterError::from(bad_ty));
        }

        // Then perform the actual search
        let mut subroot = self.root_object();
        for &(ty, idx) in path {
            // We checked the presence of a subroot cpuset in the beginning
            let cpuset = subroot
                .cpuset()
                .expect("subroot should have a cpuset per above check");

            // Define what it means to be a child
            let is_child =
                |obj: &&TopologyObject| obj.ancestors().any(|ancestor| ptr::eq(ancestor, subroot));

            // Look up child efficienty using cpuset
            if let Some(next_obj) = self
                .objects_inside_cpuset_with_type(cpuset, ty)
                .nth(idx)
                .filter(is_child)
            {
                subroot = next_obj;
            } else {
                return Ok(None);
            }
        }
        Ok(Some(subroot))
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
    /// - [`IncompatibleTypes`] if `src` is a normal/memory object and `ty` is
    ///   an I/O or Misc object type, or vice versa.
    /// - [`StringContainsNul`] if `subtype` or `name_prefix` contains NUL chars.
    ///
    /// [`ForeignSource`]: LocalObjectError::ForeignSource
    /// [`IncompatibleTypes`]: LocalObjectError::IncompatibleTypes
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
        let src_ty = src.object_type();
        if src_ty.has_sets() ^ ty.has_sets() {
            return Err(LocalObjectError::IncompatibleTypes(src_ty, ty));
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
    MissingCpuSet(#[from] MissingObjCpuSetError),
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
pub struct MissingObjCpuSetError(TopologyObjectID);
//
impl<'topology> From<&'topology TopologyObject> for MissingObjCpuSetError {
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

    /// Source object is a normal/memory object and target type is an I/O or
    /// Misc type, or vice-versa
    #[error("source object type {0} and destination object type {1} are incompatible")]
    IncompatibleTypes(ObjectType, ObjectType),

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
                #[cfg(not(tarpaulin_include))]
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
    #[cfg(feature = "hwloc-2_3_0")]
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
    pub fn ancestors(&self) -> impl FusedIterator<Item = &Self> + Clone {
        Ancestors(self)
    }

    /// Search for an ancestor at a certain depth
    ///
    /// `depth` can be a [`Depth`], a [`NormalDepth`] or an [`usize`].
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
    pub fn first_common_ancestor(&self, other: &Self) -> Option<&Self> {
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

        // Make sure there is no common ancestor at some virtual depth (can't
        // avoid O(N²) alg here as virtual depths cannot be compared and global
        // persistent indices may be redundant across different topologies)
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
    ///
    /// This operation will fail if and only if the object is the root of the
    /// topology.
    #[doc(alias = "hwloc_get_non_io_ancestor_obj")]
    pub fn first_non_io_ancestor(&self) -> Option<&Self> {
        self.ancestors().find(|obj| obj.cpuset().is_some())
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
    /// their children have identically shaped subtrees
    ///
    /// Memory, I/O and Misc children are ignored when evaluating this property,
    /// and it is false for all of these object types.
    ///
    /// If this is true of the root object, then the topology may be [exported
    /// as a synthetic string](Topology::export_synthetic()).
    #[doc(alias = "hwloc_obj::symmetric_subtree")]
    pub fn is_symmetric_subtree(&self) -> bool {
        self.0.symmetric_subtree != 0
    }

    /// Get the child covering at least the given cpuset `set`
    ///
    /// `set` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`.
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
    /// `set` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`.
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
    /// `set` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`.
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
        if self.0.infos.is_null() {
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
    #[cfg(feature = "hwloc-2_3_0")]
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

        let cpuset_str = self
            .cpuset()
            .map_or_else(String::new, |cpuset| format!(" with {cpuset}"));

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

#[allow(clippy::cognitive_complexity)]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        bitmap::OwnedSpecializedBitmap,
        strategies::{any_object, any_string, set_with_reference, test_object},
        tests::assert_panics,
    };
    use proptest::prelude::*;
    use similar_asserts::assert_eq;
    use std::{
        collections::{BTreeMap, HashMap, HashSet},
        ops::RangeInclusive,
    };

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

        fn compare_object_sets<'a>(
            result: impl Iterator<Item = &'a TopologyObject>,
            reference: impl Iterator<Item = &'a TopologyObject>,
        ) {
            assert_eq!(
                checked_object_set(result).keys().collect::<HashSet<_>>(),
                checked_object_set(reference).keys().collect::<HashSet<_>>()
            );
        }
        compare_object_sets(
            topology.pci_devices(),
            topology.objects_with_type(ObjectType::PCIDevice),
        );
        compare_object_sets(
            topology.os_devices(),
            topology.objects_with_type(ObjectType::OSDevice),
        );
        compare_object_sets(
            topology.bridges(),
            topology.objects_with_type(ObjectType::Bridge),
        );
    }

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

    /// Stuff that should be true of any object we examine
    fn check_any_object(obj: &TopologyObject) -> Result<(), TestCaseError> {
        check_sets(obj)?;
        check_parent(obj)?;
        check_first_shared_cache(obj)?;
        check_cousins_and_siblings(obj)?;
        check_children(obj)?;
        check_infos(obj)?;
        Ok(())
    }

    /// Check that an object's cpusets and nodesets have the expected properties
    fn check_sets(obj: &TopologyObject) -> Result<(), TestCaseError> {
        let has_sets = obj.object_type().has_sets();

        prop_assert_eq!(obj.cpuset().is_some(), has_sets);
        prop_assert_eq!(obj.complete_cpuset().is_some(), has_sets);
        if let (Some(complete), Some(normal)) = (obj.complete_cpuset(), obj.cpuset()) {
            prop_assert!(complete.includes(normal));
            prop_assert!(obj.is_inside_cpuset(complete));
            prop_assert!(obj.covers_cpuset(normal));
        }

        prop_assert_eq!(obj.nodeset().is_some(), has_sets);
        prop_assert_eq!(obj.complete_nodeset().is_some(), has_sets);
        if let (Some(complete), Some(normal)) = (obj.complete_nodeset(), obj.nodeset()) {
            prop_assert!(complete.includes(normal));
        }

        Ok(())
    }

    /// Check that an object's parent has the expected properties
    fn check_parent(obj: &TopologyObject) -> Result<(), TestCaseError> {
        let Some(parent) = obj.parent() else {
            prop_assert_eq!(obj.object_type(), ObjectType::Machine);
            return Ok(());
        };

        let first_ancestor = obj.ancestors().next().unwrap();
        prop_assert!(ptr::eq(parent, first_ancestor));

        if let (Depth::Normal(parent_depth), Depth::Normal(obj_depth)) =
            (parent.depth(), obj.depth())
        {
            prop_assert!(parent_depth < obj_depth);
        }

        if obj.object_type().has_sets() {
            prop_assert!(parent.object_type().has_sets());
            prop_assert!(parent.cpuset().unwrap().includes(obj.cpuset().unwrap()));
            prop_assert!(parent.nodeset().unwrap().includes(obj.nodeset().unwrap()));
            prop_assert!(parent
                .complete_cpuset()
                .unwrap()
                .includes(obj.complete_cpuset().unwrap()));
            prop_assert!(parent
                .complete_nodeset()
                .unwrap()
                .includes(obj.complete_nodeset().unwrap()));
        }

        Ok(())
    }

    /// Check that [`TopologyObject::first_shared_cache()`] works as expected
    fn check_first_shared_cache(obj: &TopologyObject) -> Result<(), TestCaseError> {
        // Call the function to begin with
        let result = obj.first_shared_cache();

        // Should not yield result on objects without cpusets
        if obj.cpuset().is_none() {
            prop_assert!(result.is_none());
            return Ok(());
        }

        // Otherwise, should yield first cache parent that has multiple normal
        // children below it
        let expected = obj
            .ancestors()
            .skip_while(|ancestor| ancestor.normal_arity() == 1)
            .find(|ancestor| ancestor.object_type().is_cpu_data_cache());
        if let (Some(result), Some(expected)) = (result, expected) {
            prop_assert!(ptr::eq(result, expected));
        } else {
            prop_assert!(result.is_none() && expected.is_none());
        }
        Ok(())
    }

    /// Check that an object's cousin and siblings have the expected properties
    fn check_cousins_and_siblings(obj: &TopologyObject) -> Result<(), TestCaseError> {
        let siblings_len = if let Some(parent) = obj.parent() {
            let ty = obj.object_type();
            if ty.is_normal() {
                parent.normal_arity()
            } else if ty.is_memory() {
                parent.memory_arity()
            } else if ty.is_io() {
                parent.io_arity()
            } else {
                prop_assert_eq!(ty, ObjectType::Misc);
                parent.misc_arity()
            }
        } else {
            1
        };
        let topology = Topology::test_instance();
        let cousins_len = topology.num_objects_at_depth(obj.depth());

        if let Some(prev_cousin) = obj.prev_cousin() {
            check_cousin(obj, prev_cousin)?;
            prop_assert_eq!(prev_cousin.logical_index(), obj.logical_index() - 1);
            prop_assert!(ptr::eq(prev_cousin.next_cousin().unwrap(), obj));
        } else {
            prop_assert_eq!(obj.logical_index(), 0);
        }
        if let Some(next_cousin) = obj.next_cousin() {
            check_cousin(obj, next_cousin)?;
            prop_assert_eq!(next_cousin.logical_index(), obj.logical_index() + 1);
            prop_assert!(ptr::eq(next_cousin.prev_cousin().unwrap(), obj));
        } else {
            prop_assert_eq!(obj.logical_index(), cousins_len - 1);
        }

        if let Some(prev_sibling) = obj.prev_sibling() {
            check_sibling(obj, prev_sibling)?;
            prop_assert_eq!(prev_sibling.sibling_rank(), obj.sibling_rank() - 1);
            prop_assert!(ptr::eq(prev_sibling.next_sibling().unwrap(), obj));
        } else {
            prop_assert_eq!(obj.sibling_rank(), 0);
        }
        if let Some(next_sibling) = obj.next_sibling() {
            check_sibling(obj, next_sibling)?;
            prop_assert_eq!(next_sibling.sibling_rank(), obj.sibling_rank() + 1);
            prop_assert!(ptr::eq(next_sibling.prev_sibling().unwrap(), obj));
        } else {
            prop_assert_eq!(obj.sibling_rank(), siblings_len - 1);
        }

        Ok(())
    }

    /// Check that an object's cousin has the expected properties
    fn check_cousin(obj: &TopologyObject, cousin: &TopologyObject) -> Result<(), TestCaseError> {
        prop_assert_eq!(cousin.object_type(), obj.object_type());
        prop_assert_eq!(cousin.depth(), obj.depth());
        if obj.object_type().has_sets() {
            prop_assert!(!obj.cpuset().unwrap().intersects(cousin.cpuset().unwrap()));
            prop_assert!(!obj
                .complete_cpuset()
                .unwrap()
                .intersects(cousin.complete_cpuset().unwrap()));
        }
        Ok(())
    }

    /// Check that an object's sibling has the expected properties
    ///
    /// This does not re-check the properties checked by `check_cousin()`, since
    /// the sibling of some object must be the cousin of another object.
    fn check_sibling(obj: &TopologyObject, sibling: &TopologyObject) -> Result<(), TestCaseError> {
        prop_assert_eq!(sibling.0.parent, obj.0.parent);
        Ok(())
    }

    /// Check that an object's children has the expected properties
    fn check_children(obj: &TopologyObject) -> Result<(), TestCaseError> {
        prop_assert_eq!(obj.normal_arity(), obj.normal_children().count());
        prop_assert_eq!(obj.memory_arity(), obj.memory_children().count());
        prop_assert_eq!(obj.io_arity(), obj.io_children().count());
        prop_assert_eq!(obj.misc_arity(), obj.misc_children().count());
        prop_assert_eq!(
            obj.all_children().count(),
            obj.normal_arity() + obj.memory_arity() + obj.io_arity() + obj.misc_arity()
        );

        // NOTE: Most parent-child relations are checked when checking the
        //       parent, since that's agnostic to the kind of child we deal with
        for (idx, normal_child) in obj.normal_children().enumerate() {
            prop_assert_eq!(normal_child.sibling_rank(), idx);
            prop_assert!(normal_child.object_type().is_normal());
        }
        for (idx, memory_child) in obj.memory_children().enumerate() {
            prop_assert_eq!(memory_child.sibling_rank(), idx);
            prop_assert!(memory_child.object_type().is_memory());
        }
        for (idx, io_child) in obj.io_children().enumerate() {
            prop_assert_eq!(io_child.sibling_rank(), idx);
            prop_assert!(io_child.object_type().is_io());
        }
        for (idx, misc_child) in obj.misc_children().enumerate() {
            prop_assert_eq!(misc_child.sibling_rank(), idx);
            prop_assert_eq!(misc_child.object_type(), ObjectType::Misc);
        }

        Ok(())
    }

    /// Check that an object's info metadata matches expectations
    fn check_infos(obj: &TopologyObject) -> Result<(), TestCaseError> {
        for info in obj.infos() {
            if let Ok(name) = info.name().to_str() {
                prop_assert_eq!(
                    obj.info(name),
                    obj.infos()
                        .iter()
                        .find(|other_info| other_info.name() == info.name())
                        .map(TextualInfo::value)
                );
            }
        }
        // NOTE: Looking up invalid info names is tested elsewhere
        Ok(())
    }

    /// [`check_any_object()`] on any object reachable from the main object list
    #[test]
    fn check_objects() -> Result<(), TestCaseError> {
        let topology = Topology::test_instance();
        for obj in topology.objects() {
            check_any_object(obj)?;
        }
        Ok(())
    }

    /// Check the root object
    ///
    /// It's the top of the topology, so we know a lot about it.
    #[test]
    fn root_object() -> Result<(), TestCaseError> {
        let topology = Topology::test_instance();

        let root = topology.root_object();

        check_any_object(root)?;

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
        Ok(())
    }

    /// Check the PU objects
    ///
    /// They're the leaves of the normal topology, so we know a lot about them.
    #[test]
    fn processing_units() -> Result<(), TestCaseError> {
        let topology = Topology::test_instance();

        assert_eq!(
            topology.objects_with_type(ObjectType::PU).count(),
            topology.cpuset().weight().unwrap()
        );

        for (idx, pu) in topology.objects_with_type(ObjectType::PU).enumerate() {
            check_any_object(pu)?;

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
        Ok(())
    }

    /// Check the NUMA node objects
    ///
    /// They're the leaves of the memory hierarchy, so we know a lot about them
    #[test]
    fn numa_nodes() -> Result<(), TestCaseError> {
        let topology = Topology::test_instance();

        assert_eq!(
            topology.objects_with_type(ObjectType::NUMANode).count(),
            topology.nodeset().weight().unwrap()
        );

        for (idx, numa) in topology.objects_with_type(ObjectType::NUMANode).enumerate() {
            check_any_object(numa)?;

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
        Ok(())
    }

    /// Check that [`TopologyObject::is_symmetric_subtree()`] is correct
    #[test]
    fn is_symmetric_subtree() {
        // Iterate over topology objects from children to parent: by the time we
        // reach a parent, we know that we can trust the is_symmetric_subtree of
        // its direct (and transitive) normal children.
        let topology = Topology::test_instance();
        for depth in NormalDepth::iter_range(NormalDepth::MIN, topology.depth()).rev() {
            'objs: for obj in topology.objects_at_depth(depth) {
                // An object is a symmetric subtree if it has no children...
                let Some(first_child) = obj.normal_children().next() else {
                    assert!(obj.is_symmetric_subtree());
                    continue 'objs;
                };

                // ...or if its children all have the following properties:
                let should_be_symmetric = obj.normal_children().all(|child| {
                    // - They are symmetric subtree themselves
                    child.is_symmetric_subtree()

                    // - All of their topologically meaningful properties are
                    //   identical (and thus equal to that of first child)
                    && child.object_type() == first_child.object_type()
                    && child.subtype() == first_child.subtype()
                    && child.attributes() == first_child.attributes()
                    && child.depth() == first_child.depth()
                    && child.normal_arity() == first_child.normal_arity()
                });
                assert_eq!(obj.is_symmetric_subtree(), should_be_symmetric);
            }
        }

        // Only normal objects can be symmetric
        assert!(topology
            .virtual_objects()
            .all(|obj| !obj.is_symmetric_subtree()));
    }

    /// Check that [`TopologyObject::total_memory()`] is correct
    #[test]
    fn total_memory() {
        // We'll compute the expected total amount of memory below each NUMA
        // node through a bottom-up tree reduction from NUMA nodes up
        let topology = Topology::test_instance();
        let mut expected_total_memory = HashMap::new();
        let mut curr_objects = HashMap::new();
        let mut next_objects = HashMap::new();

        // Seed tree reduction by counting local memory inside of each NUMA node
        for numa in topology.objects_with_type(ObjectType::NUMANode) {
            let Some(ObjectAttributes::NUMANode(attrs)) = numa.attributes() else {
                unreachable!()
            };
            let gp_index = numa.global_persistent_index();
            let local_memory = attrs.local_memory().map_or(0, u64::from);
            assert!(expected_total_memory
                .insert(gp_index, local_memory)
                .is_none());
            assert!(curr_objects.insert(gp_index, numa).is_none());
        }

        // Compute expected total_memory value through tree reduction
        while !curr_objects.is_empty() {
            for (gp_index, obj) in curr_objects.drain() {
                let obj_memory = expected_total_memory[&gp_index];
                if let Some(parent) = obj.parent() {
                    let parent_gp_index = parent.global_persistent_index();
                    *expected_total_memory.entry(parent_gp_index).or_default() += obj_memory;
                    next_objects.insert(parent_gp_index, parent);
                }
            }
            std::mem::swap(&mut curr_objects, &mut next_objects);
        }

        // At this point we should have built an accurate map of how much memory
        // lies in NUMA nodes below each object, use it to check every object.
        for obj in topology.objects() {
            assert_eq!(
                obj.total_memory(),
                expected_total_memory
                    .remove(&obj.global_persistent_index())
                    .unwrap_or(0)
            );
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

    // Tests that should only be run on a subset of objects because the property
    // of interest can only be evaluated by traversing the whole topology or a
    // major subset thereof.
    proptest! {
        /// Test that [`Topology::objects_closest_to()`] works as expected
        #[test]
        fn objects_closest_to(obj in any_object()) {
            // Invoke the query
            let topology = Topology::test_instance();
            let result = topology.objects_closest_to(obj);

            // Calling it on a foreign object is an error
            if !topology.contains(obj) {
                return Ok(prop_assert!(matches!(
                    result,
                    Err(ClosestObjectsError::ForeignObject(e))
                        if e == ForeignObjectError::from(obj)
                )));
            }

            // Calling it on an object without a cpuset is also an error
            if obj.cpuset().is_none() {
                return Ok(prop_assert!(matches!(
                    result,
                    Err(ClosestObjectsError::MissingCpuSet(e))
                        if e == MissingObjCpuSetError::from(obj)
                )));
            }

            // Build a full list of this object's cousins, sorted by common
            // ancestor distance and keyed by global persistent index
            let cousin_iter = |next: fn(&TopologyObject) -> Option<&TopologyObject>| {
                std::iter::successors(next(obj), move |cousin| next(cousin))
            };
            let all_cousins =
                cousin_iter(TopologyObject::prev_cousin)
                    .chain(cousin_iter(TopologyObject::next_cousin));
            let mut cousins_by_distance = BTreeMap::<usize, HashMap<u64, &TopologyObject>>::new();
            for cousin in all_cousins {
                let common_ancestor = obj.first_common_ancestor(cousin).unwrap();
                let ancestor_distance = obj
                    .ancestors()
                    .position(|ancestor| ptr::eq(ancestor, common_ancestor))
                    .unwrap();
                let already_seen = cousins_by_distance.entry(ancestor_distance).or_default().insert(cousin.global_persistent_index(), cousin);
                prop_assert!(already_seen.is_none());
            }
            let max_distance = cousins_by_distance.last_entry().map_or(0, |entry| *entry.key());

            // Check if iterator matches this expectation
            let mut iterator = result.unwrap();
            'distance: for (distance, mut cousin_set) in cousins_by_distance {
                // Continue iteration over neighbors, continue outer loop when
                // all cousins at this distance have been exhausted
                for neighbor in iterator.by_ref() {
                    // Check that the proposed neighbor is a cousin at the
                    // expected distance: closest cousins should come first
                    prop_assert!(
                        cousin_set.remove(&neighbor.global_persistent_index()).is_some()
                    );

                    // We reached the last cousin at this distance, move to the
                    // next cousin distance.
                    if cousin_set.is_empty() {
                        continue 'distance;
                    }
                }

                // Iteration can only end when all cousins have been seen
                prop_assert_eq!(distance, max_distance);
                prop_assert!(cousin_set.is_empty());
            }
            // Iteration should end once all cousins have been seen
            prop_assert!(iterator.next().is_none());
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
        level: NonZeroUsize,
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
            .map(|kind| usize::from(kind.level))
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
                    let level_ok = usize::from(kind.level) == cache_level;
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
    fn any_hwloc_depth() -> impl Strategy<Value = Depth> {
        let valid_depths = valid_depths().collect::<Vec<_>>();
        prop_oneof![
            4 => prop::sample::select(valid_depths),
            1 => any::<Depth>()
        ]
    }

    /// Like `any_depth()` but restricted to normal depths
    fn any_normal_depth() -> impl Strategy<Value = NormalDepth> {
        let topology = Topology::test_instance();
        let normal_depths =
            NormalDepth::iter_range(NormalDepth::MIN, topology.depth()).collect::<Vec<_>>();
        prop_oneof![
            4 => prop::sample::select(normal_depths),
            1 => any::<NormalDepth>()
        ]
    }

    /// Like `any_depth()` but covers full `usize` range
    fn any_usize_depth() -> impl Strategy<Value = usize> {
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
            check_any_object(obj)?;
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

    /// Test [`TopologyObject::ancestor_at_depth()`] for a certain
    /// [`TopologyObject`] and at a certain desired parent depth
    fn check_ancestor_at_depth<DepthLike>(
        obj: &TopologyObject,
        depth: DepthLike,
    ) -> Result<(), TestCaseError>
    where
        DepthLike: TryInto<Depth> + Copy + Debug + Eq,
        Depth: PartialEq<DepthLike>,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        let actual = obj.ancestor_at_depth(depth);
        let expected = obj.ancestors().find(|obj| obj.depth() == depth);
        if let (Some(actual), Some(expected)) = (actual, expected) {
            prop_assert!(ptr::eq(actual, expected));
        } else {
            prop_assert!(actual.is_none() && expected.is_none());
        }
        Ok(())
    }

    proptest! {
        // Probe ancestors by depth at valid and invalid depths
        #[test]
        fn ancestor_at_hwloc_depth(obj in test_object(),
                                   depth in any_hwloc_depth()) {
            check_ancestor_at_depth(obj, depth)?;
        }
        //
        #[test]
        fn ancestor_at_normal_depth(obj in test_object(),
                                    depth in any_normal_depth()) {
            check_ancestor_at_depth(obj, depth)?;
        }
        //
        #[test]
        fn ancestor_at_usize_depth(obj in test_object(),
                                   depth in any_usize_depth()) {
            check_ancestor_at_depth(obj, depth)?;
        }
    }

    // --- Querying stuff by OS index ---

    /// Build an OS index -> [`TopologyObject`] mapping for some [`ObjectType`]
    ///
    /// Only call this for object types which are guaranteed to have a unique OS
    /// index, namely PUs and NUMA nodes.
    fn os_index_to_object(ty: ObjectType) -> HashMap<usize, &'static TopologyObject> {
        let topology = Topology::test_instance();
        let mut map = HashMap::new();
        for pu in topology.objects_with_type(ty) {
            assert!(map.insert(pu.os_index().unwrap(), pu).is_none());
        }
        map
    }

    /// Check one of the `Topology::xyz_with_os_index` functions
    fn check_object_with_os_index(
        method: impl FnOnce(&Topology, usize) -> Option<&TopologyObject>,
        os_index: usize,
        expected: &HashMap<usize, &TopologyObject>,
    ) {
        let topology = Topology::test_instance();
        match (method(topology, os_index), expected.get(&os_index)) {
            (Some(obj1), Some(obj2)) if ptr::eq(obj1, *obj2) => {}
            (None, None) => {}
            other => panic!("unequected pu_with_os_index result vs expectation: {other:?}"),
        }
    }

    /// OS index -> PU mapping
    fn os_index_to_pu() -> &'static HashMap<usize, &'static TopologyObject> {
        static MAP: OnceLock<HashMap<usize, &'static TopologyObject>> = OnceLock::new();
        MAP.get_or_init(|| os_index_to_object(ObjectType::PU))
    }

    /// Test [`Topology::pu_with_os_index()`]
    fn check_pu_with_os_index(os_index: usize) {
        check_object_with_os_index(Topology::pu_with_os_index, os_index, os_index_to_pu());
    }

    /// Exhaustive check for all valid PU OS indices
    #[test]
    fn valid_pu_with_os_index() {
        for os_index in os_index_to_pu().keys() {
            check_pu_with_os_index(*os_index);
        }
    }

    proptest! {
        /// Stochastic test for possibly-nonexistent PU OS indices
        fn any_pu_with_os_index(os_index: usize) {
            check_pu_with_os_index(os_index)
        }
    }

    /// OS index -> NUMA node mapping
    fn os_index_to_node() -> &'static HashMap<usize, &'static TopologyObject> {
        static MAP: OnceLock<HashMap<usize, &'static TopologyObject>> = OnceLock::new();
        MAP.get_or_init(|| os_index_to_object(ObjectType::NUMANode))
    }

    /// Test [`Topology::pu_with_os_index()`]
    fn check_node_with_os_index(os_index: usize) {
        check_object_with_os_index(Topology::node_with_os_index, os_index, os_index_to_node());
    }

    /// Exhaustive check for all valid NUMA node OS indices
    #[test]
    fn valid_node_with_os_index() {
        for os_index in os_index_to_node().keys() {
            check_node_with_os_index(*os_index);
        }
    }

    proptest! {
        /// Stochastic test for possibly-nonexistent NUMA node OS indices
        fn any_node_with_os_index(os_index: usize) {
            check_node_with_os_index(os_index)
        }
    }

    // --- Querying stuff by cpuset/nodeset ---

    /// Shorthand for using topology-wide sets as a reference
    fn set_with_topology_reference<Set: OwnedSpecializedBitmap>(
        set: impl FnOnce(&Topology) -> BitmapRef<'_, Set>,
    ) -> impl Strategy<Value = Set> {
        set_with_reference(set(Topology::test_instance()).as_ref())
    }

    proptest! {
        /// Test [`Topology::pus_from_cpuset()`]
        #[test]
        fn pus_from_cpuset(cpuset in set_with_topology_reference(Topology::cpuset)) {
            let mut expected = os_index_to_pu().clone();
            expected.retain(|_idx, pu| {
                cpuset.includes(pu.cpuset().unwrap())
            });

            let topology = Topology::test_instance();
            let actual = topology.pus_from_cpuset(&cpuset);

            prop_assert_eq!(actual.clone().count(), expected.len());
            for pu in actual {
                prop_assert!(expected.contains_key(&pu.os_index().unwrap()));
            }
        }

        /// Test [`Topology::nodes_from_nodeset()`]
        #[test]
        fn nodes_from_nodeset(nodeset in set_with_topology_reference(Topology::nodeset)) {
            let mut expected = os_index_to_node().clone();
            expected.retain(|_idx, node| {
                nodeset.includes(node.nodeset().unwrap())
            });

            let topology = Topology::test_instance();
            let actual = topology.nodes_from_nodeset(&nodeset);

            prop_assert_eq!(actual.clone().count(), expected.len());
            for node in actual {
                prop_assert!(expected.contains_key(&node.os_index().unwrap()));
            }
        }
    }

    /// Pick an object and a related cpuset
    fn object_and_related_cpuset() -> impl Strategy<Value = (&'static TopologyObject, CpuSet)> {
        // Separate objects with and without cpusets
        let topology = Topology::test_instance();
        let mut with_cpuset = Vec::new();
        let mut without_cpuset = Vec::new();
        for obj in topology.objects() {
            if obj.object_type().has_sets() {
                with_cpuset.push(obj);
            } else {
                without_cpuset.push(obj);
            }
        }

        // For objects with cpusets, the reference cpuset is their cpuset
        fn with_reference(
            objects: Vec<&'static TopologyObject>,
            ref_cpuset: impl Fn(&TopologyObject) -> BitmapRef<'_, CpuSet>,
        ) -> Option<impl Strategy<Value = (&'static TopologyObject, CpuSet)>> {
            (!objects.is_empty()).then(move || {
                prop::sample::select(objects)
                    .prop_flat_map(move |obj| (Just(obj), set_with_reference(&ref_cpuset(obj))))
            })
        }
        let with_cpuset = with_reference(with_cpuset, |obj| obj.cpuset().unwrap());

        // For objects without cpusets, the reference is the topology cpuset
        let without_cpuset = with_reference(without_cpuset, |_obj| topology.cpuset());

        // We pick from either list with equal probability
        match (with_cpuset, without_cpuset) {
            (Some(with), Some(without)) => prop_oneof![with, without].boxed(),
            (Some(with), None) => with.boxed(),
            (None, Some(without)) => without.boxed(),
            (None, None) => unreachable!(),
        }
    }

    proptest! {
        /// Test [`TopologyObject::normal_child_covering_cpuset()`]
        #[test]
        fn normal_child_covering_cpuset((obj, set) in object_and_related_cpuset()) {
            if let Some(result) = obj.normal_child_covering_cpuset(&set) {
                prop_assert!(result.covers_cpuset(&set));
            } else {
                prop_assert!(obj.normal_children().all(|obj| !obj.covers_cpuset(&set)));
            }
        }

        /// Test [`TopologyObject::is_inside_cpuset()`]
        #[test]
        fn is_inside_cpuset((obj, set) in object_and_related_cpuset()) {
            let result = obj.is_inside_cpuset(&set);
            let Some(obj_set) = obj.cpuset() else {
                prop_assert!(!result);
                return Ok(());
            };
            if obj_set.is_empty() {
                prop_assert!(!result);
                return Ok(());
            }
            prop_assert_eq!(result, set.includes(obj_set));
        }

        /// Test [`TopologyObject::covers_cpuset()`]
        #[test]
        fn covers_cpuset((obj, set) in object_and_related_cpuset()) {
            let result = obj.covers_cpuset(&set);
            let Some(obj_set) = obj.cpuset() else {
                prop_assert!(!result);
                return Ok(());
            };
            if set.is_empty() {
                prop_assert!(!result);
                return Ok(());
            }
            prop_assert_eq!(result, obj_set.includes(&set));
        }
    }

    // --- Querying objects by type-index path ---

    /// Generate an object that has a cpuset
    fn object_with_cpuset() -> impl Strategy<Value = &'static TopologyObject> + Clone {
        let objects_with_cpusets = Topology::test_objects()
            .iter()
            .copied()
            .filter(|obj| obj.cpuset().is_some())
            .collect::<Vec<_>>();
        prop::sample::select(objects_with_cpusets)
    }

    /// Generate type-index paths that are mostly valid, but will occasionally
    /// be disordered or invalid, tell what the expected result is if the path
    /// is valid and None otherwise
    fn type_index_path(
    ) -> impl Strategy<Value = (Vec<(ObjectType, usize)>, Option<&'static TopologyObject>)> {
        // First, have a strategy for generating correct paths
        let topology = Topology::test_instance();
        let valid_path = object_with_cpuset()
            .prop_filter("Machine can't be found using by type_index_path", |obj| {
                obj.object_type() != ObjectType::Machine
            })
            .prop_flat_map(move |obj| {
                // Start by generating a valid object ancestor path, excluding the
                // topology's root object
                let mut full_ancestor_path = obj.ancestors().collect::<Vec<_>>();
                full_ancestor_path.pop();
                full_ancestor_path.reverse();
                let num_ancestors = full_ancestor_path.len();

                // Extract a subsequence of it
                prop::sample::subsequence(full_ancestor_path, 0..=num_ancestors).prop_map(
                    move |mut obj_path| {
                        // Append the object at the end to make it a full path
                        obj_path.push(obj);

                        // Convert the path to type -> index form
                        let mut last_parent = topology.root_object();
                        let type_index_path = obj_path
                            .into_iter()
                            .map(|obj| {
                                let ty = obj.object_type();
                                let index = topology
                                    .objects_inside_cpuset_with_type(
                                        last_parent.cpuset().unwrap(),
                                        ty,
                                    )
                                    .position(|candidate| ptr::eq(candidate, obj))
                                    .unwrap();
                                last_parent = obj;
                                (ty, index)
                            })
                            .collect::<Vec<_>>();
                        (type_index_path, Some(obj))
                    },
                )
            });

        // Order matters, so a path in the wrong order is not a valid path
        let disordered_path = valid_path.clone().prop_flat_map(|(path, obj)| {
            let ordered_path = path.clone();
            Just(path).prop_shuffle().prop_map(move |shuffled_path| {
                let disordered = shuffled_path != ordered_path;
                (shuffled_path, (!disordered).then(|| obj.unwrap()))
            })
        });

        // Random paths are most likely wrong, but could be right sometimes
        let random_path = any::<Vec<(ObjectType, usize)>>().prop_map(move |path| {
            // The root must not appear in the path
            if path.first().map(|(ty, _)| ty) == Some(&ObjectType::Machine) {
                return (path, None);
            }

            // Otherwise, we can search
            let mut last_parent = topology.root_object();
            for &(ty, idx) in &path {
                let is_child = |obj: &&TopologyObject| {
                    obj.ancestors()
                        .any(|ancestor| ptr::eq(ancestor, last_parent))
                };
                if let Some(obj) = topology
                    .objects_inside_cpuset_with_type(last_parent.cpuset().unwrap(), ty)
                    .nth(idx)
                    .filter(is_child)
                {
                    last_parent = obj;
                } else {
                    return (path, None);
                }
            }
            (path, Some(last_parent))
        });

        // Put it all together, biased towards the valid case
        prop_oneof![
            3 => valid_path,
            1 => disordered_path,
            1 => random_path,
        ]
    }

    proptest! {
        /// Test for [`Topology::object_by_type_index_path()`]
        #[test]
        fn object_by_type_index_path((path, obj) in type_index_path()) {
            // Perform the query
            let topology = Topology::test_instance();
            let result = topology.object_by_type_index_path(&path);

            // Check error handling for lack of cpuset
            for (ty, _) in path {
                if !ty.has_sets() {
                    prop_assert!(obj.is_none());
                    prop_assert!(matches!(
                        &result,
                        Err(e) if *e == ParameterError::from(ty)
                    ));
                    return Ok(());
                }
            }

            // Check normal search path
            match (result.unwrap(), obj) {
                (Some(actual), Some(expected)) => prop_assert!(ptr::eq(actual, expected)),
                (None, None) => {}
                other => prop_assert!(false, "result/expectation mismatch: {other:?}"),
            }
        }
    }

    // --- Finding more objects with the same locality ---

    #[cfg(feature = "hwloc-2_5_0")]
    mod object_with_same_locality {
        use super::*;
        use crate::strategies::any_string;

        /// Lists of subtypes and names in the test topology
        fn subtypes_and_name_prefixes() -> (HashSet<&'static str>, HashSet<String>) {
            fn object_strings(
                mut get_string: impl FnMut(&TopologyObject) -> Option<&CStr>,
            ) -> HashSet<&'static str> {
                Topology::test_objects()
                    .iter()
                    .filter_map(|obj| get_string(obj))
                    .flat_map(CStr::to_str)
                    .collect()
            }
            let subtypes = object_strings(TopologyObject::subtype);
            let names = object_strings(TopologyObject::name);
            let name_prefixes = names
                .into_iter()
                .flat_map(|name| {
                    (1..=name.chars().count())
                        .map(|num_chars| name.chars().take(num_chars).collect::<String>())
                })
                .chain(std::iter::once(String::new()))
                .collect();
            (subtypes, name_prefixes)
        }

        /// Generate a subtype and name prefix input for
        /// [`Topology::object_with_same_locality()`]
        fn subtype_and_name_prefix() -> impl Strategy<Value = (Option<String>, Option<String>)> {
            let (subtypes, name_prefixes) = subtypes_and_name_prefixes();
            let subtypes = subtypes.into_iter().collect::<Vec<&'static str>>();
            let name_prefixes = name_prefixes.into_iter().collect::<Vec<String>>();
            let random_string = prop_oneof![any_string().prop_map(Some), Just(None),];
            let subtype = if subtypes.is_empty() {
                random_string.clone().boxed()
            } else {
                prop_oneof![
                    3 => prop::sample::select(subtypes).prop_map(|s| Some(s.to_owned())),
                    2 => random_string.clone(),
                ]
                .boxed()
            };
            let name_prefix = if name_prefixes.is_empty() {
                random_string.boxed()
            } else {
                prop_oneof![
                    3 => prop::sample::select(name_prefixes).prop_map(Some),
                    2 => random_string,
                ]
                .boxed()
            };
            (subtype, name_prefix)
        }

        proptest! {
            /// Test for [`Topology::object_with_same_locality()`]
            #[test]
            fn object_with_same_locality(
                src in any_object(),
                ty: ObjectType,
                (subtype, name_prefix) in subtype_and_name_prefix(),
            ) {
                // Start by running the method
                let topology = Topology::test_instance();
                let subtype = subtype.as_deref();
                let name_prefix = name_prefix.as_deref();
                let result = topology.object_with_same_locality(
                    src,
                    ty,
                    subtype,
                    name_prefix,
                );

                // Handle error cases
                if handle_error_cases(src, ty, subtype, name_prefix, &result)? {
                    return Ok(());
                }

                // These are the only two error conditions, otherwise the search
                // can fail but will always return an Option.
                match result.unwrap() {
                    Some(dst) => {
                        // Successful search should match all criteria
                        prop_assert!(topology.contains(dst));
                        prop_assert_eq!(dst.object_type(), ty);
                        if let Some(expected_subtype) = subtype {
                            prop_assert_eq!(dst.subtype().unwrap().to_str().unwrap(), expected_subtype);
                        }
                        if let Some(expected_prefix) = name_prefix {
                            prop_assert!(dst.name().unwrap().to_str().unwrap().starts_with(expected_prefix));
                        }
                        if ty.has_sets() {
                            prop_assert_eq!(dst.cpuset(), src.cpuset());
                            prop_assert_eq!(dst.nodeset(), src.nodeset());
                        } else if is_supported_io_type(ty) {
                            prop_assert!(is_io_local(src, dst)?);
                        }
                    }
                    None => {
                        // Search can fail only if no object in the topology
                        // would match all search criteria
                        'search: for obj in Topology::test_objects() {
                            if obj.object_type() != ty {
                                continue 'search;
                            }
                            if let Some(req_subtype) = subtype {
                                if let Some(obj_subtype) = obj.subtype().and_then(|cs| cs.to_str().ok()) {
                                    if req_subtype != obj_subtype {
                                        continue 'search;
                                    }
                                } else {
                                    continue 'search;
                                }
                            }
                            if let Some(name_prefix) = name_prefix {
                                if let Some(name) = obj.name().and_then(|cs| cs.to_str().ok()) {
                                    if !name.starts_with(name_prefix) {
                                        continue 'search;
                                    }
                                } else {
                                    continue 'search;
                                }
                            }
                            if ty.has_sets() {
                                prop_assert!((obj.cpuset() != src.cpuset()) || (obj.nodeset() != src.nodeset()));
                            } else if is_supported_io_type(ty) {
                                prop_assert!(!is_io_local(src, obj)?);
                            }
                        }
                    }
                }
            }
        }

        /// Handle error cases of [`Topology::object_with_same_locality()`],
        /// return truth that an error case was handled
        fn handle_error_cases(
            src: &TopologyObject,
            ty: ObjectType,
            subtype: Option<&str>,
            name_prefix: Option<&str>,
            result: &Result<Option<&TopologyObject>, LocalObjectError>,
        ) -> Result<bool, TestCaseError> {
            // Foreign objects should be reported as an error
            let topology = Topology::test_instance();
            if !topology.contains(src) {
                prop_assert!(matches!(result, Err(e) if e == &LocalObjectError::from(src)));
                return Ok(true);
            }

            // Converting between normal/memory object types and I/O types
            // or Misc is not allowed
            let src_ty = src.object_type();
            if src_ty.has_sets() ^ ty.has_sets() {
                prop_assert!(matches!(
                    result,
                    Err(LocalObjectError::IncompatibleTypes(src, dst)) if *src == src_ty && *dst == ty
                ));
                return Ok(true);
            }

            // NUL in input strings should be reported as an error
            for s in subtype.as_ref().into_iter().chain(name_prefix.as_ref()) {
                if s.chars().any(|c| c == '\0') {
                    prop_assert!(
                        matches!(result, Err(e) if e == &LocalObjectError::from(NulError))
                    );
                    return Ok(true);
                }
            }
            Ok(false)
        }

        /// Supported I/O object types for
        /// [`Topology::object_with_same_locality()`]
        fn is_supported_io_type(ty: ObjectType) -> bool {
            ty == ObjectType::PCIDevice || ty == ObjectType::OSDevice
        }

        /// Truth that `dst` is another I/O object below the same PCI bridge as
        /// `src`
        fn is_io_local(src: &TopologyObject, dst: &TopologyObject) -> Result<bool, TestCaseError> {
            // First, both src and dst must be OS or PCI devices
            if !(is_supported_io_type(src.object_type()) && is_supported_io_type(dst.object_type()))
            {
                return Ok(false);
            }

            // Find the first non-OS-device ancestor (normally a PCI device, but
            // may be something else if PCI device detection is disabled)
            let expected_parent = std::iter::once(src)
                .chain(src.ancestors())
                .find(|obj| obj.object_type() != ObjectType::OSDevice)
                .expect("OS devices should have a parent (at least Machine)");

            // dst may be either that PCI parent...
            if ptr::eq(dst, expected_parent) {
                return Ok(true);
            }

            // ...or an OS device below the same parent
            if ptr::eq(
                dst.parent().expect("OS devices should have a parent"),
                expected_parent,
            ) {
                prop_assert_eq!(dst.object_type(), ObjectType::OSDevice);
                return Ok(true);
            }
            Ok(false)
        }
    }

    // --- Find PCI devices by address ---

    /// PCI device address
    #[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
    struct PCIAddress {
        domain: PCIDomain,
        bus_id: u8,
        bus_device: u8,
        function: u8,
    }
    //
    impl PCIAddress {
        /// Turn this address into its standard string form
        ///
        /// You may only cut out the domain part by setting `with_domain` to
        /// false when `domain` is zero.
        fn stringify(self, with_domain: bool) -> String {
            if with_domain {
                format!(
                    "{:04x}:{:02x}:{:02x}.{:02x}",
                    self.domain, self.bus_id, self.bus_device, self.function
                )
            } else {
                assert_eq!(self.domain, 0);
                format!(
                    "{:02x}:{:02x}.{:02x}",
                    self.bus_id, self.bus_device, self.function
                )
            }
        }
    }
    //
    impl Arbitrary for PCIAddress {
        type Parameters = <(PCIDomain, [u8; 3]) as Arbitrary>::Parameters;
        type Strategy = prop::strategy::Map<
            <(PCIDomain, [u8; 3]) as Arbitrary>::Strategy,
            fn((PCIDomain, [u8; 3])) -> Self,
        >;

        fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
            <(PCIDomain, [u8; 3]) as Arbitrary>::arbitrary_with(args).prop_map(
                |(domain, [bus_id, bus_device, function])| Self {
                    domain,
                    bus_id,
                    bus_device,
                    function,
                },
            )
        }
    }

    /// List of PCI devices keyed by address
    fn pci_devices_by_address() -> &'static HashMap<PCIAddress, &'static TopologyObject> {
        static RESULT: OnceLock<HashMap<PCIAddress, &'static TopologyObject>> = OnceLock::new();
        RESULT.get_or_init(|| {
            let mut result = HashMap::new();
            for device in Topology::test_instance().pci_devices() {
                let Some(ObjectAttributes::PCIDevice(pci)) = device.attributes() else {
                    unreachable!("All PCI devices should have PCI attributes")
                };
                assert!(result
                    .insert(
                        PCIAddress {
                            domain: pci.domain(),
                            bus_id: pci.bus_id(),
                            bus_device: pci.bus_device(),
                            function: pci.function(),
                        },
                        device
                    )
                    .is_none());
            }
            result
        })
    }

    /// Generate a PCI device address that is usually valid, but may not be
    fn pci_address() -> impl Strategy<Value = PCIAddress> {
        let valid_pci_addresses = pci_devices_by_address().keys().copied().collect::<Vec<_>>();
        if valid_pci_addresses.is_empty() {
            any::<PCIAddress>().boxed()
        } else {
            prop_oneof![
                4 => prop::sample::select(valid_pci_addresses),
                1 => any::<PCIAddress>(),
            ]
            .boxed()
        }
    }

    proptest! {
        /// Test for [`Topology::pci_device_by_bus_id()`]
        #[allow(clippy::option_if_let_else)]
        #[test]
        fn pci_device_by_bus_id(addr in pci_address()) {
            let topology = Topology::test_instance();
            let result = topology.pci_device_by_bus_id(
                addr.domain,
                addr.bus_id,
                addr.bus_device,
                addr.function,
            );
            if let Some(expected) = pci_devices_by_address().get(&addr) {
                assert!(ptr::eq(
                    result.unwrap(),
                    *expected
                ));
            } else {
                assert!(result.is_none());
            }
        }
    }

    /// List of PCI devices keyed by stringified address
    fn pci_devices_by_address_string() -> &'static HashMap<String, &'static TopologyObject> {
        static RESULT: OnceLock<HashMap<String, &'static TopologyObject>> = OnceLock::new();
        RESULT.get_or_init(|| {
            let mut result = HashMap::new();
            for (address, device) in pci_devices_by_address() {
                assert!(result.insert(address.stringify(true), *device).is_none());
                if address.domain == 0 {
                    assert!(result.insert(address.stringify(false), *device).is_none());
                }
            }
            result
        })
    }

    /// Generate a string that may or may not be a PCI device address
    fn pci_address_string() -> impl Strategy<Value = String> {
        let valid_str_addresses = pci_devices_by_address_string()
            .keys()
            .cloned()
            .collect::<Vec<_>>();
        fn push_short_addr(out: &mut String, chars: &[char]) {
            assert_eq!(chars.len(), 6);
            for &c in &chars[0..2] {
                out.push(c);
            }
            out.push(':');
            for &c in &chars[2..4] {
                out.push(c);
            }
            out.push('.');
            for &c in &chars[4..6] {
                out.push(c);
            }
        }
        let random_string = prop_oneof![
            // Same skeleton as a full address, but unlikely to be an address
            any::<[char; 10]>().prop_map(|chars| {
                let mut out = String::with_capacity(13);
                for &c in &chars[..4] {
                    out.push(c);
                }
                out.push(':');
                push_short_addr(&mut out, &chars[4..]);
                out
            }),
            // Same skeleton as a short address, but unlikely to be an address
            any::<[char; 6]>().prop_map(|chars| {
                let mut out = String::with_capacity(8);
                push_short_addr(&mut out, &chars[..]);
                out
            }),
            // Random textual junk
            any_string(),
        ];
        if valid_str_addresses.is_empty() {
            random_string.boxed()
        } else {
            prop_oneof![
                // Actually a PCI address, with or without the domain part
                2 => prop::sample::select(valid_str_addresses),
                // Random string that may or may not look like a PCI address
                3 => random_string,
            ]
            .boxed()
        }
    }

    proptest! {
        /// Test for [`Topology::pci_device_by_bus_id_string()`]
        #[allow(clippy::option_if_let_else)]
        #[test]
        fn pci_device_by_bus_id_string(addr in pci_address_string()) {
            let topology = Topology::test_instance();
            let result = topology.pci_device_by_bus_id_string(&addr);

            // Handle success case
            if let Some(expected) = pci_devices_by_address_string().get(&addr) {
                prop_assert!(ptr::eq(
                    result.unwrap().unwrap(),
                    *expected
                ));
                return Ok(());
            }

            // Determine if string at least matches expected format
            let is_hex = |s: &str| s.chars().all(|c| c.is_ascii_hexdigit());
            let is_valid_full =
                addr.len() == 13
                && addr.is_char_boundary(4) && is_hex(&addr[..4])
                && addr.is_char_boundary(5) && &addr[4..5] == ":"
                && addr.is_char_boundary(7) && is_hex(&addr[5..7])
                && addr.is_char_boundary(8) && &addr[7..8] == ":"
                && addr.is_char_boundary(10) && is_hex(&addr[8..10])
                && addr.is_char_boundary(11) && &addr[10..11] == "."
                && is_hex(&addr[11..]);
            let is_valid_short =
                addr.len() == 8
                && addr.is_char_boundary(2) && is_hex(&addr[..2])
                && addr.is_char_boundary(3) && &addr[2..3] == ":"
                && addr.is_char_boundary(5) && is_hex(&addr[3..5])
                && addr.is_char_boundary(6) && &addr[5..6] == "."
                && is_hex(&addr[6..]);
            if is_valid_full || is_valid_short {
                prop_assert!(matches!(result, Ok(None)));
            } else {
                prop_assert!(matches!(result, Err(e) if e == ParameterError::from(addr)));
            }
        }
    }

    // --- Truth that an object is a bridge covering a certain PCI bus ---

    /// Generate queries that have a reasonable chance of returning `true`
    fn bridge_coverage() -> impl Strategy<Value = (&'static TopologyObject, PCIDomain, u8)> {
        #[derive(Clone, Debug)]
        struct BridgeCoverage {
            bridge: &'static TopologyObject,
            domain: PCIDomain,
            bus_id_range: RangeInclusive<u8>,
        }
        let topology = Topology::test_instance();
        let bridge_coverages = topology
            .objects_with_type(ObjectType::Bridge)
            .filter_map(|bridge| {
                let Some(ObjectAttributes::Bridge(attrs)) = bridge.attributes() else {
                    unreachable!()
                };
                let Some(DownstreamAttributes::PCI(pci)) = attrs.downstream_attributes() else {
                    return None;
                };
                Some(BridgeCoverage {
                    bridge,
                    domain: pci.domain(),
                    bus_id_range: pci.secondary_bus()..=pci.subordinate_bus(),
                })
            })
            .collect::<Vec<_>>();
        if bridge_coverages.is_empty() {
            (any_object(), any::<PCIDomain>(), any::<u8>()).boxed()
        } else {
            prop::sample::select(bridge_coverages)
                .prop_flat_map(|bridge_coverage| {
                    let obj = prop_oneof![
                        3 => Just(bridge_coverage.bridge),
                        2 => any_object()
                    ];
                    let domain = prop_oneof![
                        3 => Just(bridge_coverage.domain),
                        2 => any::<PCIDomain>()
                    ];
                    let bus_id = prop_oneof![
                        3 => bridge_coverage.bus_id_range,
                        2 => any::<u8>()
                    ];
                    (obj, domain, bus_id)
                })
                .boxed()
        }
    }

    proptest! {
        /// Test [`TopologyObject::is_bridge_covering_pci_bus()`]
        #[test]
        fn is_bridge_covering_pci_bus((obj, domain, bus_id) in bridge_coverage()) {
            let result = obj.is_bridge_covering_pci_bus(domain, bus_id);
            let Some(ObjectAttributes::Bridge(attrs)) = obj.attributes() else {
                prop_assert!(!result);
                return Ok(());
            };
            let Some(DownstreamAttributes::PCI(pci)) = attrs.downstream_attributes() else {
                prop_assert!(!result);
                return Ok(());
            };
            prop_assert_eq!(
                result,
                domain == pci.domain() && bus_id >= pci.secondary_bus() && bus_id <= pci.subordinate_bus()
            );
        }
    }

    // --- Properties of pairs of objects ---

    proptest! {
        /// Test for [`TopologyObject::first_common_ancestor()`]
        #[test]
        fn first_common_ancestor(obj in test_object(), other in any_object()) {
            // Check result
            let result = obj.first_common_ancestor(other);

            // The topology root has no ancestor
            if obj.object_type() == ObjectType::Machine || other.object_type() == ObjectType::Machine
            {
                prop_assert!(result.is_none());
                return Ok(());
            }

            // Objects from two different topologies have no common ancestor
            let topology = Topology::test_instance();
            if !topology.contains(other) {
                prop_assert!(result.is_none());
                return Ok(());
            }

            // Otherwise, there should be a common ancestor
            let common_ancestor = result.unwrap();

            // Check if it is indeed the first common ancestor
            fn prev_ancestor_candidate<'obj>(
                obj: &'obj TopologyObject,
                common_ancestor: &TopologyObject,
            ) -> Option<&'obj TopologyObject> {
                obj.ancestors().take_while(|&ancestor| !ptr::eq(ancestor, common_ancestor)).last()
            }
            let obj_ancestor = prev_ancestor_candidate(obj, common_ancestor);
            let other_ancestor = prev_ancestor_candidate(other, common_ancestor);
            if let (Some(obj_ancestor), Some(other_ancestor)) = (obj_ancestor, other_ancestor) {
                prop_assert!(!ptr::eq(obj_ancestor, other_ancestor));
            }
        }
    }
}
