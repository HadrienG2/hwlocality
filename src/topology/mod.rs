//! Hardware topology

pub mod builder;
pub mod editor;
pub mod support;

use self::{
    builder::{BuildFlags, RawTypeFilter, TopologyBuilder, TypeFilter},
    support::FeatureSupport,
};
use crate::{
    bitmaps::{Bitmap, RawBitmap, SpecializedBitmap},
    cpu::sets::CpuSet,
    errors::{self, NulError, RawHwlocError},
    ffi::{self, IncompleteType, LibcString},
    memory::nodesets::NodeSet,
    objects::{
        attributes::ObjectAttributes,
        depth::{Depth, DepthError, DepthResult, RawDepth},
        types::{CacheType, ObjectType, RawObjectType},
        TopologyObject,
    },
};
#[cfg(doc)]
use crate::{
    memory::{attributes::LocalNUMANodeFlags, binding::MemoryBindingError},
    topology::support::{CpuBindingSupport, DiscoverySupport, MemoryBindingSupport, MiscSupport},
};
use bitflags::bitflags;
use errno::Errno;
use libc::EINVAL;
use num_enum::TryFromPrimitiveError;
use std::{
    convert::TryInto,
    ffi::{c_char, c_ulong},
    iter::FusedIterator,
    num::NonZeroU32,
    ptr::{self, NonNull},
};

/// Opaque topology struct
///
/// Represents the private `hwloc_topology` type that `hwloc_topology_t` API
/// pointers map to.
#[repr(C)]
#[doc(alias = "hwloc_topology")]
#[doc(alias = "hwloc_topology_s")]
pub(crate) struct RawTopology(IncompleteType);

/// Main entry point to the hwloc API
///
/// A `Topology` contains everything hwloc knows about the hardware and software
/// structure of a system. It can be used to query the system topology and to
/// bind threads and processes to hardware CPU cores and NUMA nodes.
///
/// Since there are **many** things you can do with a `Topology`, the API is
/// broken down into sections roughly following the structure of the upstream
/// hwloc documentation:
///
/// - [Topology building](#topology-building)
/// - [Object levels, depths and types](#object-levels-depths-and-types)
/// - [CPU cache statistics](#cpu-cache-statistics) (specific to Rust bindings)
/// - [CPU binding](#cpu-binding)
/// - [Memory binding](#memory-binding)
/// - [Modifying a loaded topology](#modifying-a-loaded-topology)
/// - [Finding objects inside a CPU set](#finding-objects-inside-a-cpu-set)
/// - [Finding objects covering at least a CPU set](#finding-objects-covering-at-least-a-cpu-set)
/// - [Finding other objects](#finding-other-objects)
/// - [Distributing work items over a topology](#distributing-work-items-over-a-topology)
/// - [CPU and node sets of entire topologies](#cpu-and-node-sets-of-entire-topologies)
/// - [Finding I/O objects](#finding-io-objects)
/// - [Exporting Topologies to XML](#exporting-topologies-to-xml)
/// - [Exporting Topologies to Synthetic](#exporting-topologies-to-synthetic)
/// - [Retrieve distances between objects](#retrieve-distances-between-objects)
/// - [Comparing memory node attributes for finding where to allocate on](#comparing-memory-node-attributes-for-finding-where-to-allocate-on)
/// - [Kinds of CPU cores](#kinds-of-cpu-cores)
#[cfg_attr(
    target_os = "linux",
    doc = "- [Linux-specific helpers](#linux-specific-helpers)"
)]
#[cfg_attr(
    target_os = "windows",
    doc = "- [Windows-specific helpers](#windows-specific-helpers)"
)]
//
// NOTE: Since the Topology API is _huge_, not all of it is implemented in the
// root lib.rs module. Instead, functionality which is very strongly related to
// one other code module is implemented inside that module, leaving the root
// module focused on basic Topology lifecycle and cross-cutting issues.
#[derive(Debug)]
#[doc(alias = "hwloc_topology_t")]
pub struct Topology(NonNull<RawTopology>);

/// # Topology building
//
// Upstream docs:
// - Creation: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__creation.html
// - Build queries: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__configuration.html
impl Topology {
    /// Creates a new Topology.
    ///
    /// If no customization of the build process is needed, this method is the
    /// main entry point to this crate. A topology is returned, which contains
    /// the logical representation of the physical hardware.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::Topology;
    /// let topology = Topology::new()?;
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn new() -> Result<Topology, RawHwlocError> {
        TopologyBuilder::new().build()
    }

    #[doc(hidden)]
    /// Test topology instance
    ///
    /// Used to avoid redundant calls to Topology::new() in unit tests and
    /// doctests that need read-only access to a default-initialized topology
    ///
    /// Do not use this in doctests where the fact that the topology is default
    /// initialized is important for the code sample to make sense.
    ///
    /// NOTE: In an ideal world, this would be cfg(any(test, doctest)) and
    ///       once_cell would be a dev-dependency, but that doesn't work for
    ///       doctests yet: https://github.com/rust-lang/rust/issues/67295
    pub fn test_instance() -> &'static Self {
        use once_cell::sync::Lazy;
        static INSTANCE: Lazy<Topology> =
            Lazy::new(|| Topology::new().expect("Failed to initialize test Topology"));
        &INSTANCE
    }

    /// Prepare to create a Topology with custom configuration
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::topology::{Topology, builder::BuildFlags};
    /// let flags = BuildFlags::IGNORE_DISTANCES
    ///             | BuildFlags::IGNORE_MEMORY_ATTRIBUTES
    ///             | BuildFlags::IGNORE_CPU_KINDS;
    /// let topology = Topology::builder().with_flags(flags)?.build()?;
    /// assert_eq!(topology.build_flags(), flags);
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[doc(alias = "hwloc_topology_init")]
    pub fn builder() -> TopologyBuilder {
        TopologyBuilder::new()
    }

    /// Check that this topology is compatible with the current hwloc library
    ///
    /// This is useful when using the same topology structure (in memory) in
    /// different libraries that may use different hwloc installations (for
    /// instance if one library embeds a specific version of hwloc, while
    /// another library uses a default system-wide hwloc installation).
    ///
    /// If all libraries/programs use the same hwloc installation, this function
    /// always returns `true`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::Topology;
    /// assert!(Topology::new()?.is_abi_compatible());
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[doc(alias = "hwloc_topology_abi_check")]
    pub fn is_abi_compatible(&self) -> bool {
        let result = errors::call_hwloc_int_normal("hwloc_topology_abi_check", || unsafe {
            ffi::hwloc_topology_abi_check(self.as_ptr())
        });
        match result {
            Ok(_) => true,
            Err(RawHwlocError {
                api: _,
                errno: Some(Errno(EINVAL)),
            }) => false,
            Err(raw_err) => unreachable!("{raw_err}"),
        }
    }

    /// Flags that were used to build this topology
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::topology::{Topology, builder::BuildFlags};
    /// assert_eq!(Topology::new()?.build_flags(), BuildFlags::empty());
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[doc(alias = "hwloc_topology_get_flags")]
    pub fn build_flags(&self) -> BuildFlags {
        let result =
            BuildFlags::from_bits_truncate(unsafe { ffi::hwloc_topology_get_flags(self.as_ptr()) });
        debug_assert!(result.is_valid());
        result
    }

    /// Was the topology built using the system running this program?
    ///
    /// It may not have been if, for instance, it was built using another
    /// file-system root or loaded from a synthetic or XML textual description.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::Topology;
    /// assert!(Topology::new()?.is_this_system());
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[doc(alias = "hwloc_topology_is_thissystem")]
    pub fn is_this_system(&self) -> bool {
        let result = errors::call_hwloc_int_normal("hwloc_topology_is_thissystem", || unsafe {
            ffi::hwloc_topology_is_thissystem(self.as_ptr())
        })
        .expect("Unexpected hwloc error");
        assert!(
            result == 0 || result == 1,
            "Unexpected result from hwloc_topology_is_thissystem: {result}"
        );
        result == 1
    }

    /// Supported hwloc features with this topology on this machine
    ///
    /// This is the information that one gets via the `hwloc-info --support` CLI.
    ///
    /// The reported features are what the current topology supports on the
    /// current machine. If the topology was exported to XML from another
    /// machine and later imported here, support still describes what is
    /// supported for this imported topology after import. By default, binding
    /// will be reported as unsupported in this case (see
    /// [`BuildFlags::ASSUME_THIS_SYSTEM`]).
    ///
    /// [`BuildFlags::IMPORT_SUPPORT`] may be used during topology building to
    /// report the supported features of the original remote machine instead. If
    /// it was successfully imported, [`MiscSupport::imported()`] will be set.
    ///
    /// # Examples
    ///
    /// ```
    /// # let topology = hwlocality::Topology::test_instance();
    /// println!("{:?}", topology.feature_support());
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[doc(alias = "hwloc_topology_get_support")]
    pub fn feature_support(&self) -> &FeatureSupport {
        let ptr = errors::call_hwloc_ptr("hwloc_topology_get_support", || unsafe {
            ffi::hwloc_topology_get_support(self.as_ptr())
        })
        .expect("Unexpected hwloc error");

        // This is correct because the output reference will be bound the the
        // lifetime of &self by the borrow checker.
        unsafe { ptr.as_ref() }
    }

    /// Quickly check a support flag
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::topology::{Topology, support::{FeatureSupport, MiscSupport}};
    /// let topology = Topology::new()?;
    /// assert!(
    ///     !topology.supports(FeatureSupport::misc, MiscSupport::imported)
    /// );
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn supports<Group>(
        &self,
        get_group: fn(&FeatureSupport) -> Option<&Group>,
        check_feature: fn(&Group) -> bool,
    ) -> bool {
        get_group(self.feature_support())
            .map(check_feature)
            .unwrap_or(false)
    }

    /// Filtering that was applied for the given object type
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::{
    /// #     objects::types::ObjectType,
    /// #     topology::builder::TypeFilter
    /// # };
    /// # let topology = hwlocality::Topology::test_instance();
    /// #
    /// // PUs, NUMANodes and Machine are always kept
    /// let always_there = [ObjectType::PU,
    ///                     ObjectType::NUMANode,
    ///                     ObjectType::Machine];
    /// for ty in always_there {
    ///     assert_eq!(topology.type_filter(ty)?, TypeFilter::KeepAll);
    /// }
    ///
    /// // Groups are only kept if they bring extra structure
    /// assert_ne!(topology.type_filter(ObjectType::Group)?, TypeFilter::KeepAll);
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[doc(alias = "hwloc_topology_get_type_filter")]
    pub fn type_filter(&self, ty: ObjectType) -> Result<TypeFilter, RawHwlocError> {
        let mut filter = RawTypeFilter::MAX;
        errors::call_hwloc_int_normal("hwloc_topology_get_type_filter", || unsafe {
            ffi::hwloc_topology_get_type_filter(self.as_ptr(), ty.into(), &mut filter)
        })?;
        Ok(TypeFilter::try_from(filter).expect("Unexpected type filter from hwloc"))
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
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__levels.html
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
    /// # let topology = hwlocality::Topology::test_instance();
    /// // The Machine and PU depths are always present
    /// assert!(topology.depth() >= 2);
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[doc(alias = "hwloc_topology_get_depth")]
    pub fn depth(&self) -> u32 {
        unsafe { ffi::hwloc_topology_get_depth(self.as_ptr()) }
            .try_into()
            .expect("Got unexpected depth from hwloc_topology_get_depth")
    }

    /// Depth of parents where memory objects are attached
    ///
    /// # Errors
    ///
    /// - [`DepthError::Multiple`] if memory objects are attached at multiple
    ///   depths
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::objects::TopologyObject;
    /// # let topology = hwlocality::Topology::test_instance();
    /// if let Ok(depth) = topology.memory_parents_depth() {
    ///     let num_memory_objects =
    ///         topology.objects_at_depth(depth)
    ///                 .flat_map(TopologyObject::memory_children)
    ///                 .count();
    ///     assert!(num_memory_objects > 0);
    /// }
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[doc(alias = "hwloc_get_memory_parents_depth")]
    pub fn memory_parents_depth(&self) -> DepthResult {
        Depth::try_from(unsafe { ffi::hwloc_get_memory_parents_depth(self.as_ptr()) })
    }

    /// Depth for the given [`ObjectType`]
    ///
    /// # Errors
    ///
    /// - [`DepthError::None`] if no object of this type is present or
    ///   if the OS doesn't provide this kind of information. If a similar type
    ///   is acceptable, consider using [depth_or_below_for_type()] or
    ///   [depth_or_above_for_type()] instead.
    /// - [`DepthError::Multiple`] if objects of this type exist at multiple
    ///   depths.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::objects::types::ObjectType;
    /// #
    /// # let topology = hwlocality::Topology::test_instance();
    /// #
    /// let machine_depth = topology.depth_for_type(ObjectType::Machine)?;
    /// let pu_depth = topology.depth_for_type(ObjectType::PU)?;
    ///
    /// assert_eq!(machine_depth.assume_normal(), 0);
    /// assert!(machine_depth.assume_normal() < pu_depth.assume_normal());
    /// #
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    ///
    /// [depth_or_below_for_type()]: Topology::depth_or_below_for_type()
    /// [depth_or_above_for_type()]: Topology::depth_or_above_for_type()
    #[doc(alias = "hwloc_get_type_depth")]
    pub fn depth_for_type(&self, object_type: ObjectType) -> DepthResult {
        Depth::try_from(unsafe { ffi::hwloc_get_type_depth(self.as_ptr(), object_type.into()) })
    }

    /// Depth for the given [`ObjectType`] or below
    ///
    /// If no object of this type is present on the underlying architecture, the
    /// function returns the depth of the first present object typically found
    /// inside `object_type`.
    ///
    /// This function is only meaningful for normal object types.
    ///
    /// # Errors
    ///
    /// - [`DepthError::Multiple`] if objects of this type exist at multiple
    ///   depths
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::{objects::types::ObjectType};
    /// #
    /// # let topology = hwlocality::Topology::test_instance();
    /// #
    /// let machine_depth = topology.depth_for_type(ObjectType::Machine)?;
    /// let package_or_below = topology.depth_or_below_for_type(ObjectType::Package)?;
    ///
    /// assert!(machine_depth.assume_normal() < package_or_below.assume_normal());
    /// #
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[doc(alias = "hwloc_get_type_or_below_depth")]
    pub fn depth_or_below_for_type(&self, object_type: ObjectType) -> DepthResult {
        assert!(
            object_type.is_normal(),
            "This is only meaningful for normal objects"
        );
        match self.depth_for_type(object_type) {
            Ok(d) => Ok(d),
            Err(DepthError::None) => {
                let pu_depth = self
                    .depth_for_type(ObjectType::PU)
                    .expect("PU objects should be present")
                    .assume_normal();
                for depth in (0..pu_depth).rev() {
                    if self
                        .type_at_depth(depth)
                        .expect("Depths above PU depth should exist")
                        < object_type
                    {
                        return Ok((depth + 1).into());
                    }
                }
                Err(DepthError::None)
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
    /// This function is only meaningful for normal object types.
    ///
    /// # Errors
    ///
    /// - [`DepthError::Multiple`] if objects of this type exist at multiple
    ///   depths
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::objects::types::ObjectType;
    /// #
    /// # let topology = hwlocality::Topology::test_instance();
    /// #
    /// let pu_depth = topology.depth_for_type(ObjectType::PU)?;
    /// let core_or_above = topology.depth_or_below_for_type(ObjectType::Core)?;
    ///
    /// assert!(core_or_above.assume_normal() < pu_depth.assume_normal());
    /// #
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[doc(alias = "hwloc_get_type_or_above_depth")]
    pub fn depth_or_above_for_type(&self, object_type: ObjectType) -> DepthResult {
        assert!(
            object_type.is_normal(),
            "This is only meaningful for normal objects"
        );
        match self.depth_for_type(object_type) {
            Ok(d) => Ok(d),
            Err(DepthError::None) => {
                for depth in (0..self.depth()).rev() {
                    if self
                        .type_at_depth(depth)
                        .expect("Depths above bottom depth should exist")
                        > object_type
                    {
                        return Ok((depth - 1).into());
                    }
                }
                Err(DepthError::None)
            }
            other_err => other_err,
        }
    }

    /// Depth for the given cache type and level
    ///
    /// Return the depth of the topology level that contains cache objects whose
    /// attributes match `cache_level` and `cache_type`.
    ///
    /// This function is similar to calling [depth_for_type()] with
    /// the corresponding type such as [`ObjectType::L1ICache`], except that it
    /// may also return a unified cache when looking for an instruction cache.
    ///
    /// If `cache_type` is `None`, it is ignored and multiple levels may match.
    /// The function returns either the depth of a uniquely matching level or
    /// Err([`DepthError::Multiple`]).
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
    /// - [`DepthError::None`] if no cache level matches
    /// - [`DepthError::Multiple`] if multiple cache depths match (this can only
    ///   happen if `cache_type` is `None`).
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::objects::types::CacheType;
    /// # let topology = hwlocality::Topology::test_instance();
    /// let l1d_depth = topology.depth_for_cache(1, Some(CacheType::Data));
    /// assert!(l1d_depth.is_ok());
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    ///
    /// [depth_for_type()]: Topology::depth_for_type()
    #[doc(alias = "hwloc_get_cache_type_depth")]
    pub fn depth_for_cache(&self, cache_level: u32, cache_type: Option<CacheType>) -> DepthResult {
        let mut result = Err(DepthError::None);
        for depth in 0..self.depth() {
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
                            Err(DepthError::None) => result = Ok(depth.into()),
                            Ok(_) => {
                                return Err(DepthError::Multiple);
                            }
                            Err(DepthError::Multiple) => {
                                unreachable!("Setting this value triggers a loop break")
                            }
                            Err(DepthError::Unknown(_)) => {
                                unreachable!("This value is never set")
                            }
                        }
                    }
                }
            }
        }
        result
    }

    /// [`ObjectType`] at the given `depth`
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::objects::{depth::Depth, types::ObjectType};
    /// # let topology = hwlocality::Topology::test_instance();
    /// let numa_type = topology.type_at_depth(Depth::NUMANode);
    /// assert_eq!(numa_type, Some(ObjectType::NUMANode));
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[doc(alias = "hwloc_get_depth_type")]
    pub fn type_at_depth(&self, depth: impl Into<Depth>) -> Option<ObjectType> {
        let depth = depth.into();
        if let Depth::Normal(depth) = depth {
            if depth >= self.depth() {
                return None;
            }
        }
        match unsafe { ffi::hwloc_get_depth_type(self.as_ptr(), depth.into()) }.try_into() {
            Ok(depth) => Some(depth),
            Err(TryFromPrimitiveError {
                number: RawObjectType::MAX,
            }) => None,
            Err(unknown) => {
                unreachable!("Got unknown object type from hwloc_get_depth_type: {unknown}")
            }
        }
    }

    /// Number of objects at the given `depth`
    ///
    /// # Examples
    ///
    /// ```
    /// # let topology = hwlocality::Topology::test_instance();
    /// #
    /// let num_roots = topology.size_at_depth(0);
    /// assert_eq!(num_roots, 1);
    ///
    /// let num_root_children = topology.size_at_depth(1);
    /// assert!(num_root_children > 0);
    /// #
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[doc(alias = "hwloc_get_nbobjs_by_depth")]
    pub fn size_at_depth(&self, depth: impl Into<Depth>) -> u32 {
        unsafe { ffi::hwloc_get_nbobjs_by_depth(self.as_ptr(), depth.into().into()) }
    }

    /// [`TopologyObject`]s at the given `depth`
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::objects::{depth::Depth, types::ObjectType};
    /// # let topology = hwlocality::Topology::test_instance();
    /// #
    /// use anyhow::Context;
    ///
    /// let root = topology.root_object();
    ///
    /// for node in topology.objects_at_depth(Depth::NUMANode) {
    ///     assert_eq!(node.object_type(), ObjectType::NUMANode);
    ///     assert!(node.is_in_subtree(root));
    ///     assert_eq!(node.normal_arity(), 0);
    ///     assert_eq!(node.memory_arity(), 0);
    ///     let num_nodes =
    ///         node.nodeset().context("A NUMANode should have a NodeSet")?
    ///             .weight().context("A NUMANode's NodeSet should be finite")?;
    ///     assert_eq!(num_nodes, 1);
    /// }
    /// #
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[doc(alias = "hwloc_get_obj_by_depth")]
    #[doc(alias = "hwloc_get_next_obj_by_depth")]
    pub fn objects_at_depth(
        &self,
        depth: impl Into<Depth>,
    ) -> impl Iterator<Item = &TopologyObject>
           + Clone
           + DoubleEndedIterator
           + ExactSizeIterator
           + FusedIterator {
        let depth = depth.into();
        let size = self.size_at_depth(depth);
        let depth = RawDepth::from(depth);
        (0..size).map(move |idx| {
            let ptr = unsafe { ffi::hwloc_get_obj_by_depth(self.as_ptr(), depth, idx) };
            assert!(
                !ptr.is_null(),
                "Got null pointer from hwloc_get_obj_by_depth"
            );
            unsafe { &*ptr }
        })
    }

    /// [`TopologyObject`] at the root of the topology
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::objects::{depth::Depth, types::ObjectType};
    /// # let topology = hwlocality::Topology::test_instance();
    /// let root = topology.root_object();
    ///
    /// assert_eq!(root.object_type(), ObjectType::Machine);
    ///
    /// assert_eq!(root.depth(), Depth::Normal(0));
    /// assert!(root.parent().is_none());
    /// assert_eq!(root.logical_index(), 0);
    /// assert_ne!(root.normal_arity(), 0);
    ///
    /// assert!(root.cpuset().is_some());
    /// assert!(root.nodeset().is_some());
    ///
    /// println!("{root:#}");
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[doc(alias = "hwloc_get_root_obj")]
    pub fn root_object(&self) -> &TopologyObject {
        self.objects_at_depth(0)
            .next()
            .expect("Root object should exist")
    }

    /// [`TopologyObject`]s with the given [`ObjectType`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::objects::types::ObjectType;
    /// # let topology = hwlocality::Topology::test_instance();
    /// #
    /// use anyhow::Context;
    ///
    /// let root = topology.root_object();
    ///
    /// for pu in topology.objects_with_type(ObjectType::PU) {
    ///     assert_eq!(pu.object_type(), ObjectType::PU);
    ///     assert!(pu.is_in_subtree(root));
    ///     assert_eq!(pu.normal_arity(), 0);
    ///     let num_cpus =
    ///         pu.cpuset().context("A PU should have a CpuSet")?
    ///           .weight().context("A PU's CpuSet should be finite")?;
    ///     assert_eq!(num_cpus, 1);
    /// }
    /// #
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[doc(alias = "hwloc_get_obj_by_type")]
    #[doc(alias = "hwloc_get_next_obj_by_type")]
    pub fn objects_with_type(
        &self,
        object_type: ObjectType,
    ) -> impl Iterator<Item = &TopologyObject>
           + Clone
           + DoubleEndedIterator
           + ExactSizeIterator
           + FusedIterator {
        let type_depth = self.depth_for_type(object_type);
        let depth_iter = (0..self.depth())
            .map(Depth::from)
            .chain(Depth::VIRTUAL_DEPTHS.iter().copied())
            .filter(move |&depth| {
                if let Ok(type_depth) = type_depth {
                    depth == type_depth
                } else {
                    self.type_at_depth(depth).expect("Depth should exist") == object_type
                }
            });
        let size = depth_iter
            .clone()
            .map(move |depth| {
                usize::try_from(self.size_at_depth(depth)).expect("Impossible object count")
            })
            .sum();
        ObjectsWithType {
            size,
            inner: depth_iter.flat_map(move |depth| self.objects_at_depth(depth)),
        }
    }
}

/// Iterator emitted by objects_with_type
#[derive(Copy, Clone)]
struct ObjectsWithType<Inner> {
    size: usize,
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

    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.size
    }
}
//
impl<'topology, Inner: Iterator<Item = &'topology TopologyObject> + DoubleEndedIterator>
    DoubleEndedIterator for ObjectsWithType<Inner>
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
impl<'topology, Inner: Iterator<Item = &'topology TopologyObject> + FusedIterator> FusedIterator
    for ObjectsWithType<Inner>
{
}

/// # Finding other objects
//
// This is inspired by the upstream functionality described at
// https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__find__misc.html
// but the code had to be ported to Rust because it's inline
impl Topology {
    /// Get the object of type [`ObjectType::PU`] with the specified OS index
    ///
    /// If you want to convert an entire CPU set into the PU objects it
    /// contains, using `pus_from_cpuset` will be more efficient than repeatedly
    /// calling this function with every OS index from the CpuSet.
    ///
    /// Requires [`DiscoverySupport::pu_count()`].
    pub fn pu_with_os_index(&self, os_index: u32) -> Option<&TopologyObject> {
        self.objs_and_os_indices(ObjectType::PU)
            .find_map(|(pu, pu_os_index)| (pu_os_index == os_index).then_some(pu))
    }

    /// Get the objects of type [`ObjectType::PU`] covered by the specified cpuset
    ///
    /// Requires [`DiscoverySupport::pu_count()`].
    pub fn pus_from_cpuset<'result>(
        &'result self,
        cpuset: &'result CpuSet,
    ) -> impl Iterator<Item = &TopologyObject> + Clone + DoubleEndedIterator + FusedIterator + 'result
    {
        self.objs_and_os_indices(ObjectType::PU)
            .filter_map(|(pu, os_index)| cpuset.is_set(os_index).then_some(pu))
    }

    /// Get the object of type [`ObjectType::NUMANode`] with the specified OS index
    ///
    /// If you want to convert an entire NodeSet into the NUMANode objects it
    /// contains, using `nodes_from_cpuset` will be more efficient than repeatedly
    /// calling this function with every OS index from the NodeSet.
    ///
    /// Requires [`DiscoverySupport::numa_count()`].
    pub fn node_with_os_index(&self, os_index: u32) -> Option<&TopologyObject> {
        self.objs_and_os_indices(ObjectType::NUMANode)
            .find_map(|(node, node_os_index)| (node_os_index == os_index).then_some(node))
    }

    /// Get the objects of type [`ObjectType::NUMANode`] covered by the
    /// specified nodeset
    ///
    /// Requires [`DiscoverySupport::numa_count()`].
    pub fn nodes_from_nodeset<'result>(
        &'result self,
        nodeset: &'result NodeSet,
    ) -> impl Iterator<Item = &TopologyObject> + Clone + DoubleEndedIterator + FusedIterator + 'result
    {
        self.objs_and_os_indices(ObjectType::NUMANode)
            .filter_map(|(node, os_index)| nodeset.is_set(os_index).then_some(node))
    }

    /// Get a list of `(&TopologyObject, OS index)` tuples for an `ObjectType`
    /// that is guaranteed to appear only at one depth of the topology and to
    /// have an OS index.
    ///
    /// # Panics
    ///
    /// Will panic if the object type appears at more than one depth or do not
    /// have an OS index.
    fn objs_and_os_indices(
        &self,
        ty: ObjectType,
    ) -> impl Iterator<Item = (&TopologyObject, u32)>
           + Clone
           + DoubleEndedIterator
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
    /// topology tree)
    ///
    /// # Panics
    ///
    /// `obj` must have a cpuset, otherwise this function will panic.
    pub fn closest_objects<'result>(
        &'result self,
        obj: &'result TopologyObject,
    ) -> impl Iterator<Item = &TopologyObject> + Clone + 'result {
        // Track which CPUs map into objects we don't want to report
        // (current object or already reported object)
        let mut known_cpuset = obj.cpuset().expect("Target object must have a cpuset");

        // Assert that an object has a cpuset, return both
        fn obj_and_cpuset<'obj>(
            obj: &'obj TopologyObject,
            error: &str,
        ) -> (&'obj TopologyObject, &'obj CpuSet) {
            (obj, obj.cpuset().expect(error))
        }

        // Find the first ancestor of an object that knows about more objects
        // than that object (if any), and return it along with its cpuset
        fn find_larger_parent<'obj>(
            known_obj: &'obj TopologyObject,
            known_cpuset: &CpuSet,
        ) -> Option<(&'obj TopologyObject, &'obj CpuSet)> {
            known_obj
                .ancestors()
                .map(|ancestor| {
                    obj_and_cpuset(
                        ancestor,
                        "Ancestors of an obj with a cpuset should have a cpuset",
                    )
                })
                .find(|&(_ancestor, ancestor_cpuset)| ancestor_cpuset != known_cpuset)
        }
        let mut ancestor_and_cpuset = find_larger_parent(obj, known_cpuset);

        // Prepare to jointly iterate over cousins and their cpusets
        let cousins_and_cpusets = self
            .objects_at_depth(obj.depth())
            .map(|cousin| {
                obj_and_cpuset(
                    cousin,
                    "Cousins of an obj with a cpuset should have a cpuset",
                )
            })
            .collect::<Vec<_>>();
        let mut cousin_idx = 0;

        // Emit the final iterator
        std::iter::from_fn(move || {
            loop {
                // Look for a cousin that is part of ancestor_cpuset but not known_cpuset
                let (ancestor, ancestor_cpuset) = ancestor_and_cpuset?;
                while let Some((cousin, cousin_cpuset)) = cousins_and_cpusets.get(cousin_idx) {
                    cousin_idx += 1;
                    if ancestor_cpuset.includes(cousin_cpuset)
                        && !known_cpuset.includes(cousin_cpuset)
                    {
                        return Some(*cousin);
                    }
                }

                // We ran out of cousins, go up one ancestor level or end
                // iteration if we reached the top of the tree.
                let known_obj = ancestor;
                known_cpuset = ancestor_cpuset;
                let (ancestor, ancestor_cpuset) = find_larger_parent(known_obj, known_cpuset)?;
                ancestor_and_cpuset = Some((ancestor, ancestor_cpuset));
                cousin_idx = 0;
            }
        })
    }

    /// Find an object via a parent->child chain specified by types and indices
    ///
    /// For example, if called with `&[(NUMANode, 0), (Package, 1), (Core, 2)]`,
    /// this will return the third core object below the second package below
    /// the first NUMA node.
    ///
    /// # Panics
    ///
    /// All objects must have a cpuset, otherwise this function will panic.
    pub fn object_by_type_index_path(
        &self,
        path: &[(ObjectType, usize)],
    ) -> Option<&TopologyObject> {
        let mut obj = self.root_object();
        for &(ty, idx) in path {
            let cpuset = obj
                .cpuset()
                .expect("All objects in path should have a cpuset");

            obj = self.objects_inside_cpuset_with_type(cpuset, ty).nth(idx)?;
        }
        Some(obj)
    }

    /// Find an object of a different type with the same locality
    ///
    /// If the source object src is a normal or memory type, this function
    /// returns an object of type type with same CPU and node sets, either below
    /// or above in the hierarchy.
    ///
    /// If the source object src is a PCI or an OS device within a PCI device,
    /// the function may either return that PCI device, or another OS device in
    /// the same PCI parent. This may for instance be useful for converting
    /// between OS devices such as "nvml0" or "rsmi1" used in distance
    /// structures into the the PCI device, or the CUDA or OpenCL OS device that
    /// correspond to the same physical card.
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
    /// - [`NulError`] if `subtype` or `name_prefix` contains NUL chars.
    #[doc(alias = "hwloc_get_obj_with_same_locality")]
    pub fn object_with_same_locality(
        &self,
        src: &TopologyObject,
        ty: ObjectType,
        subtype: Option<&str>,
        name_prefix: Option<&str>,
    ) -> Result<Option<&TopologyObject>, NulError> {
        let subtype = subtype.map(LibcString::new).transpose()?;
        let name_prefix = name_prefix.map(LibcString::new).transpose()?;
        let borrow_pchar = |opt: &Option<LibcString>| -> *const c_char {
            opt.as_ref().map(|s| s.borrow()).unwrap_or(ptr::null())
        };
        let ptr = unsafe {
            ffi::hwloc_get_obj_with_same_locality(
                self.as_ptr(),
                src,
                ty.into(),
                borrow_pchar(&subtype),
                borrow_pchar(&name_prefix),
                0,
            )
        };
        Ok((!ptr.is_null()).then(|| unsafe { &*ptr }))
    }
}

/// # Distributing work items over a topology
//
// Inspired by https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__distribute.html,
// but the inline header implementation had to be rewritten in Rust.
impl Topology {
    /// Distribute `num_items` work items over the topology under `roots`
    ///
    /// Given a number of work items to be processed (which can be, for example,
    /// a set of threads to be spawned), this function will assign a cpuset to
    /// each of them according to a recursive linear distribution algorithm.
    /// Such an algorithm spreads work evenly across CPUs and ensures that
    /// work-items with neighboring indices in the output array are processed by
    /// neighbouring locations in the topology, which have a high chance of
    /// sharing resources like fast CPU caches.
    ///
    /// The set of CPUs over which work items are distributed is designated by a
    /// set of root [`TopologyObject`]s with associated CPUs. You can distribute
    /// items across all CPUs in the topology by setting `roots` to
    /// `&[topology.root_object()]`.
    ///
    /// Since the purpose of `roots` is to designate which CPUs items should be
    /// allocated to, root objects should normally have a CPU set. If that is
    /// not the case (e.g. if some roots designate NUMA nodes or I/O objects
    /// like storage or GPUs), the algorithm will walk up affected roots'
    /// ancestor chains to locate the first ancestor with CPUs in the topology,
    /// which represents the CPUs closest to the object of interest. If none of
    /// the CPUs of that ancestor is available for binding, that root will be
    /// ignored.
    ///
    /// If there is no depth limit, which is achieved by setting `max_depth` to
    /// `u32::MAX`, the distribution will be done down to the granularity of
    /// individual CPUs, i.e. if there are more work items that CPUs, each work
    /// item will be assigned one CPU. By setting the `max_depth` parameter to a
    /// lower limit, you can distribute work at a coarser granularity, e.g.
    /// across L3 caches, giving the OS some leeway to move tasks across CPUs
    /// sharing that cache.
    ///
    /// By default, output cpusets follow the logical topology children order.
    /// By setting `flags` to [`DistributeFlags::REVERSE`], you can ask for them
    /// to be provided in reverse order instead (from last child to first child).
    ///
    /// # Panics
    ///
    /// - If there are no CPUs to distribute work to (the union of all root
    ///   cpusets is empty).
    #[doc(alias = "hwloc_distrib")]
    pub fn distribute_items(
        &self,
        roots: &[&TopologyObject],
        num_items: NonZeroU32,
        max_depth: u32,
        flags: DistributeFlags,
    ) -> Vec<CpuSet> {
        // This algorithm works on normal objects and uses cpuset, cpuset weight and depth
        type ObjSetWeightDepth<'a> = (&'a TopologyObject, &'a CpuSet, u32, u32);
        fn decode_normal_obj(obj: &TopologyObject) -> Option<ObjSetWeightDepth> {
            debug_assert!(obj.object_type().is_normal());
            let cpuset = obj.cpuset().expect("Normal objects should have cpusets");
            let weight = cpuset
                .weight()
                .expect("Topology objects should not have infinite cpusets");
            let depth =
                u32::try_from(obj.depth()).expect("Normal objects should have a normal depth");
            (weight > 0).then_some((obj, cpuset, weight, depth))
        }

        // Inner recursive algorithm
        fn recurse<'a>(
            roots_and_cpusets: impl Iterator<Item = ObjSetWeightDepth<'a>> + Clone + DoubleEndedIterator,
            num_items: u32,
            max_depth: u32,
            flags: DistributeFlags,
            result: &mut Vec<CpuSet>,
        ) {
            // Debug mode checks
            debug_assert_ne!(roots_and_cpusets.clone().count(), 0);
            debug_assert_ne!(num_items, 0);
            let initial_len = result.len();

            // Total number of cpus covered by the active root
            let tot_weight: u32 = roots_and_cpusets
                .clone()
                .map(|(_, _, weight, _)| weight)
                .sum();

            // Subset of CPUs and items covered so far
            let mut given_weight = 0;
            let mut given_items = 0;

            // What to do with each root
            let process_root = |(root, cpuset, weight, depth): ObjSetWeightDepth| {
                // Give this root a chunk of the work-items proportional to its
                // weight, with a bias towards giving more CPUs to first roots
                let weight_to_items = |given_weight| {
                    // This is exact because f64 has 54 mantissa bits and we're
                    // dealing with 32-bit integers here
                    (given_weight as f64 * num_items as f64 / tot_weight as f64).ceil() as u32
                };
                let next_given_weight = given_weight + weight;
                let next_given_items = weight_to_items(next_given_weight);
                let my_items = next_given_items - given_items;

                // Keep recursing until we reach the bottom of the topology,
                // run out of items to distribute, or hit the depth limit
                if root.normal_arity() > 0 && my_items > 1 && depth < max_depth {
                    recurse(
                        root.normal_children().filter_map(decode_normal_obj),
                        my_items,
                        max_depth,
                        flags,
                        result,
                    );
                } else if my_items > 0 {
                    // All items attributed to this root get this root's cpuset
                    for _ in 0..my_items {
                        result.push(cpuset.clone());
                    }
                } else {
                    // No item attributed to this root, merge cpuset with
                    // the previous root.
                    *result.last_mut().expect("First chunk cannot be empty") |= cpuset;
                }

                // Prepare to process the next root
                given_weight = next_given_weight;
                given_items = next_given_items;
            };

            // Process roots in the order dictated by flags
            if flags.contains(DistributeFlags::REVERSE) {
                roots_and_cpusets.rev().for_each(process_root);
            } else {
                roots_and_cpusets.for_each(process_root);
            }

            // Debug mode checks
            debug_assert_eq!(
                result.len() - initial_len,
                num_items
                    .try_into()
                    .expect("Already checked that num_items fits in usize")
            );
        }

        // Check roots, walk up to their first normal ancestor as necessary
        let decoded_roots = roots.iter().copied().filter_map(|root| {
            let mut root_then_ancestors = std::iter::once(root)
                .chain(root.ancestors())
                .skip_while(|root| !root.object_type().is_normal());
            root_then_ancestors.find_map(decode_normal_obj)
        });
        assert_ne!(
            decoded_roots.clone().count(),
            0,
            "No valid root to distribute items to"
        );

        // Run the recursion, collect results
        let num_items = u32::from(num_items);
        let num_items_usize = usize::try_from(num_items).expect("Cannot return that many items");
        let mut result = Vec::with_capacity(num_items_usize);
        recurse(decoded_roots, num_items, max_depth, flags, &mut result);
        debug_assert_eq!(result.len(), num_items_usize);
        result
    }
}
//
bitflags! {
    /// Flags to be given to [`Topology::distribute_items()`]
    #[repr(C)]
    pub struct DistributeFlags: c_ulong {
        /// Distribute in reverse order, starting from the last objects
        const REVERSE = (1<<0);
    }
}
//
impl Default for DistributeFlags {
    fn default() -> Self {
        Self::empty()
    }
}

/// # CPU and node sets of entire topologies
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__topology__sets.html
impl Topology {
    /// Topology CPU set
    ///
    /// This is equivalent to calling [`TopologyObject::cpuset()`] on
    /// the topology's root object.
    #[doc(alias = "hwloc_topology_get_topology_cpuset")]
    pub fn cpuset(&self) -> Result<&CpuSet, RawHwlocError> {
        unsafe {
            self.topology_set(
                "hwloc_topology_get_topology_cpuset",
                ffi::hwloc_topology_get_topology_cpuset,
            )
        }
    }

    /// Complete CPU set
    ///
    /// This is equivalent to calling [`TopologyObject::complete_cpuset()`] on
    /// the topology's root object.
    #[doc(alias = "hwloc_topology_get_complete_cpuset")]
    pub fn complete_cpuset(&self) -> Result<&CpuSet, RawHwlocError> {
        unsafe {
            self.topology_set(
                "hwloc_topology_get_complete_cpuset",
                ffi::hwloc_topology_get_complete_cpuset,
            )
        }
    }

    /// Allowed CPU set
    ///
    /// If [`BuildFlags::INCLUDE_DISALLOWED`] was not set, this is identical to
    /// [`Topology::cpuset()`]: all visible PUs are allowed.
    ///
    /// Otherwise, you can check whether a particular cpuset contains allowed
    /// PUs by calling `cpuset.intersects(topology.allowed_cpuset())`, and if so
    /// you can get the set of allowed PUs with
    /// `cpuset & topology.allowed_cpuset()`.
    #[doc(alias = "hwloc_topology_get_allowed_cpuset")]
    pub fn allowed_cpuset(&self) -> Result<&CpuSet, RawHwlocError> {
        unsafe {
            self.topology_set(
                "hwloc_topology_get_allowed_cpuset",
                ffi::hwloc_topology_get_allowed_cpuset,
            )
        }
    }

    /// Topology node set
    ///
    /// This is equivalent to calling [`TopologyObject::nodeset()`] on
    /// the topology's root object.
    #[doc(alias = "hwloc_topology_get_topology_nodeset")]
    pub fn nodeset(&self) -> Result<&NodeSet, RawHwlocError> {
        unsafe {
            self.topology_set(
                "hwloc_topology_get_topology_nodeset",
                ffi::hwloc_topology_get_topology_nodeset,
            )
        }
    }

    /// Complete node set
    ///
    /// This is equivalent to calling [`TopologyObject::complete_nodeset()`] on
    /// the topology's root object.
    #[doc(alias = "hwloc_topology_get_complete_nodeset")]
    pub fn complete_nodeset(&self) -> Result<&NodeSet, RawHwlocError> {
        unsafe {
            self.topology_set(
                "hwloc_topology_get_complete_nodeset",
                ffi::hwloc_topology_get_complete_nodeset,
            )
        }
    }

    /// Allowed node set
    ///
    /// If [`BuildFlags::INCLUDE_DISALLOWED`] was not set, this is identical to
    /// [`Topology::nodeset()`]: all visible NUMA nodes are allowed.
    ///
    /// Otherwise, you can check whether a particular nodeset contains allowed
    /// NUMA nodes by calling `nodeset.intersects(topology.allowed_nodeset())`,
    /// and if so you can get the set of allowed NUMA nodes with
    /// `nodeset & topology.allowed_nodeset()`.
    #[doc(alias = "hwloc_topology_get_allowed_nodeset")]
    pub fn allowed_nodeset(&self) -> Result<&NodeSet, RawHwlocError> {
        unsafe {
            self.topology_set(
                "hwloc_topology_get_allowed_nodeset",
                ffi::hwloc_topology_get_allowed_nodeset,
            )
        }
    }

    /// Query a topology-wide `CpuSet` or `NodeSet`
    ///
    /// # Safety
    ///
    /// The `*const RawBitmap` returned by `getter` must originate from `self`.
    unsafe fn topology_set<'topology, Set: SpecializedBitmap>(
        &'topology self,
        getter_name: &'static str,
        getter: unsafe extern "C" fn(*const RawTopology) -> *const RawBitmap,
    ) -> Result<&Set, RawHwlocError> {
        Ok(Set::from_bitmap_ref(unsafe {
            let bitmap_ptr = errors::call_hwloc_ptr(getter_name, || getter(self.as_ptr()))?;
            let bitmap_ref = std::mem::transmute::<
                &NonNull<RawBitmap>,
                &'topology NonNull<RawBitmap>,
            >(&bitmap_ptr);
            Bitmap::borrow_from_non_null(bitmap_ref)
        }))
    }
}

/// # Finding I/O objects
//
// Inspired by https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__advanced__io.html
// but inline functions had to be reimplemented in Rust
impl Topology {
    /// Enumerate PCI devices in the system
    #[doc(alias = "hwloc_get_next_pcidev")]
    pub fn pci_devices(
        &self,
    ) -> impl Iterator<Item = &TopologyObject>
           + Clone
           + DoubleEndedIterator
           + ExactSizeIterator
           + FusedIterator {
        self.objects_at_depth(Depth::PCIDevice)
    }

    /// Find the PCI device object matching the PCI bus id given domain, bus
    /// device and function PCI bus id
    #[doc(alias = "hwloc_get_pcidev_by_busid")]
    pub fn pci_device_by_bus_id(
        &self,
        domain: u32,
        bus_id: u8,
        bus_device: u8,
        function: u8,
    ) -> Option<&TopologyObject> {
        self.pci_devices().find(|obj| {
            let Some(ObjectAttributes::PCIDevice(pci)) = obj.attributes() else { unreachable!("All PCI devices should have PCI attributes") };
            pci.domain() == domain && pci.bus_id() == bus_id && pci.bus_device() == bus_device && pci.function() == function
        })
    }

    /// Find the PCI device object matching the PCI bus id given as a string
    /// of format "xxxx:yy:zz.t" (with domain) or "yy:zz.t" (without domain).
    ///
    /// # Panics
    ///
    /// If the given string does not match the PCI bus id format given above
    #[doc(alias = "hwloc_get_pcidev_by_busidstring")]
    pub fn pci_device_by_bus_id_string(&self, bus_id: &str) -> Option<&TopologyObject> {
        // Assume well-formatted string
        let parse_u32 = |s| u32::from_str_radix(s, 16).expect("Bad hex u32 format");
        let parse_u8 = |s| u8::from_str_radix(s, 16).expect("Bad hex u8 format");

        // Extract initial hex (whose semantics are ambiguous at this stage)
        let (int1, mut rest) = bus_id.split_once(':').expect("Bad address structure");

        // From presence/absence of second ':', deduce if int1 was a domain or
        // a bus id in the default 0 domain.
        let (domain, bus) = if let Some((bus, next_rest)) = rest.split_once(':') {
            rest = next_rest;
            (parse_u32(int1), parse_u8(bus))
        } else {
            (0, parse_u8(int1))
        };

        // Parse device and function IDs, and forward to non-textual lookup
        let (dev, func) = rest.split_once('.').expect("Bad address structure");
        self.pci_device_by_bus_id(domain, bus, parse_u8(dev), parse_u8(func))
    }

    /// Enumerate OS devices in the system
    #[doc(alias = "hwloc_get_next_osdev")]
    pub fn os_devices(
        &self,
    ) -> impl Iterator<Item = &TopologyObject>
           + Clone
           + DoubleEndedIterator
           + ExactSizeIterator
           + FusedIterator {
        self.objects_at_depth(Depth::OSDevice)
    }

    /// Enumerate bridges in the system
    #[doc(alias = "hwloc_get_next_bridge")]
    pub fn bridges(
        &self,
    ) -> impl Iterator<Item = &TopologyObject>
           + Clone
           + DoubleEndedIterator
           + ExactSizeIterator
           + FusedIterator {
        self.objects_at_depth(Depth::Bridge)
    }
}

// # General-purpose internal utilities
impl Topology {
    /// Returns the contained hwloc topology pointer for interaction with hwloc.
    pub(crate) fn as_ptr(&self) -> *const RawTopology {
        self.0.as_ptr()
    }

    /// Returns the contained hwloc topology pointer for interaction with hwloc.
    pub(crate) fn as_mut_ptr(&mut self) -> *mut RawTopology {
        self.0.as_ptr()
    }
}

impl Clone for Topology {
    #[doc(alias = "hwloc_topology_dup")]
    fn clone(&self) -> Self {
        let mut clone = ptr::null_mut();
        errors::call_hwloc_int_normal("hwloc_topology_dup", || unsafe {
            ffi::hwloc_topology_dup(&mut clone, self.as_ptr())
        })
        .expect("Failed to clone topology");
        Self(NonNull::new(clone).expect("Got null pointer from hwloc_topology_dup"))
    }
}

impl Drop for Topology {
    fn drop(&mut self) {
        unsafe { ffi::hwloc_topology_destroy(self.as_mut_ptr()) }
    }
}

unsafe impl Send for Topology {}
unsafe impl Sync for Topology {}
