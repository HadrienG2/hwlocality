#![doc = include_str!("../README.md")]

pub mod bitmaps;
pub mod builder;
pub mod cpu;
pub mod depth;
pub mod distances;
pub mod editor;
pub mod errors;
pub mod export;
pub(crate) mod ffi;
pub mod info;
pub mod memory;
pub mod objects;
pub mod support;

use crate::{
    bitmaps::{Bitmap, BitmapKind, CpuSet, NodeSet, RawBitmap, SpecializedBitmap},
    builder::{BuildFlags, RawTypeFilter, TopologyBuilder, TypeFilter},
    cpu::{
        binding::{CpuBindingError, CpuBindingFlags, CpuBindingOperation, CpuBoundObject},
        caches::CPUCacheStats,
    },
    depth::{Depth, DepthError, DepthResult, RawDepth},
    distances::{Distances, DistancesKind, RawDistances},
    editor::TopologyEditor,
    errors::{NulError, RawIntError},
    export::{
        synthetic::SyntheticExportFlags,
        xml::{XMLExportFlags, XML},
        XMLFileExportError,
    },
    ffi::{IncompleteType, LibcString},
    memory::{
        attributes::{MemoryAttribute, TargetNumaNodes},
        binding::{
            Bytes, MemoryAllocationError, MemoryBindingError, MemoryBindingFlags,
            MemoryBindingOperation, MemoryBindingPolicy, MemoryBoundObject, RawMemoryBindingPolicy,
        },
    },
    objects::{
        attributes::ObjectAttributes,
        types::{CacheType, ObjectType, RawObjectType},
        TopologyObject,
    },
    support::FeatureSupport,
};
#[cfg(doc)]
use crate::{
    memory::attributes::LocalNUMANodeFlags,
    support::{CpuBindingSupport, DiscoverySupport, MemoryBindingSupport, MiscSupport},
};
use bitflags::bitflags;
use errno::{errno, Errno};
use libc::EINVAL;
use num_enum::TryFromPrimitiveError;
use std::{
    convert::TryInto,
    ffi::{c_char, c_int, c_uint, c_ulong, c_void, CString},
    iter::FusedIterator,
    mem::MaybeUninit,
    num::NonZeroU32,
    panic::{AssertUnwindSafe, UnwindSafe},
    path::Path,
    ptr::{self, NonNull},
};

#[cfg(target_os = "windows")]
/// Thread identifier
pub type ThreadId = windows_sys::Win32::Foundation::HANDLE;
#[cfg(target_os = "windows")]
/// Process identifier
pub type ProcessId = u32;
#[cfg(not(target_os = "windows"))]
/// Thread identifier
pub type ThreadId = libc::pthread_t;
#[cfg(not(target_os = "windows"))]
/// Process identifier
pub type ProcessId = libc::pid_t;

/// Indicate at runtime which hwloc API version was used at build time.
/// This number is updated to (X<<16)+(Y<<8)+Z when a new release X.Y.Z
/// actually modifies the API.
///
/// Users may check for available features at build time using this number
pub fn get_api_version() -> u32 {
    unsafe { ffi::hwloc_get_api_version() }
}

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
    pub fn new() -> Result<Topology, Errno> {
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
    /// FIXME: In an ideal world, this would be cfg(any(test, doctest)) and
    ///        once_cell would be a dev-dependency, but that doesn't work for
    ///        doctests yet: https://github.com/rust-lang/rust/issues/67295
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
    /// # use hwlocality::{Topology, builder::BuildFlags};
    /// let flags = BuildFlags::IGNORE_DISTANCES
    ///             | BuildFlags::IGNORE_MEMORY_ATTRIBUTES
    ///             | BuildFlags::IGNORE_CPU_KINDS;
    /// let topology = Topology::builder().with_flags(flags)?.build()?;
    /// assert_eq!(topology.build_flags(), flags);
    /// # Ok::<(), anyhow::Error>(())
    /// ```
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
    pub fn is_abi_compatible(&self) -> bool {
        let result = errors::call_hwloc_int("hwloc_topology_abi_check", || unsafe {
            ffi::hwloc_topology_abi_check(self.as_ptr())
        });
        match result {
            Ok(0) => true,
            Ok(other) => panic!("Unexpected return value from hwloc_topology_abi_check: {other}"),
            Err(RawIntError::Errno {
                errno: Some(Errno(EINVAL)),
                ..
            }) => false,
            Err(raw_err) => panic!("Unexpected hwloc error: {raw_err}"),
        }
    }

    /// Flags that were used to build this topology
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::{Topology, builder::BuildFlags};
    /// assert_eq!(Topology::new()?.build_flags(), BuildFlags::empty());
    /// # Ok::<(), anyhow::Error>(())
    /// ```
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
    pub fn is_this_system(&self) -> bool {
        let result = errors::call_hwloc_int("hwloc_topology_is_thissystem", || unsafe {
            ffi::hwloc_topology_is_thissystem(self.as_ptr())
        })
        .expect("Unexpected hwloc error");
        assert!(
            result == 0 || result == 1,
            "Unexpected result from hwloc_topology_is_thissystem"
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
    /// # use hwlocality::{Topology, support::{FeatureSupport, MiscSupport}};
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
    /// #     builder::TypeFilter
    /// # };
    /// # let topology = hwlocality::Topology::test_instance();
    /// #
    /// // PUs, NUMANodes and Machine are always kept
    /// let always_there = [ObjectType::PU,
    ///                     ObjectType::NUMANode,
    ///                     ObjectType::Machine];
    /// for ty in always_there {
    ///     assert_eq!(topology.type_filter(ty), TypeFilter::KeepAll);
    /// }
    ///
    /// // Groups are only kept if they bring extra structure
    /// assert_ne!(topology.type_filter(ObjectType::Group), TypeFilter::KeepAll);
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn type_filter(&self, ty: ObjectType) -> TypeFilter {
        let mut filter = RawTypeFilter::MAX;
        errors::call_hwloc_int("hwloc_topology_get_type_filter", || unsafe {
            ffi::hwloc_topology_get_type_filter(self.as_ptr(), ty.into(), &mut filter)
        })
        .expect("Unexpected hwloc error");
        TypeFilter::try_from(filter).expect("Unexpected type filter from hwloc")
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
    pub fn full_depth(&self) -> u32 {
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
    pub fn depth_or_above_for_type(&self, object_type: ObjectType) -> DepthResult {
        assert!(
            object_type.is_normal(),
            "This is only meaningful for normal objects"
        );
        match self.depth_for_type(object_type) {
            Ok(d) => Ok(d),
            Err(DepthError::None) => {
                for depth in (0..self.full_depth()).rev() {
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
    pub fn depth_for_cache(&self, cache_level: u32, cache_type: Option<CacheType>) -> DepthResult {
        let mut result = Err(DepthError::None);
        for depth in 0..self.full_depth() {
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
    /// # use hwlocality::{depth::Depth, objects::types::ObjectType};
    /// # let topology = hwlocality::Topology::test_instance();
    /// let numa_type = topology.type_at_depth(Depth::NUMANode);
    /// assert_eq!(numa_type, Some(ObjectType::NUMANode));
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn type_at_depth(&self, depth: impl Into<Depth>) -> Option<ObjectType> {
        let depth = depth.into();
        if let Depth::Normal(depth) = depth {
            if depth >= self.full_depth() {
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
    pub fn size_at_depth(&self, depth: impl Into<Depth>) -> u32 {
        unsafe { ffi::hwloc_get_nbobjs_by_depth(self.as_ptr(), depth.into().into()) }
    }

    /// [`TopologyObject`]s at the given `depth`
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::{depth::Depth, objects::types::ObjectType};
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
    /// # use hwlocality::{objects::types::ObjectType, depth::Depth};
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
    pub fn objects_with_type(
        &self,
        object_type: ObjectType,
    ) -> impl Iterator<Item = &TopologyObject>
           + Clone
           + DoubleEndedIterator
           + ExactSizeIterator
           + FusedIterator {
        let type_depth = self.depth_for_type(object_type);
        let depth_iter = (0..self.full_depth())
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

/// # CPU cache statistics
impl Topology {
    /// Compute high-level CPU cache statistics
    ///
    /// These statistics can be used in scenarios where you're not yet ready for
    /// full locality-aware scheduling but just want to make sure that your code
    /// will use CPU caches sensibly no matter which CPU core it's running on.
    ///
    /// This functionality is unique to the Rust hwloc bindings.
    ///
    /// # Examples
    ///
    /// ```
    /// # let topology = hwlocality::Topology::test_instance();
    /// let stats = topology.cpu_cache_stats();
    /// println!(
    ///     "Minimal data cache sizes per level: {:?}",
    ///     stats.smallest_data_cache_sizes()
    /// );
    /// println!(
    ///     "Total data cache size per level: {:?}",
    ///     stats.total_data_cache_sizes()
    /// );
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn cpu_cache_stats(&self) -> CPUCacheStats {
        CPUCacheStats::new(self)
    }
}

/// # CPU binding
///
/// Some operating systems do not provide all hwloc-supported mechanisms to bind
/// processes, threads, etc. [`Topology::feature_support()`] may be used to
/// query about the actual CPU binding support in the currently used operating
/// system. Individual CPU binding functions will clarify which support flags
/// they require.
///
/// You should specify one of the [`ASSUME_SINGLE_THREAD`], [`THREAD`] and
/// [`PROCESS`] flags (listed in order of decreasing portability) when using any
/// of the functions that target a process, but some functions may only support
/// a subset of these flags.
///
/// [`ASSUME_SINGLE_THREAD`]: CpuBindingFlags::ASSUME_SINGLE_THREAD
/// [`PROCESS`]: CpuBindingFlags::PROCESS
/// [`singlify()`]: Bitmap::singlify()
/// [`THREAD`]: CpuBindingFlags::THREAD
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpubinding.html
impl Topology {
    /// Binds the current process or thread on given CPUs
    ///
    /// Some operating systems only support binding threads or processes to a
    /// single PU. Others allow binding to larger sets such as entire Cores or
    /// Packages or even random sets of individual PUs. In such operating
    /// systems, the scheduler is free to run the task on one of these PU, then
    /// migrate it to another PU, etc. It is often useful to call `singlify()`
    /// on the target CPU set before passing it to the binding function to avoid
    /// these expensive migrations. See the documentation of
    /// [`Bitmap::singlify()`] for details.
    ///
    /// By default, when the requested binding operation is not available, hwloc
    /// will go for a similar binding operation (with side-effects, smaller
    /// binding set, etc). You can inhibit this with flag [`STRICT`], at the
    /// expense of reducing portability across operating systems.
    ///
    /// To unbind, just call the binding function with either a full cpuset or a
    /// cpuset equal to the system cpuset.
    ///
    /// On some operating systems, CPU binding may have effects on memory
    /// binding, you can forbid this with flag [`NO_MEMORY_BINDING`].
    ///
    /// Running `lstopo --top` or `hwloc-ps` can be a very convenient tool to
    /// check how binding actually happened.
    ///
    /// Requires [`CpuBindingSupport::set_current_process()`] or
    /// [`CpuBindingSupport::set_current_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`BadObject(ThisProgram)`] if it is not possible to bind the current
    ///   process/thread to CPUs, generally speaking.
    /// - [`BadCpuSet`] if it is not possible to bind the current process/thread
    ///   to the requested CPU set, specifically.
    /// - [`BadFlags`] if flags [`PROCESS`] and [`THREAD`] were both specified.
    ///
    /// [`BadCpuSet`]: CpuBindingError::BadCpuSet
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ThisProgram)`]: CpuBindingFlags::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`STRICT`]: CpuBindingFlags::STRICT
    /// [`THREAD`]: CpuBindingFlags::THREAD
    pub fn bind_cpu(&self, set: &CpuSet, flags: CpuBindingFlags) -> Result<(), CpuBindingError> {
        self.bind_cpu_impl(
            set,
            flags,
            CpuBoundObject::ThisProgram,
            "hwloc_set_cpubind",
            |topology, cpuset, flags| unsafe { ffi::hwloc_set_cpubind(topology, cpuset, flags) },
        )
    }

    /// Get the current process or thread CPU binding
    ///
    /// Flag [`NO_MEMORY_BINDING`] should not be used with this function.
    ///
    /// Requires [`CpuBindingSupport::get_current_process()`] or
    /// [`CpuBindingSupport::get_current_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`BadObject(ThisProgram)`] if it is not possible to query the CPU
    ///   binding of the current process/thread.
    /// - [`BadFlags`] if flag [`NO_MEMORY_BINDING`] was specified or if
    ///   flags [`PROCESS`] and [`THREAD`] were both specified.
    ///
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ThisProgram)`]: CpuBindingFlags::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`THREAD`]: CpuBindingFlags::THREAD
    pub fn cpu_binding(&self, flags: CpuBindingFlags) -> Result<CpuSet, CpuBindingError> {
        self.cpu_binding_impl(
            flags,
            CpuBoundObject::ThisProgram,
            "hwloc_get_cpubind",
            |topology, cpuset, flags| unsafe { ffi::hwloc_get_cpubind(topology, cpuset, flags) },
        )
    }

    /// Binds a process (identified by its `pid`) on given CPUs
    ///
    /// As a special case on Linux, if a tid (thread ID) is supplied instead of
    /// a pid (process ID) and flag [`THREAD`] is specified, the specified
    /// thread is bound. Otherwise, flag [`THREAD`] should not be used with this
    /// function.
    ///
    /// See [`Topology::bind_cpu()`] for more informations, except this
    /// requires [`CpuBindingSupport::set_process()`] or
    /// [`CpuBindingSupport::set_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`BadObject(ProcessOrThread)`] if it is not possible to bind the
    ///   target process/thread to CPUs, generally speaking.
    /// - [`BadCpuSet`] if it is not possible to bind the target process/thread
    ///   to the requested CPU set, specifically.
    /// - [`BadFlags`] if flag [`THREAD`] was specified on an operating system
    ///   other than Linux, or if flags [`PROCESS`] and [`THREAD`] were both
    ///   specified.
    ///
    /// [`BadCpuSet`]: CpuBindingError::BadCpuSet
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ProcessOrThread)`]: CpuBindingFlags::BadObject
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`THREAD`]: CpuBindingFlags::THREAD
    pub fn bind_process_cpu(
        &self,
        pid: ProcessId,
        set: &CpuSet,
        flags: CpuBindingFlags,
    ) -> Result<(), CpuBindingError> {
        self.bind_cpu_impl(
            set,
            flags,
            CpuBoundObject::ProcessOrThread,
            "hwloc_set_proc_cpubind",
            |topology, cpuset, flags| unsafe {
                ffi::hwloc_set_proc_cpubind(topology, pid, cpuset, flags)
            },
        )
    }

    /// Get the current physical binding of a process, identified by its `pid`
    ///
    /// As a special case on Linux, if a tid (thread ID) is supplied instead of
    /// a pid (process ID) and flag [`THREAD`] is specified, the binding of the
    /// specified thread is returned. Otherwise, flag [`THREAD`] should not be
    /// used with this function.
    ///
    /// Flag [`NO_MEMORY_BINDING`] should not be used with this function.
    ///
    /// Requires [`CpuBindingSupport::get_process()`] or
    /// [`CpuBindingSupport::get_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`BadObject(ProcessOrThread)`] if it is not possible to query the CPU
    ///   binding of the target process/thread.
    /// - [`BadFlags`] if flag [`NO_MEMORY_BINDING`] was specified, if flag
    ///   [`THREAD`] was specified on an operating system other than Linux, or
    ///   if flags [`PROCESS`] and [`THREAD`] were both specified.
    ///
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ProcessOrThread)`]: CpuBindingFlags::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`THREAD`]: CpuBindingFlags::THREAD
    pub fn process_cpu_binding(
        &self,
        pid: ProcessId,
        flags: CpuBindingFlags,
    ) -> Result<CpuSet, CpuBindingError> {
        self.cpu_binding_impl(
            flags,
            CpuBoundObject::ProcessOrThread,
            "hwloc_get_proc_cpubind",
            |topology, cpuset, flags| unsafe {
                ffi::hwloc_get_proc_cpubind(topology, pid, cpuset, flags)
            },
        )
    }

    /// Bind a thread, identified by its `tid`, on the given CPUs
    ///
    /// Flag [`PROCESS`] should not be used with this function.
    ///
    /// See [`Topology::bind_cpu()`] for more informations, except this always
    /// requires [`CpuBindingSupport::set_thread()`].
    ///
    /// # Errors
    ///
    /// - [`BadObject(Thread)`] if it is not possible to bind the target thread
    ///   to CPUs, generally speaking.
    /// - [`BadCpuSet`] if it is not possible to bind the target thread to the
    ///   requested CPU set, specifically.
    /// - [`BadFlags`] if flag [`PROCESS`] was specified.
    ///
    /// [`BadCpuSet`]: CpuBindingError::BadCpuSet
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(Thread)`]: CpuBindingFlags::BadObject
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    pub fn bind_thread_cpu(
        &self,
        tid: ThreadId,
        set: &CpuSet,
        flags: CpuBindingFlags,
    ) -> Result<(), CpuBindingError> {
        self.bind_cpu_impl(
            set,
            flags,
            CpuBoundObject::Thread,
            "hwloc_set_thread_cpubind",
            |topology, cpuset, flags| unsafe {
                ffi::hwloc_set_thread_cpubind(topology, tid, cpuset, flags)
            },
        )
    }

    /// Get the current physical binding of thread `tid`
    ///
    /// Flags [`PROCESS`], [`STRICT`] and [`NO_MEMORY_BINDING`] should not be
    /// used with this function.
    ///
    /// Requires [`CpuBindingSupport::get_thread()`].
    ///
    /// # Errors
    ///
    /// - [`BadObject(Thread)`] if it is not possible to query the CPU
    ///   binding of the target thread.
    /// - [`BadFlags`] if at least one of the flags [`PROCESS`], [`STRICT`] and
    ///   [`NO_MEMORY_BINDING`] was specified.
    ///
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(Thread)`]: CpuBindingFlags::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`STRICT`]: CpuBindingFlags::STRICT
    pub fn thread_cpu_binding(
        &self,
        tid: ThreadId,
        flags: CpuBindingFlags,
    ) -> Result<CpuSet, CpuBindingError> {
        self.cpu_binding_impl(
            flags,
            CpuBoundObject::Thread,
            "hwloc_get_thread_cpubind",
            |topology, cpuset, flags| unsafe {
                ffi::hwloc_get_thread_cpubind(topology, tid, cpuset, flags)
            },
        )
    }

    /// Get the last physical CPUs where the current process or thread ran
    ///
    /// The operating system may move some tasks from one processor
    /// to another at any time according to their binding,
    /// so this function may return something that is already
    /// outdated.
    ///
    /// Flag [`NO_MEMORY_BINDING`] should not be used with this function.
    ///
    /// Requires [`CpuBindingSupport::get_current_process_last_cpu_location()`]
    /// or [`CpuBindingSupport::get_current_thread_last_cpu_location()`]
    /// depending on flags.
    ///
    /// # Errors
    ///
    /// - [`BadObject(ThisProgram)`] if it is not possible to query the CPU
    ///   location of the current process/thread.
    /// - [`BadFlags`] if flag [`NO_MEMORY_BINDING`] was specified or if
    ///   flags [`PROCESS`] and [`THREAD`] were both specified.
    ///
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ThisProgram)`]: CpuBindingFlags::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`THREAD`]: CpuBindingFlags::THREAD
    pub fn last_cpu_location(&self, flags: CpuBindingFlags) -> Result<CpuSet, CpuBindingError> {
        self.last_cpu_location_impl(
            flags,
            CpuBoundObject::ThisProgram,
            "hwloc_get_last_cpu_location",
            |topology, cpuset, flags| unsafe {
                ffi::hwloc_get_last_cpu_location(topology, cpuset, flags)
            },
        )
    }

    /// Get the last physical CPU where a process ran.
    ///
    /// The operating system may move some tasks from one processor to another
    /// at any time according to their binding, so this function may return
    /// something that is already outdated.
    ///
    /// As a special case on Linux, if a tid (thread ID) is supplied instead of
    /// a pid (process ID) and flag [`THREAD`] is specified, the last cpu
    /// location of the specified thread is returned. Otherwise, flag [`THREAD`]
    /// should not be used with this function.
    ///
    /// Flag [`NO_MEMORY_BINDING`] should not be used with this function.
    ///
    /// Requires [`CpuBindingSupport::get_process_last_cpu_location()`].
    ///
    /// # Errors
    ///
    /// - [`BadObject(ProcessOrThread)`] if it is not possible to query the CPU
    ///   binding of the target process/thread.
    /// - [`BadFlags`] if flag [`NO_MEMORY_BINDING`] was specified, if flag
    ///   [`THREAD`] was specified on an operating system other than Linux, or
    ///   if flags [`PROCESS`] and [`THREAD`] were both specified.
    ///
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ProcessOrThread)`]: CpuBindingFlags::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`THREAD`]: CpuBindingFlags::THREAD
    pub fn last_process_cpu_location(
        &self,
        pid: ProcessId,
        flags: CpuBindingFlags,
    ) -> Result<CpuSet, CpuBindingError> {
        self.last_cpu_location_impl(
            flags,
            CpuBoundObject::ProcessOrThread,
            "hwloc_get_proc_last_cpu_location",
            |topology, cpuset, flags| unsafe {
                ffi::hwloc_get_proc_last_cpu_location(topology, pid, cpuset, flags)
            },
        )
    }

    /// Binding for set_cpubind style functions
    fn bind_cpu_impl(
        &self,
        set: &CpuSet,
        flags: CpuBindingFlags,
        target: CpuBoundObject,
        api: &'static str,
        ffi: impl FnOnce(*const RawTopology, *const RawBitmap, c_int) -> c_int,
    ) -> Result<(), CpuBindingError> {
        if !flags.is_valid(target, CpuBindingOperation::SetBinding) {
            return Err(CpuBindingError::BadFlags(flags.into()));
        }
        cpu::binding::call_hwloc(api, target, Some(set), || {
            ffi(self.as_ptr(), set.as_ptr(), flags.bits() as i32)
        })
    }

    /// Binding for get_cpubind style functions
    fn cpu_binding_impl(
        &self,
        flags: CpuBindingFlags,
        target: CpuBoundObject,
        api: &'static str,
        ffi: impl FnOnce(*const RawTopology, *mut RawBitmap, c_int) -> c_int,
    ) -> Result<CpuSet, CpuBindingError> {
        self.get_cpuset(flags, target, CpuBindingOperation::GetBinding, api, ffi)
    }

    /// Binding for get_last_cpu_location style functions
    fn last_cpu_location_impl(
        &self,
        flags: CpuBindingFlags,
        target: CpuBoundObject,
        api: &'static str,
        ffi: impl FnOnce(*const RawTopology, *mut RawBitmap, c_int) -> c_int,
    ) -> Result<CpuSet, CpuBindingError> {
        self.get_cpuset(
            flags,
            target,
            CpuBindingOperation::GetLastLocation,
            api,
            ffi,
        )
    }

    /// Binding for all functions that get CPU bindings
    fn get_cpuset(
        &self,
        flags: CpuBindingFlags,
        target: CpuBoundObject,
        operation: CpuBindingOperation,
        api: &'static str,
        ffi: impl FnOnce(*const RawTopology, *mut RawBitmap, c_int) -> c_int,
    ) -> Result<CpuSet, CpuBindingError> {
        if !flags.is_valid(target, operation) {
            return Err(CpuBindingError::BadFlags(flags.into()));
        }
        let mut cpuset = CpuSet::new();
        cpu::binding::call_hwloc(api, target, None, || {
            ffi(self.as_ptr(), cpuset.as_mut_ptr(), flags.bits() as i32)
        })
        .map(|()| cpuset)
    }
}

/// # Memory binding
///
/// Memory binding can be done three ways:
///
/// - Explicit memory allocation through [`allocate_bound_memory()`] and friends:
///   the binding will have effect on the memory allocated by these functions.
/// - Implicit memory binding through process/thread binding policy through
///   [`bind_memory()`] and friends: the binding will be applied to subsequent
///   memory allocations by the target process/thread.
/// - Migration of existing memory ranges through [`bind_area()`] and friends:
///   already-allocated data will be migrated to the target NUMA nodes.
///
/// Not all operating systems support all three ways.
/// [`Topology::feature_support()`] may be used to query about the actual memory
/// binding support in the currently used operating system. Individual memory
/// binding functions will clarify which support flags they require. The most
/// portable operation, where usable, is [`binding_allocate_memory()`].
///
/// Memory can be bound by [`CpuSet`] or [`NodeSet`], but memory binding by
/// CPU set cannot work for CPU-less NUMA memory nodes. Binding by node set
/// should therefore be preferred whenever possible.
///
/// You should specify one of the [`ASSUME_SINGLE_THREAD`], [`THREAD`] and
/// [`PROCESS`] flags (listed in order of decreasing portability) when using any
/// of the functions that target a process, but some functions may only support
/// a subset of these flags.
///
/// On some operating systems, memory binding affects CPU binding. You can avoid
/// this at the cost of reducing portability by specifying the
/// [`NO_CPU_BINDING`] flag.
///
/// [`allocate_bound_memory()`]: Topology::allocate_bound_memory()
/// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
/// [`bind_area()`]: Topology::bind_area()
/// [`bind_memory()`]: Topology::bind_memory()
/// [`NO_CPU_BINDING`]: MemoryBindingFlags::NO_CPU_BINDING
/// [`PROCESS`]: MemoryBindingFlags::PROCESS
/// [`THREAD`]: MemoryBindingFlags::THREAD
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__membinding.html
impl Topology {
    /// Allocate some memory
    ///
    /// This is equivalent to [`libc::malloc()`], except that it tries to
    /// allocate page-aligned memory from the OS.
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot allocate page-aligned memory
    /// - [`AllocationFailed`] if memory allocation failed
    ///
    /// [`AllocationFailed`]: MemoryBindingError::AllocationFailed
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    pub fn allocate_memory(&self, len: usize) -> Result<Bytes, MemoryAllocationError<NodeSet>> {
        self.allocate_memory_impl(len)
    }

    /// Like allocate_memory, but polymorphic on Set
    fn allocate_memory_impl<Set: SpecializedBitmap>(
        &self,
        len: usize,
    ) -> Result<Bytes, MemoryAllocationError<Set>> {
        memory::binding::call_hwloc_allocate("hwloc_alloc", None, || unsafe {
            ffi::hwloc_alloc(self.as_ptr(), len)
        })
        .map(|base| unsafe { Bytes::wrap(self, base, len) })
    }

    /// Allocate some memory on NUMA nodes specified by `set`
    ///
    /// If you do not care about changing the binding of the current process or
    /// thread, you can maximize portability by using
    /// [`Topology::binding_allocate_memory()`] instead.
    ///
    /// Memory can be bound by either [`CpuSet`] or [`NodeSet`]. Binding by
    /// [`NodeSet`] is preferred because some NUMA memory nodes are not attached
    /// to CPUs, and thus cannot be bound by [`CpuSet`].
    ///
    /// Flags [`ASSUME_SINGLE_THREAD`], [`PROCESS`], [`THREAD`] and [`MIGRATE`]
    /// should not be used with this function.
    ///
    /// Requires [`MemoryBindingSupport::alloc()`].
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot allocate bound memory with the
    ///   requested policy
    /// - [`BadFlags`] if one of the flags [`MIGRATE`], [`PROCESS`] and
    ///   [`THREAD`] is specified
    /// - [`BadSet`] if the system can't bind memory to that CPU/node set
    /// - [`AllocationFailed`] if memory allocation failed
    ///
    /// [`AllocationFailed`]: MemoryBindingError::AllocationFailed
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadSet`]: MemoryBindingError::BadSet
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    pub fn allocate_bound_memory<Set: SpecializedBitmap>(
        &self,
        len: usize,
        set: &Set,
        policy: MemoryBindingPolicy,
        mut flags: MemoryBindingFlags,
    ) -> Result<Bytes, MemoryAllocationError<Set>> {
        Self::adjust_flags_for::<Set>(&mut flags);
        if !flags.is_valid(MemoryBoundObject::Area, MemoryBindingOperation::Allocate) {
            return Err(MemoryAllocationError::BadFlags(flags.into()));
        }
        memory::binding::call_hwloc_allocate("hwloc_alloc_membind", Some(set), || unsafe {
            ffi::hwloc_alloc_membind(
                self.as_ptr(),
                len,
                set.as_ref().as_ptr(),
                policy.into(),
                flags.bits(),
            )
        })
        .map(|base| unsafe { Bytes::wrap(self, base, len) })
    }

    /// Allocate some memory on NUMA nodes specified by `set` and `flags`,
    /// possibly rebinding current process or thread if needed
    ///
    /// This works like [`Topology::allocate_bound_memory()`] unless the
    /// allocation fails, in which case hwloc will attempt to change the current
    /// process or thread memory binding policy as directed instead before
    /// performing a normal allocation.
    ///
    /// Allocating memory that matches the current process/thread configuration
    /// is supported on more operating systems, so this is the most portable way
    /// to obtain a bound memory buffer.
    ///
    /// You should specify one of the [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and
    /// [`THREAD`] flags when using this function.
    ///
    /// Requires either [`MemoryBindingSupport::alloc()`], or one of
    /// [`MemoryBindingSupport::set_current_process()`] and
    /// [`MemoryBindingSupport::set_current_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system can neither allocate bound memory
    ///   nor rebind the current thread/process with the requested policy
    /// - [`BadFlags`] if flags [`PROCESS`] and [`THREAD`] were both specified
    /// - [`BadSet`] if the system can't bind memory to that CPU/node set
    /// - [`AllocationFailed`] if memory allocation failed
    ///
    /// [`AllocationFailed`]: MemoryBindingError::AllocationFailed
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadSet`]: MemoryBindingError::BadSet
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    pub fn binding_allocate_memory<Set: SpecializedBitmap>(
        &self,
        len: usize,
        set: &Set,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<Bytes, MemoryAllocationError<Set>> {
        // Try allocate_bound_memory first
        if let Ok(bytes) = self.allocate_bound_memory(len, set, policy, flags) {
            return Ok(bytes);
        }

        // If that doesn't work, try binding the current process
        self.bind_memory(set, policy, flags)?;

        // If that succeeds, try allocating more memory
        let mut bytes = self.allocate_memory_impl(len)?;

        // Depending on policy, we may or may not need to touch the memory to
        // enforce the binding
        match policy {
            MemoryBindingPolicy::FirstTouch | MemoryBindingPolicy::NextTouch => {}
            MemoryBindingPolicy::Bind | MemoryBindingPolicy::Interleave => {
                for b in &mut bytes[..] {
                    *b = MaybeUninit::new(0);
                }
            }
        }
        Ok(bytes)
    }

    /// Set the default memory binding policy of the current process or thread
    /// to prefer the NUMA node(s) specified by `set`.
    ///
    /// Memory can be bound by either [`CpuSet`] or [`NodeSet`]. Binding by
    /// [`NodeSet`] is preferred because some NUMA memory nodes are not attached
    /// to CPUs, and thus cannot be bound by [`CpuSet`].
    ///
    /// You should specify one of the [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and
    /// [`THREAD`] flags when using this function.
    ///
    /// Requires [`MemoryBindingSupport::set_current_process()`] or
    /// [`MemoryBindingSupport::set_current_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot bind the current
    ///   thread/process with the requested policy
    /// - [`BadFlags`] if flags [`PROCESS`] and [`THREAD`] were both specified
    /// - [`BadSet`] if the system can't bind memory to that CPU/node set
    ///
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadSet`]: MemoryBindingError::BadSet
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    pub fn bind_memory<Set: SpecializedBitmap>(
        &self,
        set: &Set,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingError<Set>> {
        self.bind_memory_impl(
            "hwloc_set_membind",
            set,
            policy,
            flags,
            MemoryBoundObject::ThisProgram,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_set_membind(topology, set, policy, flags)
            },
        )
    }

    /// Reset the memory allocation policy of the current process or thread to
    /// the system default
    ///
    /// Depending on the operating system, this may correspond to
    /// [`MemoryBindingPolicy::FirstTouch`] (Linux, FreeBSD) or
    /// [`MemoryBindingPolicy::Bind`] (AIX, HP-UX, Solaris, Windows).
    ///
    /// You should specify one of the [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and
    /// [`THREAD`] flags when using this function, but the [`STRICT`] and
    /// [`MIGRATE`] flags should **not** be used with this function.
    ///
    /// Requires [`MemoryBindingSupport::set_current_process()`] or
    /// [`MemoryBindingSupport::set_current_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot unbind the current thread/process
    /// - [`BadFlags`] if one of flags [`STRICT`] and [`MIGRATE`] was specified,
    ///   or if flags [`PROCESS`] and [`THREAD`] were both specified
    ///
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "HWLOC_MEMBIND_DEFAULT")]
    pub fn unbind_memory(
        &self,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingError<NodeSet>> {
        self.unbind_memory_impl(
            "hwloc_set_membind",
            flags,
            MemoryBoundObject::ThisProgram,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_set_membind(topology, set, policy, flags)
            },
        )
    }

    /// Query the default memory binding policy and physical locality of the
    /// current process or thread
    ///
    /// You should specify one of the [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and
    /// [`THREAD`] flags when using this function. However, flags [`MIGRATE`]
    /// and [`NO_CPU_BINDING`] should **not** be used with this function.
    ///
    /// The [`STRICT`] flag is only meaningful when [`PROCESS`] is also
    /// specified. In this case, hwloc will check the default memory policies
    /// and nodesets for all threads in the process. If they are not identical,
    /// Err([`MixedResults`]) is returned. Otherwise,
    /// the shared configuration is returned.
    ///
    /// Otherwise, if [`PROCESS`] is specified and [`STRICT`] is not specified,
    /// the default sets from each thread are logically OR'ed together. If all
    /// threads' default policies are the same, that shared policy is returned,
    /// otherwise no policy is returned.
    ///
    /// In the [`THREAD`] and [`ASSUME_SINGLE_THREAD`] case, there is only one
    /// set and policy, they are returned.
    ///
    /// Bindings can be queried as [`CpuSet`] or [`NodeSet`]. Querying by
    /// [`NodeSet`] is preferred because some NUMA memory nodes are not attached
    /// to CPUs, and thus cannot be bound by [`CpuSet`].
    ///
    /// Requires [`MemoryBindingSupport::get_current_process()`] or
    /// [`MemoryBindingSupport::get_current_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot query the current thread/process
    ///   binding
    /// - [`BadFlags`] if one of flags [`MIGRATE`] and [`NO_CPU_BINDING`] was
    ///   specified, if flags [`PROCESS`] and [`THREAD`] were both specified,
    ///   or if flag [`STRICT`] was specified without [`PROCESS`]
    /// - [`MixedResults`] if flags [`STRICT`] and [`PROCESS`] were specified
    ///   and memory binding is inhomogeneous across threads in the process
    ///
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`MixedResults`]: MemoryBindingError::MixedResults
    /// [`NO_CPU_BINDING`]: MemoryBindingFlags::NO_CPU_BINDING
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    pub fn memory_binding<Set: SpecializedBitmap>(
        &self,
        flags: MemoryBindingFlags,
    ) -> Result<(Set, Option<MemoryBindingPolicy>), MemoryBindingError<Set>> {
        self.memory_binding_impl(
            "hwloc_get_membind",
            flags,
            MemoryBoundObject::ThisProgram,
            MemoryBindingOperation::GetBinding,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_get_membind(topology, set, policy, flags)
            },
        )
    }

    /// Set the default memory binding policy of the specified process to prefer
    /// the NUMA node(s) specified by `set`.
    ///
    /// See also [`Topology::bind_memory()`] for general semantics, except this
    /// function requires [`MemoryBindingSupport::set_process()`].
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot bind the specified
    ///   thread/process with the requested policy
    /// - [`BadFlags`] if flags [`PROCESS`] and [`THREAD`] were both specified
    /// - [`BadSet`] if the system can't bind memory to that CPU/node set
    ///
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadSet`]: MemoryBindingError::BadSet
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    pub fn bind_process_memory<Set: SpecializedBitmap>(
        &self,
        pid: ProcessId,
        set: &Set,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingError<Set>> {
        self.bind_memory_impl(
            "hwloc_set_proc_membind",
            set,
            policy,
            flags,
            MemoryBoundObject::Process,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_set_proc_membind(topology, pid, set, policy, flags)
            },
        )
    }

    /// Reset the memory allocation policy of the specified process to the
    /// system default
    ///
    /// See also [`Topology::unbind_memory()`] for general semantics, except
    /// this function requires [`MemoryBindingSupport::set_process()`].
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot unbind the specified
    ///   thread/process
    /// - [`BadFlags`] if one of flags [`STRICT`] and [`MIGRATE`] was specified,
    ///   or if flags [`PROCESS`] and [`THREAD`] were both specified
    ///
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    pub fn unbind_process_memory(
        &self,
        pid: ProcessId,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingError<NodeSet>> {
        self.unbind_memory_impl(
            "hwloc_set_proc_membind",
            flags,
            MemoryBoundObject::Process,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_set_proc_membind(topology, pid, set, policy, flags)
            },
        )
    }

    /// Query the default memory binding policy and physical locality of the
    /// specified process
    ///
    /// See [`Topology::memory_binding()`] for general semantics, except this
    /// function requires [`MemoryBindingSupport::get_process()`].
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot query the specified
    ///   thread/process' binding
    /// - [`BadFlags`] if one of flags [`MIGRATE`] and [`NO_CPU_BINDING`] was
    ///   specified, if flags [`PROCESS`] and [`THREAD`] were both specified,
    ///   or if flag [`STRICT`] was specified without [`PROCESS`]
    /// - [`MixedResults`] if flags [`STRICT`] and [`PROCESS`] were specified
    ///   and memory binding is inhomogeneous across threads in the process
    ///
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`MixedResults`]: MemoryBindingError::MixedResults
    /// [`NO_CPU_BINDING`]: MemoryBindingFlags::NO_CPU_BINDING
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    pub fn process_memory_binding<Set: SpecializedBitmap>(
        &self,
        pid: ProcessId,
        flags: MemoryBindingFlags,
    ) -> Result<(Set, Option<MemoryBindingPolicy>), MemoryBindingError<Set>> {
        self.memory_binding_impl(
            "hwloc_get_proc_membind",
            flags,
            MemoryBoundObject::Process,
            MemoryBindingOperation::GetBinding,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_get_proc_membind(topology, pid, set, policy, flags)
            },
        )
    }

    /// Bind the memory identified by `target` to the NUMA node(s) specified by
    /// `set`
    ///
    /// Beware that only the memory directly targeted by the `target` reference
    /// will be covered. So for example, you cannot pass in an `&Vec<T>` and
    /// expect the Vec's contents to be covered, instead you must pass in the
    /// `&[T]` corresponding to the Vec's contents as `&vec[..]`. You may want
    /// to manually specify the `Target` type via turbofish to make sure that
    /// you don't get tripped up by references of references like `&&[T]`.
    ///
    /// See also [`Topology::bind_memory()`] for general semantics, except the
    /// [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and [`THREAD`] flags should not be
    /// used with this function, and it requires
    /// [`MemoryBindingSupport::set_area()`].
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot bind the specified memory area
    ///   with the requested policy
    /// - [`BadFlags`] if one of flags [`PROCESS`] and [`THREAD`] was specified
    /// - [`BadSet`] if the system can't bind memory to that CPU/node set
    ///
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadSet`]: MemoryBindingError::BadSet
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    pub fn bind_memory_area<Target: ?Sized, Set: SpecializedBitmap>(
        &self,
        target: &Target,
        set: &Set,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingError<Set>> {
        self.bind_memory_impl(
            "hwloc_set_area_membind",
            set,
            policy,
            flags,
            MemoryBoundObject::Area,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_set_area_membind(
                    topology,
                    target as *const Target as *const c_void,
                    std::mem::size_of_val(target),
                    set,
                    policy,
                    flags,
                )
            },
        )
    }

    /// Reset the memory allocation policy of the memory identified by `target`
    /// to the system default
    ///
    /// The warning about `Target` coverage in the documentation of
    /// [`Topology::bind_memory_area()`] also applies here.
    ///
    /// See also [`Topology::unbind_memory()`] for general semantics, except the
    /// [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and [`THREAD`] flags should not be
    /// used with this function, and it requires
    /// [`MemoryBindingSupport::set_area()`].
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot unbind the specified memory area
    /// - [`BadFlags`] if one of flags [`PROCESS`], [`THREAD`], [`STRICT`]
    ///   and [`MIGRATE`] was specified
    ///
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    pub fn unbind_memory_area<Target: ?Sized>(
        &self,
        target: &Target,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingError<NodeSet>> {
        self.unbind_memory_impl(
            "hwloc_set_area_membind",
            flags,
            MemoryBoundObject::Area,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_set_area_membind(
                    topology,
                    target as *const Target as *const c_void,
                    std::mem::size_of_val(target),
                    set,
                    policy,
                    flags,
                )
            },
        )
    }

    /// Query the memory binding policy and physical locality of the
    /// memory identified by `target`
    ///
    /// The warning about `Target` coverage in the documentation of
    /// [`Topology::bind_memory_area()`] also applies here.
    ///
    /// If the [`STRICT`] flag is specified, hwloc will check the default memory
    /// policies and nodesets for all memory pages covered by `target`. If these
    /// are not identical,
    /// Err([`MemoryBindingQueryError::MixedResults`]) is returned. Otherwise,
    /// the shared configuration is returned.
    ///
    /// If [`STRICT`] is not specified, the union of all NUMA nodes containing
    /// pages in the address range is calculated. If all pages in the target
    /// have the same policy, it is returned, otherwise no policy is returned.
    ///
    /// See also [`Topology::memory_binding()`] for general semantics, except...
    /// - The [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and [`THREAD`] flags should
    ///   not be used with this function
    /// - As mentioned above, [`STRICT`] has a specific meaning in the context
    ///   of this function.
    /// - This function requires [`MemoryBindingSupport::get_area()`].
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot query the specified
    ///   memory area's binding
    /// - [`BadFlags`] if one of flags [`PROCESS`], [`THREAD`], [`MIGRATE`]
    ///   and [`NO_CPU_BINDING`] was specified
    /// - [`MixedResults`] if flags [`STRICT`] and [`PROCESS`] were specified
    ///   and memory binding is inhomogeneous across target memory pages
    ///
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`MixedResults`]: MemoryBindingError::MixedResults
    /// [`NO_CPU_BINDING`]: MemoryBindingFlags::NO_CPU_BINDING
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    pub fn area_memory_binding<Target: ?Sized, Set: SpecializedBitmap>(
        &self,
        target: &Target,
        flags: MemoryBindingFlags,
    ) -> Result<(Set, Option<MemoryBindingPolicy>), MemoryBindingError<Set>> {
        assert!(
            std::mem::size_of_val(target) > 0,
            "Zero-sized target covers no memory!"
        );
        self.memory_binding_impl(
            "hwloc_get_area_membind",
            flags,
            MemoryBoundObject::Area,
            MemoryBindingOperation::GetBinding,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_get_area_membind(
                    topology,
                    target as *const Target as *const c_void,
                    std::mem::size_of_val(target),
                    set,
                    policy,
                    flags,
                )
            },
        )
    }

    /// Get the NUMA nodes where the memory identified by `target` is physically
    /// allocated
    ///
    /// The warning about `Target` coverage in the documentation of
    /// [`Topology::bind_memory_area()`] also applies here.
    ///
    /// If pages spread to multiple nodes, it is not specified whether they
    /// spread equitably, or whether most of them are on a single node, etc.
    ///
    /// The operating system may move memory pages from one processor to another
    /// at any time according to their binding, so this function may return
    /// something that is already outdated.
    ///
    /// See also [`Topology::memory_binding()`] for general semantics, except
    /// the [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and [`THREAD`] flags should
    /// not be used with this function, and it requires
    /// [`MemoryBindingSupport::get_area_memory_location()`].
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot query the specified
    ///   memory area's location
    /// - [`BadFlags`] if one of flags [`PROCESS`], [`THREAD`], [`MIGRATE`]
    ///   and [`NO_CPU_BINDING`] was specified
    /// - [`MixedResults`] if flags [`STRICT`] and [`PROCESS`] were specified
    ///   and memory binding is inhomogeneous across target memory pages
    ///
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`MixedResults`]: MemoryBindingError::MixedResults
    /// [`NO_CPU_BINDING`]: MemoryBindingFlags::NO_CPU_BINDING
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    pub fn area_memory_location<Target: ?Sized, Set: SpecializedBitmap>(
        &self,
        target: &Target,
        flags: MemoryBindingFlags,
    ) -> Result<Set, MemoryBindingError<Set>> {
        self.memory_binding_impl(
            "hwloc_get_area_memlocation",
            flags,
            MemoryBoundObject::ThisProgram,
            MemoryBindingOperation::GetLastLocation,
            |topology, set, policy, flags| unsafe {
                *policy = -1;
                ffi::hwloc_get_area_memlocation(
                    topology,
                    target as *const Target as *const c_void,
                    std::mem::size_of_val(target),
                    set,
                    flags,
                )
            },
        )
        .map(|(set, _policy)| set)
    }

    /// Adjust binding flags for a certain kind of Set
    fn adjust_flags_for<Set: SpecializedBitmap>(flags: &mut MemoryBindingFlags) {
        match Set::BITMAP_KIND {
            BitmapKind::CpuSet => flags.remove(MemoryBindingFlags::BY_NODE_SET),
            BitmapKind::NodeSet => flags.insert(MemoryBindingFlags::BY_NODE_SET),
        }
    }

    /// Call an hwloc memory binding function to bind some memory
    fn bind_memory_impl<Set: SpecializedBitmap>(
        &self,
        api: &'static str,
        set: &Set,
        policy: MemoryBindingPolicy,
        mut flags: MemoryBindingFlags,
        target: MemoryBoundObject,
        set_membind_like: impl FnOnce(
            *const RawTopology,
            *const RawBitmap,
            RawMemoryBindingPolicy,
            c_int,
        ) -> c_int,
    ) -> Result<(), MemoryBindingError<Set>> {
        let operation = MemoryBindingOperation::Bind;
        Self::adjust_flags_for::<Set>(&mut flags);
        if !flags.is_valid(target, operation) {
            return Err(MemoryBindingError::BadFlags(flags.into()));
        }
        memory::binding::call_hwloc_int(api, target, operation, Some(set), || {
            set_membind_like(
                self.as_ptr(),
                set.as_ref().as_ptr(),
                policy.into(),
                flags.bits(),
            )
        })
    }

    /// Call an hwloc memory binding function to unbind some memory
    fn unbind_memory_impl(
        &self,
        api: &'static str,
        flags: MemoryBindingFlags,
        target: MemoryBoundObject,
        set_membind_like: impl FnOnce(
            *const RawTopology,
            *const RawBitmap,
            RawMemoryBindingPolicy,
            c_int,
        ) -> c_int,
    ) -> Result<(), MemoryBindingError<NodeSet>> {
        let operation = MemoryBindingOperation::Unbind;
        if !flags.is_valid(target, operation) {
            return Err(MemoryBindingError::BadFlags(flags.into()));
        }
        memory::binding::call_hwloc_int(api, target, operation, None, || {
            set_membind_like(self.as_ptr(), ptr::null(), 0, flags.bits())
        })
    }

    /// Call an hwloc memory binding query function
    fn memory_binding_impl<Set: SpecializedBitmap>(
        &self,
        api: &'static str,
        mut flags: MemoryBindingFlags,
        target: MemoryBoundObject,
        operation: MemoryBindingOperation,
        get_membind_like: impl FnOnce(
            *const RawTopology,
            *mut RawBitmap,
            *mut RawMemoryBindingPolicy,
            c_int,
        ) -> c_int,
    ) -> Result<(Set, Option<MemoryBindingPolicy>), MemoryBindingError<Set>> {
        Self::adjust_flags_for::<Set>(&mut flags);
        if !flags.is_valid(target, operation) {
            return Err(MemoryBindingError::BadFlags(flags.into()));
        }
        let mut set = Bitmap::new();
        let mut raw_policy = 0;
        memory::binding::call_hwloc_int(api, target, operation, None, || {
            get_membind_like(
                self.as_ptr(),
                set.as_mut_ptr(),
                &mut raw_policy,
                flags.bits(),
            )
        })
        .map(|()| {
            let policy = match MemoryBindingPolicy::try_from(raw_policy) {
                Ok(policy) => Some(policy),
                Err(TryFromPrimitiveError { number: -1 }) => None,
                Err(TryFromPrimitiveError { number }) => {
                    panic!("Got unexpected memory policy #{number}")
                }
            };
            (set.into(), policy)
        })
    }
}

/// # Modifying a loaded `Topology`
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__tinker.html
impl Topology {
    /// Modify this topology
    ///
    /// hwloc employs lazy caching patterns that do not interact well with
    /// Rust's shared XOR mutable aliasing model. This API lets you safely
    /// modify the active `Topology` through a [`TopologyEditor`] proxy object,
    /// with the guarantee that by the time `Topology::edit()` returns, the
    /// `Topology` will be back in a state where it is safe to use `&self` again.
    pub fn edit<R>(&mut self, edit: impl UnwindSafe + FnOnce(&mut TopologyEditor) -> R) -> R {
        // Set up topology editing
        let mut editor = TopologyEditor::new(self);
        let mut editor = AssertUnwindSafe(&mut editor);

        // Run the user-provided edit callback, catching panics
        let result = std::panic::catch_unwind(move || edit(&mut editor));

        // Force eager evaluation of all caches
        self.refresh();

        // Return user callback result or resume unwinding as appropriate
        match result {
            Ok(result) => result,
            Err(e) => std::panic::resume_unwind(e),
        }
    }

    /// Force eager evaluation of all lazily evaluated caches in preparation for
    /// using or exposing &self
    ///
    /// # Aborts
    ///
    /// A process abort will occur if this fails as we must not let an invalid
    /// `Topology` state escape, not even via unwinding, as that would result in
    /// undefined behavior (mutation which the compiler assumes will not happen).
    pub(crate) fn refresh(&mut self) {
        let refresh_result = unsafe { ffi::hwloc_topology_refresh(self.as_mut_ptr()) };
        if refresh_result < 0 {
            eprintln!("Topology stuck in a state that violates Rust aliasing rules, must abort");
            std::process::abort();
        }
    }
}

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

/// # CPU and node sets of entire topologies
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__topology__sets.html
impl Topology {
    /// Topology CPU set
    ///
    /// This is equivalent to calling [`TopologyObject::cpuset()`] on
    /// the topology's root object.
    pub fn cpuset(&self) -> &CpuSet {
        self.topology_set(|topology| unsafe { ffi::hwloc_topology_get_topology_cpuset(topology) })
    }

    /// Complete CPU set
    ///
    /// This is equivalent to calling [`TopologyObject::complete_cpuset()`] on
    /// the topology's root object.
    pub fn complete_cpuset(&self) -> &CpuSet {
        self.topology_set(|topology| unsafe { ffi::hwloc_topology_get_complete_cpuset(topology) })
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
    pub fn allowed_cpuset(&self) -> &CpuSet {
        self.topology_set(|topology| unsafe { ffi::hwloc_topology_get_allowed_cpuset(topology) })
    }

    /// Topology node set
    ///
    /// This is equivalent to calling [`TopologyObject::nodeset()`] on
    /// the topology's root object.
    pub fn nodeset(&self) -> &NodeSet {
        self.topology_set(|topology| unsafe { ffi::hwloc_topology_get_topology_nodeset(topology) })
    }

    /// Complete node set
    ///
    /// This is equivalent to calling [`TopologyObject::complete_nodeset()`] on
    /// the topology's root object.
    pub fn complete_nodeset(&self) -> &NodeSet {
        self.topology_set(|topology| unsafe { ffi::hwloc_topology_get_complete_nodeset(topology) })
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
    pub fn allowed_nodeset(&self) -> &NodeSet {
        self.topology_set(|topology| unsafe { ffi::hwloc_topology_get_allowed_nodeset(topology) })
    }

    fn topology_set<'topology, Set: SpecializedBitmap>(
        &'topology self,
        getter: impl Fn(*const RawTopology) -> *const RawBitmap,
    ) -> &Set {
        Set::from_bitmap_ref(
            unsafe {
                let bitmap_ptr = getter(self.as_ptr());
                let bitmap_ref = std::mem::transmute::<
                    &*const RawBitmap,
                    &'topology *const RawBitmap,
                >(&bitmap_ptr);
                Bitmap::borrow_from_raw(bitmap_ref)
            }
            .expect("Topology bitmap getters should return non-null bitmaps"),
        )
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

/// # Exporting Topologies to XML
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__xmlexport.html
impl Topology {
    /// Export the topology into an XML file at filesystem location `path`
    ///
    /// If no path is given, the XML output is sent to standard output.
    ///
    /// This file may be loaded later using [`TopologyBuilder::from_xml_file()`].
    ///
    /// By default, the latest export format is used, which means older hwloc
    /// releases (e.g. v1.x) will not be able to import it. Exporting to v1.x
    /// specific XML format is possible using flag
    /// [`XMLExportFlags::V1`] but it may miss some details about the topology.
    /// Also, note that this option will be removed from the (upcoming at the
    /// time of writing) hwloc v3.0 release.
    ///
    /// If there is any chance that the exported file may ever be imported back
    /// by a process using hwloc 1.x, one should consider detecting it at
    /// runtime and using the corresponding export format.
    ///
    /// Only printable characters may be exported to XML string attributes. Any
    /// other character, especially any non-ASCII character, will be silently
    /// dropped.
    ///
    /// # Errors
    ///
    /// - [`NulError`] if `path` contains NUL chars.
    #[doc(alias = "hwloc_topology_export_xml")]
    pub fn export_xml_file(
        &self,
        path: Option<impl AsRef<Path>>,
        flags: XMLExportFlags,
    ) -> Result<(), XMLFileExportError> {
        let path = if let Some(path) = path {
            export::make_hwloc_path(path.as_ref())?
        } else {
            export::make_hwloc_path(Path::new("-"))?
        };
        unsafe {
            errors::call_hwloc_int("hwloc_topology_export_xml", || {
                ffi::hwloc_topology_export_xml(self.as_ptr(), path.borrow(), flags.bits())
            })?
        };
        Ok(())
    }

    /// Export the topology into an XML memory buffer
    ///
    /// This memory buffer may be loaded later using
    /// [`TopologyBuilder::from_xml()`].
    ///
    /// By default, the latest export format is used, which means older hwloc
    /// releases (e.g. v1.x) will not be able to import it. Exporting to v1.x
    /// specific XML format is possible using flag
    /// [`XMLExportFlags::V1`] but it may miss some details about the topology.
    /// Also, note that this option will be removed from the (upcoming at the
    /// time of writing) hwloc v3.0 release.
    ///
    /// If there is any chance that the exported file may ever be imported back
    /// by a process using hwloc 1.x, one should consider detecting it at
    /// runtime and using the corresponding export format.
    ///
    /// Only printable characters may be exported to XML string attributes. Any
    /// other character, especially any non-ASCII character, will be silently
    /// dropped.
    #[doc(alias = "hwloc_topology_export_xmlbuffer")]
    pub fn export_xml(&self, flags: XMLExportFlags) -> Result<XML, Errno> {
        let mut xmlbuffer = ptr::null_mut();
        let mut buflen = 0;
        let result = unsafe {
            ffi::hwloc_topology_export_xmlbuffer(
                self.as_ptr(),
                &mut xmlbuffer,
                &mut buflen,
                flags.bits(),
            )
        };
        match result {
            0 => Ok(unsafe { XML::wrap(self, xmlbuffer, buflen) }
                .expect("Got null pointer from hwloc_topology_export_xmlbuffer")),
            -1 => Err(errno()),
            other => {
                unreachable!("Unexpected return value from hwloc_topology_export_xml: {other}")
            }
        }
    }
}

/// # Exporting Topologies to Synthetic
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__syntheticexport.html
impl Topology {
    /// Export the topology as a synthetic string
    ///
    /// I/O and Misc children are ignored, the synthetic string only describes
    /// normal children.
    ///
    /// By default, the exported topology is only meant to be compatible with
    /// the latest hwloc version. You may want to set some of the `flags` to be
    /// compatible with older hwloc releases, at the cost of dropping support
    /// for newer features.
    ///
    /// # Errors
    ///
    /// Synthetic topologies cannot express the full range of hardware
    /// topologies supported by hwloc, for example they don't support asymmetric
    /// topologies. An error will be returned if the current topology cannot be
    /// expressed as a synthetic topology.
    #[doc(alias = "hwloc_topology_export_synthetic")]
    pub fn export_synthetic(&self, flags: SyntheticExportFlags) -> Result<String, Errno> {
        let mut buf = vec![0u8; 1024];
        loop {
            let result = unsafe {
                ffi::hwloc_topology_export_synthetic(
                    self.as_ptr(),
                    buf.as_mut_ptr() as *mut c_char,
                    buf.len(),
                    flags.bits(),
                )
            };
            match result {
                len if len >= 0 => {
                    if usize::try_from(len).expect("Should fit if I can build the vec")
                        == buf.len() - 1
                    {
                        // hwloc exactly filled the buffer, which suggests the
                        // output was truncated. Try a larget buffer.
                        buf.resize(2 * buf.len(), 0);
                        continue;
                    } else {
                        // Buffer seems alright, return it
                        return Ok(CString::from_vec_with_nul(buf)
                            .expect("Missing NUL from hwloc")
                            .into_string()
                            .expect("Synthetic export should yield an ASCII string"));
                    }
                }
                // An error occured
                -1 => return Err(errno()),
                other => {
                    unreachable!(
                        "Unexpected return value from hwloc_topology_export_synthetic: {other}"
                    )
                }
            }
        }
    }
}

/// # Retrieve distances between objects
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__get.html
impl Topology {
    /// Retrieve distance matrices from the topology
    ///
    /// By default, all available distance matrices are returned. Some filtering
    /// may be applied using the `kind` parameter: if it contains some
    /// [`DistancesKind`]`::FROM_xyz` options, only distance matrices matching
    /// one of them is returned. The same applies for `MEANS_xyz` options.
    #[doc(alias = "hwloc_distances_get")]
    pub fn distances(&self, kind: DistancesKind) -> Vec<Distances> {
        self.get_distances(|topology, nr, distances, flags| unsafe {
            ffi::hwloc_distances_get(topology, nr, distances, kind.bits(), flags)
        })
    }

    /// Retrieve distance matrices for object at a specific depth in the topology
    ///
    /// Identical to `distances()` with the additional `depth` filter.
    #[doc(alias = "hwloc_distances_get_by_depth")]
    pub fn distances_at_depth(
        &self,
        kind: DistancesKind,
        depth: impl Into<Depth>,
    ) -> Vec<Distances> {
        let depth = depth.into();
        self.get_distances(|topology, nr, distances, flags| unsafe {
            ffi::hwloc_distances_get_by_depth(
                topology,
                depth.into(),
                nr,
                distances,
                kind.bits(),
                flags,
            )
        })
    }

    /// Retrieve distance matrices for object with a specific type
    ///
    /// Identical to `distances()` with the additional `ty` filter.
    #[doc(alias = "hwloc_distances_get_by_type")]
    pub fn distances_with_type(&self, kind: DistancesKind, ty: ObjectType) -> Vec<Distances> {
        self.get_distances(|topology, nr, distances, flags| unsafe {
            ffi::hwloc_distances_get_by_type(topology, ty.into(), nr, distances, kind.bits(), flags)
        })
    }

    /// Retrieve a distance matrix with the given name
    ///
    /// Usually only one distances matrix may match a given name.
    ///
    /// Names of distances matrices currently created by hwloc may be found
    /// [in the hwloc documentation](https://hwloc.readthedocs.io/en/v2.9/topoattrs.html#topoattrs_distances).
    ///
    /// # Errors
    ///
    /// - [`NulError`] if `name` contains NUL chars.
    #[doc(alias = "hwloc_distances_get_by_name")]
    pub fn distances_with_name(&self, name: &str) -> Result<Vec<Distances>, NulError> {
        let name = LibcString::new(name)?;
        Ok(self.get_distances(|topology, nr, distances, flags| unsafe {
            ffi::hwloc_distances_get_by_name(topology, name.borrow(), nr, distances, flags)
        }))
    }

    /// Call one of the hwloc_distances_get(_by)? APIs
    ///
    /// Takes care of all parameters except for kind, which is not universal to
    /// these APIs. So the last c_ulong is the flags parameter.
    fn get_distances(
        &self,
        mut getter: impl FnMut(
            *const RawTopology,
            *mut c_uint,
            *mut *mut RawDistances,
            c_ulong,
        ) -> c_int,
    ) -> Vec<Distances> {
        // Common setup to all getter calls
        let mut nr = 0;
        let flags = 0;
        let check_result = |result: c_int| {
            assert!(result >= 0, "Unexpected result from hwloc distances getter");
        };

        // Allocate array of distances pointers
        check_result(getter(self.as_ptr(), &mut nr, ptr::null_mut(), flags));
        let mut distances_ptrs = vec![
            ptr::null_mut();
            usize::try_from(nr)
                .expect("Impossibly large amount of distance matrices")
        ];

        // Let hwloc fill the distance pointers
        let old_nr = nr;
        check_result(getter(
            self.as_ptr(),
            &mut nr,
            distances_ptrs.as_mut_ptr(),
            flags,
        ));
        assert_eq!(
            nr, old_nr,
            "Inconsistent reported number of distance matrices"
        );

        // Wrap them into a safe interface
        distances_ptrs
            .into_iter()
            .map(|raw| unsafe { Distances::wrap(self, raw) })
            .collect()
    }
}

/// # Comparing memory node attributes for finding where to allocate on
///
/// Platforms with heterogeneous memory require ways to decide whether a buffer
/// should be allocated on "fast" memory (such as HBM), "normal" memory (DDR) or
/// even "slow" but large-capacity memory (non-volatile memory). These memory
/// nodes are called "Targets" while the CPU accessing them is called the
/// "Initiator". Access performance depends on their locality (NUMA platforms)
/// as well as the intrinsic performance of the targets (heterogeneous platforms).
///
/// The following attributes describe the performance of memory accesses from an
/// Initiator to a memory Target, for instance their latency or bandwidth.
/// Initiators performing these memory accesses are usually some PUs or Cores
/// (described as a CPU set). Hence a Core may choose where to allocate a memory
/// buffer by comparing the attributes of different target memory nodes nearby.
///
/// There are also some attributes that are system-wide. Their value does not
/// depend on a specific initiator performing an access. The memory node
/// Capacity is an example of such attribute without initiator.
///
/// One way to use this API is to start with a cpuset describing the Cores where
/// a program is bound. The best target NUMA node for allocating memory in this
/// program on these Cores may be obtained by passing this cpuset as an
/// initiator to [`MemoryAttribute::best_target()`] with the relevant
/// memory attribute. For instance, if the code is latency limited, use the
/// Latency attribute.
///
/// A more flexible approach consists in getting the list of local NUMA nodes by
/// passing this cpuset to [`Topology::local_numa_nodes()`]. Attribute values
/// for these nodes, if any, may then be obtained with
/// [`MemoryAttribute::value()`] and manually compared with the desired criteria.
///
/// The API also supports specific objects as initiator, but it is currently not
/// used internally by hwloc. Users may for instance use it to provide custom
/// performance values for host memory accesses performed by GPUs.
/// The interface actually also accepts targets that are not NUMA nodes.
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs.html
impl Topology {
    /// Return the identifier of the memory attribute with the given name
    ///
    /// Note that a number of predefined memory attributes have predefined
    /// identifiers and need not be queried by name at runtime, see the
    /// different constructors of [`MemoryAttribute`] for more information.
    ///
    /// # Errors
    ///
    /// - [`NulError`] if `name` contains NUL chars.
    #[doc(alias = "hwloc_memattr_get_by_name")]
    pub fn memory_attribute_named(&self, name: &str) -> Result<Option<MemoryAttribute>, NulError> {
        let name = LibcString::new(name)?;
        let mut id = MaybeUninit::uninit();
        let result = unsafe {
            ffi::hwloc_memattr_get_by_name(self.as_ptr(), name.borrow(), id.as_mut_ptr())
        };
        match result {
            0 => Ok(Some(MemoryAttribute::wrap(self, unsafe {
                id.assume_init()
            }))),
            -1 => {
                let errno = errno();
                match errno.0 {
                    EINVAL => Ok(None),
                    _ => panic!("Unexpected errno from hwloc_memattr_get_by_name: {errno}"),
                }
            }
            other => panic!("Unexpected result from hwloc_memattr_get_by_name: {other}"),
        }
    }

    /// Return an array of local NUMA nodes
    ///
    /// If `target` is given as a `TopologyObject`, its CPU set is used to
    /// find NUMA nodes with the corresponding locality. If the object does not
    /// have a CPU set (e.g. I/O object), the CPU parent (where the I/O object
    /// is attached) is used.
    ///
    /// Some of these NUMA nodes may not have any memory attribute values and
    /// hence not be reported as actual targets in other functions.
    ///
    /// When an object CPU set is given as locality, for instance a Package, and
    /// when `flags` contains both [`LocalNUMANodeFlags::LARGER_LOCALITY`] and
    /// [`LocalNUMANodeFlags::SMALLER_LOCALITY`], the returned array corresponds
    /// to the nodeset of that object.
    #[doc(alias = "hwloc_get_local_numanode_objs")]
    pub fn local_numa_nodes(&self, target: TargetNumaNodes) -> Result<Vec<&TopologyObject>, Errno> {
        // Prepare to call hwloc
        let (location, flags) = target.into_raw_params();
        let mut nr = 0;
        let call_ffi = |nr_mut, out_ptr| {
            let result = unsafe {
                ffi::hwloc_get_local_numanode_objs(
                    self.as_ptr(),
                    &location,
                    nr_mut,
                    out_ptr,
                    flags.bits(),
                )
            };
            match result {
                0 => Ok(()),
                -1 => Err(errno()),
                other => panic!("Unexpected result from hwloc_get_local_numanode_objs: {other}"),
            }
        };

        // Query node count
        call_ffi(&mut nr, ptr::null_mut())?;
        let len = usize::try_from(nr).expect("Impossible node count from hwloc");

        // Allocate storage and fill node list
        let mut out = vec![ptr::null(); len];
        let old_nr = nr;
        call_ffi(&mut nr, out.as_mut_ptr())?;
        assert_eq!(old_nr, nr, "Inconsistent node count from hwloc");

        // Translate node pointers into node references
        Ok(out
            .into_iter()
            .map(|ptr| {
                assert!(!ptr.is_null(), "Invalid NUMA node pointer from hwloc");
                unsafe { &*ptr }
            })
            .collect())
    }
}

// # General-purpose internal utilities
impl Topology {
    /// Returns the contained hwloc topology pointer for interaction with hwloc.
    fn as_ptr(&self) -> *const RawTopology {
        self.0.as_ptr()
    }

    /// Returns the contained hwloc topology pointer for interaction with hwloc.
    pub(crate) fn as_mut_ptr(&mut self) -> *mut RawTopology {
        self.0.as_ptr()
    }
}

impl Clone for Topology {
    fn clone(&self) -> Self {
        let mut clone = ptr::null_mut();
        let result = unsafe { ffi::hwloc_topology_dup(&mut clone, self.as_ptr()) };
        assert!(result >= 0, "Topology clone failed with error {result}");
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
