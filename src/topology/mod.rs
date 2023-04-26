//! Hardware topology (main hwloc entry point)

pub mod builder;
#[cfg(feature = "hwloc-2_3_0")]
pub mod editor;
pub mod export;
pub mod support;

use self::{
    builder::{BuildFlags, RawTypeFilter, TopologyBuilder, TypeFilter},
    support::FeatureSupport,
};
#[cfg(all(feature = "hwloc-2_3_0", doc))]
use crate::topology::support::MiscSupport;
use crate::{
    bitmaps::{Bitmap, RawBitmap, SpecializedBitmap},
    cpu::cpusets::CpuSet,
    errors::{self, RawHwlocError},
    ffi::{self, IncompleteType},
    memory::nodesets::NodeSet,
    objects::{types::ObjectType, TopologyObject},
};
use bitflags::bitflags;
use errno::Errno;
use libc::EINVAL;
use std::{
    convert::TryInto,
    ffi::c_ulong,
    num::NonZeroU32,
    ptr::{self, NonNull},
};

/// Opaque topology struct
///
/// Represents the private `hwloc_topology` type that `hwloc_topology_t` API
/// pointers map to.
#[repr(C)]
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
#[cfg_attr(
    feature = "hwloc-2_3_0",
    doc = "- [Comparing memory node attributes for finding where to allocate on](#comparing-memory-node-attributes-for-finding-where-to-allocate-on) (hwloc 2.3+)"
)]
#[cfg_attr(
    feature = "hwloc-2_4_0",
    doc = "- [Kinds of CPU cores](#kinds-of-cpu-cores) (hwloc 2.4+)"
)]
#[cfg_attr(
    any(doc, target_os = "linux"),
    doc = "- [Linux-specific helpers](#linux-specific-helpers)"
)]
#[cfg_attr(
    any(doc, all(target_os = "windows", feature = "hwloc-2_5_0")),
    doc = "- [Windows-specific helpers](#windows-specific-helpers) (hwloc 2.5+)"
)]
//
// NOTE: Since the Topology API is _huge_, not all of it is implemented in the
//       topology module. Instead, functionality which is very strongly related
//       to one other code module is implemented inside that module, leaving
//       this module focused on basic lifecycle and cross-cutting issues.
#[derive(Debug)]
#[doc(alias = "hwloc_topology")]
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
    /// let flags = BuildFlags::INCLUDE_DISALLOWED;
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
    //
    // TODO: Propagate note about interprocess sharing from upstream docs
    //       once interprocess sharing is implemented.
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
        errors::call_hwloc_bool("hwloc_topology_is_thissystem", || unsafe {
            ffi::hwloc_topology_is_thissystem(self.as_ptr())
        })
        .expect("Should not involve faillible syscalls")
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
    #[cfg_attr(
        feature = "hwloc-2_3_0",
        doc = "On hwloc 2.3+, [`BuildFlags::IMPORT_SUPPORT`] may be used during topology building to"
    )]
    #[cfg_attr(
        feature = "hwloc-2_3_0",
        doc = "report the supported features of the original remote machine instead. If"
    )]
    #[cfg_attr(
        feature = "hwloc-2_3_0",
        doc = "it was successfully imported, [`MiscSupport::imported()`] will be set."
    )]
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
    /// # use hwlocality::topology::{Topology, support::{FeatureSupport, DiscoverySupport}};
    /// let topology = Topology::new()?;
    /// assert!(topology.supports(
    ///     FeatureSupport::discovery,
    ///     DiscoverySupport::pu_count
    /// ));
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
    /// assert_eq!(
    ///     topology.type_filter(ObjectType::Group)?,
    ///     TypeFilter::KeepStructure
    /// );
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
                    (f64::from(given_weight) * f64::from(num_items) / f64::from(tot_weight)).ceil()
                        as u32
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
    #[doc(alias = "hwloc_topology_destroy")]
    fn drop(&mut self) {
        unsafe { ffi::hwloc_topology_destroy(self.as_mut_ptr()) }
    }
}

unsafe impl Send for Topology {}
unsafe impl Sync for Topology {}
