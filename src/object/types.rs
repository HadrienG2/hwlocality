//! Object types
//!
//! Hardware components that hwloc can probe are categorized into
//! [`ObjectType`]s. Some of them get a finer categorization, which can be
//! probed via [`TopologyObject::attributes()`]. All the enumerated types
//! associated with these categories are collected into this module.

// - Enums: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__object__types.html
// - Kinds: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__types.html

use crate::errors;
#[cfg(doc)]
use crate::{
    object::{depth::Depth, TopologyObject},
    topology::{
        builder::{TopologyBuilder, TypeFilter},
        support::DiscoverySupport,
    },
};
use derive_more::Display;
use hwlocality_sys::{
    hwloc_obj_type_t, HWLOC_OBJ_BRIDGE, HWLOC_OBJ_BRIDGE_HOST, HWLOC_OBJ_BRIDGE_PCI,
    HWLOC_OBJ_CACHE_DATA, HWLOC_OBJ_CACHE_INSTRUCTION, HWLOC_OBJ_CACHE_UNIFIED, HWLOC_OBJ_CORE,
    HWLOC_OBJ_GROUP, HWLOC_OBJ_L1CACHE, HWLOC_OBJ_L1ICACHE, HWLOC_OBJ_L2CACHE, HWLOC_OBJ_L2ICACHE,
    HWLOC_OBJ_L3CACHE, HWLOC_OBJ_L3ICACHE, HWLOC_OBJ_L4CACHE, HWLOC_OBJ_L5CACHE, HWLOC_OBJ_MACHINE,
    HWLOC_OBJ_MISC, HWLOC_OBJ_NUMANODE, HWLOC_OBJ_OSDEV_COPROC, HWLOC_OBJ_OSDEV_DMA,
    HWLOC_OBJ_OSDEV_GPU, HWLOC_OBJ_OSDEV_NETWORK, HWLOC_OBJ_OSDEV_OPENFABRICS,
    HWLOC_OBJ_OSDEV_STORAGE, HWLOC_OBJ_OS_DEVICE, HWLOC_OBJ_PACKAGE, HWLOC_OBJ_PCI_DEVICE,
    HWLOC_OBJ_PU, HWLOC_TYPE_UNORDERED,
};
#[cfg(feature = "hwloc-2_1_0")]
use hwlocality_sys::{HWLOC_OBJ_DIE, HWLOC_OBJ_MEMCACHE};
use num_enum::{IntoPrimitive, TryFromPrimitive};
use std::{
    cmp::{Ordering, PartialOrd},
    ffi::c_int,
};

/// Type of one side (upstream or downstream) of an I/O bridge.
#[derive(Copy, Clone, Debug, Display, Eq, Hash, IntoPrimitive, TryFromPrimitive, PartialEq)]
#[doc(alias = "hwloc_obj_bridge_type_e")]
#[doc(alias = "hwloc_obj_bridge_type_t")]
#[repr(u32)]
pub enum BridgeType {
    /// Host-side of a bridge, only possible upstream
    #[doc(alias = "HWLOC_OBJ_BRIDGE_HOST")]
    Host = HWLOC_OBJ_BRIDGE_HOST,

    /// PCI-side of a bridge
    #[doc(alias = "HWLOC_OBJ_BRIDGE_PCI")]
    PCI = HWLOC_OBJ_BRIDGE_PCI,
}

/// Cache type
#[derive(Copy, Clone, Debug, Display, Eq, Hash, IntoPrimitive, TryFromPrimitive, PartialEq)]
#[doc(alias = "hwloc_obj_cache_type_e")]
#[doc(alias = "hwloc_obj_cache_type_t")]
#[repr(u32)]
pub enum CacheType {
    /// Unified cache
    #[doc(alias = "HWLOC_OBJ_CACHE_UNIFIED")]
    Unified = HWLOC_OBJ_CACHE_UNIFIED,

    /// Data cache
    #[doc(alias = "HWLOC_OBJ_CACHE_DATA")]
    Data = HWLOC_OBJ_CACHE_DATA,

    /// Instruction cache (filtered out by default)
    #[doc(alias = "HWLOC_OBJ_CACHE_INSTRUCTION")]
    Instruction = HWLOC_OBJ_CACHE_INSTRUCTION,
}

/// Type of a OS device
#[derive(Copy, Clone, Debug, Display, Eq, Hash, IntoPrimitive, TryFromPrimitive, PartialEq)]
#[doc(alias = "hwloc_obj_osdev_type_e")]
#[doc(alias = "hwloc_obj_osdev_type_t")]
#[repr(u32)]
pub enum OSDeviceType {
    /// Operating system storage device (e.g. block)
    ///
    /// For instance "sda" or "dax2.0" on Linux.
    #[doc(alias = "HWLOC_OBJ_OSDEV_BLOCK")]
    #[doc(alias = "HWLOC_OBJ_OSDEV_STORAGE")]
    Storage = HWLOC_OBJ_OSDEV_STORAGE,

    /// Operating system GPU device
    ///
    /// For instance ":0.0" for a GL display, "card0" for a Linux DRM device.
    #[doc(alias = "HWLOC_OBJ_OSDEV_GPU")]
    GPU = HWLOC_OBJ_OSDEV_GPU,

    /// Operating system network device
    ///
    /// For instance the "eth0" interface on Linux.
    #[doc(alias = "HWLOC_OBJ_OSDEV_NETWORK")]
    Network = HWLOC_OBJ_OSDEV_NETWORK,

    /// Operating system openfabrics device
    ///
    /// For instance the "mlx4_0" InfiniBand HCA, "hfi1_0" Omni-Path interface,
    /// or "bxi0" Atos/Bull BXI HCA on Linux.
    #[doc(alias = "HWLOC_OBJ_OSDEV_OPENFABRICS")]
    OpenFabrics = HWLOC_OBJ_OSDEV_OPENFABRICS,

    /// Operating system dma engine device
    ///
    /// For instance the "dma0chan0" DMA channel on Linux.
    #[doc(alias = "HWLOC_OBJ_OSDEV_DMA")]
    DMA = HWLOC_OBJ_OSDEV_DMA,

    /// Operating system co-processor device
    ///
    /// For instance "opencl0d0" for a OpenCL device, "cuda0" for a CUDA device.
    #[doc(alias = "HWLOC_OBJ_OSDEV_COPROC")]
    CoProcessor = HWLOC_OBJ_OSDEV_COPROC,

    /// Operating system memory device
    ///
    /// For instance DAX file for non-volatile or high-bandwidth memory, like
    /// "dax2.0" on Linux.
    #[cfg(feature = "hwloc-3_0_0")]
    #[doc(alias = "HWLOC_OBJ_OSDEV_MEMORY")]
    Memory = HWLOC_OBJ_OSDEV_MEMORY,
}

/// Represents the type of a [`TopologyObject`].
///
/// Note that (partial) ordering for object types is implemented as a call
/// into the `hwloc` library which defines ordering as follows:
///
/// - A == B if `ObjectType::A` and `ObjectType::B` are the same.
/// - A < B if `ObjectType::A` includes objects of type `ObjectType::B`.
/// - A > B if objects of `ObjectType::A` are included in type `ObjectType::B`.
/// - [`ObjectType::Machine`] is always the highest and [`ObjectType::PU`] is
///   always the deepest.
///
/// It can also help to think of it as comparing the relative depths of each type, so
/// a `ObjectType::Machine` will be smaller than a `ObjectType::PU` since the machine
/// contains processing units.
#[derive(Copy, Clone, Debug, Display, Eq, Hash, IntoPrimitive, TryFromPrimitive, PartialEq)]
#[doc(alias = "hwloc_obj_type_e")]
#[doc(alias = "hwloc_obj_type_t")]
#[non_exhaustive]
#[repr(u32)]
pub enum ObjectType {
    /// The root object, a set of processors and memory with cache coherency
    ///
    /// This type is always used for the root object of a topology, and never
    /// used anywhere else. Hence it never has a parent.
    #[doc(alias = "HWLOC_OBJ_MACHINE")]
    Machine = HWLOC_OBJ_MACHINE,

    /// Physical package, what goes into a physical motherboard socket
    ///
    /// Usually contains multiple cores, and possibly some dies.
    #[doc(alias = "HWLOC_OBJ_PACKAGE")]
    Package = HWLOC_OBJ_PACKAGE,

    /// A computation unit (may be shared by several PUs aka logical processors).
    #[doc(alias = "HWLOC_OBJ_CORE")]
    Core = HWLOC_OBJ_CORE,

    /// Processing Unit, or (Logical) Processor
    ///
    /// An execution unit (may share a core with some other logical
    /// processors, e.g. in the case of an SMT core).
    ///
    /// This is the leaf of the CPU resource hierarchy, it can only have Misc
    /// children.
    ///
    /// It is always reported even when other objects are not detected. However,
    /// an incorrect number of PUs may be reported in the absence of
    /// [`DiscoverySupport::pu_count()`].
    #[doc(alias = "HWLOC_OBJ_PU")]
    PU = HWLOC_OBJ_PU,

    /// Level 1 Data (or Unified) Cache
    #[doc(alias = "HWLOC_OBJ_L1CACHE")]
    L1Cache = HWLOC_OBJ_L1CACHE,

    /// Level 2 Data (or Unified) Cache
    #[doc(alias = "HWLOC_OBJ_L2CACHE")]
    L2Cache = HWLOC_OBJ_L2CACHE,

    /// Level 3 Data (or Unified) Cache
    #[doc(alias = "HWLOC_OBJ_L3CACHE")]
    L3Cache = HWLOC_OBJ_L3CACHE,

    /// Level 4 Data (or Unified) Cache
    #[doc(alias = "HWLOC_OBJ_L4CACHE")]
    L4Cache = HWLOC_OBJ_L4CACHE,

    /// Level 5 Data (or Unified) Cache
    //
    // TODO: If hwloc adds more cache levels, update the cache module accordingly
    #[doc(alias = "HWLOC_OBJ_L5CACHE")]
    L5Cache = HWLOC_OBJ_L5CACHE,

    /// Level 1 Instruction cache (filtered out by default)
    #[doc(alias = "HWLOC_OBJ_L1ICACHE")]
    L1ICache = HWLOC_OBJ_L1ICACHE,

    /// Level 2 Instruction cache (filtered out by default)
    #[doc(alias = "HWLOC_OBJ_L2ICACHE")]
    L2ICache = HWLOC_OBJ_L2ICACHE,

    /// Level 3 Instruction cache (filtered out by default)
    #[doc(alias = "HWLOC_OBJ_L3ICACHE")]
    L3ICache = HWLOC_OBJ_L3ICACHE,

    /// Group object
    ///
    /// Objects which do not fit in the above but are detected by hwloc and
    /// are useful to take into account for affinity. For instance, some
    /// operating systems expose their arbitrary processors aggregation this
    /// way. And hwloc may insert such objects to group NUMA nodes according
    /// to their distances.
    ///
    /// These objects are ignored when they do not bring any structure (see
    /// [`TypeFilter::KeepStructure`])
    #[doc(alias = "HWLOC_OBJ_GROUP")]
    Group = HWLOC_OBJ_GROUP,

    /// NUMA node
    ///
    /// An object that contains memory that is directly and byte-accessible to
    /// the host processors. It is usually close to some cores
    /// (the corresponding objects are descendants of the NUMA node object in
    /// the hwloc tree).
    ///
    /// This is the smallest object representing Memory resources, it cannot
    /// have any child except Misc objects. However it may have Memory-side
    /// cache parents.
    ///
    /// There is always at least one such object in the topology even if the
    /// machine is not NUMA. However, an incorrect number of NUMA nodes may be
    /// reported in the absence of [`DiscoverySupport::numa_count()`].
    ///
    /// Memory objects are not listed in the main children list, but rather in
    /// the dedicated Memory children list. They also have a special depth
    /// [`Depth::NUMANode`] instead of a normal depth just like other objects
    /// in the main tree.
    #[doc(alias = "HWLOC_OBJ_NUMANODE")]
    NUMANode = HWLOC_OBJ_NUMANODE,

    /// Bridge (filtered out by default)
    ///
    /// Any bridge that connects the host or an I/O bus, to another I/O bus.
    ///
    /// Bridges are not added to the topology unless their filtering is changed
    /// (see [`TopologyBuilder::with_type_filter()`] and
    /// [`TopologyBuilder::with_io_type_filter()`]).
    ///
    /// I/O objects are not listed in the main children list, but rather in the
    /// dedicated Memory children list. They don't have CPU and node sets. They
    /// also have a special depth [`Depth::Bridge`] instead of a normal depth
    /// just like other objects in the main tree.
    #[doc(alias = "HWLOC_OBJ_BRIDGE")]
    Bridge = HWLOC_OBJ_BRIDGE,

    /// PCI device (filtered out by default)
    ///
    /// PCI devices are not added to the topology unless their filtering is
    /// changed (see [`TopologyBuilder::with_type_filter()`] and
    /// [`TopologyBuilder::with_io_type_filter()`]).
    ///
    /// I/O objects are not listed in the main children list, but rather in the
    /// dedicated I/O children list. They don't have CPU and node sets. They
    /// also have a special depth [`Depth::PCIDevice`] instead of a normal depth
    /// just like other objects in the main tree.
    #[doc(alias = "HWLOC_OBJ_PCI_DEVICE")]
    PCIDevice = HWLOC_OBJ_PCI_DEVICE,

    /// Operating system device (filtered out by default)
    ///
    /// OS devices are not added to the topology unless their filtering is
    /// changed (see [`TopologyBuilder::with_type_filter()`] and
    /// [`TopologyBuilder::with_io_type_filter()`]).
    ///
    /// I/O objects are not listed in the main children list, but rather in the
    /// dedicated I/O children list. They don't have CPU and node sets. They
    /// also have a special depth [`Depth::OSDevice`] instead of a normal depth
    /// just like other objects in the main tree.
    #[doc(alias = "HWLOC_OBJ_OS_DEVICE")]
    OSDevice = HWLOC_OBJ_OS_DEVICE,

    /// Miscellaneous object (filtered out by default)
    ///
    /// Objects without particular meaning, that can e.g. be added by the
    /// application for its own use, or by hwloc for miscellaneous objects such
    /// as MemoryModule (DIMMs).
    ///
    /// They are not added to the topology unless their filtering is
    /// changed (see [`TopologyBuilder::with_type_filter()`]).
    ///
    /// Misc objects have no CPU and node sets, and may only have other Misc
    /// objects as children. They are not part of the main children list, but
    /// rather reside in the dedicated Misc children list. They don't have CPU
    /// and node sets. They also have a special depth [`Depth::Misc`] instead
    /// of a normal depth just like other objects in the main tree.
    #[doc(alias = "HWLOC_OBJ_MISC")]
    Misc = HWLOC_OBJ_MISC,

    /// Memory-side cache (filtered out by default)
    ///
    /// A cache in front of a specific NUMA node. This object always has at
    /// least one NUMA node as a memory child.
    ///
    /// Memory objects are not listed in the main children list, but rather in
    /// the dedicated Memory children list. They also have a special depth
    /// [`Depth::MemCache`] instead of a normal depth just like other objects
    /// in the main tree.
    #[cfg(feature = "hwloc-2_1_0")]
    #[doc(alias = "HWLOC_OBJ_MEMCACHE")]
    MemCache = HWLOC_OBJ_MEMCACHE,

    /// Die within a physical package
    ///
    /// A subpart of the physical package, that contains multiple cores.
    #[cfg(feature = "hwloc-2_1_0")]
    #[doc(alias = "HWLOC_OBJ_DIE")]
    Die = HWLOC_OBJ_DIE,
}

impl ObjectType {
    /// Truth that this type is part of the normal hierarchy (not Memory, I/O or Misc)
    #[doc(alias = "hwloc_obj_type_is_normal")]
    pub fn is_normal(self) -> bool {
        // SAFETY: hwloc_obj_type_is_normal is supported by definition
        unsafe {
            self.type_predicate(
                "hwloc_obj_type_is_normal",
                hwlocality_sys::hwloc_obj_type_is_normal,
            )
        }
    }

    /// Truth that this object type is a leaf of the normal hierarchy and
    /// cannot have non-Misc children
    pub fn is_normal_leaf(self) -> bool {
        self == Self::PU || self == Self::NUMANode
    }

    /// Truth that this is a CPU-side cache type
    #[cfg_attr(feature = "hwloc-2_1_0", doc = "(not [`MemCache`](Self::MemCache))")]
    #[doc(alias = "hwloc_obj_type_is_cache")]
    pub fn is_cpu_cache(self) -> bool {
        // SAFETY: hwloc_obj_type_is_cache behaves like hwloc_obj_type_is_normal
        unsafe {
            self.type_predicate(
                "hwloc_obj_type_is_cache",
                hwlocality_sys::hwloc_obj_type_is_cache,
            )
        }
    }

    /// Truth that this is a CPU-side data or unified cache type
    #[cfg_attr(feature = "hwloc-2_1_0", doc = "(not [`MemCache`](Self::MemCache))")]
    #[doc(alias = "hwloc_obj_type_is_dcache")]
    pub fn is_cpu_data_cache(self) -> bool {
        // SAFETY: hwloc_obj_type_is_dcache behaves like hwloc_obj_type_is_normal
        unsafe {
            self.type_predicate(
                "hwloc_obj_type_is_dcache",
                hwlocality_sys::hwloc_obj_type_is_dcache,
            )
        }
    }

    /// Truth that this is a CPU-side instruction cache type
    #[cfg_attr(feature = "hwloc-2_1_0", doc = "(not [`MemCache`](Self::MemCache))")]
    #[doc(alias = "hwloc_obj_type_is_icache")]
    pub fn is_cpu_instruction_cache(self) -> bool {
        // SAFETY: hwloc_obj_type_is_icache behaves like hwloc_obj_type_is_normal
        unsafe {
            self.type_predicate(
                "hwloc_obj_type_is_icache",
                hwlocality_sys::hwloc_obj_type_is_icache,
            )
        }
    }

    /// Truth that this is a memory object type (not Normal, I/O or Misc)
    ///
    /// Memory objects are not listed in the main children list, but rather in
    /// the dedicated memory children list. They have special depth values
    /// instead of normal depths like other objects in the main tree.
    #[doc(alias = "hwloc_obj_type_is_memory")]
    pub fn is_memory(self) -> bool {
        // SAFETY: hwloc_obj_type_is_memory behaves like hwloc_obj_type_is_normal
        unsafe {
            self.type_predicate(
                "hwloc_obj_type_is_memory",
                hwlocality_sys::hwloc_obj_type_is_memory,
            )
        }
    }

    /// Truth that this is an I/O object type (not Normal, Memory or Misc)
    ///
    /// I/O objects are not added to the topology unless I/O discovery is
    /// enabled through the custom flags. They have empty CPU and node sets.
    /// They are not part of the main children list, but rather reside in the
    /// dedicated I/O children list.
    #[doc(alias = "hwloc_obj_type_is_io")]
    pub fn is_io(self) -> bool {
        // SAFETY: hwloc_obj_type_is_io behaves like hwloc_obj_type_is_normal
        unsafe { self.type_predicate("hwloc_obj_type_is_io", hwlocality_sys::hwloc_obj_type_is_io) }
    }

    /// Convert to the internal representation used by hwloc
    ///
    /// Used to avoid Into/From type inference ambiguities.
    fn to_raw(self) -> hwloc_obj_type_t {
        hwloc_obj_type_t::from(self)
    }

    /// Query the type of some hwloc object
    ///
    /// These queries should be simple infaillible lookup tables or boolean
    /// expressions, without syscalls, so we can assume they don't error out.
    ///
    /// # Safety
    ///
    /// `pred` must be a valid object type predicate with semantics akin to
    /// those of `hwloc_obj_type_is_normal()`
    unsafe fn type_predicate(
        self,
        api: &'static str,
        pred: unsafe extern "C" fn(hwloc_obj_type_t) -> c_int,
    ) -> bool {
        // SAFETY: By construction, ObjectType only exposes values that map into
        //         hwloc_obj_type_t values understood by the configured version
        //         of hwloc, and build.rs checks that the active version of
        //         hwloc is not older than that, so to_raw may only generate
        //         valid hwloc_obj_type_t values for current hwloc
        errors::call_hwloc_bool(api, || unsafe { pred(self.to_raw()) })
            .expect("Object type queries should not fail")
    }
}

impl PartialOrd for ObjectType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // SAFETY: By construction, ObjectType only exposes values that map into
        //         hwloc_obj_type_t values understood by the configured version
        //         of hwloc, and build.rs checks that the active version of
        //         hwloc is not older than that, so to_raw may only generate
        //         valid hwloc_obj_type_t values for current hwloc
        let result = unsafe { hwlocality_sys::hwloc_compare_types(self.to_raw(), other.to_raw()) };
        match result {
            HWLOC_TYPE_UNORDERED => None,
            c if c > 0 => Some(Ordering::Greater),
            0 => Some(Ordering::Equal),
            c if c < 0 => Some(Ordering::Less),
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn should_compare_object_types() {
        assert!(ObjectType::Machine == ObjectType::Machine);
        assert!(ObjectType::PU == ObjectType::PU);

        assert!(ObjectType::Machine < ObjectType::PU);
        assert!(ObjectType::PU > ObjectType::L1Cache);
    }
}
