//! Object types

// - Enums: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__object__types.html
// - Kinds: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__types.html

use crate::{errors, ffi};
#[cfg(doc)]
use crate::{
    object::TopologyObject,
    topology::{
        builder::{TopologyBuilder, TypeFilter},
        support::DiscoverySupport,
    },
};
use derive_more::Display;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use std::{
    cmp::{Ordering, PartialOrd},
    ffi::{c_int, c_uint},
};

/// Rust mapping of the hwloc_obj_type_e enum
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
///
pub(crate) type RawObjectType = c_uint;

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
    Machine,

    /// Physical package, what goes into a physical motherboard socket
    ///
    /// Usually contains multiple cores, and possibly some dies.
    #[doc(alias = "HWLOC_OBJ_PACKAGE")]
    Package,

    /// A computation unit (may be shared by several PUs aka logical processors).
    #[doc(alias = "HWLOC_OBJ_CORE")]
    Core,

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
    PU,

    /// Level 1 Data (or Unified) Cache
    #[doc(alias = "HWLOC_OBJ_L1CACHE")]
    L1Cache,

    /// Level 2 Data (or Unified) Cache
    #[doc(alias = "HWLOC_OBJ_L2CACHE")]
    L2Cache,

    /// Level 3 Data (or Unified) Cache
    #[doc(alias = "HWLOC_OBJ_L3CACHE")]
    L3Cache,

    /// Level 4 Data (or Unified) Cache
    #[doc(alias = "HWLOC_OBJ_L4CACHE")]
    L4Cache,

    /// Level 5 Data (or Unified) Cache
    // NOTE: If hwloc adds more cache levels, update the cache module accordingly
    #[doc(alias = "HWLOC_OBJ_L5CACHE")]
    L5Cache,

    /// Level 1 Instruction cache (filtered out by default)
    #[doc(alias = "HWLOC_OBJ_L1ICACHE")]
    L1ICache,

    /// Level 2 Instruction cache (filtered out by default)
    #[doc(alias = "HWLOC_OBJ_L2ICACHE")]
    L2ICache,

    /// Level 3 Instruction cache (filtered out by default)
    #[doc(alias = "HWLOC_OBJ_L3ICACHE")]
    L3ICache,

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
    Group,

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
    /// the dedicated Memory children list. They also have a special depth.
    #[doc(alias = "HWLOC_OBJ_NUMANODE")]
    NUMANode,

    /// Bridge (filtered out by default)
    ///
    /// Any bridge that connects the host or an I/O bus, to another I/O bus.
    ///
    /// Bridges are not added to the topology unless their filtering is changed
    /// (see [`TopologyBuilder::with_type_filter()`] and
    /// [`TopologyBuilder::with_io_type_filter()`]).
    ///
    /// I/O objects are not listed in the main children list, but rather in
    /// the dedicated Memory children list. They also have a special depth.
    #[doc(alias = "HWLOC_OBJ_BRIDGE")]
    Bridge,

    /// PCI device (filtered out by default)
    ///
    /// PCI devices are not added to the topology unless their filtering is
    /// changed (see [`TopologyBuilder::with_type_filter()`] and
    /// [`TopologyBuilder::with_io_type_filter()`]).
    ///
    /// I/O objects are not listed in the main children list, but rather in
    /// the dedicated I/O children list. They also have a special depth.
    #[doc(alias = "HWLOC_OBJ_PCI_DEVICE")]
    PCIDevice,

    /// Operating system device (filtered out by default)
    ///
    /// OS devices are not added to the topology unless their filtering is
    /// changed (see [`TopologyBuilder::with_type_filter()`] and
    /// [`TopologyBuilder::with_io_type_filter()`]).
    ///
    /// I/O objects are not listed in the main children list, but rather in
    /// the dedicated I/O children list. They also have a special depth.
    #[doc(alias = "HWLOC_OBJ_OS_DEVICE")]
    OSDevice,

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
    /// rather reside in the dedicated Misc children list.
    #[doc(alias = "HWLOC_OBJ_MISC")]
    Misc,

    /// Memory-side cache (filtered out by default)
    ///
    /// A cache in front of a specific NUMA node. This object always has at
    /// least one NUMA node as a memory child.
    ///
    /// Memory objects are not listed in the main children list, but rather in
    /// the dedicated Memory children list. They also have a special depth.
    #[cfg(feature = "hwloc-2_1_0")]
    #[doc(alias = "HWLOC_OBJ_MEMCACHE")]
    MemCache,

    /// Die within a physical package
    ///
    /// A subpart of the physical package, that contains multiple cores.
    #[cfg(feature = "hwloc-2_1_0")]
    #[doc(alias = "HWLOC_OBJ_DIE")]
    Die,
}

impl ObjectType {
    /// Truth that this type is part of the normal hierarchy (not Memory, I/O or Misc)
    #[doc(alias = "hwloc_obj_type_is_normal")]
    pub fn is_normal(&self) -> bool {
        unsafe { self.type_predicate("hwloc_obj_type_is_normal", ffi::hwloc_obj_type_is_normal) }
    }

    /// Truth that this object type is a leaf of the normal hierarchy and
    /// cannot have non-Misc children
    pub fn is_normal_leaf(&self) -> bool {
        *self == Self::PU || *self == Self::NUMANode
    }

    /// Truth that this is a CPU-side cache type (not MemCache)
    #[doc(alias = "hwloc_obj_type_is_cache")]
    pub fn is_cpu_cache(&self) -> bool {
        unsafe { self.type_predicate("hwloc_obj_type_is_cache", ffi::hwloc_obj_type_is_cache) }
    }

    /// Truth that this is a CPU-side data or unified cache type (not MemCache)
    #[doc(alias = "hwloc_obj_type_is_dcache")]
    pub fn is_cpu_data_cache(&self) -> bool {
        unsafe { self.type_predicate("hwloc_obj_type_is_dcache", ffi::hwloc_obj_type_is_dcache) }
    }

    /// Truth that this is a CPU-side instruction cache type (not MemCache)
    #[doc(alias = "hwloc_obj_type_is_icache")]
    pub fn is_cpu_instruction_cache(&self) -> bool {
        unsafe { self.type_predicate("hwloc_obj_type_is_icache", ffi::hwloc_obj_type_is_icache) }
    }

    /// Truth that this is a memory object type (not Normal, I/O or Misc)
    ///
    /// Memory objects are not listed in the main children list, but rather in
    /// the dedicated memory children list. They have special depth values
    /// instead of normal depths like other objects in the main tree.
    #[doc(alias = "hwloc_obj_type_is_memory")]
    pub fn is_memory(&self) -> bool {
        unsafe { self.type_predicate("hwloc_obj_type_is_memory", ffi::hwloc_obj_type_is_memory) }
    }

    /// Truth that this is an I/O object type (not Normal, Memory or Misc)
    ///
    /// I/O objects are not added to the topology unless I/O discovery is
    /// enabled through the custom flags. They have empty CPU and node sets.
    /// They are not part of the main children list, but rather reside in the
    /// dedicated I/O children list.
    #[doc(alias = "hwloc_obj_type_is_io")]
    pub fn is_io(&self) -> bool {
        unsafe { self.type_predicate("hwloc_obj_type_is_io", ffi::hwloc_obj_type_is_io) }
    }

    /// Convert to the internal representation used by hwloc
    ///
    /// Used to avoid Into/From type inference ambiguities.
    fn to_raw(self) -> RawObjectType {
        RawObjectType::from(self)
    }

    /// Query the type of some hwloc object
    ///
    /// These queries should be simple infaillible lookup tables or boolean
    /// expressions, without syscalls, so we can assume they don't error out.
    ///
    /// # Safety
    ///
    /// `pred` must be a valid object type predicate
    unsafe fn type_predicate(
        &self,
        api: &'static str,
        pred: unsafe extern "C" fn(RawObjectType) -> c_int,
    ) -> bool {
        errors::call_hwloc_bool(api, || unsafe { pred(self.to_raw()) })
            .expect("Object type queries should not fail")
    }
}

impl PartialOrd for ObjectType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let result = unsafe { ffi::hwloc_compare_types(self.to_raw(), other.to_raw()) };
        match result {
            c_int::MAX => None,
            c if c > 0 => Some(Ordering::Greater),
            0 => Some(Ordering::Equal),
            c if c < 0 => Some(Ordering::Less),
            _ => unreachable!(),
        }
    }
}

/// Rust mapping of the hwloc_obj_bridge_type_e enum
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
///
pub(crate) type RawBridgeType = c_uint;

/// Type of one side (upstream or downstream) of an I/O bridge.
#[derive(Copy, Clone, Debug, Display, Eq, Hash, IntoPrimitive, TryFromPrimitive, PartialEq)]
#[doc(alias = "hwloc_obj_bridge_type_e")]
#[doc(alias = "hwloc_obj_bridge_type_t")]
#[repr(u32)]
pub enum BridgeType {
    /// Host-side of a bridge, only possible upstream
    #[doc(alias = "HWLOC_OBJ_BRIDGE_HOST")]
    Host,

    /// PCI-side of a bridge
    #[doc(alias = "HWLOC_OBJ_BRIDGE_PCI")]
    PCI,
}

/// Rust mapping of the hwloc_obj_cache_type_e enum
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
///
pub(crate) type RawCacheType = c_uint;

/// Cache type
#[derive(Copy, Clone, Debug, Display, Eq, Hash, IntoPrimitive, TryFromPrimitive, PartialEq)]
#[doc(alias = "hwloc_obj_cache_type_e")]
#[doc(alias = "hwloc_obj_cache_type_t")]
#[repr(u32)]
pub enum CacheType {
    /// Unified cache
    #[doc(alias = "HWLOC_OBJ_CACHE_UNIFIED")]
    Unified,

    /// Data cache
    #[doc(alias = "HWLOC_OBJ_CACHE_DATA")]
    Data,

    /// Instruction cache (filtered out by default
    #[doc(alias = "HWLOC_OBJ_CACHE_INSTRUCTION")]
    Instruction,
}

/// Rust mapping of the hwloc_obj_osdev_type_e enum
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
///
pub(crate) type RawOSDeviceType = c_uint;

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
    Storage,

    /// Operating system GPU device
    ///
    /// For instance ":0.0" for a GL display, "card0" for a Linux DRM device.
    #[doc(alias = "HWLOC_OBJ_OSDEV_GPU")]
    GPU,

    /// Operating system network device
    ///
    /// For instance the "eth0" interface on Linux.
    #[doc(alias = "HWLOC_OBJ_OSDEV_NETWORK")]
    Network,

    /// Operating system openfabrics device
    ///
    /// For instance the "mlx4_0" InfiniBand HCA, "hfi1_0" Omni-Path interface,
    /// or "bxi0" Atos/Bull BXI HCA on Linux.
    #[doc(alias = "HWLOC_OBJ_OSDEV_OPENFABRICS")]
    OpenFabrics,

    /// Operating system dma engine device
    ///
    /// For instance the "dma0chan0" DMA channel on Linux.
    #[doc(alias = "HWLOC_OBJ_OSDEV_DMA")]
    DMA,

    /// Operating system co-processor device
    ///
    /// For instance "opencl0d0" for a OpenCL device, "cuda0" for a CUDA device.
    #[doc(alias = "HWLOC_OBJ_OSDEV_COPROC")]
    CoProcessor,

    /// Operating system memory device
    ///
    /// For instance DAX file for non-volatile or high-bandwidth memory, like
    /// "dax2.0" on Linux.
    #[doc(alias = "HWLOC_OBJ_OSDEV_MEMORY")]
    Memory,
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
