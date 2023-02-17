//! Object types

// - Enums: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__object__types.html
// - Kinds: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__types.html

use crate::ffi;
#[cfg(doc)]
use crate::objects::TopologyObject;
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
///
/// It can also help to think of it as comparing the relative depths of each type, so
/// a `ObjectType::System` will be smaller than a `ObjectType::PU` since the system
/// contains processing units.
#[repr(u32)]
#[non_exhaustive]
#[derive(Copy, Clone, Debug, Eq, IntoPrimitive, TryFromPrimitive, PartialEq)]
pub enum ObjectType {
    /// The root object, a set of processors and memory with cache coherency.
    Machine,

    /// Physical package, what goes into a physical motherboard socket.
    ///
    /// Usually contains multiple cores, and possibly some dies.
    Package,

    /// A computation unit (may be shared by several PUs aka logical processors).
    Core,

    /// Processing Unit, or (Logical) Processor.
    ///
    /// An execution unit (may share a core with some other logical
    /// processors, e.g. in the case of an SMT core).
    ///
    /// This is the leaf of the CPU resource hierarchy, it can only have Misc children.
    /// It is always reported even when other objects are not detected.
    PU,

    /// Level 1 Data (or Unified) Cache.
    L1Cache,

    /// Level 2 Data (or Unified) Cache.
    L2Cache,

    /// Level 3 Data (or Unified) Cache.
    L3Cache,

    /// Level 4 Data (or Unified) Cache.
    L4Cache,

    /// Level 5 Data (or Unified) Cache.
    // NOTE: If hwloc adds more cache levels, update the cache module accordingly
    L5Cache,

    /// Level 1 Instruction cache (filtered out by default)
    L1iCache,

    /// Level 2 Instruction cache (filtered out by default)
    L2iCache,

    /// Level 3 Instruction cache (filtered out by default)
    L3iCache,

    /// Group objects.
    ///
    /// Objects which do not fit in the above but are detected by hwloc and
    /// are useful to take into account for affinity. For instance, some
    /// operating systems expose their arbitrary processors aggregation this
    /// way. And hwloc may insert such objects to group NUMA nodes according
    /// to their distances.
    ///
    /// These objects are ignored when they do not bring any structure.
    Group,

    /// NUMA node. An object that contains memory that is directly and
    /// byte-accessible to the host processors. It is usually close to
    /// some cores (the corresponding objects are descendants of the NUMA node
    /// object in the hwloc tree).
    ///
    /// This is the smallest object representing Memory resources, it cannot
    /// have any child except Misc objects. However it may have Memory-side
    /// cache parents.
    ///
    /// There is always at least one such object in the topology even if the
    /// machine is not NUMA.
    NUMANode,

    /// Bridge (filtered out by default).
    ///
    /// Any bridge that connects the host or an I/O bus, to another I/O bus.
    Bridge,

    /// PCI device (filtered out by default).
    PCIDevice,

    /// Operating system device (filtered out by default).
    OSDevice,

    /// Miscellaneous objects (filtered out by default).
    ///
    /// Objects without particular meaning, that can e.g. be added by the
    /// application for its own use, or by hwloc for miscellaneous objects such
    /// as MemoryModule (DIMMs).
    ///
    /// Misc objects have empty CPU and node sets. They are not part of the main
    /// children list, but rather reside in the dedicated misc children list.
    Misc,

    /// Memory-side cache (filtered out by default).
    ///
    /// A cache in front of a specific NUMA node. This object always has at
    /// least one NUMA node as a memory child.
    MemCache,

    /// Die within a physical package.
    ///
    /// A subpart of the physical package, that contains multiple cores.
    Die,
}

impl ObjectType {
    /// Truth that this type is part of the normal hierarchy (not Memory, I/O or Misc)
    pub fn is_normal(&self) -> bool {
        let result = unsafe { ffi::hwloc_obj_type_is_normal(self.to_raw()) };
        assert!(
            result == 0 || result == 1,
            "hwloc_obj_type_is_normal returned unexpected result {result}"
        );
        result == 1
    }

    /// Truth that this is a CPU-side cache type (not MemCache)
    pub fn is_cpu_cache(&self) -> bool {
        let result = unsafe { ffi::hwloc_obj_type_is_cache(self.to_raw()) };
        assert!(
            result == 0 || result == 1,
            "hwloc_obj_type_is_cache returned unexpected result {result}"
        );
        result == 1
    }

    /// Truth that this is a CPU-side data or unified cache type (not MemCache)
    pub fn is_cpu_data_cache(&self) -> bool {
        let result = unsafe { ffi::hwloc_obj_type_is_dcache(self.to_raw()) };
        assert!(
            result == 0 || result == 1,
            "hwloc_obj_type_is_dcache returned unexpected result {result}"
        );
        result == 1
    }

    /// Truth that this is a CPU-side instruction cache type (not MemCache)
    pub fn is_cpu_instruction_cache(&self) -> bool {
        let result = unsafe { ffi::hwloc_obj_type_is_icache(self.to_raw()) };
        assert!(
            result == 0 || result == 1,
            "hwloc_obj_type_is_icache returned unexpected result {result}"
        );
        result == 1
    }

    /// Truth that this is a memory object type (not Normal, I/O or Misc)
    ///
    /// Memory objects are not listed in the main children list, but rather in
    /// the dedicated memory children list. They have special depth values
    /// instead of normal depths like other objects in the main tree.
    pub fn is_memory(&self) -> bool {
        let result = unsafe { ffi::hwloc_obj_type_is_memory(self.to_raw()) };
        assert!(
            result == 0 || result == 1,
            "hwloc_obj_type_is_memory returned unexpected result {result}"
        );
        result == 1
    }

    /// Truth that this is an I/O object type (not Normal, Memory or Misc)
    ///
    /// I/O objects are not added to the topology unless I/O discovery is
    /// enabled through the custom flags. They have empty CPU and node sets.
    /// They are not part of the main children list, but rather reside in the
    /// dedicated I/O children list.
    pub fn is_io(&self) -> bool {
        let result = unsafe { ffi::hwloc_obj_type_is_io(self.to_raw()) };
        assert!(
            result == 0 || result == 1,
            "hwloc_obj_type_is_io returned unexpected result {result}"
        );
        result == 1
    }

    /// Truth that this object type is a leaf of the hardware hierarchy and
    /// cannot have non-Misc children
    pub fn is_leaf(&self) -> bool {
        match self {
            Self::PU | Self::NUMANode => true,
            Self::Machine
            | Self::Package
            | Self::Core
            | Self::L1iCache
            | Self::L2iCache
            | Self::L3iCache
            | Self::L1Cache
            | Self::L2Cache
            | Self::L3Cache
            | Self::L4Cache
            | Self::L5Cache
            | Self::Group
            | Self::Bridge
            | Self::PCIDevice
            | Self::OSDevice
            | Self::Misc
            | Self::MemCache
            | Self::Die => false,
        }
    }

    /// Convert to the internal representation used by hwloc
    fn to_raw(self) -> RawObjectType {
        RawObjectType::from(self)
    }
}

impl PartialOrd for ObjectType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let result = unsafe { ffi::hwloc_compare_types(self.to_raw(), other.to_raw()) };
        match result {
            c_int::MAX => None,
            c if c < 0 => Some(Ordering::Less),
            c if c == 0 => Some(Ordering::Equal),
            c if c > 0 => Some(Ordering::Greater),
            _ => unreachable!("hwloc_compare_types returned unexpected result {result}"),
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
#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, IntoPrimitive, TryFromPrimitive, PartialEq)]
pub enum BridgeType {
    /// Host-side of a bridge, only possible upstream
    Host,

    /// PCI-side of a bridge
    PCI,
}

/// Rust mapping of the hwloc_obj_cache_type_e enum
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
///
pub(crate) type RawCacheType = c_uint;

/// Cache type
#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, IntoPrimitive, TryFromPrimitive, PartialEq)]
pub enum CacheType {
    /// Unified cache
    Unified,

    /// Data cache
    Data,

    /// Instruction cache (filtered out by default
    Instruction,
}

/// Rust mapping of the hwloc_obj_osdev_type_e enum
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
///
pub(crate) type RawOSDeviceType = c_uint;

/// Type of a OS device
#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, IntoPrimitive, TryFromPrimitive, PartialEq)]
pub enum OSDeviceType {
    /// Operating system storage device (e.g. block)
    ///
    /// For instance "sda" or "dax2.0" on Linux.
    Storage,

    /// Operating system GPU device
    ///
    /// For instance ":0.0" for a GL display, "card0" for a Linux DRM device.
    GPU,

    /// Operating system network device
    ///
    /// For instance the "eth0" interface on Linux.
    Network,

    /// Operating system openfabrics device
    ///
    /// For instance the "mlx4_0" InfiniBand HCA, "hfi1_0" Omni-Path interface,
    /// or "bxi0" Atos/Bull BXI HCA on Linux.
    OpenFabrics,

    /// Operating system dma engine device
    ///
    /// For instance the "dma0chan0" DMA channel on Linux.
    DMA,

    /// Operating system co-processor device
    ///
    /// For instance "opencl0d0" for a OpenCL device, "cuda0" for a CUDA device.
    CoProcessor,

    /// Operating system memory device
    ///
    /// For instance DAX file for non-volatile or high-bandwidth memory, like
    /// "dax2.0" on Linux.
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
