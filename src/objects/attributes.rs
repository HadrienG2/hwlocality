//! Topology object attributes

// - Main docs: https://hwloc.readthedocs.io/en/v2.9/unionhwloc__obj__attr__u.html
// - Union semantics: https://hwloc.readthedocs.io/en/v2.9/attributes.html#attributes_normal

use crate::{
    ffi,
    objects::types::{
        BridgeType, CacheType, OSDeviceType, ObjectType, RawBridgeType, RawCacheType,
        RawOSDeviceType,
    },
};
use libc::{c_char, c_float, c_int, c_uchar, c_uint, c_ulonglong, c_ushort};
use std::num::NonZeroU32;

/// hwloc FFI for the hwloc_obj_attr_u union
#[repr(C)]
#[derive(Copy, Clone)]
pub(crate) union RawObjectAttributes {
    numa: NUMANodeAttributes,
    cache: CacheAttributes,
    group: GroupAttributes,
    pcidev: PCIDeviceAttributes,
    bridge: BridgeAttributes,
    osdev: OSDeviceAttributes,
}

/// ObjectType-specific attributes
pub enum ObjectAttributes<'attr> {
    /// NUMANode-specific attributes
    NUMANode(&'attr NUMANodeAttributes),

    /// Cache-specific attributes
    Cache(&'attr CacheAttributes),

    /// Group-specific attributes
    Group(&'attr GroupAttributes),

    /// PCIDevice-specific attributes
    PCIDevice(&'attr PCIDeviceAttributes),

    /// Bridge-specific attributes
    Bridge(&'attr BridgeAttributes),

    /// OSDevice-specific attributes
    OSDevice(&'attr OSDeviceAttributes),
}
//
impl<'attr> ObjectAttributes<'attr> {
    /// Wrap the hwloc object type specific attributes behind a safe API
    ///
    /// If non-null, the `attr` pointer must target valid `RawObjectAttributes`.
    ///
    pub(crate) unsafe fn new(
        ty: ObjectType,
        attr: &'attr *mut RawObjectAttributes,
    ) -> Option<Self> {
        if attr.is_null() {
            return None;
        }
        let attr: &RawObjectAttributes = unsafe { &**attr };

        match ty {
            ObjectType::NUMANode => Some(Self::NUMANode(&attr.numa)),
            ObjectType::Group => Some(Self::Group(&attr.group)),
            ObjectType::PCIDevice => Some(Self::PCIDevice(&attr.pcidev)),
            ObjectType::Bridge => Some(Self::Bridge(&attr.bridge)),
            ObjectType::OSDevice => Some(Self::OSDevice(&attr.osdev)),
            _ if ty.is_cpu_cache() => Some(Self::Cache(&attr.cache)),
            _ => None,
        }
    }
}

/// NUMANode-specific attributes
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct NUMANodeAttributes {
    local_memory: u64,
    page_types_len: c_uint,
    page_types: *mut MemoryPageType,
}

impl NUMANodeAttributes {
    /// Local memory in bytes
    pub fn local_memory(&self) -> u64 {
        self.local_memory
    }

    /// Memory page types sorted by increasing page size
    pub fn page_types(&self) -> &[MemoryPageType] {
        if self.page_types.is_null() {
            return &[];
        }
        unsafe {
            std::slice::from_raw_parts(
                self.page_types as *const MemoryPageType,
                // If this fails, it means pages_types_len does not fit in a
                // size_t, but by definition of size_t that cannot happen...
                self.page_types_len.try_into().expect("Should not happen"),
            )
        }
    }
}

unsafe impl Send for NUMANodeAttributes {}
unsafe impl Sync for NUMANodeAttributes {}

/// Local memory page type
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct MemoryPageType {
    size: u64,
    count: u64,
}

impl MemoryPageType {
    /// Size of pages
    pub fn size(&self) -> u64 {
        self.size
    }

    /// Number of pages of this size
    pub fn count(&self) -> u64 {
        self.count
    }
}

/// Cache-specific attributes
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct CacheAttributes {
    size: c_ulonglong,
    depth: c_uint,
    linesize: c_uint,
    associativity: c_int,
    ty: RawCacheType,
}
//
impl CacheAttributes {
    /// Size of the cache in bytes
    pub fn size(&self) -> u64 {
        self.size
    }

    /// Depth ofthe cache (e.g. L1, L2, ...)
    pub fn depth(&self) -> u32 {
        self.depth
    }

    /// Cache line size in bytes
    pub fn line_size(&self) -> Option<NonZeroU32> {
        NonZeroU32::new(self.linesize)
    }

    /// Ways of associativity
    pub fn associativity(&self) -> CacheAssociativity {
        match self.associativity {
            -1 => CacheAssociativity::Full,
            0 => CacheAssociativity::Unknown,
            ways if ways > 0 => CacheAssociativity::Ways(
                NonZeroU32::new(u32::try_from(ways).expect("i32 > 0 -> u32 cannot fail"))
                    .expect("u32 > 0 -> NonZeroU32 cannot fail"),
            ),
            unexpected => unreachable!("Got unexpected cache associativity {unexpected}"),
        }
    }

    /// Cache type
    pub fn cache_type(&self) -> CacheType {
        self.ty.try_into().expect("Got unexpected cache type")
    }
}

/// Cache associativity
pub enum CacheAssociativity {
    /// Unknown associativity
    Unknown,

    /// Fully associative
    Full,

    /// N-ways associative
    Ways(NonZeroU32),
}

/// Group-specific attributes
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct GroupAttributes {
    depth: c_uint,
    kind: c_uint,
    subkind: c_uint,
    dont_merge: c_uchar,
}
//
impl GroupAttributes {
    /// Depth of group object
    ///
    /// It may change if intermediate Group objects are added.
    pub fn depth(&self) -> u32 {
        self.depth
    }

    /// Internally-used kind of group
    // TODO: Consider hiding depending on what "internal" we're talking about
    pub fn kind(&self) -> u32 {
        self.kind
    }

    /// Internally-used subkind to distinguish different levels of groups with
    /// the same kind
    // TODO: Consider hiding depending on what "internal" we're talking about
    pub fn subkind(&self) -> u32 {
        self.subkind
    }

    /// Flag preventing groups from being automatically merged with identical
    /// parent or children
    // TODO: Consider casting to bool
    pub fn do_not_merge(&self) -> u8 {
        self.dont_merge
    }
}

/// PCIDevice-specific attributes
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct PCIDeviceAttributes {
    domain: c_uint,
    bus: c_uchar,
    dev: c_uchar,
    func: c_uchar,
    prog_if: c_uchar,
    class_id: c_ushort,
    vendor_id: c_ushort,
    device_id: c_ushort,
    subvendor_id: c_ushort,
    subdevice_id: c_ushort,
    revision: c_uchar,
    linkspeed: c_float,
}
//
impl PCIDeviceAttributes {
    pub fn domain(&self) -> u32 {
        self.domain
    }

    pub fn bus(&self) -> u8 {
        self.bus
    }

    pub fn dev(&self) -> u8 {
        self.dev
    }

    pub fn func(&self) -> u8 {
        self.func
    }

    /// Register-level programming interface
    pub fn prog_if(&self) -> u8 {
        self.prog_if
    }

    pub fn class_id(&self) -> u16 {
        self.class_id
    }

    pub fn vendor_id(&self) -> u16 {
        self.vendor_id
    }

    pub fn device_id(&self) -> u16 {
        self.device_id
    }

    pub fn subvendor_id(&self) -> u16 {
        self.subvendor_id
    }

    pub fn subdevice_id(&self) -> u16 {
        self.subdevice_id
    }

    pub fn revision(&self) -> u8 {
        self.revision
    }

    /// Link speed in GB/s
    pub fn link_speed(&self) -> f32 {
        self.linkspeed
    }
}

/// Bridge-specific attributes
#[repr(C)]
#[derive(Copy, Clone)]
pub struct BridgeAttributes {
    upstream: RawUpstreamAttributes,
    upstream_type: RawBridgeType,
    downstream: RawDownstreamAttributes,
    downstream_type: RawBridgeType,
    depth: c_uint,
}
//
impl BridgeAttributes {
    /// Bridge upstream type
    pub fn upstream_type(&self) -> BridgeType {
        self.upstream_type
            .try_into()
            .expect("Got unexpected upstream type")
    }

    /// Upstream attributes
    pub fn upstream_attributes(&self) -> Option<UpstreamAttributes> {
        UpstreamAttributes::new(self.upstream_type(), &self.upstream)
    }

    /// Bridge downstream type
    pub fn downstream_type(&self) -> BridgeType {
        self.downstream_type
            .try_into()
            .expect("Got unexpected downstream type")
    }

    /// Downstream attributes
    pub fn downstream_attributes(&self) -> Option<DownstreamAttributes> {
        DownstreamAttributes::new(self.downstream_type(), &self.downstream)
    }

    /// Bridge object depth
    pub fn depth(&self) -> u32 {
        self.depth
    }
}

/// hwloc FFI for hwloc_bridge_attr_s::upstream
#[repr(C)]
#[derive(Copy, Clone)]
pub(crate) union RawUpstreamAttributes {
    pci: PCIDeviceAttributes,
}

/// Bridge upstream attributes
pub enum UpstreamAttributes<'attr> {
    /// PCI-specific attributes
    PCI(&'attr PCIDeviceAttributes),
}
//
impl<'attr> UpstreamAttributes<'attr> {
    /// Wrap the upstream attributes behind a safe API
    pub(crate) fn new(ty: BridgeType, attr: &'attr RawUpstreamAttributes) -> Option<Self> {
        unsafe {
            match ty {
                BridgeType::PCI => Some(Self::PCI(&attr.pci)),
                BridgeType::Host => None,
            }
        }
    }
}

/// Downstream PCI device attributes
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct DownstreamPCIAttributes {
    domain: c_uint,
    secondary_bus: c_uchar,
    subordinate_bus: c_uchar,
}
//
impl DownstreamPCIAttributes {
    pub fn domain(&self) -> u32 {
        self.domain
    }

    pub fn secondary_bus(&self) -> u8 {
        self.secondary_bus
    }

    pub fn subordinate_bus(&self) -> u8 {
        self.subordinate_bus
    }
}

/// hwloc FFI for hwloc_bridge_attr_s::downstream
#[repr(C)]
#[derive(Copy, Clone)]
pub(crate) union RawDownstreamAttributes {
    pci: DownstreamPCIAttributes,
}

/// Bridge downstream attributes
pub enum DownstreamAttributes<'attr> {
    /// PCI-specific attributes
    PCI(&'attr DownstreamPCIAttributes),
}
//
impl<'attr> DownstreamAttributes<'attr> {
    /// Wrap the upstream attributes behind a safe API
    pub(crate) fn new(ty: BridgeType, attr: &'attr RawDownstreamAttributes) -> Option<Self> {
        unsafe {
            match ty {
                BridgeType::PCI => Some(Self::PCI(&attr.pci)),
                BridgeType::Host => unreachable!("Host bridge type should not appear downstream"),
            }
        }
    }
}

/// OSDevice-specific attributes
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct OSDeviceAttributes {
    ty: RawOSDeviceType,
}

impl OSDeviceAttributes {
    /// OS device type
    pub fn device_type(&self) -> OSDeviceType {
        self.ty.try_into().expect("Got unexpected OS device type")
    }
}

/// Key-value string attributes
///
/// hwloc defines a number of standard info attribute names with associated
/// semantics, please check out
/// https://hwloc.readthedocs.io/en/v2.9/attributes.html#attributes_info for
/// more information.
#[repr(C)]
pub struct ObjectInfo {
    name: *mut c_char,
    value: *mut c_char,
}

impl ObjectInfo {
    /// The name of the ObjectInfo
    pub fn name(&self) -> Option<&str> {
        unsafe { ffi::deref_string(&self.name) }
    }

    /// The value of the ObjectInfo
    pub fn value(&self) -> Option<&str> {
        unsafe { ffi::deref_string(&self.value) }
    }
}

unsafe impl Send for ObjectInfo {}
unsafe impl Sync for ObjectInfo {}
