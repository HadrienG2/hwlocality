//! Topology object attributes

// - Main docs: https://hwloc.readthedocs.io/en/v2.9/unionhwloc__obj__attr__u.html
// - Union semantics: https://hwloc.readthedocs.io/en/v2.9/attributes.html#attributes_normal

#[cfg(doc)]
use crate::support::DiscoverySupport;
use crate::{
    ffi,
    objects::types::{
        BridgeType, CacheType, OSDeviceType, ObjectType, RawBridgeType, RawCacheType,
        RawOSDeviceType,
    },
};
use std::{
    ffi::{c_char, c_float, c_int, c_uchar, c_uint, c_ulonglong, c_ushort},
    fmt,
    hash::Hash,
    num::NonZeroU32,
};

/// hwloc FFI for the hwloc_obj_attr_u union
#[repr(C)]
#[derive(Copy, Clone)]
pub(crate) union RawObjectAttributes {
    numa: NUMANodeAttributes,
    cache: CacheAttributes,
    pub(crate) group: GroupAttributes,
    pcidev: PCIDeviceAttributes,
    bridge: BridgeAttributes,
    osdev: OSDeviceAttributes,
}

/// ObjectType-specific attributes
#[derive(Copy, Clone, Debug, PartialEq)]
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
#[derive(Copy, Clone, Debug, Eq)]
pub struct NUMANodeAttributes {
    local_memory: u64,
    page_types_len: c_uint,
    page_types: *mut MemoryPageType,
}
//
impl NUMANodeAttributes {
    /// Local memory in bytes
    ///
    /// Requires [`DiscoverySupport::numa_memory()`].
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
                self.page_types,
                // If this fails, it means pages_types_len does not fit in a
                // size_t, but by definition of size_t that cannot happen...
                self.page_types_len.try_into().expect("Should not happen"),
            )
        }
    }
}
//
impl Default for NUMANodeAttributes {
    fn default() -> Self {
        Self {
            local_memory: 0,
            page_types_len: 0,
            page_types: std::ptr::null_mut(),
        }
    }
}
//
impl Hash for NUMANodeAttributes {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.local_memory().hash(state);
        self.page_types().hash(state);
    }
}
//
impl PartialEq for NUMANodeAttributes {
    fn eq(&self, other: &Self) -> bool {
        self.local_memory() == other.local_memory() && self.page_types() == other.page_types()
    }
}
//
unsafe impl Send for NUMANodeAttributes {}
unsafe impl Sync for NUMANodeAttributes {}

/// Local memory page type
#[repr(C)]
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct MemoryPageType {
    size: u64,
    count: u64,
}
//
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
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
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
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
pub enum CacheAssociativity {
    /// Unknown associativity
    #[default]
    Unknown,

    /// Fully associative
    Full,

    /// N-ways associative
    Ways(NonZeroU32),
}

/// Group-specific attributes
#[repr(C)]
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
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
    #[allow(unused)]
    pub(crate) fn kind(&self) -> u32 {
        self.kind
    }

    /// Tell hwloc that this group object should always be discarded in favor of
    /// any existing `Group` with the same locality.
    pub(crate) fn favor_merging(&mut self) {
        self.kind = c_uint::MAX
    }

    /// Internally-used subkind to distinguish different levels of groups with
    /// the same kind
    #[allow(unused)]
    pub(crate) fn subkind(&self) -> u32 {
        self.subkind
    }

    /// Flag preventing groups from being automatically merged with identical
    /// parent or children
    pub fn do_not_merge(&self) -> bool {
        assert!(
            self.dont_merge == 0 || self.dont_merge == 1,
            "Unexpected bool value"
        );
        self.dont_merge != 0
    }

    /// Tell hwloc that it should not merge this group object with other
    /// hierarchically-identical objects.
    pub(crate) fn prevent_merging(&mut self) {
        self.dont_merge = 1
    }
}

/// PCIDevice-specific attributes
#[repr(C)]
#[derive(Copy, Clone, Debug, Default, PartialEq)]
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
    /// PCI domain
    pub fn domain(&self) -> u32 {
        self.domain
    }

    /// PCI bus id
    pub fn bus_id(&self) -> u8 {
        self.bus
    }

    /// PCI bus device
    pub fn bus_device(&self) -> u8 {
        self.dev
    }

    /// PCI function
    pub fn function(&self) -> u8 {
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
//
impl fmt::Debug for BridgeAttributes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BridgeAttributes")
            .field("upstream_type", &self.upstream_type())
            .field("upstream_attributes", &self.upstream_attributes())
            .field("downstream_type", &self.downstream_type())
            .field("downstream_attributes", &self.downstream_attributes())
            .field("depth", &self.depth)
            .finish()
    }
}
//
impl PartialEq for BridgeAttributes {
    fn eq(&self, other: &Self) -> bool {
        self.upstream_type() == other.upstream_type()
            && self.upstream_attributes() == other.upstream_attributes()
            && self.downstream_type() == other.downstream_type()
            && self.downstream_attributes() == other.downstream_attributes()
    }
}

/// hwloc FFI for hwloc_bridge_attr_s::upstream
#[repr(C)]
#[derive(Copy, Clone)]
pub(crate) union RawUpstreamAttributes {
    pci: PCIDeviceAttributes,
}

/// Bridge upstream attributes
#[derive(Copy, Clone, Debug, PartialEq)]
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
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
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
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
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
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct OSDeviceAttributes {
    ty: RawOSDeviceType,
}
//
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
/// <https://hwloc.readthedocs.io/en/v2.9/attributes.html#attributes_info> for
/// more information.
#[repr(C)]
#[derive(Eq)]
pub struct ObjectInfo {
    name: *mut c_char,
    value: *mut c_char,
}
//
impl ObjectInfo {
    /// The name of the ObjectInfo
    pub fn name(&self) -> &str {
        unsafe { ffi::deref_string(&self.name) }.expect("Infos should have names")
    }

    /// The value of the ObjectInfo
    pub fn value(&self) -> &str {
        unsafe { ffi::deref_string(&self.value) }.expect("Infos should have values")
    }
}
//
impl fmt::Debug for ObjectInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ObjectInfo")
            .field("name", &self.name())
            .field("value", &self.value())
            .finish()
    }
}
//
impl Hash for ObjectInfo {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name().hash(state);
        self.value().hash(state);
    }
}
//
impl PartialEq for ObjectInfo {
    fn eq(&self, other: &Self) -> bool {
        self.name() == other.name() && self.value() == other.value()
    }
}
//
unsafe impl Send for ObjectInfo {}
unsafe impl Sync for ObjectInfo {}
