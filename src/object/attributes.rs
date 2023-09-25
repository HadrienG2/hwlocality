//! Object attributes
//!
//! Some [`TopologyObject` types](ObjectType) come with supplementary attributes
//! that extend the object's description. These attributes can be accessed using
//! the [`TopologyObject::attributes()`] method, and are described using types
//! defined inside of this module.

// - Main docs: https://hwloc.readthedocs.io/en/v2.9/unionhwloc__obj__attr__u.html
// - Union semantics: https://hwloc.readthedocs.io/en/v2.9/attributes.html#attributes_normal

use crate::{
    ffi::int,
    object::types::{
        BridgeType, CacheType, OSDeviceType, ObjectType, RawBridgeType, RawCacheType,
        RawOSDeviceType,
    },
};
#[cfg(doc)]
use crate::{object::TopologyObject, topology::support::DiscoverySupport};
use std::{
    ffi::{c_float, c_int, c_uchar, c_uint, c_ushort},
    fmt,
    hash::Hash,
    num::NonZeroUsize,
};

/// hwloc FFI for the `hwloc_obj_attr_u` union
///
/// Exposed to users via the safe [`ObjectAttributes`] enum.
#[derive(Copy, Clone)]
#[repr(C)]
pub(crate) union RawObjectAttributes {
    /// [`NUMANode`]-specific attributes
    ///
    /// [`NUMANode`]: ObjectType::NUMANode
    numa: NUMANodeAttributes,

    /// CPU cache-specific attributes
    cache: CacheAttributes,

    /// [`Group`]-specific attributes
    ///
    /// [`Group`]: ObjectType::Group
    pub(crate) group: GroupAttributes,

    /// [`PCIDevice`]-specific attributes
    ///
    /// [`PCIDevice`]: ObjectType::PCIDevice
    pcidev: PCIDeviceAttributes,

    /// [`Bridge`]-specific attributes
    ///
    /// [`Bridge`]: ObjectType::Bridge
    bridge: BridgeAttributes,

    /// [`OSDevice`]-specific attributes
    ///
    /// [`OSDevice`]: ObjectType::OSDevice
    osdev: OSDeviceAttributes,
}

/// ObjectType-specific attributes
#[derive(Copy, Clone, Debug, PartialEq)]
#[doc(alias = "hwloc_obj_attr_u")]
pub enum ObjectAttributes<'object> {
    /// [`NUMANode`]-specific attributes
    ///
    /// [`NUMANode`]: ObjectType::NUMANode
    #[doc(alias = "hwloc_obj_attr_u::numanode")]
    NUMANode(&'object NUMANodeAttributes),

    /// CPU cache-specific attributes
    #[doc(alias = "hwloc_obj_attr_u::cache")]
    Cache(&'object CacheAttributes),

    /// [`Group`]-specific attributes
    ///
    /// [`Group`]: ObjectType::Group
    #[doc(alias = "hwloc_obj_attr_u::group")]
    Group(&'object GroupAttributes),

    /// [`PCIDevice`]-specific attributes
    ///
    /// [`PCIDevice`]: ObjectType::PCIDevice
    #[doc(alias = "hwloc_obj_attr_u::pcidev")]
    PCIDevice(&'object PCIDeviceAttributes),

    /// [`Bridge`]-specific attributes
    ///
    /// [`Bridge`]: ObjectType::Bridge
    #[doc(alias = "hwloc_obj_attr_u::bridge")]
    Bridge(&'object BridgeAttributes),

    /// [`OSDevice`]-specific attributes
    ///
    /// [`OSDevice`]: ObjectType::OSDevice
    #[doc(alias = "hwloc_obj_attr_u::osdev")]
    OSDevice(&'object OSDeviceAttributes),
}
//
impl<'object> ObjectAttributes<'object> {
    /// Wrap the hwloc object type specific attributes behind a safe API
    ///
    /// # Safety
    ///
    /// If non-null, the `attr` pointer must target `RawObjectAttributes` that
    /// are valid for lifetime `'object` and consistent with object type `ty`.
    pub(crate) unsafe fn new(
        ty: ObjectType,
        attr: &'object *mut RawObjectAttributes,
    ) -> Option<Self> {
        if attr.is_null() {
            return None;
        }

        // SAFETY: Safe due to input precondition
        let attr: &RawObjectAttributes = unsafe { &**attr };

        // SAFETY: Safe because we checked for union field access validity
        unsafe {
            #[allow(clippy::wildcard_enum_match_arm)]
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
}

/// [`NUMANode`]-specific attributes
///
/// [`NUMANode`]: ObjectType::NUMANode
#[derive(Copy, Clone, Debug, Eq)]
#[doc(alias = "hwloc_numanode_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s")]
#[repr(C)]
pub struct NUMANodeAttributes {
    /// Node-local memory in bytes
    local_memory: u64,

    /// Number of memory page types
    page_types_len: c_uint,

    /// # Safety
    ///
    /// If non-null, this is trusted to point to a C-style array of
    /// `page_types_len` memory page types, sorted by increasing page size.
    page_types: *mut MemoryPageType,
}
//
impl NUMANodeAttributes {
    /// Node-local memory in bytes
    ///
    /// Requires [`DiscoverySupport::numa_memory()`].
    #[doc(alias = "hwloc_numanode_attr_s::local_memory")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::local_memory")]
    pub fn local_memory(&self) -> u64 {
        self.local_memory
    }

    /// Memory page types, sorted by increasing page size
    #[doc(alias = "hwloc_numanode_attr_s::page_types")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::page_types")]
    pub fn page_types(&self) -> &[MemoryPageType] {
        if self.page_types.is_null() {
            return &[];
        }
        // SAFETY: Per type invariant
        unsafe {
            std::slice::from_raw_parts(
                self.page_types,
                // If this fails, it means pages_types_len does not fit in a
                // size_t, but by definition of size_t that cannot happen
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
// SAFETY: No internal mutability
unsafe impl Send for NUMANodeAttributes {}
//
// SAFETY: No internal mutability
unsafe impl Sync for NUMANodeAttributes {}

/// Local memory page type
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_memory_page_type_s")]
#[doc(alias = "hwloc_numanode_attr_s::hwloc_memory_page_type_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::hwloc_memory_page_type_s")]
#[repr(C)]
pub struct MemoryPageType {
    /// Size of pages
    size: u64,

    /// Number of pages of this size
    count: u64,
}
//
impl MemoryPageType {
    /// Size of pages
    #[doc(alias = "hwloc_memory_page_type_s::size")]
    #[doc(alias = "hwloc_numanode_attr_s::hwloc_memory_page_type_s::size")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::hwloc_memory_page_type_s::size")]
    pub fn size(&self) -> u64 {
        self.size
    }

    /// Number of pages of this size
    #[doc(alias = "hwloc_memory_page_type_s::count")]
    #[doc(alias = "hwloc_numanode_attr_s::hwloc_memory_page_type_s::count")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::hwloc_memory_page_type_s::count")]
    pub fn count(&self) -> u64 {
        self.count
    }
}

/// Cache-specific attributes
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_cache_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s")]
#[repr(C)]
pub struct CacheAttributes {
    /// Size of the cache in bytes
    size: u64,

    /// Depth ofthe cache (e.g. L1, L2, ...)
    depth: c_uint,

    /// Cache line size in bytes
    linesize: c_uint,

    /// Ways of associativity
    associativity: c_int,

    /// Cache type
    ty: RawCacheType,
}
//
impl CacheAttributes {
    /// Size of the cache in bytes
    #[doc(alias = "hwloc_cache_attr_s::size")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::size")]
    pub fn size(&self) -> u64 {
        self.size
    }

    /// Depth ofthe cache (e.g. L1, L2, ...)
    #[doc(alias = "hwloc_cache_attr_s::depth")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::depth")]
    pub fn depth(&self) -> usize {
        int::expect_usize(self.depth)
    }

    /// Cache line size in bytes
    #[doc(alias = "hwloc_cache_attr_s::linesize")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::linesize")]
    pub fn line_size(&self) -> Option<NonZeroUsize> {
        NonZeroUsize::new(int::expect_usize(self.linesize))
    }

    /// Ways of associativity
    #[doc(alias = "hwloc_cache_attr_s::associativity")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::associativity")]
    pub fn associativity(&self) -> CacheAssociativity {
        match self.associativity {
            -1 => CacheAssociativity::Full,
            0 => CacheAssociativity::Unknown,
            ways if ways > 0 => {
                let ways = c_uint::try_from(ways).expect("int > 0 -> uint should not fail");
                let ways = int::expect_usize(ways);
                let ways = NonZeroUsize::new(ways).expect("usize > 0 -> NonZeroUsize cannot fail");
                CacheAssociativity::Ways(ways)
            }
            unexpected => unreachable!("Got unexpected cache associativity {unexpected}"),
        }
    }

    /// Cache type
    #[doc(alias = "hwloc_cache_attr_s::type")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::type")]
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
    Ways(NonZeroUsize),
}

/// [`Group`]-specific attributes
///
/// [`Group`]: ObjectType::Group
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_group_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_group_attr_s")]
#[repr(C)]
pub struct GroupAttributes {
    /// Depth of group object
    depth: c_uint,

    /// Internally-used kind of group
    kind: c_uint,

    /// Internally-used subkind to distinguish different levels of groups with
    /// the same kind
    subkind: c_uint,

    /// Flag preventing groups from being automatically merged with identical
    /// parent or children
    #[cfg(feature = "hwloc-2_0_4")]
    dont_merge: c_uchar,
}
//
impl GroupAttributes {
    /// Depth of group object
    ///
    /// It may change if intermediate Group objects are added.
    #[doc(alias = "hwloc_group_attr_s::depth")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_group_attr_s::depth")]
    pub fn depth(&self) -> usize {
        int::expect_usize(self.depth)
    }

    /// Internally-used kind of group
    #[allow(unused)]
    pub(crate) fn kind(&self) -> usize {
        int::expect_usize(self.kind)
    }

    /// Tell hwloc that this group object should always be discarded in favor of
    /// any existing `Group` with the same locality.
    #[cfg(feature = "hwloc-2_3_0")]
    pub(crate) fn favor_merging(&mut self) {
        self.kind = c_uint::MAX
    }

    /// Internally-used subkind to distinguish different levels of groups with
    /// the same kind
    #[allow(unused)]
    #[doc(alias = "hwloc_group_attr_s::subkind")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_group_attr_s::subkind")]
    pub(crate) fn subkind(&self) -> usize {
        int::expect_usize(self.subkind)
    }

    /// Flag preventing groups from being automatically merged with identical
    /// parent or children
    #[cfg(feature = "hwloc-2_0_4")]
    pub fn merging_prevented(&self) -> bool {
        assert!(
            self.dont_merge == 0 || self.dont_merge == 1,
            "Unexpected hwloc_group_attr_s::dont_merge value"
        );
        self.dont_merge != 0
    }

    /// Tell hwloc that it should not merge this group object with other
    /// hierarchically-identical objects.
    #[cfg(feature = "hwloc-2_3_0")]
    pub(crate) fn prevent_merging(&mut self) {
        self.dont_merge = 1
    }
}

/// PCI domain width (depends on hwloc version)
#[cfg(feature = "hwloc-3_0_0")]
#[cfg_attr(docsrs, doc(cfg(all())))]
pub type PCIDomain = u32;

/// PCI domain width (depends on hwloc version)
#[cfg(not(feature = "hwloc-3_0_0"))]
#[cfg_attr(docsrs, doc(cfg(all())))]
pub type PCIDomain = u16;

/// [`PCIDevice`]-specific attributes
///
/// [`PCIDevice`]: ObjectType::PCIDevice
#[derive(Copy, Clone, Debug, Default, PartialEq)]
#[doc(alias = "hwloc_pcidev_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s")]
#[repr(C)]
pub struct PCIDeviceAttributes {
    /// PCI domain
    domain: PCIDomain,

    /// PCI bus id
    bus: c_uchar,

    /// PCI bus device
    dev: c_uchar,

    /// PCI function
    func: c_uchar,

    /// PCI class id
    class_id: c_ushort,

    /// PCI vendor id
    vendor_id: c_ushort,

    /// PCI device id
    device_id: c_ushort,

    /// PCI subvendor id
    subvendor_id: c_ushort,

    /// PCI subdevice id
    subdevice_id: c_ushort,

    /// PCI revision
    revision: c_uchar,

    /// Link speed in GB/s
    linkspeed: c_float,
}
//
impl PCIDeviceAttributes {
    /// PCI domain
    #[doc(alias = "hwloc_pcidev_attr_s::domain")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::domain")]
    pub fn domain(&self) -> PCIDomain {
        self.domain
    }

    /// PCI bus id
    #[doc(alias = "hwloc_pcidev_attr_s::bus")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::bus")]
    pub fn bus_id(&self) -> u8 {
        self.bus
    }

    /// PCI bus device
    #[doc(alias = "hwloc_pcidev_attr_s::dev")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::dev")]
    pub fn bus_device(&self) -> u8 {
        self.dev
    }

    /// PCI function
    #[doc(alias = "hwloc_pcidev_attr_s::func")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::func")]
    pub fn function(&self) -> u8 {
        self.func
    }

    /// PCI class id
    #[doc(alias = "hwloc_pcidev_attr_s::class_id")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::class_id")]
    pub fn class_id(&self) -> u16 {
        self.class_id
    }

    /// PCI vendor id
    #[doc(alias = "hwloc_pcidev_attr_s::vendor_id")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::vendor_id")]
    pub fn vendor_id(&self) -> u16 {
        self.vendor_id
    }

    /// PCI device id
    #[doc(alias = "hwloc_pcidev_attr_s::device_id")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::device_id")]
    pub fn device_id(&self) -> u16 {
        self.device_id
    }

    /// PCI subvendor id
    #[doc(alias = "hwloc_pcidev_attr_s::subvendor_id")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::subvendor_id")]
    pub fn subvendor_id(&self) -> u16 {
        self.subvendor_id
    }

    /// PCI subdevice id
    #[doc(alias = "hwloc_pcidev_attr_s::subdevice_id")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::subdevice_id")]
    pub fn subdevice_id(&self) -> u16 {
        self.subdevice_id
    }

    /// PCI revision
    #[doc(alias = "hwloc_pcidev_attr_s::revision")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::revision")]
    pub fn revision(&self) -> u8 {
        self.revision
    }

    /// Link speed in GB/s
    #[doc(alias = "hwloc_pcidev_attr_s::linkspeed")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::linkspeed")]
    pub fn link_speed(&self) -> f32 {
        self.linkspeed
    }
}

/// [`Bridge`]-specific attributes
///
/// [`Bridge`]: ObjectType::Bridge
#[derive(Copy, Clone)]
#[doc(alias = "hwloc_bridge_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s")]
#[repr(C)]
pub struct BridgeAttributes {
    /// # Safety
    ///
    /// This union is trusted to be in sync with `upstream_type`
    upstream: RawUpstreamAttributes,

    /// Upstream type
    upstream_type: RawBridgeType,

    /// # Safety
    ///
    /// This union is trusted to be in sync with `downstream_type`
    downstream: RawDownstreamAttributes,

    /// Downstream type
    downstream_type: RawBridgeType,

    /// Object depth
    depth: c_uint,
}
//
impl BridgeAttributes {
    /// Upstream type
    #[doc(alias = "hwloc_bridge_attr_s::upstream_type")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::upstream_type")]
    pub fn upstream_type(&self) -> BridgeType {
        self.upstream_type
            .try_into()
            .expect("Got unexpected upstream type")
    }

    /// Upstream attributes
    #[doc(alias = "hwloc_bridge_attr_s::upstream")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::upstream")]
    pub fn upstream_attributes(&self) -> Option<UpstreamAttributes<'_>> {
        // SAFETY: Per type invariant
        unsafe { UpstreamAttributes::new(self.upstream_type(), &self.upstream) }
    }

    /// Downstream type
    #[doc(alias = "hwloc_bridge_attr_s::downstream_type")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::downstream_type")]
    pub fn downstream_type(&self) -> BridgeType {
        self.downstream_type
            .try_into()
            .expect("Got unexpected downstream type")
    }

    /// Downstream attributes
    #[doc(alias = "hwloc_bridge_attr_s::downstream")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::downstream")]
    pub fn downstream_attributes(&self) -> Option<DownstreamAttributes<'_>> {
        // SAFETY: Per type invariant
        unsafe { DownstreamAttributes::new(self.downstream_type(), &self.downstream) }
    }

    /// Object depth
    #[doc(alias = "hwloc_bridge_attr_s::depth")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::depth")]
    pub fn depth(&self) -> usize {
        int::expect_usize(self.depth)
    }
}
//
#[allow(clippy::missing_fields_in_debug)]
impl fmt::Debug for BridgeAttributes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BridgeAttributes")
            .field("upstream_attributes", &self.upstream_attributes())
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

/// hwloc FFI for `hwloc_bridge_attr_s::upstream`
#[derive(Copy, Clone)]
#[repr(C)]
pub(crate) union RawUpstreamAttributes {
    /// PCI-specific attributes
    pci: PCIDeviceAttributes,
}

/// Bridge upstream attributes
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum UpstreamAttributes<'object> {
    /// PCI-specific attributes
    PCI(&'object PCIDeviceAttributes),
}
//
impl<'object> UpstreamAttributes<'object> {
    /// Wrap the upstream attributes behind a safe API
    ///
    /// # Safety
    ///
    /// `attr` must be consistent with `ty`.
    pub(crate) unsafe fn new(ty: BridgeType, attr: &'object RawUpstreamAttributes) -> Option<Self> {
        // SAFETY: Per input precondition
        unsafe {
            match ty {
                BridgeType::PCI => Some(Self::PCI(&attr.pci)),
                BridgeType::Host => None,
            }
        }
    }
}

/// Downstream PCI device attributes
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[repr(C)]
pub struct DownstreamPCIAttributes {
    /// PCI domain
    domain: PCIDomain,

    /// PCI secondary bus
    secondary_bus: c_uchar,

    /// PCI subordinate bus
    subordinate_bus: c_uchar,
}
//
impl DownstreamPCIAttributes {
    /// PCI domain
    pub fn domain(&self) -> PCIDomain {
        self.domain
    }

    /// PCI secondary bus
    pub fn secondary_bus(&self) -> u8 {
        self.secondary_bus
    }

    /// PCI subordinate bus
    pub fn subordinate_bus(&self) -> u8 {
        self.subordinate_bus
    }
}

/// hwloc FFI for `hwloc_bridge_attr_s::downstream`
#[derive(Copy, Clone)]
#[repr(C)]
pub(crate) union RawDownstreamAttributes {
    /// PCI-specific attributes
    pci: DownstreamPCIAttributes,
}

/// Bridge downstream attributes
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum DownstreamAttributes<'object> {
    /// PCI-specific attributes
    PCI(&'object DownstreamPCIAttributes),
}
//
impl<'object> DownstreamAttributes<'object> {
    /// Wrap the upstream attributes behind a safe API
    ///
    /// # Safety
    ///
    /// `attr` must be consistent with `ty`.
    #[allow(clippy::unnecessary_wraps)]
    pub(crate) unsafe fn new(
        ty: BridgeType,
        attr: &'object RawDownstreamAttributes,
    ) -> Option<Self> {
        // SAFETY: Per input precondition
        unsafe {
            match ty {
                BridgeType::PCI => Some(Self::PCI(&attr.pci)),
                BridgeType::Host => unreachable!("Host bridge type should not appear downstream"),
            }
        }
    }
}

/// [`OSDevice`]-specific attributes
///
/// [`OSDevice`]: ObjectType::OSDevice
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_osdev_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_osdev_attr_s")]
#[repr(C)]
pub struct OSDeviceAttributes {
    /// OS device type
    ty: RawOSDeviceType,
}
//
impl OSDeviceAttributes {
    /// OS device type
    #[doc(alias = "hwloc_osdev_attr_s::type")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_osdev_attr_s::type")]
    pub fn device_type(&self) -> OSDeviceType {
        self.ty.try_into().expect("Got unexpected OS device type")
    }
}
