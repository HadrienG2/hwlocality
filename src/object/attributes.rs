//! Object attributes

// - Main docs: https://hwloc.readthedocs.io/en/v2.9/unionhwloc__obj__attr__u.html
// - Union semantics: https://hwloc.readthedocs.io/en/v2.9/attributes.html#attributes_normal

#[cfg(doc)]
use crate::topology::support::DiscoverySupport;
use crate::{
    ffi,
    object::types::{
        BridgeType, CacheType, OSDeviceType, ObjectType, RawBridgeType, RawCacheType,
        RawOSDeviceType,
    },
};
use hwlocality_sys::{
    hwloc_bridge_attr_s, hwloc_cache_attr_s, hwloc_group_attr_s, hwloc_memory_page_type_s,
    hwloc_numanode_attr_s, hwloc_obj_attr_u, hwloc_osdev_attr_s, hwloc_pcidev_attr_s,
    RawDownstreamAttributes, RawDownstreamPCIAttributes, RawUpstreamAttributes,
};
use std::{
    ffi::{c_float, c_int, c_uchar, c_uint, c_ushort},
    fmt,
    hash::Hash,
    num::NonZeroUsize,
};

/// hwloc FFI for the hwloc_obj_attr_u union
pub(crate) type RawObjectAttributes = hwloc_obj_attr_u;

/// ObjectType-specific attributes
#[derive(Copy, Clone, Debug, PartialEq)]
#[doc(alias = "hwloc_obj_attr_u")]
pub enum ObjectAttributes<'attr> {
    /// [`NUMANode`]-specific attributes
    ///
    /// [`NUMANode`]: ObjectType::NUMANode
    #[doc(alias = "hwloc_obj_attr_u::numanode")]
    NUMANode(&'attr NUMANodeAttributes),

    /// Cache-specific attributes
    #[doc(alias = "hwloc_obj_attr_u::cache")]
    Cache(&'attr CacheAttributes),

    /// [`Group`]-specific attributes
    ///
    /// [`Group`]: ObjectType::Group
    #[doc(alias = "hwloc_obj_attr_u::group")]
    Group(&'attr GroupAttributes),

    /// [`PCIDevice`]-specific attributes
    ///
    /// [`PCIDevice`]: ObjectType::PCIDevice
    #[doc(alias = "hwloc_obj_attr_u::pcidev")]
    PCIDevice(&'attr PCIDeviceAttributes),

    /// [`Bridge`]-specific attributes
    ///
    /// [`Bridge`]: ObjectType::Bridge
    #[doc(alias = "hwloc_obj_attr_u::bridge")]
    Bridge(&'attr BridgeAttributes),

    /// [`OSDevice`]-specific attributes
    ///
    /// [`OSDevice`]: ObjectType::OSDevice
    #[doc(alias = "hwloc_obj_attr_u::osdev")]
    OSDevice(&'attr OSDeviceAttributes),
}
//
impl<'attr> ObjectAttributes<'attr> {
    /// Wrap the hwloc object type specific attributes behind a safe API
    ///
    /// # Safety
    ///
    /// If non-null, the `attr` pointer must target `RawObjectAttributes` that
    /// are valid for lifetime `'attr` and consistent with object type `ty`.
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

/// [`NUMANode`]-specific attributes
///
/// [`NUMANode`]: ObjectType::NUMANode
#[derive(Copy, Clone, Debug, Default, Eq)]
#[doc(alias = "hwloc_numanode_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s")]
#[repr(transparent)]
pub struct NUMANodeAttributes(hwloc_numanode_attr_s);
//
impl NUMANodeAttributes {
    /// Local memory in bytes
    ///
    /// Requires [`DiscoverySupport::numa_memory()`].
    #[doc(alias = "hwloc_numanode_attr_s::local_memory")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::local_memory")]
    pub fn local_memory(&self) -> u64 {
        self.0.local_memory
    }

    /// Memory page types, sorted by increasing page size
    #[doc(alias = "hwloc_numanode_attr_s::page_types")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::page_types")]
    pub fn page_types(&self) -> &[MemoryPageType] {
        if self.0.page_types.is_null() {
            return &[];
        }
        unsafe {
            std::slice::from_raw_parts(
                self.0.page_types,
                // If this fails, it means pages_types_len does not fit in a
                // size_t, but by definition of size_t that cannot happen...
                self.0.page_types_len.try_into().expect("Should not happen"),
            )
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
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_memory_page_type_s")]
#[doc(alias = "hwloc_numanode_attr_s::hwloc_memory_page_type_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::hwloc_memory_page_type_s")]
#[repr(transparent)]
pub struct MemoryPageType(hwloc_memory_page_type_s);
//
impl MemoryPageType {
    /// Size of pages
    #[doc(alias = "hwloc_memory_page_type_s::size")]
    #[doc(alias = "hwloc_numanode_attr_s::hwloc_memory_page_type_s::size")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::hwloc_memory_page_type_s::size")]
    pub fn size(&self) -> u64 {
        self.0.size
    }

    /// Number of pages of this size
    #[doc(alias = "hwloc_memory_page_type_s::count")]
    #[doc(alias = "hwloc_numanode_attr_s::hwloc_memory_page_type_s::count")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::hwloc_memory_page_type_s::count")]
    pub fn count(&self) -> u64 {
        self.0.count
    }
}

/// Cache-specific attributes
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_cache_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s")]
#[repr(transparent)]
pub struct CacheAttributes(hwloc_cache_attr_s);
//
impl CacheAttributes {
    /// Size of the cache in bytes
    #[doc(alias = "hwloc_cache_attr_s::size")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::size")]
    pub fn size(&self) -> u64 {
        self.0.size
    }

    /// Depth of the cache (e.g. L1, L2, ...)
    #[doc(alias = "hwloc_cache_attr_s::depth")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::depth")]
    pub fn depth(&self) -> usize {
        ffi::expect_usize(self.0.depth)
    }

    /// Cache line size in bytes
    #[doc(alias = "hwloc_cache_attr_s::linesize")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::linesize")]
    pub fn line_size(&self) -> Option<NonZeroUsize> {
        NonZeroUsize::new(ffi::expect_usize(self.0.linesize))
    }

    /// Ways of associativity
    #[doc(alias = "hwloc_cache_attr_s::associativity")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::associativity")]
    pub fn associativity(&self) -> CacheAssociativity {
        match self.0.associativity {
            -1 => CacheAssociativity::Full,
            0 => CacheAssociativity::Unknown,
            ways if ways > 0 => {
                let ways = c_uint::try_from(ways).expect("int > 0 -> uint should not fail");
                let ways = ffi::expect_usize(ways);
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
        self.0.ty.try_into().expect("Got unexpected cache type")
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
#[repr(transparent)]
pub struct GroupAttributes(hwloc_group_attr_s);
//
impl GroupAttributes {
    /// Depth of group object
    ///
    /// It may change if intermediate Group objects are added.
    #[doc(alias = "hwloc_group_attr_s::depth")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_group_attr_s::depth")]
    pub fn depth(&self) -> usize {
        ffi::expect_usize(self.0.depth)
    }

    /// Internally-used kind of group
    #[allow(unused)]
    pub(crate) fn kind(&self) -> usize {
        ffi::expect_usize(self.0.kind)
    }

    /// Tell hwloc that this group object should always be discarded in favor of
    /// any existing `Group` with the same locality.
    #[cfg(feature = "hwloc-2_3_0")]
    pub(crate) fn favor_merging(&mut self) {
        self.0.kind = c_uint::MAX
    }

    /// Internally-used subkind to distinguish different levels of groups with
    /// the same kind
    #[allow(unused)]
    #[doc(alias = "hwloc_group_attr_s::subkind")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_group_attr_s::subkind")]
    pub(crate) fn subkind(&self) -> usize {
        ffi::expect_usize(self.0.subkind)
    }

    /// Flag preventing groups from being automatically merged with identical
    /// parent or children
    #[cfg(feature = "hwloc-2_0_4")]
    pub fn merging_prevented(&self) -> bool {
        assert!(
            self.0.dont_merge == 0 || self.0.dont_merge == 1,
            "Unexpected hwloc_group_attr_s::dont_merge value"
        );
        self.0.dont_merge != 0
    }

    /// Tell hwloc that it should not merge this group object with other
    /// hierarchically-identical objects.
    #[cfg(feature = "hwloc-2_3_0")]
    pub(crate) fn prevent_merging(&mut self) {
        self.0.dont_merge = 1
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
#[repr(transparent)]
pub struct PCIDeviceAttributes(hwloc_pcidev_attr_s);
//
impl PCIDeviceAttributes {
    /// PCI domain
    #[doc(alias = "hwloc_pcidev_attr_s::domain")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::domain")]
    pub fn domain(&self) -> PCIDomain {
        self.0.domain
    }

    /// PCI bus id
    #[doc(alias = "hwloc_pcidev_attr_s::bus")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::bus")]
    pub fn bus_id(&self) -> u8 {
        self.0.bus
    }

    /// PCI bus device
    #[doc(alias = "hwloc_pcidev_attr_s::dev")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::dev")]
    pub fn bus_device(&self) -> u8 {
        self.0.dev
    }

    /// PCI function
    #[doc(alias = "hwloc_pcidev_attr_s::func")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::func")]
    pub fn function(&self) -> u8 {
        self.0.func
    }

    /// PCI class ID
    #[doc(alias = "hwloc_pcidev_attr_s::class_id")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::class_id")]
    pub fn class_id(&self) -> u16 {
        self.0.class_id
    }

    /// PCI vendor ID
    #[doc(alias = "hwloc_pcidev_attr_s::vendor_id")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::vendor_id")]
    pub fn vendor_id(&self) -> u16 {
        self.0.vendor_id
    }

    /// PCI device ID
    #[doc(alias = "hwloc_pcidev_attr_s::device_id")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::device_id")]
    pub fn device_id(&self) -> u16 {
        self.0.device_id
    }

    /// PCI sub-vendor ID
    #[doc(alias = "hwloc_pcidev_attr_s::subvendor_id")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::subvendor_id")]
    pub fn subvendor_id(&self) -> u16 {
        self.0.subvendor_id
    }

    /// PCI sub-device ID
    #[doc(alias = "hwloc_pcidev_attr_s::subdevice_id")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::subdevice_id")]
    pub fn subdevice_id(&self) -> u16 {
        self.0.subdevice_id
    }

    /// PCI revision
    #[doc(alias = "hwloc_pcidev_attr_s::revision")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::revision")]
    pub fn revision(&self) -> u8 {
        self.0.revision
    }

    /// Link speed in GB/s
    #[doc(alias = "hwloc_pcidev_attr_s::linkspeed")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::linkspeed")]
    pub fn link_speed(&self) -> f32 {
        self.0.linkspeed
    }
}

/// [`Bridge`]-specific attributes
///
/// [`Bridge`]: ObjectType::Bridge
#[derive(Copy, Clone)]
#[doc(alias = "hwloc_bridge_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s")]
#[repr(transparent)]
pub struct BridgeAttributes(hwloc_bridge_attr_s);
//
impl BridgeAttributes {
    /// Upstream type
    #[doc(alias = "hwloc_bridge_attr_s::upstream_type")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::upstream_type")]
    pub fn upstream_type(&self) -> BridgeType {
        self.0
            .upstream_type
            .try_into()
            .expect("Got unexpected upstream type")
    }

    /// Upstream attributes
    #[doc(alias = "hwloc_bridge_attr_s::upstream")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::upstream")]
    pub fn upstream_attributes(&self) -> Option<UpstreamAttributes> {
        unsafe { UpstreamAttributes::new(self.upstream_type(), &self.0.upstream) }
    }

    /// Downstream type
    #[doc(alias = "hwloc_bridge_attr_s::downstream_type")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::downstream_type")]
    pub fn downstream_type(&self) -> BridgeType {
        self.0
            .downstream_type
            .try_into()
            .expect("Got unexpected downstream type")
    }

    /// Downstream attributes
    #[doc(alias = "hwloc_bridge_attr_s::downstream")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::downstream")]
    pub fn downstream_attributes(&self) -> Option<DownstreamAttributes> {
        unsafe { DownstreamAttributes::new(self.downstream_type(), &self.0.downstream) }
    }

    /// Bridge depth
    #[doc(alias = "hwloc_bridge_attr_s::depth")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::depth")]
    pub fn depth(&self) -> usize {
        ffi::expect_usize(self.0.depth)
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

/// Bridge upstream attributes
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum UpstreamAttributes<'attr> {
    /// PCI-specific attributes
    PCI(&'attr PCIDeviceAttributes),
}
//
impl<'attr> UpstreamAttributes<'attr> {
    /// Wrap the upstream attributes behind a safe API
    ///
    /// # Safety
    ///
    /// `attr` must be consistent with `ty`.
    pub(crate) unsafe fn new(ty: BridgeType, attr: &'attr RawUpstreamAttributes) -> Option<Self> {
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
#[repr(transparent)]
pub struct DownstreamPCIAttributes(RawDownstreamPCIAttributes);
//
impl DownstreamPCIAttributes {
    /// Downstram domain
    pub fn domain(&self) -> PCIDomain {
        self.0.domain
    }

    /// Downstream secondary bus
    pub fn secondary_bus(&self) -> u8 {
        self.0.secondary_bus
    }

    /// Downstream subordinate bus
    pub fn subordinate_bus(&self) -> u8 {
        self.0.subordinate_bus
    }
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
    ///
    /// # Safety
    ///
    /// `attr` must be consistent with `ty`.
    pub(crate) unsafe fn new(ty: BridgeType, attr: &'attr RawDownstreamAttributes) -> Option<Self> {
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
pub struct OSDeviceAttributes(hwloc_osdev_attr_s);
//
impl OSDeviceAttributes {
    /// OS device type
    #[doc(alias = "hwloc_osdev_attr_s::type")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_osdev_attr_s::type")]
    pub fn device_type(&self) -> OSDeviceType {
        self.0.ty.try_into().expect("Got unexpected OS device type")
    }
}
