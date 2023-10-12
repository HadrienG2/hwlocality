//! Object attributes
//!
//! Some [`TopologyObject` types](ObjectType) come with supplementary attributes
//! that extend the object's description. These attributes can be accessed using
//! the [`TopologyObject::attributes()`] method, and are described using types
//! defined inside of this module.

// - Main docs: https://hwloc.readthedocs.io/en/v2.9/unionhwloc__obj__attr__u.html
// - Union semantics: https://hwloc.readthedocs.io/en/v2.9/attributes.html#attributes_normal

use crate::{
    ffi::{
        int,
        transparent::{AsNewtype, TransparentNewtype},
    },
    object::types::{BridgeType, CacheType, OSDeviceType, ObjectType},
};
#[cfg(doc)]
use crate::{object::TopologyObject, topology::support::DiscoverySupport};
use hwlocality_sys::{
    hwloc_bridge_attr_s, hwloc_cache_attr_s, hwloc_group_attr_s, hwloc_memory_page_type_s,
    hwloc_numanode_attr_s, hwloc_obj_attr_u, hwloc_osdev_attr_s, hwloc_pcidev_attr_s,
    RawDownstreamAttributes, RawDownstreamPCIAttributes, RawUpstreamAttributes,
};
#[allow(unused)]
#[cfg(test)]
use pretty_assertions::{assert_eq, assert_ne};
use std::{
    ffi::c_uint,
    fmt,
    hash::Hash,
    marker::PhantomData,
    num::{NonZeroU64, NonZeroUsize},
};

/// ObjectType-specific attributes
#[derive(Copy, Clone, Debug, PartialEq)]
#[doc(alias = "hwloc_obj_attr_u")]
pub enum ObjectAttributes<'object> {
    /// [`NUMANode`]-specific attributes
    ///
    /// [`NUMANode`]: ObjectType::NUMANode
    #[doc(alias = "hwloc_obj_attr_u::numanode")]
    NUMANode(&'object NUMANodeAttributes<'object>),

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
    /// If non-null, the `attr` pointer must target `hwloc_obj_attr_u` that
    /// are valid for lifetime `'object` and consistent with object type `ty`.
    pub(crate) unsafe fn new(ty: ObjectType, attr: &'object *mut hwloc_obj_attr_u) -> Option<Self> {
        if attr.is_null() {
            return None;
        }
        // SAFETY: Safe due to input precondition
        let attr: &hwloc_obj_attr_u = unsafe { &**attr };

        // SAFETY: - We checked for union field access validity via the type
        //         - Type is truted to match union state per input precondition
        unsafe {
            #[allow(clippy::wildcard_enum_match_arm)]
            match ty {
                ObjectType::NUMANode => Some(Self::NUMANode((&attr.numa).as_newtype())),
                ObjectType::Group => Some(Self::Group((&attr.group).as_newtype())),
                ObjectType::PCIDevice => Some(Self::PCIDevice((&attr.pcidev).as_newtype())),
                ObjectType::Bridge => Some(Self::Bridge((&attr.bridge).as_newtype())),
                ObjectType::OSDevice => Some(Self::OSDevice((&attr.osdev).as_newtype())),
                _ if ty.is_cpu_cache() => Some(Self::Cache((&attr.cache).as_newtype())),
                _ => None,
            }
        }
    }
}

/// [`NUMANode`]-specific attributes
///
/// You cannot create an owned object of this type, it belongs to the topology.
///
/// [`NUMANode`]: ObjectType::NUMANode
//
// --- Implementation details ---
//
// # Safety
//
// If non-null, `page_types` is trusted to point to a C-style array of
// `page_types_len` memory page types, sorted by increasing page size.
#[allow(missing_copy_implementations)]
#[derive(Copy, Clone, Debug, Default)]
#[doc(alias = "hwloc_numanode_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s")]
#[repr(transparent)]
pub struct NUMANodeAttributes<'object>(hwloc_numanode_attr_s, PhantomData<&'object MemoryPageType>);
//
impl<'object> NUMANodeAttributes<'object> {
    /// Node-local memory in bytes
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
    pub fn page_types(&self) -> &'object [MemoryPageType] {
        if self.0.page_types.is_null() {
            assert_eq!(
                self.0.page_types_len, 0,
                "Got null pages types pointer with non-zero length"
            );
            return &[];
        }
        // SAFETY: - Pointer and length assumed valid per type invariant
        //         - AsNewtype is trusted to be implemented correctly
        unsafe {
            std::slice::from_raw_parts(
                self.0.page_types.as_newtype(),
                // If this fails, it means pages_types_len does not fit in a
                // size_t, but by definition of size_t that cannot happen
                self.0
                    .page_types_len
                    .try_into()
                    .expect("should fit in usize"),
            )
        }
    }
}
//
impl Eq for NUMANodeAttributes<'_> {}
//
impl Hash for NUMANodeAttributes<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.local_memory().hash(state);
        self.page_types().hash(state);
    }
}
//
impl PartialEq for NUMANodeAttributes<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.local_memory() == other.local_memory() && self.page_types() == other.page_types()
    }
}
//
// SAFETY: No internal mutability
unsafe impl Send for NUMANodeAttributes<'_> {}
//
// SAFETY: No internal mutability
unsafe impl Sync for NUMANodeAttributes<'_> {}
//
// SAFETY: NUMANodeAttributes is a repr(transparent) newtype of hwloc_numanode_attr_s
unsafe impl TransparentNewtype for NUMANodeAttributes<'_> {
    type Inner = hwloc_numanode_attr_s;
}

/// Local memory page type
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_memory_page_type_s")]
#[doc(alias = "hwloc_numanode_attr_s::hwloc_memory_page_type_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::hwloc_memory_page_type_s")]
#[repr(transparent)]
pub struct MemoryPageType(hwloc_memory_page_type_s);
//
impl MemoryPageType {
    /// Size of pages, if known
    #[doc(alias = "hwloc_memory_page_type_s::size")]
    #[doc(alias = "hwloc_numanode_attr_s::hwloc_memory_page_type_s::size")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::hwloc_memory_page_type_s::size")]
    pub fn size(&self) -> Option<NonZeroU64> {
        NonZeroU64::new(self.0.size)
    }

    /// Number of pages of this size
    #[doc(alias = "hwloc_memory_page_type_s::count")]
    #[doc(alias = "hwloc_numanode_attr_s::hwloc_memory_page_type_s::count")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::hwloc_memory_page_type_s::count")]
    pub fn count(&self) -> u64 {
        self.0.count
    }
}
//
#[cfg(any(test, feature = "quickcheck"))]
impl quickcheck::Arbitrary for MemoryPageType {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        // Bias RNG to ensure reasonable odds of zero sizes
        Self(hwloc_memory_page_type_s {
            size: *g
                .choose(&[0, 1, 2, u64::MAX - 1, u64::MAX])
                .expect("slice isn't empty"),
            count: u64::arbitrary(g),
        })
    }

    #[cfg(not(tarpaulin_include))]
    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(
            ((self.0.size, self.0.count).shrink())
                .map(|(size, count)| Self(hwloc_memory_page_type_s { size, count })),
        )
    }
}
//
// SAFETY: MemoryPageType is a repr(transparent) newtype of hwloc_memory_page_type_s
unsafe impl TransparentNewtype for MemoryPageType {
    type Inner = hwloc_memory_page_type_s;
}

/// Cache-specific attributes
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_cache_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s")]
#[repr(transparent)]
pub struct CacheAttributes(hwloc_cache_attr_s);
//
impl CacheAttributes {
    /// Size of the cache in bytes, if known
    #[doc(alias = "hwloc_cache_attr_s::size")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::size")]
    pub fn size(&self) -> Option<NonZeroU64> {
        NonZeroU64::new(self.0.size)
    }

    /// Depth of the cache (e.g. L1, L2, ...)
    #[doc(alias = "hwloc_cache_attr_s::depth")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::depth")]
    pub fn depth(&self) -> usize {
        int::expect_usize(self.0.depth)
    }

    /// Cache line size in bytes, if known
    #[doc(alias = "hwloc_cache_attr_s::linesize")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::linesize")]
    pub fn line_size(&self) -> Option<NonZeroUsize> {
        NonZeroUsize::new(int::expect_usize(self.0.linesize))
    }

    /// Ways of associativity
    #[doc(alias = "hwloc_cache_attr_s::associativity")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::associativity")]
    pub fn associativity(&self) -> CacheAssociativity {
        match self.0.associativity {
            -1 => CacheAssociativity::Full,
            0 => CacheAssociativity::Unknown,
            ways if ways > 0 => {
                let ways = c_uint::try_from(ways).expect("int > 0 -> uint can't fail");
                let ways = int::expect_usize(ways);
                let ways = NonZeroUsize::new(ways).expect("usize > 0 -> NonZeroUsize can't fail");
                CacheAssociativity::Ways(ways)
            }
            unexpected => unreachable!("got unexpected cache associativity {unexpected}"),
        }
    }

    /// Cache type
    #[doc(alias = "hwloc_cache_attr_s::type")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::type")]
    pub fn cache_type(&self) -> CacheType {
        self.0.ty.try_into().expect("got unexpected cache type")
    }
}
//
#[cfg(any(test, feature = "quickcheck"))]
impl quickcheck::Arbitrary for CacheAttributes {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        use hwlocality_sys::hwloc_obj_cache_type_t;
        use std::ffi::c_int;

        // Bias RNG to ensure reasonable odds of zero sizes
        let size = *g
            .choose(&[0, 1, 2, u64::MAX - 1, u64::MAX])
            .expect("slice isn't empty");
        let linesize = *g
            .choose(&[0, 1, 2, c_uint::MAX - 1, c_uint::MAX])
            .expect("slice isn't empty");

        // Bias RNG to ensure reasonable odds of valid cache types
        let max_valid_cache_type = enum_iterator::all::<CacheType>()
            .map(hwloc_obj_cache_type_t::from)
            .max()
            .expect("enum has >= 1 variants");
        let cache_type_range = 2 * max_valid_cache_type;
        let ty = hwloc_obj_cache_type_t::arbitrary(g) % cache_type_range;

        // Bias RNG to ensure reasonably uniform coverage of associativity
        // alternatives
        let associativity = *g
            .choose(&[
                // Invalid range
                c_int::MIN,
                c_int::MIN + 1,
                -3,
                -2,
                // Full
                -1,
                // Unknown
                0,
                // N-ways range
                1,
                2,
                c_int::MAX - 1,
                c_int::MAX,
            ])
            .expect("slice isn't empty");

        // Let depth use a uniform distribution
        Self(hwloc_cache_attr_s {
            size,
            depth: c_uint::arbitrary(g),
            linesize,
            associativity,
            ty,
        })
    }

    #[cfg(not(tarpaulin_include))]
    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(
            (
                self.0.size,
                self.0.depth,
                self.0.linesize,
                self.0.associativity,
                self.0.ty,
            )
                .shrink()
                .map(|(size, depth, linesize, associativity, ty)| {
                    Self(hwloc_cache_attr_s {
                        size,
                        depth,
                        linesize,
                        associativity,
                        ty,
                    })
                }),
        )
    }
}
//
// SAFETY: CacheAttributes is a repr(transparent) newtype of hwloc_cache_attr_s
unsafe impl TransparentNewtype for CacheAttributes {
    type Inner = hwloc_cache_attr_s;
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
//
#[cfg(any(test, feature = "quickcheck"))]
impl quickcheck::Arbitrary for CacheAssociativity {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        // Bias RNG to ensure reasonably uniform variant coverage
        *g.choose(&[
            Self::Unknown,
            Self::Full,
            Self::Ways(NonZeroUsize::MIN),
            Self::Ways(NonZeroUsize::new(2).expect("not zero")),
            Self::Ways(NonZeroUsize::new(usize::MAX - 1).expect("not zero")),
            Self::Ways(NonZeroUsize::MAX),
        ])
        .expect("slice isn't empty")
    }

    #[cfg(not(tarpaulin_include))]
    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        match *self {
            Self::Ways(ways) => Box::new(
                ways.shrink()
                    .map(Self::Ways)
                    .chain([Self::Full, Self::Unknown]),
            ),
            Self::Full => quickcheck::single_shrinker(Self::Unknown),
            Self::Unknown => quickcheck::empty_shrinker(),
        }
    }
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
        int::expect_usize(self.0.depth)
    }

    /// Internally-used kind of group
    #[allow(unused)]
    pub(crate) fn kind(&self) -> usize {
        int::expect_usize(self.0.kind)
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
        int::expect_usize(self.0.subkind)
    }

    /// Flag preventing groups from being automatically merged with identical
    /// parent or children
    #[cfg(feature = "hwloc-2_0_4")]
    pub fn merging_prevented(&self) -> bool {
        assert!(
            self.0.dont_merge == 0 || self.0.dont_merge == 1,
            "unexpected hwloc_group_attr_s::dont_merge value"
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
//
#[cfg(any(test, feature = "quickcheck"))]
impl quickcheck::Arbitrary for GroupAttributes {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        // Bias RNG to ensure reasonable odds of valid dont_merge flags
        Self(hwloc_group_attr_s {
            depth: c_uint::arbitrary(g),
            kind: c_uint::arbitrary(g),
            subkind: c_uint::arbitrary(g),
            #[cfg(feature = "hwloc-2_0_4")]
            dont_merge: std::ffi::c_uchar::arbitrary(g) % 4,
        })
    }

    #[cfg(not(tarpaulin_include))]
    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        #[cfg(feature = "hwloc-2_0_4")]
        {
            Box::new(
                (self.0.depth, self.0.kind, self.0.subkind, self.0.dont_merge)
                    .shrink()
                    .map(|(depth, kind, subkind, dont_merge)| {
                        Self(hwloc_group_attr_s {
                            depth,
                            kind,
                            subkind,
                            dont_merge,
                        })
                    }),
            )
        }
        #[cfg(not(feature = "hwloc-2_0_4"))]
        {
            Box::new((self.0.depth, self.0.kind, self.0.subkind).shrink().map(
                |(depth, kind, subkind)| {
                    Self(hwloc_group_attr_s {
                        depth,
                        kind,
                        subkind,
                    })
                },
            ))
        }
    }
}
//
// SAFETY: GroupAttributes is a repr(transparent) newtype of hwloc_group_attr_s
unsafe impl TransparentNewtype for GroupAttributes {
    type Inner = hwloc_group_attr_s;
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
//
#[cfg(any(test, feature = "quickcheck"))]
impl quickcheck::Arbitrary for PCIDeviceAttributes {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        Self(hwloc_pcidev_attr_s {
            domain: PCIDomain::arbitrary(g),
            bus: u8::arbitrary(g),
            dev: u8::arbitrary(g),
            func: u8::arbitrary(g),
            class_id: u16::arbitrary(g),
            vendor_id: u16::arbitrary(g),
            device_id: u16::arbitrary(g),
            subvendor_id: u16::arbitrary(g),
            subdevice_id: u16::arbitrary(g),
            revision: u8::arbitrary(g),
            linkspeed: f32::arbitrary(g),
        })
    }

    #[cfg(not(tarpaulin_include))]
    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(
            (
                (self.0.domain, self.0.bus, self.0.dev, self.0.func),
                (self.0.class_id, self.0.vendor_id, self.0.device_id),
                (self.0.subvendor_id, self.0.subdevice_id, self.0.revision),
                self.0.linkspeed,
            )
                .shrink()
                .map(
                    |(
                        (domain, bus, dev, func),
                        (class_id, vendor_id, device_id),
                        (subvendor_id, subdevice_id, revision),
                        linkspeed,
                    )| {
                        Self(hwloc_pcidev_attr_s {
                            domain,
                            bus,
                            dev,
                            func,
                            class_id,
                            vendor_id,
                            device_id,
                            subvendor_id,
                            subdevice_id,
                            revision,
                            linkspeed,
                        })
                    },
                ),
        )
    }
}
//
// SAFETY: PCIDeviceAttributes is a repr(transparent) newtype of hwloc_pcidev_attr_s
unsafe impl TransparentNewtype for PCIDeviceAttributes {
    type Inner = hwloc_pcidev_attr_s;
}

/// [`Bridge`]-specific attributes
///
/// [`Bridge`]: ObjectType::Bridge
//
// --- Implementation details ---
//
// # Safety
//
// - `upstream` and `upstream_type` are trusted to be in sync.
// - `downstream` and `downstream_type` are trusted to be in sync.
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
            .expect("got unexpected upstream type")
    }

    /// Upstream attributes
    #[doc(alias = "hwloc_bridge_attr_s::upstream")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::upstream")]
    pub fn upstream_attributes(&self) -> Option<UpstreamAttributes<'_>> {
        // SAFETY: Per type invariant
        unsafe { UpstreamAttributes::new(self.upstream_type(), &self.0.upstream) }
    }

    /// Downstream type
    #[doc(alias = "hwloc_bridge_attr_s::downstream_type")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::downstream_type")]
    pub fn downstream_type(&self) -> BridgeType {
        self.0
            .downstream_type
            .try_into()
            .expect("got unexpected downstream type")
    }

    /// Downstream attributes
    #[doc(alias = "hwloc_bridge_attr_s::downstream")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::downstream")]
    pub fn downstream_attributes(&self) -> Option<DownstreamAttributes<'_>> {
        // SAFETY: Per type invariant
        unsafe { DownstreamAttributes::new(self.downstream_type(), &self.0.downstream) }
    }

    /// Bridge depth
    #[doc(alias = "hwloc_bridge_attr_s::depth")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::depth")]
    pub fn depth(&self) -> usize {
        int::expect_usize(self.0.depth)
    }
}
//
#[cfg(any(test, feature = "quickcheck"))]
impl quickcheck::Arbitrary for BridgeAttributes {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        use hwlocality_sys::hwloc_obj_bridge_type_t;

        // Bias RNG to ensure reasonable odds of valid bridge types
        let max_valid_bridge_type = enum_iterator::all::<BridgeType>()
            .map(hwloc_obj_bridge_type_t::from)
            .max()
            .expect("enum has >= 1 variants");
        let bridge_type_range = 2 * max_valid_bridge_type;

        // Rest is reasonably straightforward since currently only PCI upstreams
        // and downstreams are supported.
        Self(hwloc_bridge_attr_s {
            upstream_type: hwloc_obj_bridge_type_t::arbitrary(g) % bridge_type_range,
            upstream: RawUpstreamAttributes {
                pci: PCIDeviceAttributes::arbitrary(g).0,
            },
            downstream_type: hwloc_obj_bridge_type_t::arbitrary(g) % bridge_type_range,
            downstream: RawDownstreamAttributes {
                pci: DownstreamPCIAttributes::arbitrary(g).0,
            },
            depth: c_uint::arbitrary(g),
        })
    }

    #[cfg(not(tarpaulin_include))]
    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let self_ = *self;

        // We don't swich upstream/downstream type during shrinking, we just
        // simplify the type-specific attributes if any.
        let shrunk_upstream: Box<dyn Iterator<Item = RawUpstreamAttributes>> =
            match self.upstream_attributes() {
                Some(UpstreamAttributes::PCI(pci)) => {
                    Box::new(pci.shrink().map(|pci| RawUpstreamAttributes { pci: pci.0 }))
                }
                None => quickcheck::empty_shrinker(),
            };
        let shrunk_downstream: Box<dyn Iterator<Item = RawDownstreamAttributes>> =
            match self.downstream_attributes() {
                Some(DownstreamAttributes::PCI(pci)) => Box::new(
                    pci.shrink()
                        .map(|pci| RawDownstreamAttributes { pci: pci.0 }),
                ),
                None => quickcheck::empty_shrinker(),
            };

        // In the end, we sequence shrinkers together like the quickcheck tuple
        // shrinker does.
        Box::new(
            (shrunk_upstream.map(move |upstream| {
                Self(hwloc_bridge_attr_s {
                    upstream,
                    ..self_.0
                })
            }))
            .chain(shrunk_downstream.map(move |downstream| {
                Self(hwloc_bridge_attr_s {
                    downstream,
                    ..self_.0
                })
            }))
            .chain(
                (self.0.depth.shrink())
                    .map(move |depth| Self(hwloc_bridge_attr_s { depth, ..self_.0 })),
            ),
        )
    }
}
//
#[allow(clippy::missing_fields_in_debug)]
impl fmt::Debug for BridgeAttributes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BridgeAttributes")
            .field("upstream_attributes", &self.upstream_attributes())
            .field("downstream_attributes", &self.downstream_attributes())
            .field("depth", &self.0.depth)
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
//
// SAFETY: BridgeAttributes is a repr(transparent) newtype of hwloc_bridge_attr_s
unsafe impl TransparentNewtype for BridgeAttributes {
    type Inner = hwloc_bridge_attr_s;
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
        // SAFETY: attr.pci assumed valid if ty is PCI per input precondition
        unsafe {
            match ty {
                BridgeType::PCI => Some(Self::PCI((&attr.pci).as_newtype())),
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
    /// PCI domain
    pub fn domain(&self) -> PCIDomain {
        self.0.domain
    }

    /// PCI secondary bus
    pub fn secondary_bus(&self) -> u8 {
        self.0.secondary_bus
    }

    /// PCI subordinate bus
    pub fn subordinate_bus(&self) -> u8 {
        self.0.subordinate_bus
    }
}
//
#[cfg(any(test, feature = "quickcheck"))]
impl quickcheck::Arbitrary for DownstreamPCIAttributes {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        Self(RawDownstreamPCIAttributes {
            domain: PCIDomain::arbitrary(g),
            secondary_bus: u8::arbitrary(g),
            subordinate_bus: u8::arbitrary(g),
        })
    }

    #[cfg(not(tarpaulin_include))]
    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(
            (self.0.domain, self.0.secondary_bus, self.0.subordinate_bus)
                .shrink()
                .map(|(domain, secondary_bus, subordinate_bus)| {
                    Self(RawDownstreamPCIAttributes {
                        domain,
                        secondary_bus,
                        subordinate_bus,
                    })
                }),
        )
    }
}
//
// SAFETY: DownstreamPCIAttributes is a repr(transparent) newtype of RawDownstreamPCIAttributes
unsafe impl TransparentNewtype for DownstreamPCIAttributes {
    type Inner = RawDownstreamPCIAttributes;
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
        // SAFETY: attr.pci assumed valid if ty is PCI per input precondition
        unsafe {
            match ty {
                BridgeType::PCI => Some(Self::PCI((&attr.pci).as_newtype())),
                BridgeType::Host => unreachable!("Host bridge type should not appear downstream"),
            }
        }
    }
}

/// [`OSDevice`]-specific attributes
///
/// [`OSDevice`]: ObjectType::OSDevice
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_osdev_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_osdev_attr_s")]
#[repr(transparent)]
pub struct OSDeviceAttributes(hwloc_osdev_attr_s);
//
impl OSDeviceAttributes {
    /// OS device type
    #[doc(alias = "hwloc_osdev_attr_s::type")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_osdev_attr_s::type")]
    pub fn device_type(&self) -> OSDeviceType {
        self.0.ty.try_into().expect("got unexpected OS device type")
    }
}
//
#[cfg(any(test, feature = "quickcheck"))]
impl quickcheck::Arbitrary for OSDeviceAttributes {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        // Bias RNG to ensure reasonable odds of valid device types
        use hwlocality_sys::hwloc_obj_osdev_type_t;
        let max_valid_raw_device_type = enum_iterator::all::<OSDeviceType>()
            .map(hwloc_obj_osdev_type_t::from)
            .max()
            .expect("enum has >= 1 variants");
        Self(hwloc_osdev_attr_s {
            ty: hwloc_obj_osdev_type_t::arbitrary(g) % (2 * max_valid_raw_device_type),
        })
    }

    #[cfg(not(tarpaulin_include))]
    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(self.0.ty.shrink().map(|ty| Self(hwloc_osdev_attr_s { ty })))
    }
}
//
// SAFETY: OSDeviceAttributes is a repr(transparent) newtype of hwloc_osdev_attr_s
unsafe impl TransparentNewtype for OSDeviceAttributes {
    type Inner = hwloc_osdev_attr_s;
}
