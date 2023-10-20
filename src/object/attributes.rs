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
    hwloc_numanode_attr_s, hwloc_obj_attr_u, hwloc_obj_bridge_type_t, hwloc_osdev_attr_s,
    hwloc_pcidev_attr_s, RawDownstreamAttributes, RawDownstreamPCIAttributes,
    RawUpstreamAttributes,
};
#[cfg(any(test, feature = "proptest"))]
use proptest::prelude::*;
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::{
    cmp::Ordering,
    ffi::c_uint,
    fmt::{self, Debug, DebugStruct},
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
    #[allow(clippy::wildcard_enum_match_arm)]
    pub(crate) unsafe fn new(ty: ObjectType, attr: &'object *mut hwloc_obj_attr_u) -> Option<Self> {
        if attr.is_null() {
            return None;
        }
        // SAFETY: Safe due to input precondition
        let attr: &hwloc_obj_attr_u = unsafe { &**attr };

        // SAFETY: - We checked for union field access validity via the type
        //         - Type is truted to match union state per input precondition
        unsafe {
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
#[derive(Copy, Clone, Default)]
#[doc(alias = "hwloc_numanode_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s")]
#[repr(transparent)]
pub struct NUMANodeAttributes<'object>(hwloc_numanode_attr_s, PhantomData<&'object MemoryPageType>);
//
impl<'object> NUMANodeAttributes<'object> {
    /// Node-local memory in bytes
    ///
    /// Requires [`DiscoverySupport::numa_memory()`], but may not be present
    /// even when this support flag is set.
    #[doc(alias = "hwloc_numanode_attr_s::local_memory")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::local_memory")]
    pub fn local_memory(&self) -> Option<NonZeroU64> {
        NonZeroU64::new(self.0.local_memory)
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
impl Debug for NUMANodeAttributes<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug = f.debug_struct("NUMANodeAttributes");

        debug.field("local_memory", &self.local_memory());

        if self.0.page_types_len == 0 || !self.0.page_types.is_null() {
            debug.field("page_types", &self.page_types());
        } else {
            debug.field(
                "page_types",
                &format!("NULL with len={:?}", self.0.page_types_len),
            );
        }

        debug.finish()
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
#[derive(Copy, Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
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
    pub fn size(&self) -> NonZeroU64 {
        NonZeroU64::new(self.0.size).expect("memory page types of unknown size are useless")
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
#[cfg(any(test, feature = "proptest"))]
impl Arbitrary for MemoryPageType {
    type Parameters = <u64 as Arbitrary>::Parameters;
    type Strategy = prop::strategy::Map<
        (
            crate::strategies::IntSpecial0<u64>,
            <u64 as Arbitrary>::Strategy,
        ),
        fn((u64, u64)) -> Self,
    >;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        let size = crate::strategies::u64_special0();
        let count = u64::arbitrary_with(args);
        (size, count).prop_map(|(size, count)| Self(hwloc_memory_page_type_s { size, count }))
    }
}
//
impl Debug for MemoryPageType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug = f.debug_struct("MemoryPageType");

        if self.0.size == 0 {
            debug.field("size", &"0");
        } else {
            debug.field("size", &self.size());
        }

        debug.field("count", &self.count()).finish()
    }
}
//
// SAFETY: MemoryPageType is a repr(transparent) newtype of hwloc_memory_page_type_s
unsafe impl TransparentNewtype for MemoryPageType {
    type Inner = hwloc_memory_page_type_s;
}

/// Cache-specific attributes
#[derive(Copy, Clone, Eq, Hash, PartialEq)]
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
    pub fn depth(&self) -> NonZeroUsize {
        NonZeroUsize::new(int::expect_usize(self.0.depth)).expect("Cache depths should start at 1")
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
#[cfg(any(test, feature = "proptest"))]
impl Arbitrary for CacheAttributes {
    type Parameters = ();
    type Strategy = prop::strategy::Map<
        (
            crate::strategies::IntSpecial0<u64>,
            crate::strategies::IntSpecial0<c_uint>,
            crate::strategies::IntSpecial0<c_uint>,
            prop::strategy::TupleUnion<(
                prop::strategy::WA<Just<std::ffi::c_int>>,
                prop::strategy::WA<std::ops::RangeInclusive<std::ffi::c_int>>,
                prop::strategy::WA<Just<std::ffi::c_int>>,
                prop::strategy::WA<std::ops::RangeInclusive<std::ffi::c_int>>,
            )>,
            crate::strategies::EnumRepr<hwlocality_sys::hwloc_obj_cache_type_t>,
        ),
        fn(
            (
                u64,
                c_uint,
                c_uint,
                std::ffi::c_int,
                hwlocality_sys::hwloc_obj_cache_type_t,
            ),
        ) -> Self,
    >;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        use crate::strategies;
        use hwlocality_sys::hwloc_obj_cache_type_t;
        use std::ffi::c_int;

        // Biased RNGs ensuring reasonable odds of zero size/depth
        let size = strategies::u64_special0();
        let depth = strategies::uint_special0();
        let linesize = strategies::uint_special0();

        // Biased RNG ensuring reasonable associativity branch coverage
        let associativity = prop_oneof![
            1 => Just(0),  // Unknown associativity
            2 => 1..=c_int::MAX,  // N-ways associative
            1 => Just(-1),  // Fully associative
            1 => c_int::MIN..=-2  // Invalid associativity
        ];

        // Biased RNG ensuring reasonable valid/invalid cache type coverage
        let cache_type = strategies::enum_repr::<CacheType, hwloc_obj_cache_type_t>(
            hwloc_obj_cache_type_t::MIN,
            hwloc_obj_cache_type_t::MAX,
        );

        // Put it all together
        (size, depth, linesize, associativity, cache_type).prop_map(
            |(size, depth, linesize, associativity, ty)| {
                Self(hwloc_cache_attr_s {
                    size,
                    depth,
                    linesize,
                    associativity,
                    ty,
                })
            },
        )
    }
}
//
impl Debug for CacheAttributes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug = f.debug_struct("CacheAttributes");

        debug.field("size", &self.size());

        if self.0.depth == 0 {
            debug.field("depth", &"0");
        } else {
            debug.field("depth", &self.depth());
        }

        debug.field("line_size", &self.line_size());

        if self.0.associativity >= -1 {
            debug.field("associativity", &self.associativity());
        } else {
            debug.field("associativity", &format!("{:?}", self.0.associativity));
        }

        if CacheType::try_from(self.0.ty).is_ok() {
            debug.field("cache_type", &self.cache_type());
        } else {
            debug.field("cache_type", &format!("{:?}", self.0.ty));
        }

        debug.finish()
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

    /// N-ways associative
    Ways(NonZeroUsize),

    /// Fully associative
    Full,
}
//
#[cfg(any(test, feature = "proptest"))]
impl Arbitrary for CacheAssociativity {
    type Parameters = <NonZeroUsize as Arbitrary>::Parameters;
    type Strategy = prop::strategy::TupleUnion<(
        prop::strategy::WA<Just<Self>>,
        prop::strategy::WA<
            prop::strategy::Map<<NonZeroUsize as Arbitrary>::Strategy, fn(NonZeroUsize) -> Self>,
        >,
        prop::strategy::WA<Just<Self>>,
    )>;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        prop_oneof![
            1 => Just(Self::Unknown),
            3 => NonZeroUsize::arbitrary_with(args).prop_map(Self::Ways),
            1 => Just(Self::Full),
        ]
    }
}
//
impl PartialOrd for CacheAssociativity {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Self::Unknown, _) | (_, Self::Unknown) => None,
            (Self::Full, Self::Full) => Some(Ordering::Equal),
            (Self::Full, Self::Ways(_)) => Some(Ordering::Greater),
            (Self::Ways(_), Self::Full) => Some(Ordering::Less),
            (Self::Ways(x), Self::Ways(y)) => x.partial_cmp(y),
        }
    }
}

/// [`Group`]-specific attributes
///
/// [`Group`]: ObjectType::Group
#[derive(Copy, Clone, Default, Eq, Hash, PartialEq)]
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
        self.0.kind = c_uint::MAX;
        self.0.dont_merge = 0;
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
        self.0.dont_merge = 1;
    }
}
//
#[cfg(any(test, feature = "proptest"))]
impl Arbitrary for GroupAttributes {
    type Parameters = <[c_uint; 3] as Arbitrary>::Parameters;
    type Strategy = prop::strategy::Map<
        (
            <[c_uint; 3] as Arbitrary>::Strategy,
            crate::strategies::HwlocBool,
        ),
        fn(([c_uint; 3], std::ffi::c_uchar)) -> Self,
    >;

    #[allow(unused)]
    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        let depth_kind_subkind = <[c_uint; 3] as Arbitrary>::arbitrary_with(args);
        let dont_merge = crate::strategies::hwloc_bool();
        (depth_kind_subkind, dont_merge).prop_map(|([depth, kind, subkind], dont_merge)| {
            Self(hwloc_group_attr_s {
                depth,
                kind,
                subkind,
                #[cfg(feature = "hwloc-2_0_4")]
                dont_merge,
            })
        })
    }
}
//
impl Debug for GroupAttributes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug = f.debug_struct("GroupAttributes");

        debug.field("depth", &self.depth());

        #[cfg(feature = "hwloc-2_0_4")]
        if self.0.dont_merge <= 1 {
            debug.field("merging_prevented", &self.merging_prevented());
        } else {
            debug.field("merging_prevented", &format!("{:?}", self.0.dont_merge));
        }

        debug
            .field("kind", &self.kind())
            .field("subkind", &self.subkind())
            .finish()
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
#[cfg(any(test, feature = "proptest"))]
impl Arbitrary for PCIDeviceAttributes {
    type Parameters = <(PCIDomain, [u8; 4], [u16; 5]) as Arbitrary>::Parameters;
    type Strategy = prop::strategy::Map<
        (
            <(PCIDomain, [u8; 4], [u16; 5]) as Arbitrary>::Strategy,
            prop::num::f32::Any,
        ),
        fn(((PCIDomain, [u8; 4], [u16; 5]), f32)) -> Self,
    >;

    #[allow(unused)]
    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        (
            <(PCIDomain, [u8; 4], [u16; 5])>::arbitrary_with(args),
            prop::num::f32::ANY,
        )
            .prop_map(
                |(
                    (
                        domain,
                        [bus, dev, func, revision],
                        [class_id, vendor_id, device_id, subvendor_id, subdevice_id],
                    ),
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
#[cfg(any(test, feature = "proptest"))]
impl Arbitrary for BridgeAttributes {
    type Parameters =
        <(PCIDeviceAttributes, DownstreamPCIAttributes, c_uint) as Arbitrary>::Parameters;
    type Strategy = prop::strategy::Map<
        (
            [crate::strategies::EnumRepr<hwloc_obj_bridge_type_t>; 2],
            <(PCIDeviceAttributes, DownstreamPCIAttributes, c_uint) as Arbitrary>::Strategy,
        ),
        fn(
            (
                [hwloc_obj_bridge_type_t; 2],
                (PCIDeviceAttributes, DownstreamPCIAttributes, c_uint),
            ),
        ) -> Self,
    >;

    #[allow(unused)]
    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        let bridge_type = crate::strategies::enum_repr::<BridgeType, hwloc_obj_bridge_type_t>(
            hwloc_obj_bridge_type_t::MIN,
            hwloc_obj_bridge_type_t::MAX,
        );
        (
            [bridge_type.clone(), bridge_type],
            <(PCIDeviceAttributes, DownstreamPCIAttributes, c_uint)>::arbitrary_with(args),
        )
            .prop_map(
                |([upstream_type, downstream_type], (upstream_pci, downstream_pci, depth))| {
                    Self(hwloc_bridge_attr_s {
                        upstream_type,
                        upstream: RawUpstreamAttributes {
                            pci: upstream_pci.0,
                        },
                        downstream_type,
                        downstream: RawDownstreamAttributes {
                            pci: downstream_pci.0,
                        },
                        depth,
                    })
                },
            )
    }
}
//
impl Debug for BridgeAttributes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug = f.debug_struct("BridgeAttributes");

        let show_type =
            |debug: &mut DebugStruct<'_, '_>, name: &str, ty: hwloc_obj_bridge_type_t| {
                if let Ok(ty) = BridgeType::try_from(ty) {
                    debug.field(name, &ty);
                } else {
                    debug.field(name, &format!("{ty:?}"));
                }
            };

        show_type(&mut debug, "upstream_type", self.0.upstream_type);
        if BridgeType::try_from(self.0.upstream_type).is_ok() {
            debug.field("upstream_attributes", &self.upstream_attributes());
        } else {
            debug.field("upstream_attributes", &format!("{:?}", self.0.upstream));
        }

        show_type(&mut debug, "downstream_type", self.0.downstream_type);
        match BridgeType::try_from(self.0.downstream_type) {
            Ok(BridgeType::PCI) => {
                debug.field("downstream_attributes", &self.downstream_attributes())
            }
            Ok(BridgeType::Host) | Err(_) => {
                debug.field("downstream_attributes", &format!("{:?}", self.0.downstream))
            }
        };

        debug.field("depth", &self.depth()).finish()
    }
}
//
impl PartialEq for BridgeAttributes {
    fn eq(&self, other: &Self) -> bool {
        self.upstream_type() == other.upstream_type()
            && self.upstream_attributes() == other.upstream_attributes()
            && self.downstream_type() == other.downstream_type()
            && self.downstream_attributes() == other.downstream_attributes()
            && self.depth() == other.depth()
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
#[cfg(any(test, feature = "proptest"))]
impl Arbitrary for DownstreamPCIAttributes {
    type Parameters = <(PCIDomain, [u8; 2]) as Arbitrary>::Parameters;
    type Strategy = prop::strategy::Map<
        <(PCIDomain, [u8; 2]) as Arbitrary>::Strategy,
        fn((PCIDomain, [u8; 2])) -> Self,
    >;

    #[allow(unused)]
    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        <(PCIDomain, [u8; 2])>::arbitrary_with(args).prop_map(
            |(domain, [secondary_bus, subordinate_bus])| {
                Self(RawDownstreamPCIAttributes {
                    domain,
                    secondary_bus,
                    subordinate_bus,
                })
            },
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
#[derive(Copy, Clone, Eq, Hash, PartialEq)]
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
#[cfg(any(test, feature = "proptest"))]
impl Arbitrary for OSDeviceAttributes {
    type Parameters = ();
    type Strategy = prop::strategy::Map<
        crate::strategies::EnumRepr<hwlocality_sys::hwloc_obj_osdev_type_t>,
        fn(hwlocality_sys::hwloc_obj_osdev_type_t) -> Self,
    >;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        use hwlocality_sys::hwloc_obj_osdev_type_t;
        crate::strategies::enum_repr::<OSDeviceType, hwloc_obj_osdev_type_t>(
            hwloc_obj_osdev_type_t::MIN,
            hwloc_obj_osdev_type_t::MAX,
        )
        .prop_map(|ty| Self(hwloc_osdev_attr_s { ty }))
    }
}
//
impl Debug for OSDeviceAttributes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug = f.debug_struct("OSDeviceAttributes");
        if OSDeviceType::try_from(self.0.ty).is_ok() {
            debug.field("device_type", &self.device_type());
        } else {
            debug.field("device_type", &format!("{:?}", self.0.ty));
        }
        debug.finish()
    }
}
//
// SAFETY: OSDeviceAttributes is a repr(transparent) newtype of hwloc_osdev_attr_s
unsafe impl TransparentNewtype for OSDeviceAttributes {
    type Inner = hwloc_osdev_attr_s;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ffi::transparent::AsInner,
        object::{depth::NormalDepth, TopologyObject},
        tests::assert_panics,
        topology::Topology,
    };
    use proptest::sample::Selector;
    #[allow(unused)]
    use similar_asserts::assert_eq;
    use static_assertions::{assert_impl_all, assert_not_impl_any};
    use std::{
        collections::hash_map::RandomState,
        error::Error,
        fmt::{
            self, Binary, Debug, Display, LowerExp, LowerHex, Octal, Pointer, UpperExp, UpperHex,
        },
        hash::{BuildHasher, Hash},
        io::{self, Read},
        iter::{Product, Sum},
        ops::{
            Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Deref,
            Div, DivAssign, Mul, MulAssign, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign,
            Sub, SubAssign,
        },
        panic::UnwindSafe,
        str::FromStr,
        sync::OnceLock,
    };

    // Check that public types in this module keep implementing all expected
    // traits, in the interest of detecting future semver-breaking changes
    assert_impl_all!(CacheAssociativity:
        Copy, Debug, Default, Hash, PartialOrd, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(CacheAssociativity:
        Binary, Deref, Display, Drop, IntoIterator, LowerExp, LowerHex,
        Octal, Pointer, Read, UpperExp, UpperHex, fmt::Write, io::Write
    );
    assert_impl_all!(CacheAttributes:
        Copy, Debug, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(CacheAttributes:
        Binary, Default, Deref, Display, Drop, IntoIterator, LowerExp, LowerHex,
        Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write,
        io::Write
    );
    assert_impl_all!(DownstreamAttributes<'static>:
        Copy, Debug, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(DownstreamAttributes<'static>:
        Binary, Default, Deref, Display, Drop, IntoIterator, LowerExp, LowerHex,
        Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write,
        io::Write
    );
    assert_impl_all!(DownstreamPCIAttributes:
        Copy, Debug, Default, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(DownstreamPCIAttributes:
        Binary, Deref, Display, Drop, IntoIterator, LowerExp, LowerHex,
        Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write,
        io::Write
    );
    assert_impl_all!(GroupAttributes:
        Copy, Debug, Default, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(GroupAttributes:
        Binary, Deref, Display, Drop, IntoIterator, LowerExp, LowerHex,
        Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write,
        io::Write
    );
    assert_impl_all!(MemoryPageType:
        Copy, Debug, Hash, Ord, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(MemoryPageType:
        Binary, Default, Deref, Display, Drop, IntoIterator, LowerExp, LowerHex,
        Octal, Pointer, Read, UpperExp, UpperHex, fmt::Write, io::Write
    );
    assert_impl_all!(NUMANodeAttributes<'static>:
        Copy, Debug, Default, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(NUMANodeAttributes<'static>:
        Binary, Deref, Display, Drop, IntoIterator, LowerExp, LowerHex, Octal,
        PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write, io::Write
    );
    assert_impl_all!(ObjectAttributes<'static>:
        Copy, Debug, PartialEq, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(ObjectAttributes<'static>:
        Binary, Default, Deref, Display, Drop, Eq, IntoIterator, LowerExp,
        LowerHex, Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex,
        fmt::Write, io::Write
    );
    assert_impl_all!(OSDeviceAttributes:
        Copy, Debug, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(OSDeviceAttributes:
        Binary, Deref, Default, Display, Drop, IntoIterator, LowerExp, LowerHex,
        Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write,
        io::Write
    );
    assert_impl_all!(PCIDeviceAttributes:
        Copy, Debug, Default, PartialEq, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(PCIDeviceAttributes:
        Binary, Deref, Display, Drop, Eq, IntoIterator, LowerExp, LowerHex,
        Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write,
        io::Write
    );
    assert_impl_all!(PCIDomain:
        Add, AddAssign, Binary, BitAnd, BitAndAssign, BitOr, BitOrAssign,
        BitXor, BitXorAssign, Copy, Debug, Default, Display, Div, DivAssign,
        FromStr, Hash, LowerExp, LowerHex, Mul, MulAssign, Not, Octal, Ord,
        Product, Sized, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign, Sum, Sync,
        TryFrom<i8>, TryFrom<u8>,
        TryFrom<i16>, TryFrom<u16>,
        TryFrom<i32>, TryFrom<u32>,
        TryFrom<i64>, TryFrom<u64>,
        TryFrom<i128>, TryFrom<u128>,
        TryFrom<isize>, TryFrom<usize>,
        TryInto<i8>, TryInto<u8>,
        TryInto<i16>, TryInto<u16>,
        TryInto<i32>, TryInto<u32>,
        TryInto<i64>, TryInto<u64>,
        TryInto<i128>, TryInto<u128>,
        TryInto<isize>, TryInto<usize>,
        Unpin, UnwindSafe, UpperExp, UpperHex
    );
    assert_not_impl_any!(PCIDomain:
        Deref, Drop, Error, IntoIterator, Pointer, Read, fmt::Write, io::Write
    );
    assert_impl_all!(UpstreamAttributes<'static>:
        Copy, Debug, PartialEq, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(UpstreamAttributes<'static>:
        Binary, Default, Deref, Display, Drop, Eq, IntoIterator, LowerExp,
        LowerHex, Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex,
        fmt::Write, io::Write
    );

    #[test]
    fn default() -> Result<(), TestCaseError> {
        check_any_numa(&NUMANodeAttributes::default())?;
        check_any_group(&GroupAttributes::default())?;
        check_any_pci(&PCIDeviceAttributes::default())?;
        Ok(())
    }

    proptest! {
        #[test]
        fn unary_numa(local_memory: u64, page_types: Vec<MemoryPageType>, null: bool) {
            let numa_attr = if null {
                NUMANodeAttributes(
                    hwloc_numanode_attr_s {
                        local_memory,
                        page_types_len: u32::try_from(page_types.len()).unwrap_or(u32::MAX),
                        page_types: std::ptr::null_mut(),
                    },
                    PhantomData,
                )
            } else {
                let numa_attr = make_numa_attributes(local_memory, &page_types);
                prop_assert_eq!(numa_attr.page_types(), &page_types);
                numa_attr
            };
            prop_assert_eq!(numa_attr.local_memory(), NonZeroU64::new(local_memory));
            check_any_numa(&numa_attr)?;

            let mut raw = hwloc_obj_attr_u { numa: numa_attr.0 };
            let ptr: *mut hwloc_obj_attr_u = &mut raw;
            // SAFETY: Type is consistent with union variant, data is valid
            unsafe {
                prop_assert!(matches!(
                    ObjectAttributes::new(ObjectType::NUMANode, &ptr),
                    Some(ObjectAttributes::NUMANode(attr)) if std::ptr::eq(attr.as_inner(), &raw.numa)
                ));
            }
        }
    }

    /// Pick a random CPU cache type
    fn cpu_cache_type() -> impl Strategy<Value = ObjectType> {
        static CACHE_TYPES: OnceLock<Box<[ObjectType]>> = OnceLock::new();
        let cache_types = CACHE_TYPES.get_or_init(|| {
            enum_iterator::all::<ObjectType>()
                .filter(|ty| ty.is_cpu_cache())
                .collect()
        });
        prop::sample::select(&cache_types[..])
    }

    proptest! {
        #[test]
        fn unary_cache(ty in cpu_cache_type(), cache_attr: CacheAttributes) {
            check_any_cache(&cache_attr)?;
            let mut raw = hwloc_obj_attr_u {
                cache: cache_attr.0,
            };
            let ptr: *mut hwloc_obj_attr_u = &mut raw;
            // SAFETY: Type is consistent with union variant, data is valid
            unsafe {
                prop_assert!(matches!(
                    ObjectAttributes::new(ty, &ptr),
                    Some(ObjectAttributes::Cache(attr)) if std::ptr::eq(attr.as_inner(), &raw.cache)
                ));
            }
        }

        #[test]
        fn unary_group(group_attr: GroupAttributes) {
            check_any_group(&group_attr)?;
            let mut raw = hwloc_obj_attr_u {
                group: group_attr.0,
            };
            let ptr: *mut hwloc_obj_attr_u = &mut raw;
            // SAFETY: Type is consistent with union variant, data is valid
            unsafe {
                prop_assert!(matches!(
                    ObjectAttributes::new(ObjectType::Group, &ptr),
                    Some(ObjectAttributes::Group(attr)) if std::ptr::eq(attr.as_inner(), &raw.group)
                ));
            }
        }

        #[test]
        fn unary_pci(pcidev_attr: PCIDeviceAttributes) {
            check_any_pci(&pcidev_attr)?;
            let mut raw = hwloc_obj_attr_u {
                pcidev: pcidev_attr.0,
            };
            let ptr: *mut hwloc_obj_attr_u = &mut raw;
            // SAFETY: Type is consistent with union variant, data is valid
            unsafe {
                prop_assert!(matches!(
                    ObjectAttributes::new(ObjectType::PCIDevice, &ptr),
                    Some(ObjectAttributes::PCIDevice(attr)) if std::ptr::eq(attr.as_inner(), &raw.pcidev)
                ));
            }
        }

        #[test]
        fn unary_bridge(bridge_attr: BridgeAttributes) {
            check_any_bridge(&bridge_attr)?;
            let mut raw = hwloc_obj_attr_u {
                bridge: bridge_attr.0,
            };
            let ptr: *mut hwloc_obj_attr_u = &mut raw;
            // SAFETY: Type is consistent with union variant, data is valid
            unsafe {
                prop_assert!(matches!(
                    ObjectAttributes::new(ObjectType::Bridge, &ptr),
                    Some(ObjectAttributes::Bridge(attr)) if std::ptr::eq(attr.as_inner(), &raw.bridge)
                ));
            }
        }

        #[test]
        fn unary_osdev(osdev_attr: OSDeviceAttributes) {
            check_any_osdev(&osdev_attr)?;
            let mut raw = hwloc_obj_attr_u {
                osdev: osdev_attr.0,
            };
            let ptr: *mut hwloc_obj_attr_u = &mut raw;
            // SAFETY: Type is consistent with union variant, data is valid
            unsafe {
                prop_assert!(matches!(
                    ObjectAttributes::new(ObjectType::OSDevice, &ptr),
                    Some(ObjectAttributes::OSDevice(attr)) if std::ptr::eq(attr.as_inner(), &raw.osdev)
                ));
            }
        }

        #[test]
        fn unary_nonexistent(ty: ObjectType, osdev_attr: OSDeviceAttributes) {
            // SAFETY: Sending in a null pointer is safe
            let is_nonexistent = unsafe { ObjectAttributes::new(ty, &std::ptr::null_mut()).is_none() };
            prop_assert!(is_nonexistent);

            // ...and types that have no attributes are safe as well
            let check_nonexistent = || {
                let mut raw = hwloc_obj_attr_u {
                    osdev: osdev_attr.0,
                };
                let ptr: *mut hwloc_obj_attr_u = &mut raw;
                // SAFETY: Types with associated attributes have all been
                //         covered above, so None is the only outcome and union
                //         variant doesn't matter.
                let is_nonexistent = unsafe { ObjectAttributes::new(ty, &ptr).is_none() };
                prop_assert!(is_nonexistent);
                Ok(())
            };
            match ty {
                ObjectType::NUMANode
                | ObjectType::Group
                | ObjectType::PCIDevice
                | ObjectType::Bridge
                | ObjectType::OSDevice
                | ObjectType::L1Cache
                | ObjectType::L2Cache
                | ObjectType::L3Cache
                | ObjectType::L4Cache
                | ObjectType::L5Cache
                | ObjectType::L1ICache
                | ObjectType::L2ICache
                | ObjectType::L3ICache => {}
                ObjectType::Machine
                | ObjectType::Package
                | ObjectType::Core
                | ObjectType::PU
                | ObjectType::Misc => check_nonexistent()?,
                #[cfg(feature = "hwloc-2_1_0")]
                ObjectType::MemCache | ObjectType::Die => check_nonexistent()?,
            }
        }
    }

    /// Check properties that should be true of all topology objects
    #[test]
    fn unary_valid() -> Result<(), TestCaseError> {
        for obj in Topology::test_objects() {
            check_valid_object(obj.object_type(), obj.attributes())?;
            match obj.attributes() {
                Some(ObjectAttributes::NUMANode(attr)) => {
                    prop_assert_eq!(
                        attr.local_memory().map_or(0u64, u64::from),
                        obj.total_memory()
                    );
                }
                Some(ObjectAttributes::Cache(attr)) => match attr.cache_type() {
                    CacheType::Unified | CacheType::Data => {
                        prop_assert!(obj.object_type().is_cpu_data_cache());
                    }
                    CacheType::Instruction => {
                        prop_assert!(obj.object_type().is_cpu_instruction_cache());
                    }
                },
                #[allow(unused)]
                Some(ObjectAttributes::Group(attr)) => {
                    #[cfg(feature = "hwloc-2_0_4")]
                    prop_assert!(!attr.merging_prevented());
                }
                Some(ObjectAttributes::PCIDevice(pci)) => {
                    let Some(ObjectAttributes::Bridge(bridge)) = obj.parent().unwrap().attributes()
                    else {
                        panic!("PCI devices should have a Bridge parent")
                    };
                    prop_assert_eq!(bridge.downstream_type(), BridgeType::PCI);
                    let Some(DownstreamAttributes::PCI(downstream)) =
                        bridge.downstream_attributes()
                    else {
                        panic!("Parent of PCI device should have a PCI downstream")
                    };
                    prop_assert_eq!(downstream.domain(), pci.domain());
                }
                Some(ObjectAttributes::Bridge(attr)) => {
                    let parent_type = obj.parent().unwrap().object_type();
                    let has_pci_parent = (parent_type == ObjectType::PCIDevice)
                        || (parent_type == ObjectType::Bridge);
                    match attr.upstream_type() {
                        BridgeType::PCI => prop_assert!(has_pci_parent),
                        BridgeType::Host => prop_assert!(!has_pci_parent),
                    }
                }
                Some(ObjectAttributes::OSDevice(_attr)) => {
                    // Nothing else we can check knowing the topology around
                }
                None => {}
            }
        }
        Ok(())
    }

    proptest! {
        #[test]
        fn binary_cache_associativity(assoc1: CacheAssociativity, assoc2: CacheAssociativity) {
            let ord = match (assoc1, assoc2) {
                (CacheAssociativity::Unknown, _) | (_, CacheAssociativity::Unknown) => None,
                (CacheAssociativity::Full, CacheAssociativity::Full) => Some(Ordering::Equal),
                (CacheAssociativity::Full, CacheAssociativity::Ways(_)) => Some(Ordering::Greater),
                (CacheAssociativity::Ways(_), CacheAssociativity::Full) => Some(Ordering::Less),
                (CacheAssociativity::Ways(x), CacheAssociativity::Ways(y)) => x.partial_cmp(&y),
            };
            prop_assert_eq!(assoc1.partial_cmp(&assoc2), ord);
        }
    }

    /// List of objects from the test topology that have attributes
    struct ObjectsWithAttrs {
        numa_nodes: Box<[&'static TopologyObject]>,
        caches: Box<[&'static TopologyObject]>,
        groups: Box<[&'static TopologyObject]>,
        pci_devices: Box<[&'static TopologyObject]>,
        bridges: Box<[&'static TopologyObject]>,
    }
    //
    impl ObjectsWithAttrs {
        /// Memoized instance of [`ObjectsWithAttrs`]
        fn instance() -> &'static Self {
            static INSTANCE: OnceLock<ObjectsWithAttrs> = OnceLock::new();
            INSTANCE.get_or_init(|| {
                let topology = Topology::test_instance();
                Self {
                    numa_nodes: topology.objects_with_type(ObjectType::NUMANode).collect(),
                    caches: topology
                        .normal_objects()
                        .filter(|obj| obj.object_type().is_cpu_cache())
                        .collect(),
                    groups: topology.objects_with_type(ObjectType::Group).collect(),
                    pci_devices: topology.objects_with_type(ObjectType::PCIDevice).collect(),
                    bridges: topology.objects_with_type(ObjectType::Bridge).collect(),
                }
            })
        }
    }

    /// Strategy that selects pairs of objects from pre-computed lists
    fn object_pair(
        type1: &'static [&'static TopologyObject],
        type2: &'static [&'static TopologyObject],
    ) -> impl Strategy<Value = Option<[&'static TopologyObject; 2]>> {
        (any::<(Selector, Selector)>()).prop_map(move |(sel1, sel2)| {
            let obj1 = sel1.try_select(type1.iter().copied())?;
            let obj2 = sel2.try_select(type2.iter().copied())?;
            Some([obj1, obj2])
        })
    }

    /// Pick a pair of NUMA nodes in the test topology if possible
    fn numa_pair() -> impl Strategy<Value = Option<[&'static TopologyObject; 2]>> {
        let numa_nodes = &ObjectsWithAttrs::instance().numa_nodes;
        object_pair(numa_nodes, numa_nodes)
    }

    proptest! {
        /// Check properties that should be true of any pair of NUMA nodes
        #[test]
        fn valid_numa_pair(numa_pair in numa_pair()) {
            if let Some(pair) = numa_pair {
                check_valid_numa_pair(pair)?;
            }
        }
    }

    /// Pick a pair of CPU caches in the test topology if possible
    fn cache_pair() -> impl Strategy<Value = Option<[&'static TopologyObject; 2]>> {
        let caches = &ObjectsWithAttrs::instance().caches;
        object_pair(caches, caches)
    }

    proptest! {
        /// Check properties that should be true of any pair of CPU caches
        #[test]
        fn valid_cache_pair(cache_pair in cache_pair()) {
            if let Some(pair) = cache_pair {
                check_valid_cache_pair(pair)?;
            }
        }
    }

    /// Pick a pair of goups in the test topology if possible
    fn group_pair() -> impl Strategy<Value = Option<[&'static TopologyObject; 2]>> {
        let groups = &ObjectsWithAttrs::instance().groups;
        object_pair(groups, groups)
    }

    proptest! {
        /// Check properties that should be true of any pair of groups
        #[test]
        fn valid_group_pair(group_pair in group_pair()) {
            if let Some(pair) = group_pair {
                check_valid_group_pair(pair)?;
            }
        }
    }

    /// Pick a pair of PCI devices in the test topology if possible
    fn pci_pair() -> impl Strategy<Value = Option<[&'static TopologyObject; 2]>> {
        let pci_devices = &ObjectsWithAttrs::instance().pci_devices;
        object_pair(pci_devices, pci_devices)
    }

    proptest! {
        /// Check properties that should be true of any pair of pcis
        #[test]
        fn valid_pci_pair(pci_pair in pci_pair()) {
            if let Some(pair) = pci_pair {
                check_valid_pci_pair(pair)?;
            }
        }
    }

    /// Pick a pair of bridges in the test topology if possible
    fn bridge_pair() -> impl Strategy<Value = Option<[&'static TopologyObject; 2]>> {
        let bridges = &ObjectsWithAttrs::instance().bridges;
        object_pair(bridges, bridges)
    }

    proptest! {
        /// Check properties that should be true of any pair of bridges
        #[test]
        fn valid_bridge_pair(bridge_pair in bridge_pair()) {
            if let Some(pair) = bridge_pair {
                check_valid_bridge_pair(pair)?;
            }
        }
    }

    /// Pick a (bridge, PCI device) pair in the test topology if possible
    fn bridge_pci() -> impl Strategy<Value = Option<[&'static TopologyObject; 2]>> {
        let bridges = &ObjectsWithAttrs::instance().bridges;
        let pci_devices = &ObjectsWithAttrs::instance().pci_devices;
        object_pair(bridges, pci_devices)
    }

    proptest! {
        /// Check properties that should be true of any pair of bridges
        #[test]
        fn valid_bridge_pci(bridge_pci in bridge_pci()) {
            if let Some(pair) = bridge_pci {
                check_valid_bridge_pci(pair)?;
            }
        }
    }

    /// Check object attributes under the assumption that the inner data is in a
    /// valid state (no boolean representation equal to 42, etc)
    fn check_valid_object(
        ty: ObjectType,
        attr: Option<ObjectAttributes<'_>>,
    ) -> Result<(), TestCaseError> {
        match (ty, attr) {
            (ObjectType::NUMANode, Some(ObjectAttributes::NUMANode(attr))) => {
                check_valid_numa(attr)?
            }
            (cache, Some(ObjectAttributes::Cache(attr))) if cache.is_cpu_cache() => {
                check_valid_cache(attr)?
            }
            (ObjectType::Group, Some(ObjectAttributes::Group(attr))) => check_valid_group(attr)?,
            (ObjectType::PCIDevice, Some(ObjectAttributes::PCIDevice(attr))) => {
                check_valid_pci(attr)?
            }
            (ObjectType::Bridge, Some(ObjectAttributes::Bridge(attr))) => check_valid_bridge(attr)?,
            (ObjectType::OSDevice, Some(ObjectAttributes::OSDevice(attr))) => {
                check_valid_osdev(attr)?
            }
            (_, None) => {}
            _ => unreachable!(),
        }
        Ok(())
    }

    fn check_valid_numa(attr: &NUMANodeAttributes<'_>) -> Result<(), TestCaseError> {
        check_any_numa(attr)?;

        let mut prev_page_size = None;
        for page_type in attr.page_types() {
            let page_size = page_type.size();
            prop_assert!(page_size.is_power_of_two());
            if let Some(prev_page_size) = prev_page_size {
                prop_assert!(page_size > prev_page_size);
            }
            prev_page_size = Some(page_size);

            prop_assert_eq!(
                format!("{page_type:?}"),
                format!(
                    "MemoryPageType {{ \
                        size: {:?}, \
                        count: {:?} \
                    }}",
                    page_type.size(),
                    page_type.count(),
                )
            )
        }

        prop_assert_eq!(
            format!("{attr:?}"),
            format!(
                "NUMANodeAttributes {{ \
                    local_memory: {:?}, \
                    page_types: {:?} \
                }}",
                attr.local_memory(),
                attr.page_types(),
            )
        );

        Ok(())
    }

    fn check_any_numa(attr: &NUMANodeAttributes<'_>) -> Result<(), TestCaseError> {
        let hwloc_numanode_attr_s {
            local_memory,
            page_types_len,
            page_types,
        } = attr.0;

        prop_assert_eq!(attr.local_memory(), NonZeroU64::new(local_memory));

        if !page_types.is_null() {
            prop_assert_eq!(
                attr.page_types().as_ptr().as_inner(),
                page_types.cast_const()
            );
            prop_assert_eq!(
                attr.page_types().len(),
                usize::try_from(page_types_len).unwrap()
            );
            for page_type in attr.page_types() {
                check_any_page_type(page_type)?;
            }
        } else if page_types_len == 0 {
            prop_assert_eq!(attr.page_types(), &[]);
        } else {
            assert_panics(|| attr.page_types())?;
            prop_assert_eq!(
                format!("{attr:?}"),
                format!(
                    "NUMANodeAttributes {{ \
                        local_memory: {:?}, \
                        page_types: \"NULL with len={page_types_len}\" \
                    }}",
                    attr.local_memory(),
                )
            );
        }
        Ok(())
    }

    fn check_any_page_type(page_type: &MemoryPageType) -> Result<(), TestCaseError> {
        let hwloc_memory_page_type_s { size, count } = page_type.0;
        #[allow(clippy::option_if_let_else)]
        if let Some(size) = NonZeroU64::new(size) {
            prop_assert_eq!(page_type.size(), size);
        } else {
            assert_panics(|| page_type.size())?;
            prop_assert_eq!(
                format!("{page_type:?}"),
                format!(
                    "MemoryPageType {{ \
                        size: \"0\", \
                        count: {:?} \
                    }}",
                    page_type.count(),
                )
            );
        }
        prop_assert_eq!(page_type.count(), count);
        Ok(())
    }

    fn check_valid_cache(attr: &CacheAttributes) -> Result<(), TestCaseError> {
        check_any_cache(attr)?;

        // True on every non-niche hardware architecture, which makes it a
        // reasonable data consistency check
        if let Some(linesize) = attr.line_size() {
            prop_assert!(linesize.is_power_of_two());
        }

        Ok(())
    }

    fn check_any_cache(attr: &CacheAttributes) -> Result<(), TestCaseError> {
        let hwloc_cache_attr_s {
            size,
            depth,
            linesize,
            associativity,
            ty,
        } = attr.0;

        prop_assert_eq!(attr.size(), NonZeroU64::new(size));

        #[allow(clippy::option_if_let_else)]
        let depth_dbg = if let Some(depth) = NonZeroUsize::new(usize::try_from(depth).unwrap()) {
            prop_assert_eq!(attr.depth(), depth);
            format!("{:?}", attr.depth())
        } else {
            assert_panics(|| attr.depth())?;
            "\"0\"".to_owned()
        };

        prop_assert_eq!(
            attr.line_size(),
            NonZeroUsize::new(usize::try_from(linesize).unwrap())
        );

        let assoc_dbg = if associativity < -1 {
            assert_panics(|| attr.associativity())?;
            format!("\"{associativity:?}\"")
        } else {
            match associativity {
                -1 => prop_assert_eq!(attr.associativity(), CacheAssociativity::Full),
                0 => prop_assert_eq!(attr.associativity(), CacheAssociativity::Unknown),
                positive => prop_assert_eq!(
                    attr.associativity(),
                    CacheAssociativity::Ways(
                        NonZeroUsize::new(usize::try_from(positive).unwrap()).unwrap()
                    )
                ),
            }
            format!("{:?}", attr.associativity())
        };

        #[allow(clippy::option_if_let_else)]
        let ty_dbg = if let Ok(cache_type) = CacheType::try_from(ty) {
            prop_assert_eq!(attr.cache_type(), cache_type);
            format!("{:?}", attr.cache_type())
        } else {
            assert_panics(|| attr.cache_type())?;
            format!("\"{ty:?}\"")
        };

        prop_assert_eq!(
            format!("{attr:?}"),
            format!(
                "CacheAttributes {{ \
                    size: {:?}, \
                    depth: {}, \
                    line_size: {:?}, \
                    associativity: {}, \
                    cache_type: {} \
                }}",
                attr.size(),
                depth_dbg,
                attr.line_size(),
                assoc_dbg,
                ty_dbg
            )
        );

        Ok(())
    }

    fn check_valid_group(attr: &GroupAttributes) -> Result<(), TestCaseError> {
        check_any_group(attr)
    }

    fn check_any_group(attr: &GroupAttributes) -> Result<(), TestCaseError> {
        #[cfg(feature = "hwloc-2_0_4")]
        let hwloc_group_attr_s {
            depth,
            kind,
            subkind,
            dont_merge,
        } = attr.0;
        #[cfg(not(feature = "hwloc-2_0_4"))]
        let hwloc_group_attr_s {
            depth,
            kind,
            subkind,
        } = attr.0;

        prop_assert_eq!(attr.depth(), usize::try_from(depth).unwrap());
        prop_assert_eq!(attr.kind(), usize::try_from(kind).unwrap());
        prop_assert_eq!(attr.subkind(), usize::try_from(subkind).unwrap());

        #[cfg(feature = "hwloc-2_0_4")]
        let merging_prevented_dbg = match dont_merge {
            0 | 1 => {
                prop_assert_eq!(attr.merging_prevented(), dont_merge != 0);
                format!("merging_prevented: {:?}, ", attr.merging_prevented())
            }
            _ => {
                assert_panics(|| attr.merging_prevented())?;
                format!("merging_prevented: \"{dont_merge:?}\", ")
            }
        };
        #[cfg(not(feature = "hwloc-2_0_4"))]
        let merging_prevented_dbg = String::new();

        prop_assert_eq!(
            format!("{attr:?}"),
            format!(
                "GroupAttributes {{ \
                    depth: {:?}, \
                    {}\
                    kind: {:?}, \
                    subkind: {:?} \
                }}",
                attr.depth(),
                merging_prevented_dbg,
                attr.kind(),
                attr.subkind(),
            )
        );

        #[cfg(feature = "hwloc-2_3_0")]
        {
            let mut buf = *attr;
            let mut expected = *attr;

            buf.prevent_merging();
            expected.0.dont_merge = 1;
            prop_assert_eq!(buf, expected);
            prop_assert!(buf.merging_prevented());

            buf.favor_merging();
            expected.0.dont_merge = 0;
            prop_assert!(buf.0.kind > 0);
            expected.0.kind = buf.0.kind;
            prop_assert_eq!(buf, expected);
            prop_assert!(!buf.merging_prevented());
        }

        Ok(())
    }

    #[allow(
        clippy::cast_possible_truncation,
        clippy::cast_precision_loss,
        clippy::cast_sign_loss
    )]
    fn check_valid_pci(attr: &PCIDeviceAttributes) -> Result<(), TestCaseError> {
        check_any_pci(attr)?;

        let link_speed = attr.link_speed();
        prop_assert!(
            link_speed.is_finite() && link_speed >= 0.0 && link_speed < f32::from(u16::MAX)
        );

        Ok(())
    }

    fn check_any_pci(attr: &PCIDeviceAttributes) -> Result<(), TestCaseError> {
        let hwloc_pcidev_attr_s {
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
        } = attr.0;
        prop_assert_eq!(attr.domain(), domain);
        prop_assert_eq!(attr.bus_id(), bus);
        prop_assert_eq!(attr.bus_device(), dev);
        prop_assert_eq!(attr.function(), func);
        prop_assert_eq!(attr.class_id(), class_id);
        prop_assert_eq!(attr.device_id(), device_id);
        prop_assert_eq!(attr.vendor_id(), vendor_id);
        prop_assert_eq!(attr.subvendor_id(), subvendor_id);
        prop_assert_eq!(attr.subdevice_id(), subdevice_id);
        prop_assert_eq!(attr.revision(), revision);
        prop_assert_eq!(attr.link_speed().to_bits(), linkspeed.to_bits());
        Ok(())
    }

    fn check_valid_bridge(attr: &BridgeAttributes) -> Result<(), TestCaseError> {
        check_any_bridge(attr)?;

        prop_assert_eq!(attr.upstream_type() == BridgeType::Host, attr.depth() == 0);
        match attr.upstream_attributes() {
            Some(UpstreamAttributes::PCI(upstream)) => {
                check_valid_pci(upstream)?;
            }
            None => {
                prop_assert_eq!(attr.upstream_type(), BridgeType::Host);
            }
        }
        prop_assert_ne!(attr.downstream_type(), BridgeType::Host);
        match attr.downstream_attributes() {
            Some(DownstreamAttributes::PCI(downstream)) => {
                check_valid_downstream_pci(downstream)?;
            }
            None => unreachable!(),
        }

        Ok(())
    }

    fn check_any_bridge(attr: &BridgeAttributes) -> Result<(), TestCaseError> {
        let hwloc_bridge_attr_s {
            upstream_type,
            upstream,
            downstream_type,
            downstream,
            depth,
        } = attr.0;

        #[allow(clippy::option_if_let_else)]
        let upstream_dbg = if let Ok(upstream_type) = BridgeType::try_from(upstream_type) {
            prop_assert_eq!(attr.upstream_type(), upstream_type);
            #[allow(clippy::single_match_else)]
            match attr.upstream_attributes() {
                Some(UpstreamAttributes::PCI(pci)) => {
                    prop_assert_eq!(upstream_type, BridgeType::PCI);
                    let actual_ptr: *const hwloc_pcidev_attr_s = pci.as_inner();
                    // SAFETY: We must assume correct union tagging here
                    let expected_ptr: *const hwloc_pcidev_attr_s = unsafe { &attr.0.upstream.pci };
                    prop_assert_eq!(actual_ptr, expected_ptr);
                    check_any_pci(pci)?;
                }
                None => prop_assert_ne!(upstream_type, BridgeType::PCI),
            }
            format!(
                "upstream_type: {:?}, upstream_attributes: {:?}",
                attr.upstream_type(),
                attr.upstream_attributes()
            )
        } else {
            assert_panics(|| attr.upstream_type())?;
            assert_panics(|| attr.upstream_attributes())?;
            format!(
                "upstream_type: \"{upstream_type:?}\", \
                upstream_attributes: \"{upstream:?}\""
            )
        };

        #[allow(clippy::option_if_let_else)]
        let downstream_dbg = if let Ok(downstream_type) = BridgeType::try_from(downstream_type) {
            prop_assert_eq!(attr.downstream_type(), downstream_type);
            let downstream_type_dbg = format!("downstream_type: {downstream_type:?}");
            match downstream_type {
                BridgeType::PCI => {
                    #[allow(clippy::single_match_else)]
                    match attr.downstream_attributes() {
                        Some(DownstreamAttributes::PCI(downstream)) => {
                            let actual_ptr: *const RawDownstreamPCIAttributes =
                                downstream.as_inner();
                            let expected_ptr: *const RawDownstreamPCIAttributes =
                            // SAFETY: We must assume correct union tagging here
                            unsafe { &attr.0.downstream.pci };
                            prop_assert_eq!(actual_ptr, expected_ptr);
                            check_any_downstream_pci(downstream)?;
                            format!(
                                "{downstream_type_dbg}, downstream_attributes: {:?}",
                                attr.downstream_attributes()
                            )
                        }
                        None => {
                            prop_assert!(false, "should have returned PCI attributes");
                            unreachable!()
                        }
                    }
                }
                BridgeType::Host => {
                    assert_panics(|| attr.downstream_attributes())?;
                    format!(
                        "{downstream_type_dbg}, \
                        downstream_attributes: \"{downstream:?}\""
                    )
                }
            }
        } else {
            assert_panics(|| attr.downstream_type())?;
            assert_panics(|| attr.downstream_attributes())?;
            format!(
                "downstream_type: \"{downstream_type:?}\", \
                downstream_attributes: \"{downstream:?}\""
            )
        };

        prop_assert_eq!(attr.depth(), usize::try_from(depth).unwrap());

        prop_assert_eq!(
            format!("{attr:?}"),
            format!(
                "BridgeAttributes {{ \
                    {upstream_dbg}, \
                    {downstream_dbg}, \
                    depth: {:?} \
                }}",
                attr.depth()
            )
        );

        Ok(())
    }

    #[allow(clippy::trivially_copy_pass_by_ref)]
    fn check_valid_downstream_pci(attr: &DownstreamPCIAttributes) -> Result<(), TestCaseError> {
        check_any_downstream_pci(attr)
    }

    #[allow(clippy::trivially_copy_pass_by_ref)]
    fn check_any_downstream_pci(attr: &DownstreamPCIAttributes) -> Result<(), TestCaseError> {
        let RawDownstreamPCIAttributes {
            domain,
            secondary_bus,
            subordinate_bus,
        } = attr.0;
        prop_assert_eq!(attr.domain(), domain);
        prop_assert_eq!(attr.secondary_bus(), secondary_bus);
        prop_assert_eq!(attr.subordinate_bus(), subordinate_bus);
        Ok(())
    }

    #[allow(clippy::trivially_copy_pass_by_ref)]
    fn check_valid_osdev(attr: &OSDeviceAttributes) -> Result<(), TestCaseError> {
        check_any_osdev(attr)
    }

    #[allow(clippy::option_if_let_else, clippy::trivially_copy_pass_by_ref)]
    fn check_any_osdev(attr: &OSDeviceAttributes) -> Result<(), TestCaseError> {
        let hwloc_osdev_attr_s { ty } = attr.0;
        let device_type_dbg = if let Ok(device_type) = OSDeviceType::try_from(ty) {
            prop_assert_eq!(attr.device_type(), device_type);
            format!("{device_type:?}")
        } else {
            assert_panics(|| attr.device_type())?;
            format!("\"{ty:?}\"")
        };
        prop_assert_eq!(
            format!("{attr:?}"),
            format!("OSDeviceAttributes {{ device_type: {device_type_dbg} }}")
        );
        Ok(())
    }

    fn check_valid_numa_pair(
        [numa1, numa2]: [&'static TopologyObject; 2],
    ) -> Result<(), TestCaseError> {
        fn numa_attr(
            numa: &'static TopologyObject,
        ) -> Result<NUMANodeAttributes<'static>, TestCaseError> {
            let res = if let Some(ObjectAttributes::NUMANode(attr)) = numa.attributes() {
                *attr
            } else {
                prop_assert!(false, "Not a NUMA node");
                unreachable!()
            };
            Ok(res)
        }
        let [attr1, attr2] = [numa_attr(numa1)?, numa_attr(numa2)?];

        if attr1.local_memory() == attr2.local_memory() && attr1.page_types() == attr2.page_types()
        {
            prop_assert_eq!(attr1, attr2);
            let state = RandomState::new();
            prop_assert_eq!(state.hash_one(attr1), state.hash_one(attr2));
        } else {
            prop_assert_ne!(attr1, attr2);
        }

        Ok(())
    }

    fn check_valid_cache_pair([cache1, cache2]: [&TopologyObject; 2]) -> Result<(), TestCaseError> {
        fn cache_depth(
            cache: &TopologyObject,
        ) -> Result<(NormalDepth, CacheAttributes), TestCaseError> {
            let res = if let Some(ObjectAttributes::Cache(attr)) = cache.attributes() {
                (cache.depth().assume_normal(), *attr)
            } else {
                prop_assert!(false, "Not a CPU cache");
                unreachable!()
            };
            Ok(res)
        }
        let (depth1, attr1) = cache_depth(cache1)?;
        let (depth2, attr2) = cache_depth(cache2)?;

        let obj_depth_cmp = depth1.cmp(&depth2);
        let cache_depth_cmp = attr2.depth().cmp(&attr1.depth());
        if attr1.cache_type() == attr2.cache_type() {
            prop_assert_eq!(obj_depth_cmp, cache_depth_cmp);
        } else {
            prop_assert!(cache_depth_cmp == obj_depth_cmp || cache_depth_cmp == Ordering::Equal);
        }

        prop_assert_eq!(
            attr1.associativity() == CacheAssociativity::Unknown,
            attr2.associativity() == CacheAssociativity::Unknown
        );

        Ok(())
    }

    fn check_valid_group_pair([group1, group2]: [&TopologyObject; 2]) -> Result<(), TestCaseError> {
        fn group_depth(
            group: &TopologyObject,
        ) -> Result<(NormalDepth, GroupAttributes), TestCaseError> {
            let res = if let Some(ObjectAttributes::Group(attr)) = group.attributes() {
                (group.depth().assume_normal(), *attr)
            } else {
                prop_assert!(false, "Not a group");
                unreachable!()
            };
            Ok(res)
        }
        let (depth1, attr1) = group_depth(group1)?;
        let (depth2, attr2) = group_depth(group2)?;

        prop_assert_eq!(depth1.cmp(&depth2), attr1.depth().cmp(&attr2.depth()));

        Ok(())
    }

    fn check_valid_pci_pair([pci1, pci2]: [&TopologyObject; 2]) -> Result<(), TestCaseError> {
        let attr1 = pci_attributes(pci1)?;
        let attr2 = pci_attributes(pci2)?;

        let parent_child_attr = parent_child([(pci1, attr1), (pci2, attr2)]);
        if let Some([parent, child]) = parent_child_attr {
            prop_assert!(child.revision() <= parent.revision());
            prop_assert!(child.link_speed() <= parent.link_speed());
        }

        Ok(())
    }

    fn check_valid_bridge_pair(
        [bridge1, bridge2]: [&TopologyObject; 2],
    ) -> Result<(), TestCaseError> {
        let attr1 = bridge_attributes(bridge1)?;
        let attr2 = bridge_attributes(bridge2)?;

        let parent_child_attr = parent_child([(bridge1, attr1), (bridge2, attr2)]);
        if let Some([parent, child]) = parent_child_attr {
            if !std::ptr::eq(bridge1, bridge2) {
                prop_assert!(parent.depth() < child.depth());
            }
        }

        if attr1.upstream_type() == attr2.upstream_type()
            && attr1.upstream_attributes() == attr2.upstream_attributes()
            && attr1.downstream_type() == attr2.downstream_type()
            && attr1.downstream_attributes() == attr2.downstream_attributes()
            && attr1.depth() == attr2.depth()
        {
            prop_assert_eq!(attr1, attr2);
        } else {
            prop_assert_ne!(attr1, attr2);
        }

        Ok(())
    }

    fn check_valid_bridge_pci([bridge, pci]: [&TopologyObject; 2]) -> Result<(), TestCaseError> {
        let bridge_attr = bridge_attributes(bridge)?;
        let pci_attr = pci_attributes(pci)?;
        prop_assert!(!bridge.is_in_subtree(pci));
        if pci.is_in_subtree(bridge) {
            if let Some(DownstreamAttributes::PCI(downstream_attr)) =
                bridge_attr.downstream_attributes()
            {
                prop_assert_eq!(downstream_attr.domain(), pci_attr.domain());
            }
        }
        Ok(())
    }

    /// If obj1 and obj2 have a parent-child relationship, provide their
    /// attributes in (parent, child) order.
    fn parent_child<Attributes>(
        [(obj1, attr1), (obj2, attr2)]: [(&TopologyObject, Attributes); 2],
    ) -> Option<[Attributes; 2]> {
        if obj1.is_in_subtree(obj2) {
            Some([attr2, attr1])
        } else if obj2.is_in_subtree(obj1) {
            Some([attr1, attr2])
        } else {
            None
        }
    }

    fn pci_attributes(pci: &TopologyObject) -> Result<PCIDeviceAttributes, TestCaseError> {
        let res = if let Some(ObjectAttributes::PCIDevice(attr)) = pci.attributes() {
            *attr
        } else {
            prop_assert!(false, "Not a PCI device");
            unreachable!()
        };
        Ok(res)
    }

    fn bridge_attributes(bridge: &TopologyObject) -> Result<BridgeAttributes, TestCaseError> {
        let res = if let Some(ObjectAttributes::Bridge(attr)) = bridge.attributes() {
            *attr
        } else {
            prop_assert!(false, "Not an I/O bridge");
            unreachable!()
        };
        Ok(res)
    }

    fn make_numa_attributes(
        local_memory: u64,
        page_types: &[MemoryPageType],
    ) -> NUMANodeAttributes<'_> {
        NUMANodeAttributes(
            hwloc_numanode_attr_s {
                local_memory,
                page_types_len: page_types.len().try_into().unwrap(),
                page_types: page_types.as_ptr().as_inner().cast_mut(),
            },
            PhantomData,
        )
    }
}
