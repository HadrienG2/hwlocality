//! Cache-specific attributes

use crate::{
    ffi::{int, transparent::TransparentNewtype},
    object::types::CacheType,
};
use hwlocality_sys::hwloc_cache_attr_s;
#[cfg(any(test, feature = "proptest"))]
use proptest::prelude::*;
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::{
    cmp::Ordering,
    ffi::c_uint,
    fmt::{self, Debug},
    hash::Hash,
    num::{NonZeroU64, NonZeroUsize},
};

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
    ///
    /// Note that following hardware nomenclature, cache depths normally start
    /// at 1, corresponding to the L1 cache.
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

        debug
            .field("size", &self.size())
            .field("depth", &self.depth())
            .field("line_size", &self.line_size());

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

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use crate::{
        ffi::transparent::AsInner,
        object::{
            attributes::{
                tests::{object_pair, ObjectsWithAttrs},
                ObjectAttributes,
            },
            depth::NormalDepth,
            types::{CacheType, ObjectType},
            TopologyObject,
        },
        tests::assert_panics,
    };
    use hwlocality_sys::{hwloc_cache_attr_s, hwloc_obj_attr_u};
    #[allow(unused)]
    use similar_asserts::assert_eq;
    use static_assertions::{assert_impl_all, assert_not_impl_any};
    use std::{
        fmt::{
            self, Binary, Debug, Display, LowerExp, LowerHex, Octal, Pointer, UpperExp, UpperHex,
        },
        hash::Hash,
        io::{self, Read},
        ops::Deref,
        panic::UnwindSafe,
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

    /// Pick a random CPU cache type
    fn cpu_cache_type() -> impl Strategy<Value = ObjectType> {
        let cache_types = enum_iterator::all::<ObjectType>()
            .filter(|ty| ty.is_cpu_cache())
            .collect::<Vec<_>>();
        prop::sample::select(cache_types)
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

    /// Check [`CacheAttributes`] properties that should be true of valid
    /// [`TopologyObject`]s coming from hwloc
    pub(crate) fn check_valid_cache(attr: &CacheAttributes) -> Result<(), TestCaseError> {
        check_any_cache(attr)?;

        // True on every non-niche hardware architecture, which makes it a
        // reasonable data consistency check
        if let Some(linesize) = attr.line_size() {
            prop_assert!(linesize.is_power_of_two());
        }

        Ok(())
    }

    /// Check [`CacheAttributes`] properties that should always be true
    fn check_any_cache(attr: &CacheAttributes) -> Result<(), TestCaseError> {
        let hwloc_cache_attr_s {
            size,
            depth,
            linesize,
            associativity,
            ty,
        } = attr.0;

        prop_assert_eq!(attr.size(), NonZeroU64::new(size));

        prop_assert_eq!(attr.depth(), usize::try_from(depth).unwrap());
        let depth_dbg = format!("{:?}", attr.depth());

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

    /// Check attribute properties that should be true of any pair of valid CPU
    /// caches from the hwloc topology
    fn check_valid_cache_pair([cache1, cache2]: [&TopologyObject; 2]) -> Result<(), TestCaseError> {
        fn cache_depth(
            cache: &TopologyObject,
        ) -> Result<(NormalDepth, CacheAttributes), TestCaseError> {
            let res = if let Some(ObjectAttributes::Cache(attr)) = cache.attributes() {
                (cache.depth().expect_normal(), *attr)
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
}
