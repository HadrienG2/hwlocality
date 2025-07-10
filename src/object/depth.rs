//! Object depth
//!
//! An hwloc topology is a tree of [`TopologyObject`]s. Within this tree, almost
//! every [`ObjectType`] that exists in the topology has its own, designated
//! depth, with the exception of [Group] objects which may exist at multiple
//! depths. This mechanism makes it possible to cheaply look up objects of most
//! types in the topology by just querying the associated depth, at the expense
//! of allowing some counterintuitive depth jumps from parents of depth N to
//! children of depth `N + M` with `M != 1` in complex topologies with
//! heterogeneous CPU cores.
//!
//! Like [Group] objects, [Memory], [I/O] and [Misc] objects can appear at
//! multiple depths of the topology. However, these objects types are handled
//! differently from [Group] objects. Instead of having a normal depth like all
//! other objects, they use a "virtual depth" mechanism where all objects of
//! these types appear to reside at the same virtual depth. This extends the
//! cheap depth lookup of normal object types to these special object types, at
//! the expense of making the depth type not totally ordered.
//!
//! [Group]: ObjectType::Group
//! [I/O]: ObjectType::is_io()
//! [Memory]: ObjectType::is_memory()
//! [Misc]: ObjectType::Misc

// Main docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__levels.html

use crate::ffi::{int::PositiveInt, unknown::UnknownVariant};
#[cfg(doc)]
use crate::object::{types::ObjectType, TopologyObject};
#[cfg(feature = "hwloc-2_1_0")]
use hwlocality_sys::HWLOC_TYPE_DEPTH_MEMCACHE;
use hwlocality_sys::{
    hwloc_get_type_depth_e, HWLOC_TYPE_DEPTH_BRIDGE, HWLOC_TYPE_DEPTH_MISC,
    HWLOC_TYPE_DEPTH_MULTIPLE, HWLOC_TYPE_DEPTH_NUMANODE, HWLOC_TYPE_DEPTH_OS_DEVICE,
    HWLOC_TYPE_DEPTH_PCI_DEVICE, HWLOC_TYPE_DEPTH_UNKNOWN,
};
#[cfg(any(test, feature = "proptest"))]
use proptest::prelude::*;
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::{ffi::c_int, fmt, num::TryFromIntError};
use thiserror::Error;

/// Depth of a normal object (not Memory, I/O or Misc)
pub type NormalDepth = PositiveInt;

/// Valid object/type depth values
///
/// See the [module-level documentation](self) for context.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_get_type_depth_e")]
pub enum Depth {
    /// Depth of a normal object (not Memory, I/O or Misc)
    Normal(NormalDepth),

    /// Virtual depth for [`ObjectType::NUMANode`]
    #[doc(alias = "HWLOC_TYPE_DEPTH_NUMANODE")]
    NUMANode,

    /// Virtual depth for [`ObjectType::Bridge`]
    #[doc(alias = "HWLOC_TYPE_DEPTH_BRIDGE")]
    Bridge,

    /// Virtual depth for [`ObjectType::PCIDevice`]
    #[doc(alias = "HWLOC_TYPE_DEPTH_PCI_DEVICE")]
    PCIDevice,

    /// Virtual depth for [`ObjectType::OSDevice`]
    #[doc(alias = "HWLOC_TYPE_DEPTH_OS_DEVICE")]
    OSDevice,

    /// Virtual depth for [`ObjectType::Misc`]
    #[doc(alias = "HWLOC_TYPE_DEPTH_MISC")]
    Misc,

    /// Virtual depth for [`ObjectType::MemCache`]
    #[cfg(feature = "hwloc-2_1_0")]
    #[doc(alias = "HWLOC_TYPE_DEPTH_MEMCACHE")]
    MemCache,
    // NOTE: Also add new virtual depths to the VIRTUAL_DEPTHS array and its
    //       type-specific declination below
    //
    /// Unknown [`hwloc_get_type_depth_e`] from hwloc
    Unknown(UnknownVariant<hwloc_get_type_depth_e>),
}
//
impl Depth {
    /// Assert that this should be a normal object depth, panicking if it turns
    /// out not to be the case.
    pub fn expect_normal(self) -> NormalDepth {
        NormalDepth::try_from(self).expect("Not a normal object depth")
    }

    /// List of virtual depths
    pub const VIRTUAL_DEPTHS: &'static [Self] = &[
        #[cfg(feature = "hwloc-2_1_0")]
        Self::MemCache,
        Self::NUMANode,
        Self::Bridge,
        Self::PCIDevice,
        Self::OSDevice,
        Self::Misc,
    ];

    /// List of memory object virtual depths
    pub const MEMORY_DEPTHS: &'static [Self] = &[
        #[cfg(feature = "hwloc-2_1_0")]
        Self::MemCache,
        Self::NUMANode,
    ];

    /// List of I/O object virtual depths
    pub const IO_DEPTHS: &'static [Self] = &[Self::Bridge, Self::PCIDevice, Self::OSDevice];

    /// Decode depth results from hwloc
    ///
    /// # Safety
    ///
    /// This type normally maintains the invariant that it holds a valid hwloc
    /// input, and safe code relies on this to treat any C representation of
    /// this enum as valid to send to hwloc. Therefore, you must enforce that
    /// either of the following is true:
    ///
    /// - `value` is a known hwloc depth valueor was emitted by hwloc as output,
    ///   and therefore is known/suspected to be a safe hwloc input.
    /// - The output of `from_hwloc` from a `value` that is _not_ a known-good
    ///   hwloc input is never sent to any hwloc API, either directly or via a
    ///   safe `hwlocality` method. This possibility is mainly provided for
    ///   unit testing code and not meant to be used on a larger scale.
    pub(crate) unsafe fn from_hwloc(
        value: hwloc_get_type_depth_e,
    ) -> Result<Self, TypeToDepthError> {
        match value {
            normal if normal >= 0 => {
                let normal = NormalDepth::try_from_c_int(normal)
                    .expect("NormalDepth should support all positive depths");
                Ok(normal.into())
            }
            HWLOC_TYPE_DEPTH_UNKNOWN => Err(TypeToDepthError::Nonexistent),
            HWLOC_TYPE_DEPTH_MULTIPLE => Err(TypeToDepthError::Multiple),
            HWLOC_TYPE_DEPTH_NUMANODE => Ok(Self::NUMANode),
            HWLOC_TYPE_DEPTH_BRIDGE => Ok(Self::Bridge),
            HWLOC_TYPE_DEPTH_PCI_DEVICE => Ok(Self::PCIDevice),
            HWLOC_TYPE_DEPTH_OS_DEVICE => Ok(Self::OSDevice),
            HWLOC_TYPE_DEPTH_MISC => Ok(Self::Misc),
            #[cfg(feature = "hwloc-2_1_0")]
            HWLOC_TYPE_DEPTH_MEMCACHE => Ok(Self::MemCache),
            other => Ok(Self::Unknown(UnknownVariant(other))),
        }
    }

    /// Convert back to the hwloc depth format
    pub(crate) fn to_hwloc(self) -> hwloc_get_type_depth_e {
        match self {
            Self::Normal(value) => value.to_c_int(),
            Self::NUMANode => HWLOC_TYPE_DEPTH_NUMANODE,
            Self::Bridge => HWLOC_TYPE_DEPTH_BRIDGE,
            Self::PCIDevice => HWLOC_TYPE_DEPTH_PCI_DEVICE,
            Self::OSDevice => HWLOC_TYPE_DEPTH_OS_DEVICE,
            Self::Misc => HWLOC_TYPE_DEPTH_MISC,
            #[cfg(feature = "hwloc-2_1_0")]
            Self::MemCache => HWLOC_TYPE_DEPTH_MEMCACHE,
            Self::Unknown(unknown) => unknown.0,
        }
    }
}
//
#[cfg(any(test, feature = "proptest"))]
impl Arbitrary for Depth {
    type Parameters = <NormalDepth as Arbitrary>::Parameters;
    type Strategy = prop::strategy::TupleUnion<(
        prop::strategy::WA<
            prop::strategy::Map<<NormalDepth as Arbitrary>::Strategy, fn(NormalDepth) -> Self>,
        >,
        prop::strategy::WA<prop::sample::Select<Self>>,
    )>;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        prop_oneof![
            4 => NormalDepth::arbitrary_with(args).prop_map(Self::Normal),
            1 => prop::sample::select(Self::VIRTUAL_DEPTHS)
        ]
    }
}
//
impl Default for Depth {
    fn default() -> Self {
        Self::from(NormalDepth::default())
    }
}
//
impl fmt::Display for Depth {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[allow(clippy::wildcard_enum_match_arm)]
        match self {
            Self::Normal(d) => <NormalDepth as fmt::Display>::fmt(d, f),
            abnormal => {
                let s = format!("<{abnormal:?}>");
                f.pad(&s)
            }
        }
    }
}
//
impl From<NormalDepth> for Depth {
    fn from(value: NormalDepth) -> Self {
        Self::Normal(value)
    }
}
//
impl PartialEq<NormalDepth> for Depth {
    fn eq(&self, other: &NormalDepth) -> bool {
        *self == Self::Normal(*other)
    }
}
//
impl PartialEq<Depth> for NormalDepth {
    fn eq(&self, other: &Depth) -> bool {
        other == self
    }
}
//
impl PartialEq<usize> for Depth {
    fn eq(&self, other: &usize) -> bool {
        Self::try_from(*other) == Ok(*self)
    }
}
//
impl PartialEq<Depth> for usize {
    fn eq(&self, other: &Depth) -> bool {
        other == self
    }
}
//
impl TryFrom<usize> for Depth {
    type Error = TryFromIntError;

    fn try_from(value: usize) -> Result<Self, TryFromIntError> {
        NormalDepth::try_from(value).map(Self::from)
    }
}
//
impl TryFrom<Depth> for NormalDepth {
    type Error = Depth;

    fn try_from(value: Depth) -> Result<Self, Depth> {
        if let Depth::Normal(depth) = value {
            Ok(depth)
        } else {
            Err(value)
        }
    }
}
//
impl TryFrom<Depth> for usize {
    type Error = Depth;

    fn try_from(value: Depth) -> Result<Self, Depth> {
        NormalDepth::try_from(value).map(Self::from)
    }
}

/// Error from an hwloc query looking for the depth of a certain object type
#[derive(Copy, Clone, Debug, Eq, Error, Hash, PartialEq)]
pub enum TypeToDepthError {
    /// No object of the requested type exists in the topology
    #[doc(alias = "HWLOC_TYPE_DEPTH_UNKNOWN")]
    #[error("no object of requested type exists in the topology")]
    Nonexistent,

    /// Objects of the requested type exist at different depths in the topology
    ///
    /// At the time of writing, this can only happen with [`ObjectType::Group`].
    #[doc(alias = "HWLOC_TYPE_DEPTH_MULTIPLE")]
    #[error("objects of requested type exist at different depths in the topology")]
    Multiple,
}

#[cfg(test)]
mod tests {
    use crate::tests::assert_panics;

    use super::*;
    #[allow(unused)]
    use similar_asserts::assert_eq;
    use static_assertions::{assert_impl_all, assert_not_impl_any, assert_type_eq_all};
    use std::{
        error::Error,
        fmt::{Binary, Debug, Display, LowerExp, LowerHex, Octal, Pointer, UpperExp, UpperHex},
        hash::Hash,
        io::{self, Read},
        ops::Deref,
        panic::UnwindSafe,
    };

    // Check that public types in this module keep implementing all expected
    // traits, in the interest of detecting future semver-breaking changes
    assert_impl_all!(Depth:
        Copy, Debug, Default, Display, From<NormalDepth>, Hash,
        PartialEq<NormalDepth>, PartialEq<usize>, Sized, Sync, TryFrom<usize>,
        TryInto<NormalDepth>, TryInto<usize>, Unpin, UnwindSafe
    );
    assert_not_impl_any!(Depth:
        Binary, Deref, Drop, Error, IntoIterator, LowerExp, LowerHex,
        Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write,
        io::Write
    );
    assert_type_eq_all!(NormalDepth, PositiveInt);
    assert_impl_all!(TypeToDepthError:
        Copy, Error, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(TypeToDepthError:
        Binary, Default, Deref, Drop, IntoIterator, LowerExp, LowerHex, Octal,
        PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write, io::Write
    );

    #[test]
    fn special_values() {
        assert_eq!(Depth::default(), Depth::from(NormalDepth::default()));
        assert_eq!(
            // SAFETY: Expected output from hwloc
            unsafe { Depth::from_hwloc(HWLOC_TYPE_DEPTH_UNKNOWN) },
            Err(TypeToDepthError::Nonexistent)
        );
        assert_eq!(
            // SAFETY: Expected output from hwloc
            unsafe { Depth::from_hwloc(HWLOC_TYPE_DEPTH_MULTIPLE) },
            Err(TypeToDepthError::Multiple)
        );
        const RAW_DEPTHS: &[hwloc_get_type_depth_e] = &[
            #[cfg(feature = "hwloc-2_1_0")]
            {
                HWLOC_TYPE_DEPTH_MEMCACHE
            },
            HWLOC_TYPE_DEPTH_NUMANODE,
            HWLOC_TYPE_DEPTH_BRIDGE,
            HWLOC_TYPE_DEPTH_PCI_DEVICE,
            HWLOC_TYPE_DEPTH_OS_DEVICE,
            HWLOC_TYPE_DEPTH_MISC,
        ];
        assert_eq!(RAW_DEPTHS.len(), Depth::VIRTUAL_DEPTHS.len());
        for (&raw, &depth) in RAW_DEPTHS.iter().zip(Depth::VIRTUAL_DEPTHS) {
            // SAFETY: Expected output from hwloc
            assert_eq!(unsafe { Depth::from_hwloc(raw) }, Ok(depth))
        }
    }

    proptest! {
        #[test]
        fn unary(depth: Depth) {
            // A depth is either normal or virtual
            prop_assert!(matches!(depth, Depth::Normal(_)) || Depth::VIRTUAL_DEPTHS.contains(&depth));
            if let Depth::Normal(normal) = depth {
                prop_assert_eq!(depth.to_string(), normal.to_string());
                prop_assert_eq!(NormalDepth::try_from(depth), Ok(normal));
                prop_assert_eq!(usize::try_from(depth).unwrap(), normal);
                prop_assert_eq!(depth.expect_normal(), normal);
                prop_assert!(depth.to_hwloc() >= 0);
            } else {
                prop_assert_eq!(depth.to_string(), format!("<{depth:?}>"));
                prop_assert!(NormalDepth::try_from(depth).is_err());
                prop_assert!(usize::try_from(depth).is_err());
                assert_panics(|| depth.expect_normal())?;
                prop_assert!(depth.to_hwloc() <= HWLOC_TYPE_DEPTH_NUMANODE);
            }
        }

        #[test]
        fn from_normal(normal: NormalDepth) {
            prop_assert_eq!(Depth::from(normal), normal);
            prop_assert_eq!(normal, Depth::from(normal));
        }
    }

    /// Generate [`usize`] values that are mostly in [`NormalDepth`] range to
    /// make sure the [`from_usize()`] test has good coverage
    fn mostly_small_usize() -> impl Strategy<Value = usize> {
        prop_oneof![
            4 => usize::from(NormalDepth::MIN)..usize::from(NormalDepth::MAX),
            1 => any::<usize>()
        ]
    }

    proptest! {
        #[test]
        fn from_usize(value in mostly_small_usize()) {
            if value < usize::from(NormalDepth::MAX) {
                prop_assert_eq!(Depth::try_from(value).unwrap(), value);
                prop_assert_eq!(value, Depth::try_from(value).unwrap());
            } else {
                prop_assert!(Depth::try_from(value).is_err());
            }
        }

        #[test]
        fn from_raw(value: hwloc_get_type_depth_e) {
            // SAFETY: value is not necessarily a valid output from hwloc here,
            //         but we will not send the resulting invalid depth to any
            //         hwloc function so we can get away with it.
            let depth_res = unsafe { Depth::from_hwloc(value) };
            if value >= 0 {
                prop_assert!(depth_res.is_ok());
                prop_assert_eq!(depth_res.unwrap(), usize::try_from(value).unwrap());
            } else if value == HWLOC_TYPE_DEPTH_UNKNOWN {
                prop_assert_eq!(depth_res, Err(TypeToDepthError::Nonexistent));
            } else if value == HWLOC_TYPE_DEPTH_MULTIPLE {
                prop_assert_eq!(depth_res, Err(TypeToDepthError::Multiple));
            } else if value
                > -2 - hwloc_get_type_depth_e::try_from(Depth::VIRTUAL_DEPTHS.len()).unwrap()
            {
                prop_assert!(depth_res.is_ok());
            } else {
                prop_assert_eq!(depth_res, Ok(Depth::Unknown(UnknownVariant(value))));
            }
        }

        #[test]
        fn eq_int(depth: Depth, normal: NormalDepth) {
            prop_assert_eq!(depth == normal, depth == Depth::Normal(normal));
        }

        #[test]
        fn eq_usize(depth: Depth, value: usize) {
            prop_assert_eq!(
                depth == value,
                PositiveInt::try_from(value).is_ok_and(|value| depth == value)
            );
        }
    }
}
