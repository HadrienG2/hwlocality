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

use crate::ffi::int::PositiveInt;
#[cfg(doc)]
use crate::object::{types::ObjectType, TopologyObject};
#[cfg(feature = "hwloc-2_1_0")]
use hwlocality_sys::HWLOC_TYPE_DEPTH_MEMCACHE;
use hwlocality_sys::{
    hwloc_get_type_depth_e, HWLOC_TYPE_DEPTH_BRIDGE, HWLOC_TYPE_DEPTH_MISC,
    HWLOC_TYPE_DEPTH_MULTIPLE, HWLOC_TYPE_DEPTH_NUMANODE, HWLOC_TYPE_DEPTH_OS_DEVICE,
    HWLOC_TYPE_DEPTH_PCI_DEVICE, HWLOC_TYPE_DEPTH_UNKNOWN,
};
#[allow(unused)]
#[cfg(test)]
use pretty_assertions::{assert_eq, assert_ne};
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
    // NOTE: Also add new virtual depths to the VIRTUAL_DEPTHS array below
}
//
impl Depth {
    /// Assert that this should be a normal object depth
    pub fn assume_normal(self) -> NormalDepth {
        NormalDepth::try_from(self).expect("Not a normal object depth")
    }

    /// List of virtual depths
    pub const VIRTUAL_DEPTHS: &'static [Self] = &[
        Self::NUMANode,
        Self::Bridge,
        Self::PCIDevice,
        Self::OSDevice,
        Self::Misc,
        #[cfg(feature = "hwloc-2_1_0")]
        Self::MemCache,
    ];

    /// Decode depth results from hwloc
    pub(crate) fn from_raw(value: hwloc_get_type_depth_e) -> Result<Self, TypeToDepthError> {
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
            other => Err(TypeToDepthError::Unexpected(other)),
        }
    }

    /// Convert back to the hwloc depth format
    pub(crate) fn into_raw(self) -> hwloc_get_type_depth_e {
        match self {
            Self::Normal(value) => value.into_c_int(),
            Self::NUMANode => HWLOC_TYPE_DEPTH_NUMANODE,
            Self::Bridge => HWLOC_TYPE_DEPTH_BRIDGE,
            Self::PCIDevice => HWLOC_TYPE_DEPTH_PCI_DEVICE,
            Self::OSDevice => HWLOC_TYPE_DEPTH_OS_DEVICE,
            Self::Misc => HWLOC_TYPE_DEPTH_MISC,
            #[cfg(feature = "hwloc-2_1_0")]
            Self::MemCache => HWLOC_TYPE_DEPTH_MEMCACHE,
        }
    }
}
//
#[cfg(any(test, feature = "quickcheck"))]
impl quickcheck::Arbitrary for Depth {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        if bool::arbitrary(g) {
            NormalDepth::arbitrary(g).into()
        } else {
            Self::VIRTUAL_DEPTHS[usize::arbitrary(g) % Self::VIRTUAL_DEPTHS.len()]
        }
    }

    #[cfg(not(tarpaulin_include))]
    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        if let Self::Normal(normal) = self {
            Box::new(normal.shrink().map(Self::Normal))
        } else {
            Box::new(std::iter::empty())
        }
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
        Self::try_from(*other).map_or(false, |other| *self == other)
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

    /// Unexpected special depth value or hwloc error
    ///
    /// You can get this error for two different reasons:
    ///
    /// - hwloc introduced a new virtual depth, and the version of the Rust
    ///   bindings that you are using has not yet been updated to handle this
    ///   new virtual depth. This is the most likely scenario.
    /// - hwloc failed to probe the requested depth and returned a negative
    ///   value to indicate that, but this negative value is not documented so
    ///   the Rust bindings couldn't figure out what's going on.
    #[error("got unexpected special object depth value or hwloc error code {0}")]
    Unexpected(c_int),
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused)]
    use pretty_assertions::{assert_eq, assert_ne};
    use quickcheck_macros::quickcheck;
    use static_assertions::{assert_impl_all, assert_not_impl_any, assert_type_eq_all};
    use std::{
        error::Error,
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
            Depth::from_raw(HWLOC_TYPE_DEPTH_UNKNOWN),
            Err(TypeToDepthError::Nonexistent)
        );
        assert_eq!(
            Depth::from_raw(HWLOC_TYPE_DEPTH_MULTIPLE),
            Err(TypeToDepthError::Multiple)
        );
        const RAW_DEPTHS: &[hwloc_get_type_depth_e] = &[
            HWLOC_TYPE_DEPTH_NUMANODE,
            HWLOC_TYPE_DEPTH_BRIDGE,
            HWLOC_TYPE_DEPTH_PCI_DEVICE,
            HWLOC_TYPE_DEPTH_OS_DEVICE,
            HWLOC_TYPE_DEPTH_MISC,
            #[cfg(feature = "hwloc-2_1_0")]
            {
                HWLOC_TYPE_DEPTH_MEMCACHE
            },
        ];
        assert_eq!(RAW_DEPTHS.len(), Depth::VIRTUAL_DEPTHS.len());
        for (&raw, &depth) in RAW_DEPTHS.iter().zip(Depth::VIRTUAL_DEPTHS) {
            assert_eq!(Depth::from_raw(raw), Ok(depth))
        }
    }

    #[quickcheck]
    fn unary(depth: Depth) {
        // A depth is either normal or virtual
        assert!(matches!(depth, Depth::Normal(_)) || Depth::VIRTUAL_DEPTHS.contains(&depth));
        assert_eq!(depth.clone(), depth);

        if let Depth::Normal(normal) = depth {
            assert_eq!(depth.to_string(), normal.to_string());
            assert_eq!(NormalDepth::try_from(depth), Ok(normal));
            assert_eq!(usize::try_from(depth).unwrap(), normal);
            assert_eq!(depth.assume_normal(), normal);
            assert!(depth.into_raw() >= 0);
        } else {
            assert_eq!(depth.to_string(), format!("<{depth:?}>"));
            NormalDepth::try_from(depth).unwrap_err();
            usize::try_from(depth).unwrap_err();
            std::panic::catch_unwind(|| depth.assume_normal()).unwrap_err();
            assert!(depth.into_raw() <= HWLOC_TYPE_DEPTH_NUMANODE);
        }
    }

    #[quickcheck]
    fn from_normal(normal: NormalDepth) {
        assert_eq!(Depth::from(normal), normal);
        assert_eq!(normal, Depth::from(normal));
    }

    #[quickcheck]
    fn from_usize(value: usize) {
        if value < usize::from(NormalDepth::MAX) {
            assert_eq!(Depth::try_from(value).unwrap(), value);
            assert_eq!(value, Depth::try_from(value).unwrap());
        } else {
            Depth::try_from(value).unwrap_err();
        }
    }

    #[quickcheck]
    fn from_raw(value: hwloc_get_type_depth_e) {
        let depth_res = Depth::from_raw(value);
        if value >= 0 {
            assert_eq!(depth_res.unwrap(), usize::try_from(value).unwrap());
        } else if value == HWLOC_TYPE_DEPTH_UNKNOWN {
            assert_eq!(depth_res, Err(TypeToDepthError::Nonexistent));
        } else if value == HWLOC_TYPE_DEPTH_MULTIPLE {
            assert_eq!(depth_res, Err(TypeToDepthError::Multiple));
        } else if value
            > -2 - hwloc_get_type_depth_e::try_from(Depth::VIRTUAL_DEPTHS.len()).unwrap()
        {
            depth_res.unwrap();
        } else {
            assert_eq!(depth_res, Err(TypeToDepthError::Unexpected(value)));
        }
    }

    #[quickcheck]
    fn eq_int(depth: Depth, normal: NormalDepth) {
        assert_eq!(depth == normal, depth == Depth::Normal(normal));
    }

    #[quickcheck]
    fn eq_usize(depth: Depth, value: usize) {
        assert_eq!(
            depth == value,
            PositiveInt::try_from(value).map_or(false, |value| depth == value)
        );
    }
}
