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

use crate::ffi;
#[cfg(doc)]
use crate::object::{types::ObjectType, TopologyObject};
use std::{
    ffi::{c_int, c_uint},
    fmt,
};
use thiserror::Error;

/// Rust mapping of the `hwloc_get_type_depth_e` enum
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
pub(crate) type RawDepth = c_int;

/// Valid object/type depth values
///
/// See the [module-level documentation](self) for context.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
#[doc(alias("hwloc_get_type_depth_e"))]
pub enum Depth {
    /// Depth of a normal object (not Memory, I/O or Misc)
    Normal(usize),

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
    pub fn assume_normal(self) -> usize {
        usize::try_from(self).expect("Not a normal object depth")
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
}
//
impl fmt::Display for Depth {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[allow(clippy::wildcard_enum_match_arm)]
        match self {
            Self::Normal(d) => <usize as fmt::Display>::fmt(d, f),
            abnormal => {
                let s = format!("<{abnormal:?}>");
                f.pad(&s)
            }
        }
    }
}
//
impl From<usize> for Depth {
    fn from(value: usize) -> Self {
        Self::Normal(value)
    }
}
//
impl TryFrom<Depth> for usize {
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
impl TryFrom<RawDepth> for Depth {
    type Error = TypeToDepthError;

    fn try_from(value: RawDepth) -> Result<Self, TypeToDepthError> {
        match value {
            d if d >= 0 => {
                let d = c_uint::try_from(d).expect("int >= 0 -> uint conversion can't fail");
                Ok(Self::Normal(ffi::expect_usize(d)))
            }
            -1 => Err(TypeToDepthError::Nonexistent),
            -2 => Err(TypeToDepthError::Multiple),
            -3 => Ok(Self::NUMANode),
            -4 => Ok(Self::Bridge),
            -5 => Ok(Self::PCIDevice),
            -6 => Ok(Self::OSDevice),
            -7 => Ok(Self::Misc),
            #[cfg(feature = "hwloc-2_1_0")]
            -8 => Ok(Self::MemCache),
            other => Err(TypeToDepthError::Unexpected(other)),
        }
    }
}
//
impl From<Depth> for RawDepth {
    fn from(value: Depth) -> Self {
        match value {
            Depth::Normal(value) => value.try_into().expect("Depth is too high for hwloc"),
            Depth::NUMANode => -3,
            Depth::Bridge => -4,
            Depth::PCIDevice => -5,
            Depth::OSDevice => -6,
            Depth::Misc => -7,
            #[cfg(feature = "hwloc-2_1_0")]
            Depth::MemCache => -8,
        }
    }
}

/// Error from an hwloc query looking for the depth of a certain object type
#[derive(Copy, Clone, Debug, Eq, Error, Hash, PartialEq)]
pub enum TypeToDepthError {
    /// No object of the requested type exists in the topology
    #[doc(alias = "HWLOC_TYPE_DEPTH_UNKNOWN")]
    #[error("no object of given type exists in the topology")]
    Nonexistent,

    /// Objects of the requested type exist at different depths in the topology
    ///
    /// At the time of writing, this can only happen with [`ObjectType::Group`].
    #[doc(alias = "HWLOC_TYPE_DEPTH_MULTIPLE")]
    #[error("objects of given type exist at different depths in the topology")]
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
    #[error("unexpected special depth value or hwloc error: {0}")]
    Unexpected(c_int),
}

/// Result from an hwloc query looking for the depth of a certain object type
pub type TypeToDepthResult = Result<Depth, TypeToDepthError>;
