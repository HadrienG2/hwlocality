//! Object depth

// Main docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__levels.html

#[cfg(doc)]
use crate::objects::types::ObjectType;
use std::{ffi::c_int, fmt};
use thiserror::Error;

/// Rust mapping of the hwloc_get_type_depth_e enum
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
pub(crate) type RawDepth = c_int;

/// Valid object/type depth values
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum Depth {
    /// Depth of a normal object (not Memory, I/O or Misc)
    Normal(u32),

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
    // NOTE: Add new virtual depths to VIRTUAL_DEPTHS below
}

impl Depth {
    /// Assert that this should be a normal object depth
    pub fn assume_normal(self) -> u32 {
        u32::try_from(self).expect("Not a normal object depth")
    }

    /// List of virtual depths
    pub const VIRTUAL_DEPTHS: &[Self] = &[
        Self::NUMANode,
        Self::Bridge,
        Self::PCIDevice,
        Self::OSDevice,
        Self::Misc,
        #[cfg(feature = "hwloc-2_1_0")]
        Self::MemCache,
    ];
}

impl fmt::Display for Depth {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Normal(d) => write!(f, "{d}"),
            abnormal => write!(f, "<{abnormal:?}>"),
        }
    }
}

impl From<u32> for Depth {
    fn from(value: u32) -> Self {
        Self::Normal(value)
    }
}

impl TryFrom<Depth> for u32 {
    type Error = Depth;

    fn try_from(value: Depth) -> Result<Self, Depth> {
        if let Depth::Normal(depth) = value {
            Ok(depth)
        } else {
            Err(value)
        }
    }
}

impl TryFrom<RawDepth> for Depth {
    type Error = DepthError;

    fn try_from(value: RawDepth) -> Result<Self, DepthError> {
        match value {
            d if d >= 0 => Ok(Self::Normal(
                u32::try_from(d).expect("i32 >= 0 -> u32 cannot fail"),
            )),
            -1 => Err(DepthError::None),
            -2 => Err(DepthError::Multiple),
            -3 => Ok(Self::NUMANode),
            -4 => Ok(Self::Bridge),
            -5 => Ok(Self::PCIDevice),
            -6 => Ok(Self::OSDevice),
            -7 => Ok(Self::Misc),
            #[cfg(feature = "hwloc-2_1_0")]
            -8 => Ok(Self::MemCache),
            other => Err(DepthError::Unknown(other)),
        }
    }
}

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

/// Error from an hwloc depth query
#[derive(Copy, Clone, Debug, Eq, Error, Hash, PartialEq)]
pub enum DepthError {
    /// No object of given type exists in the topology
    #[doc(alias = "HWLOC_TYPE_DEPTH_UNKNOWN")]
    #[error("no object of given type exists in the topology")]
    None,

    /// Objects of given type exist at different depths in the topology
    ///
    /// You can only get this error while querying the depth of Group objects.
    #[doc(alias = "HWLOC_TYPE_DEPTH_MULTIPLE")]
    #[error("objects of given type exist at different depths in the topology")]
    Multiple,

    /// Unexpected special depth value or hwloc error
    ///
    /// You can get this error for two different reasons:
    ///
    /// - hwloc introduced a new virtual depth, and the version of the Rust
    ///   bindings that you are using has not yet been extended to handle this
    ///   new virtual depth. This is the most likely scenario.
    /// - hwloc failed to probe the requested depth and returned a negative
    ///   value to indicate that, but this negative value is not documented so
    ///   the Rust bindings couldn't figure out what's not going on.
    #[error("unexpected special depth value or hwloc error: {0}")]
    Unknown(i32),
}

/// Result from an hwloc depth query
pub type DepthResult = Result<Depth, DepthError>;
