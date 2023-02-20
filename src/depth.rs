//! Topology object depth

// Main docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__levels.html

#[cfg(doc)]
use crate::objects::types::ObjectType;
use std::{ffi::c_int, fmt};
use thiserror::Error;

/// Rust mapping of the hwloc_get_type_depth_e enum
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
///
pub(crate) type RawDepth = c_int;

/// Valid object/type depth values
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Depth {
    /// Depth of a normal object (not Memory, I/O or Misc)
    Normal(u32),

    /// Virtual depth for [`ObjectType::NUMANode`]
    NUMANode,

    /// Virtual depth for [`ObjectType::Bridge`]
    Bridge,

    /// Virtual depth for [`ObjectType::PCIDevice`]
    PCIDevice,

    /// Virtual depth for [`ObjectType::OSDevice`]
    OSDevice,

    /// Virtual depth for [`ObjectType::Misc`]
    Misc,

    /// Virtual depth for [`ObjectType::MemCache`]
    MemCache,
}

impl Depth {
    /// Assert that this should be a normal object depth
    pub fn assume_normal(self) -> u32 {
        u32::try_from(self).expect("Not a normal object depth")
    }
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
            Depth::MemCache => -8,
        }
    }
}

/// Error from an hwloc depth query
#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
pub enum DepthError {
    /// No object of given type exists in the topology
    #[error("no object of given type exists in the topology")]
    None,

    /// Objects of given type exist at different depths in the topology
    #[error("objects of given type exist at different depths in the topology")]
    Multiple,

    /// Unexpected hwloc error or special depth value
    #[error("unexpected hwloc error or special depth value {0}")]
    Unknown(i32),
}

/// Result from an hwloc depth query
pub type DepthResult = Result<Depth, DepthError>;
