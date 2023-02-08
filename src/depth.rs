//! Topology object depth

// Main docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__levels.html

use std::ffi::c_int;

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

    /// Virtual depth for NUMA nodes
    NUMANode,

    /// Virtual depth for bridge objects
    Bridge,

    /// Virtual depth for PCI devices
    PCIDevice,

    /// Virtual depth for OS devices
    OSDevice,

    /// Virtual depth for Misc objects
    Misc,

    /// Virtual depth for near-memory caches
    MemCache,
}

impl Depth {
    /// Assert that this should be a normal object depth
    pub fn assert_normal(self) -> u32 {
        u32::try_from(self).unwrap()
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
            d if d >= 0 => Ok(Self::Normal(u32::try_from(d).unwrap())),
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
            Depth::Normal(value) => value.try_into().unwrap(),
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
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum DepthError {
    /// No object of given type exists in the topology.
    None,

    /// Objects of given type exist at different depths in the topology.
    Multiple,

    /// Unexpected hwloc error or special depth value
    Unknown(i32),
}

/// Result from an hwloc depth query
pub type DepthResult = Result<Depth, DepthError>;