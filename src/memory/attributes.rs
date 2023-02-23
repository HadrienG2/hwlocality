//! Memory attributes

// Upstream docs:
// - https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs.html
// - https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs__manage.html

use crate::{
    bitmap::{CpuSet, RawBitmap},
    objects::TopologyObject,
    Topology,
};
use bitflags::bitflags;
use derive_more::Display;
use std::ffi::{c_int, c_ulong};
use thiserror::Error;

/// Memory attribute identifier
///
/// May be either one of the predefined identifiers (see associated consts) or
/// a new identifier returned by hwloc_memattr_register() (TODO: bind and link).
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Display, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_memattr_id_e")]
#[doc(alias = "hwloc_memattr_id_t")]
pub struct MemoryAttributeID(u32);
//
impl MemoryAttributeID {
    /// Node capacity in bytes (see [`TopologyObject::total_memory()`])
    #[doc(alias = "HWLOC_MEMATTR_ID_CAPACITY")]
    pub const CAPACITY: Self = Self(0);

    /// Number of PUs in that locality (i.e. cpuset weight)
    #[doc(alias = "HWLOC_MEMATTR_ID_LOCALITY")]
    pub const LOCALITY: Self = Self(1);

    /// Average bandwidth in MiB/s, as seen from the given initiator location
    ///
    /// This is the average bandwidth for read and write accesses. If the
    /// platform provides individual read and write bandwidths but no explicit
    /// average value, hwloc computes and returns the average.
    #[doc(alias = "HWLOC_MEMATTR_ID_BANDWIDTH")]
    pub const BANDWIDTH: Self = Self(2);

    /// Read bandwidth in MiB/s, as seen from the given initiator location
    #[doc(alias = "HWLOC_MEMATTR_ID_READ_BANDWIDTH")]
    pub const READ_BANDWIDTH: Self = Self(4);

    /// Write bandwidth in MiB/s, as seen from the given initiator location
    #[doc(alias = "HWLOC_MEMATTR_ID_WRITE_BANDWIDTH")]
    pub const WRITE_BANDWIDTH: Self = Self(5);

    /// Latency in nanoseconds, as seen from the given initiator location
    ///
    /// This is the average latency for read and write accesses. If the platform
    /// value, provides individual read and write latencies but no explicit
    /// average hwloc computes and returns the average.
    #[doc(alias = "HWLOC_MEMATTR_ID_LATENCY")]
    pub const LATENCY: Self = Self(3);

    /// Read latency in nanoseconds, as seen from the given initiator location
    #[doc(alias = "HWLOC_MEMATTR_ID_READ_LATENCY")]
    pub const READ_LATENCY: Self = Self(6);

    /// Write latency in nanoseconds, as seen from the given initiator location
    // TODO: When adding new memory attributes, add them to attribute_flags below
    #[doc(alias = "HWLOC_MEMATTR_ID_WRITE_LATENCY")]
    pub const WRITE_LATENCY: Self = Self(7);

    /// Attribute flags corresponding to this memory attribute
    pub fn flags(self, topology: &Topology) -> MemoryAttributeFlags {
        match self {
            Self::CAPACITY => MemoryAttributeFlags::HIGHER_IS_BEST,
            Self::LOCALITY => MemoryAttributeFlags::LOWER_IS_BEST,
            Self::BANDWIDTH | Self::READ_BANDWIDTH | Self::WRITE_BANDWIDTH => {
                MemoryAttributeFlags::HIGHER_IS_BEST | MemoryAttributeFlags::NEED_INITIATOR
            }
            Self::LATENCY | Self::READ_LATENCY | Self::WRITE_LATENCY => {
                MemoryAttributeFlags::LOWER_IS_BEST | MemoryAttributeFlags::NEED_INITIATOR
            }
            // TODO: Dispatch to hwloc_memattr_get_flags once binding exists
            //       and run result through is_valid() before returning it
            _ => unimplemented!(),
        }
    }
}

/// Where to measure attributes from
#[doc(alias = "hwloc_location")]
#[doc(alias = "hwloc_location_u")]
#[doc(alias = "hwloc_location_type_e")]
#[derive(Copy, Clone, Debug)]
pub enum Location<'target> {
    /// Directly provide CPU set to find NUMA nodes with corresponding locality
    ///
    /// This is the only initiator type supported by most memory attribute
    /// queries on hwloc-defined memory attributes, though `Object` remains an
    /// option for user-defined memory attributes.
    CpuSet(&'target CpuSet),

    /// Use a topology object as an initiator
    ///
    /// Most memory attribute queries on hwloc-defined memory attributes do not
    /// support this initiator type, or translate it to a cpuset (going up the
    /// ancestor chain if necessary). But user-defined memory attributes may for
    /// instance use it to provide custom information about host memory accesses
    /// performed by GPUs.
    Object(&'target TopologyObject),
}
//
impl<'target> Location<'target> {
    /// Convert to the C representation
    pub(crate) fn into_raw(self) -> RawLocation {
        match self {
            Self::CpuSet(cpuset) => RawLocation {
                ty: RawLocationType::CPUSET,
                location: RawLocationUnion {
                    cpuset: cpuset.as_ptr(),
                },
            },
            Self::Object(object) => RawLocation {
                ty: RawLocationType::OBJECT,
                location: RawLocationUnion { object },
            },
        }
    }

    /// Convert from the C representation
    ///
    /// # Safety
    ///
    /// Only use this on RawLocation structs from hwloc or to_raw().
    pub(crate) unsafe fn from_raw(
        topology: &'target Topology,
        raw: RawLocation,
    ) -> Result<Option<Self>, UnknownLocationType> {
        match raw.ty {
            RawLocationType::CPUSET => {
                let topology_bitmap_ptr = unsafe {
                    Self::topology_reference(
                        topology,
                        &raw.location.cpuset as *const *const RawBitmap,
                    )
                    .expect("Can't be null")
                };
                let cpuset_opt = unsafe { CpuSet::borrow_from_raw(topology_bitmap_ptr) };
                Ok(cpuset_opt.map(Location::CpuSet))
            }
            RawLocationType::OBJECT => {
                let object_opt = unsafe { Self::topology_reference(topology, raw.location.object) };
                Ok(object_opt.map(Location::Object))
            }
            unknown => Err(UnknownLocationType(unknown.0)),
        }
    }

    /// Turn a pointer to topology data into a reference with suitable lifetime
    unsafe fn topology_reference<T>(
        _topology: &'target Topology,
        ptr: *const T,
    ) -> Option<&'target T> {
        (!ptr.is_null()).then(|| unsafe { &*ptr })
    }
}

/// C version of Location
#[repr(C)]
pub(crate) struct RawLocation {
    ty: RawLocationType,
    location: RawLocationUnion,
}
//
impl RawLocation {
    /// Produce an invalid state, which hwloc is assumed not to observe
    fn null() -> Self {
        Self {
            ty: RawLocationType(0),
            location: RawLocationUnion {
                cpuset: std::ptr::null(),
            },
        }
    }
}

/// Type of location
///
/// C enums can't be modeled as Rust enums because new variants would be UB
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Display, Eq, Hash, PartialEq)]
pub(crate) struct RawLocationType(c_int);
//
impl RawLocationType {
    /// Location is given as a cpuset, in the [`Location.cpuset`] union field
    pub const CPUSET: Self = Self(1);

    /// Location is given as an object, in the [`Location.object`] union field
    pub const OBJECT: Self = Self(0);
}

/// Error returned when an unknown location type is observed
#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
#[error("hwloc provided a location of unknown type {0} (time to update the Rust bindings?)")]
pub struct UnknownLocationType(c_int);

/// Actual location
#[repr(C)]
pub(crate) union RawLocationUnion {
    cpuset: *const RawBitmap,
    object: *const TopologyObject,
}

bitflags! {
    /// Flags for selecting more target NUMA nodes
    ///
    /// By default only NUMA nodes whose locality is exactly the given location
    /// are selected.
    #[repr(C)]
    #[doc(alias = "hwloc_local_numanode_flag_e")]
    pub struct LocalNUMANodeFlags: c_ulong {
        /// Select NUMA nodes whose locality is larger than the given cpuset
        ///
        /// For instance, if a single PU (or its cpuset) is given in `initiator`,
        /// select all nodes close to the package that contains this PU.
        #[doc(alias = "HWLOC_LOCAL_NUMANODE_FLAG_LARGER_LOCALITY")]
        const LARGER_LOCALITY = (1<<0);

        /// Select NUMA nodes whose locality is smaller than the given cpuset
        ///
        /// For instance, if a package (or its cpuset) is given in `initiator`,
        /// also select nodes that are attached to only a half of that package.
        #[doc(alias = "HWLOC_LOCAL_NUMANODE_FLAG_SMALLER_LOCALITY")]
        const SMALLER_LOCALITY = (1<<1);

        /// Select all NUMA nodes in the topology
        ///
        /// The initiator is ignored.
        //
        // NOTE: This flag is automatically set when users specify
        ///      [`TargetNumaNodes::All`] as the target NUMA node set.
        #[doc(hidden)]
        const ALL = (1<<2);
    }
}

/// Target NUMA nodes
pub enum TargetNumaNodes<'topology> {
    /// Nodes local to some object
    Local {
        /// Initiator which NUMA nodes should be local to
        location: Location<'topology>,

        /// Flags for enlarging the NUMA node search
        flags: LocalNUMANodeFlags,
    },

    /// All NUMA nodes in the topology
    #[doc(alias = "HWLOC_LOCAL_NUMANODE_FLAG_ALL")]
    All,
}
//
impl TargetNumaNodes<'_> {
    /// Convert to the inputs expected by `hwloc_get_local_numanode_objs`
    pub(crate) fn into_raw_params(self) -> (RawLocation, LocalNUMANodeFlags) {
        match self {
            Self::Local { location, flags } => (location.into_raw(), flags),
            Self::All => (RawLocation::null(), LocalNUMANodeFlags::ALL),
        }
    }
}

bitflags! {
    /// Memory attribute flags.
    ///
    /// These flags are given to hwloc_memattr_register() (TODO: wrap and link)
    /// and returned by `Memhwloc_memattr_get_flags() (TODO: wrap and link)
    ///
    /// At least one of `HIGHER_IS_BEST` and `LOWER_IS_BEST` must be set.
    #[repr(C)]
    #[doc(alias = "hwloc_memattr_flag_e")]
    pub struct MemoryAttributeFlags: c_ulong {
        /// The best nodes for this memory attribute are those with the higher
        /// values
        ///
        /// For instance [Bandwidth].
        ///
        /// [Bandwidth]: MemoryAttributeID::BANDWIDTH
        #[doc(alias = "HWLOC_MEMATTR_FLAG_HIGHER_FIRST")]
        const HIGHER_IS_BEST = (1<<0);

        /// The best nodes for this memory attribute are those with the lower
        /// values
        ///
        /// For instance [Latency].
        ///
        /// [Latency]: MemoryAttributeID::LATENCY
        #[doc(alias = "HWLOC_MEMATTR_FLAG_LOWER_FIRST")]
        const LOWER_IS_BEST = (1<<1);

        /// The value returned for this memory attribute depends on the given
        /// initiator
        ///
        /// For instance [Bandwidth] and [Latency], but not [Capacity].
        ///
        /// [Bandwidth]: MemoryAttributeID::BANDWIDTH
        /// [Latency]: MemoryAttributeID::LATENCY
        /// [Capacity]: MemoryAttributeID::CAPACITY
        #[doc(alias = "HWLOC_MEMATTR_FLAG_NEED_INITIATOR")]
        const NEED_INITIATOR = (1<<2);
    }
}
//
impl MemoryAttributeFlags {
    /// Truth that these flags are in a valid state (TODO: use)
    pub(crate) fn is_valid(self) -> bool {
        self.contains(Self::HIGHER_IS_BEST) ^ self.contains(Self::LOWER_IS_BEST)
    }
}
