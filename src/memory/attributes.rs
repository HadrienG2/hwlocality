//! Memory attributes

// Upstream docs:
// - https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs.html
// - https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs__manage.html

#[cfg(doc)]
use crate::support::DiscoverySupport;
use crate::{
    bitmap::{CpuSet, RawBitmap},
    ffi,
    objects::TopologyObject,
    RawTopology, Topology,
};
use bitflags::bitflags;
use derive_more::Display;
use errno::{errno, Errno};
use libc::ENOENT;
use std::ffi::{c_int, c_ulong, CStr};
use thiserror::Error;

//// Memory attribute identifier
///
/// May be either one of the predefined identifiers (see associated consts) or
/// a new identifier returned by hwloc_memattr_register() (TODO: bind and link).
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Display, Eq, Hash, PartialEq)]
pub(crate) struct MemoryAttributeID(u32);
//
impl MemoryAttributeID {
    const CAPACITY: Self = Self(0);
    const LOCALITY: Self = Self(1);
    const BANDWIDTH: Self = Self(2);
    const READ_BANDWIDTH: Self = Self(4);
    const WRITE_BANDWIDTH: Self = Self(5);
    const LATENCY: Self = Self(3);
    const READ_LATENCY: Self = Self(6);
    const WRITE_LATENCY: Self = Self(7);
    // TODO: Add new attributes to methods below and MemoryAttribute const fns

    /// For predefined attributes, flags are known at compile time
    fn static_flags(self) -> Option<MemoryAttributeFlags> {
        match self {
            Self::CAPACITY => Some(MemoryAttributeFlags::HIGHER_IS_BEST),
            Self::LOCALITY => Some(MemoryAttributeFlags::LOWER_IS_BEST),
            Self::BANDWIDTH | Self::READ_BANDWIDTH | Self::WRITE_BANDWIDTH => {
                Some(MemoryAttributeFlags::HIGHER_IS_BEST | MemoryAttributeFlags::NEED_INITIATOR)
            }
            Self::LATENCY | Self::READ_LATENCY | Self::WRITE_LATENCY => {
                Some(MemoryAttributeFlags::LOWER_IS_BEST | MemoryAttributeFlags::NEED_INITIATOR)
            }
            _ => None,
        }
    }
}

/// Generate MemoryAttribute constructors around a certain ID with minimal boilerplate
macro_rules! wrap_ids {
    (
        $(
            $(#[$attr:meta])*
            $id:ident -> $constructor:ident
        ),*
    ) => {
        $(
            $(#[$attr])*
            pub const fn $constructor(topology: &'topology Topology) -> Self {
                Self::wrap(topology, MemoryAttributeID::$id)
            }
        )*
    };
}

/// Memory attribute identifier
///
/// May be either one of the predefined identifiers (see associated const fns)
/// or a new identifier returned by hwloc_memattr_register() (TODO: bind and link).
#[derive(Copy, Clone, Debug)]
#[doc(alias = "hwloc_memattr_id_e")]
#[doc(alias = "hwloc_memattr_id_t")]
pub struct MemoryAttribute<'topology> {
    topology: &'topology Topology,
    id: MemoryAttributeID,
}
//
impl<'topology> MemoryAttribute<'topology> {
    /// Extend a MemoryAttributeID with topology access to enable method syntax
    pub(crate) const fn wrap(topology: &'topology Topology, id: MemoryAttributeID) -> Self {
        Self { id, topology }
    }

    wrap_ids!(
        /// Node capacity in bytes (see [`TopologyObject::total_memory()`])
        ///
        /// Requires [`DiscoverySupport::numa_memory()`].
        #[doc(alias = "HWLOC_MEMATTR_ID_CAPACITY")]
        CAPACITY -> capacity,

        /// Number of PUs in that locality (i.e. cpuset weight)
        ///
        /// Requires [`DiscoverySupport::pu_count()`].
        #[doc(alias = "HWLOC_MEMATTR_ID_LOCALITY")]
        LOCALITY -> locality,

        /// Average bandwidth in MiB/s, as seen from the given initiator location
        ///
        /// This is the average bandwidth for read and write accesses. If the
        /// platform provides individual read and write bandwidths but no
        /// explicit average value, hwloc computes and returns the average.
        #[doc(alias = "HWLOC_MEMATTR_ID_BANDWIDTH")]
        BANDWIDTH -> bandwidth,

        /// Read bandwidth in MiB/s, as seen from the given initiator location
        #[doc(alias = "HWLOC_MEMATTR_ID_READ_BANDWIDTH")]
        READ_BANDWIDTH -> read_bandwidth,

        /// Write bandwidth in MiB/s, as seen from the given initiator location
        #[doc(alias = "HWLOC_MEMATTR_ID_WRITE_BANDWIDTH")]
        WRITE_BANDWIDTH -> write_bandwidth,

        /// Latency in nanoseconds, as seen from the given initiator location
        ///
        /// This is the average latency for read and write accesses. If the
        /// platform value provides individual read and write latencies but no
        /// explicit average, hwloc computes and returns the average.
        #[doc(alias = "HWLOC_MEMATTR_ID_LATENCY")]
        LATENCY -> latency,

        /// Read latency in nanoseconds, as seen from the given initiator location
        #[doc(alias = "HWLOC_MEMATTR_ID_READ_LATENCY")]
        READ_LATENCY -> read_latency,

        /// Write latency in nanoseconds, as seen from the given initiator location
        #[doc(alias = "HWLOC_MEMATTR_ID_WRITE_LATENCY")]
        WRITE_LATENCY -> write_latency
    );

    /// Name of this memory attribute, if any
    #[doc(alias = "hwloc_memattr_get_name")]
    pub fn name(&self) -> Option<&CStr> {
        let mut name = std::ptr::null();
        let result =
            unsafe { ffi::hwloc_memattr_get_name(self.topology.as_ptr(), self.id, &mut name) };
        assert!(result >= 0, "Unexpected result from hwloc_memattr_get_name");
        (!name.is_null()).then(|| unsafe { CStr::from_ptr(name) })
    }

    /// Memory attribute flags
    #[doc(alias = "hwloc_memattr_get_flags")]
    pub fn flags(&self) -> MemoryAttributeFlags {
        let flags = if let Some(flags) = self.id.static_flags() {
            flags
        } else {
            self.dynamic_flags()
        };
        debug_assert!(flags.is_valid(), "Flags should be valid");
        flags
    }

    /// Dynamically query this memory attribute's flags
    fn dynamic_flags(&self) -> MemoryAttributeFlags {
        let mut flags = 0;
        let result =
            unsafe { ffi::hwloc_memattr_get_flags(self.topology.as_ptr(), self.id, &mut flags) };
        assert!(
            result >= 0,
            "Unexpected result from hwloc_memattr_get_flags"
        );
        MemoryAttributeFlags::from_bits_truncate(flags)
    }

    /// Value of this attribute for a specific initiator and target NUMA node
    ///
    /// `initiator` should be specified if and only if this attribute has the
    /// flag [`MemoryAttributeFlags::NEED_INITIATOR`].
    ///
    /// The initiator should be a CpuSet when refering to accesses performed by
    /// CPU cores. `Location::Object` is currently unused internally by hwloc,
    /// but user-defined memory attributes may for instance use it to provide
    /// custom information about host memory accesses performed by GPUs.
    ///
    /// # Errors
    ///
    /// - [BadInitiator] if the `initiator` parameter was not set correctly.
    ///
    /// [BadInitiator]: MemoryAttributeQueryError::BadInitiator
    #[doc(alias = "hwloc_memattr_get_value")]
    pub fn value<'result>(
        &'result self,
        initiator: Option<Location<'result>>,
        target_node: &TopologyObject,
    ) -> Result<u64, MemoryAttributeQueryError<'result>> {
        self.query_with_initiator(
            initiator,
            |topology, attribute, initiator, flags, value| unsafe {
                ffi::hwloc_memattr_get_value(
                    topology,
                    attribute,
                    target_node,
                    initiator,
                    flags,
                    value,
                )
            },
        )
    }

    /// Best target node and associated attribute value for a given initiator
    ///
    /// See [`MemoryAttribute::value()`] to know more about `initiator`.
    ///
    /// If multiple targets have the same attribute values, only one is returned
    /// (and there is no way to clarify how that one is chosen). Applications
    /// that want to detect targets with identical/similar values, or that want
    /// to look at values for multiple attributes, should rather get all values
    /// using [`MemoryAttribute::value()`] and manually select the target they
    /// consider the best.
    #[doc(alias = "hwloc_memattr_get_best_target")]
    pub fn best_target<'result>(
        &'result self,
        initiator: Option<Location<'result>>,
    ) -> Result<(&'topology TopologyObject, u64), MemoryAttributeQueryError<'result>> {
        let mut best_target = std::ptr::null();
        self.query_with_initiator(
            initiator,
            |topology, attribute, initiator, flags, value| unsafe {
                ffi::hwloc_memattr_get_best_target(
                    topology,
                    attribute,
                    initiator,
                    flags,
                    &mut best_target,
                    value,
                )
            },
        )
        .map(|value| {
            assert!(
                !best_target.is_null(),
                "Got null target pointer from hwloc_memattr_get_best_target"
            );
            (unsafe { &*best_target }, value)
        })
    }

    /// Best initiator and associated attribute value for a given target node
    ///
    /// If multiple initiators have the same attribute values, only one is
    /// returned (and there is no way to clarify how that one is chosen).
    /// Applications that want to detect initiators with identical/similar
    /// values, or that want to look at values for multiple attributes, should
    /// rather get all values using [`MemoryAttribute::value()`] and manually
    /// select the initiator they consider the best.
    #[doc(alias = "hwloc_memattr_get_best_initiator")]
    pub fn best_initiator(
        &self,
        target: &TopologyObject,
    ) -> Result<(Location<'topology>, u64), MemoryAttributeQueryError> {
        let mut best_initiator = RawLocation::null();
        self.query(|topology, attribute, flags, value| unsafe {
            ffi::hwloc_memattr_get_best_initiator(
                topology,
                attribute,
                target,
                flags,
                &mut best_initiator,
                value,
            )
        })
        .map(|value| {
            let location = unsafe { Location::from_raw(self.topology, best_initiator) }
                .expect("Failed to decode location from hwloc")
                .expect("Got null location pointer from hwloc");
            (location, value)
        })
    }

    /// Perform a memory attribute query that has an initiator
    fn query_with_initiator<'result>(
        &'result self,
        initiator: Option<Location<'result>>,
        query: impl FnOnce(
            *const RawTopology,
            MemoryAttributeID,
            *const RawLocation,
            c_ulong,
            *mut u64,
        ) -> i32,
    ) -> Result<u64, MemoryAttributeQueryError<'result>> {
        if self.flags().contains(MemoryAttributeFlags::NEED_INITIATOR) ^ initiator.is_some() {
            return Err(MemoryAttributeQueryError::BadInitiator(initiator));
        }
        let initiator = initiator
            .map(Location::into_raw)
            .unwrap_or_else(RawLocation::null);
        self.query(|topology, attribute, flags, value| {
            query(topology, attribute, &initiator, flags, value)
        })
    }

    /// Perform a memory attribute query that doesn't have an initiator (or
    /// whose initiator is taken care of higher up the abstraction stack)
    fn query(
        &self,
        query: impl FnOnce(*const RawTopology, MemoryAttributeID, c_ulong, *mut u64) -> i32,
    ) -> Result<u64, MemoryAttributeQueryError> {
        // Call hwloc
        let mut value = 0;
        let result = query(self.topology.as_ptr(), self.id, 0, &mut value);

        // Process and extract result
        match result {
            0 => Ok(value),
            -1 => {
                let errno = errno();
                match errno.0 {
                    ENOENT => Err(MemoryAttributeQueryError::NoMatch),
                    _ => Err(MemoryAttributeQueryError::UnexpectedErrno(errno)),
                }
            }
            other => Err(MemoryAttributeQueryError::UnexpectedResult(other, errno())),
        }
    }
}

/// Error while querying a memory attribute
#[derive(Copy, Clone, Debug, Error)]
pub enum MemoryAttributeQueryError<'params> {
    /// Incorrect `initiator` parameter
    ///
    /// Either an initiator had to be specified and was not specified, or the
    /// requested attribute has no notion of initiator (e.g. Capacity) but an
    /// initiator was specified nonetheless.
    #[error("incorrect initiator: {0:?}")]
    BadInitiator(Option<Location<'params>>),

    /// Query returned no matching entity (value, object...)
    #[error("no entity matches this query")]
    NoMatch,

    /// Unexpected errno value
    #[error("unexpected errno value {0}")]
    UnexpectedErrno(Errno),

    /// Unexpected binding function result
    #[error("unexpected binding function result {0} with errno {1}")]
    UnexpectedResult(i32, Errno),
}

/// Where to measure attributes from
#[doc(alias = "hwloc_location")]
#[doc(alias = "hwloc_location_u")]
#[doc(alias = "hwloc_location_type_e")]
#[derive(Copy, Clone, Debug, Display)]
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
    fn into_raw(self) -> RawLocation {
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
    unsafe fn from_raw(
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

/// Error returned when an unknown location type is observed
#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
#[error("hwloc provided a location of unknown type {0}")]
struct UnknownLocationType(c_int);

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
        ///
        /// By default, the search only returns NUMA nodes whose locality is
        /// exactly the given `location`. More nodes can be selected using
        /// `flags`.
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
    /// and returned by [`MemoryAttribute::flags()`].
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
