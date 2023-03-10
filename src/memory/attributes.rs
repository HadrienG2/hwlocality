//! Memory attributes

// Upstream docs:
// - https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs.html
// - https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs__manage.html

use crate::{
    bitmaps::{CpuSet, RawBitmap},
    errors::{self, RawIntError},
    ffi,
    objects::TopologyObject,
    RawTopology, Topology,
};
#[cfg(doc)]
use crate::{editor::TopologyEditor, support::DiscoverySupport};
use bitflags::bitflags;
use derive_more::Display;
use libc::ENOENT;
use std::{
    ffi::{c_int, c_uint, c_ulong, CStr},
    ptr,
};
use thiserror::Error;

//// Memory attribute identifier
///
/// May be a predefined identifier (see associated consts) or come from
/// [`TopologyEditor::register_memory_attribute()`].
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Default, Display, Eq, Hash, PartialEq)]
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
    // TODO: Add new attributes to methods below and MemoryAttribute constructors

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
/// May be either one of the predefined attributes (see associated const fns)
/// or a new attribute created using
/// [`TopologyEditor::register_memory_attribute()`].
#[derive(Copy, Clone, Debug)]
#[doc(alias = "hwloc_memattr_id_e")]
#[doc(alias = "hwloc_memattr_id_t")]
pub struct MemoryAttribute<'topology> {
    topology: &'topology Topology,
    id: MemoryAttributeID,
}
//
/// # Predefined memory attributes
impl<'topology> MemoryAttribute<'topology> {
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
}
//
/// # Memory attribute API
impl<'topology> MemoryAttribute<'topology> {
    /// Extend a MemoryAttributeID with topology access to enable method syntax
    pub(crate) const fn wrap(topology: &'topology Topology, id: MemoryAttributeID) -> Self {
        Self { id, topology }
    }

    /// Name of this memory attribute
    #[doc(alias = "hwloc_memattr_get_name")]
    pub fn name(&self) -> &CStr {
        let mut name = ptr::null();
        let result =
            unsafe { ffi::hwloc_memattr_get_name(self.topology.as_ptr(), self.id, &mut name) };
        assert!(result >= 0, "Unexpected result from hwloc_memattr_get_name");
        assert!(
            !name.is_null(),
            "Memory attributes should have non-NULL names"
        );
        unsafe { CStr::from_ptr(name) }
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
    /// CPU cores. [`MemoryAttributeLocation::Object`] is currently unused
    /// internally by hwloc, but user-defined memory attributes may for instance
    /// use it to provide custom information about host memory accesses
    /// performed by GPUs.
    ///
    /// # Errors
    ///
    /// - [BadInitiator] if the `initiator` parameter was not set correctly
    ///
    /// [BadInitiator]: MemoryAttributeQueryError::BadInitiator
    #[doc(alias = "hwloc_memattr_get_value")]
    pub fn value(
        &self,
        initiator: Option<MemoryAttributeLocation>,
        target_node: &TopologyObject,
    ) -> Result<Option<u64>, MemoryAttributeQueryError> {
        let initiator = self.checked_initiator(initiator, false)?;
        self.value_query(
            "hwloc_memattr_get_value",
            |topology, attribute, flags, value| unsafe {
                ffi::hwloc_memattr_get_value(
                    topology,
                    attribute,
                    target_node,
                    &initiator,
                    flags,
                    value,
                )
            },
        )
    }

    /// Best target node and associated attribute value for a given initiator
    ///
    /// The notes on initiator semantics in [`MemoryAttribute::value()`] also
    /// apply to this function.
    ///
    /// If multiple targets have the same attribute values, only one is returned
    /// (and there is no way to clarify how that one is chosen). Applications
    /// that want to detect targets with identical/similar values, or that want
    /// to look at values for multiple attributes, should rather get all values
    /// using [`MemoryAttribute::value()`] and manually select the target they
    /// consider the best.
    ///
    /// # Errors
    ///
    /// - [BadInitiator] if the `initiator` parameter was not set correctly
    /// - [NoMatch] if this attribute has no specified value for this initiator
    ///
    /// [BadInitiator]: MemoryAttributeQueryError::BadInitiator
    /// [NoMatch]: MemoryAttributeQueryError::NoMatch
    #[doc(alias = "hwloc_memattr_get_best_target")]
    pub fn best_target(
        &self,
        initiator: Option<MemoryAttributeLocation>,
    ) -> Result<Option<(&'topology TopologyObject, u64)>, MemoryAttributeQueryError> {
        let initiator = self.checked_initiator(initiator, false)?;
        let mut best_target = ptr::null();
        self.value_query(
            "hwloc_memattr_get_best_target",
            |topology, attribute, flags, value| unsafe {
                ffi::hwloc_memattr_get_best_target(
                    topology,
                    attribute,
                    &initiator,
                    flags,
                    &mut best_target,
                    value,
                )
            },
        )
        .map(|opt| opt.map(|value| (unsafe { self.encapsulate_target_node(best_target) }, value)))
    }

    /// Best initiator and associated attribute value for a given target node
    ///
    /// If multiple initiators have the same attribute values, only one is
    /// returned (and there is no way to clarify how that one is chosen).
    /// Applications that want to detect initiators with identical/similar
    /// values, or that want to look at values for multiple attributes, should
    /// rather get all values using [`MemoryAttribute::value()`] and manually
    /// select the initiator they consider the best.
    ///
    /// # Errors
    ///
    /// - [NoInitiator] if this attribute cannot have an initiator
    /// - [NoMatch] if this attribute has no specified value for this target node
    ///
    /// [NoInitiator]: MemoryAttributeQueryError::NoInitiator
    /// [NoMatch]: MemoryAttributeQueryError::NoMatch
    #[doc(alias = "hwloc_memattr_get_best_initiator")]
    pub fn best_initiator(
        &self,
        target: &TopologyObject,
    ) -> Result<Option<(MemoryAttributeLocation<'topology>, u64)>, MemoryAttributeQueryError> {
        // Validate the query
        if !self.flags().contains(MemoryAttributeFlags::NEED_INITIATOR) {
            return Err(MemoryAttributeQueryError::NoInitiator);
        }

        // Run it
        let mut best_initiator = RawLocation::null();
        self.value_query(
            "hwloc_memattr_get_best_initiator",
            |topology, attribute, flags, value| unsafe {
                ffi::hwloc_memattr_get_best_initiator(
                    topology,
                    attribute,
                    target,
                    flags,
                    &mut best_initiator,
                    value,
                )
            },
        )
        .map(|opt| opt.map(|value| (unsafe { self.encapsulate_initiator(best_initiator) }, value)))
    }

    /// Return the target NUMA nodes that have some values for a given
    /// attribute, along with the associated values.
    ///
    /// An `initiator` may only be specified if this attribute has the flag
    /// [`MemoryAttributeFlags::NEED_INITIATOR`]. In that case, it acts as a
    /// filter to only report targets that have a value for this initiator.
    ///
    /// The initiator should be a CpuSet when refering to accesses performed by
    /// CPU cores. [`MemoryAttributeLocation::Object`] is currently unused
    /// internally by hwloc, but user-defined memory attributes may for instance
    /// use it to provide custom information about host memory accesses
    /// performed by GPUs.
    ///
    /// This function is meant for tools and debugging (listing internal
    /// information) rather than for application queries. Applications should
    /// rather select useful NUMA nodes with [`Topology::local_numa_nodes()`]
    /// and then look at their attribute values.
    ///
    /// # Errors
    ///
    /// - [BadInitiator] if the `initiator` parameter was not set correctly
    ///
    /// [BadInitiator]: MemoryAttributeQueryError::BadInitiator
    #[doc(alias = "hwloc_memattr_get_targets")]
    pub fn targets(
        &self,
        initiator: Option<MemoryAttributeLocation>,
    ) -> Result<(Vec<&'topology TopologyObject>, Vec<u64>), MemoryAttributeQueryError> {
        // Check parameters and query target list + associated values
        let initiator = self.checked_initiator(initiator, true)?;
        let (targets, values) = self.array_query(
            "hwloc_memattr_get_targets",
            ptr::null(),
            |topology, attribute, flags, nr, targets, values| unsafe {
                ffi::hwloc_memattr_get_targets(
                    topology, attribute, &initiator, flags, nr, targets, values,
                )
            },
        )?;

        // Convert target list into a safe high-level form
        let targets = targets
            .into_iter()
            .map(|node_ptr| unsafe { self.encapsulate_target_node(node_ptr) })
            .collect();
        Ok((targets, values))
    }

    /// Return the initiators that have values for a given attribute for a
    /// specific target NUMA node, along with the associated values
    ///
    /// This function is meant for tools and debugging (listing internal
    /// information) rather than for application queries. Applications should
    /// rather select useful NUMA nodes with [`Topology::local_numa_nodes()`]
    /// and then look at their attribute values.
    ///
    /// # Errors
    ///
    /// - [NoInitiator] if this attribute cannot have an initiator
    ///
    /// [NoInitiator]: MemoryAttributeQueryError::NoInitiator
    #[doc(alias = "hwloc_memattr_get_initiators")]
    pub fn initiators(
        &self,
        target_node: &TopologyObject,
    ) -> Result<(Vec<MemoryAttributeLocation>, Vec<u64>), MemoryAttributeQueryError> {
        // Validate the query
        if !self.flags().contains(MemoryAttributeFlags::NEED_INITIATOR) {
            return Err(MemoryAttributeQueryError::NoInitiator);
        }

        // Run it
        let (initiators, values) = self.array_query(
            "hwloc_memattr_get_initiators",
            RawLocation::null(),
            |topology, attribute, flags, nr, initiators, values| unsafe {
                ffi::hwloc_memattr_get_initiators(
                    topology,
                    attribute,
                    target_node,
                    flags,
                    nr,
                    initiators,
                    values,
                )
            },
        )?;

        // Convert initiators into a safe high-level form
        let initiators = initiators
            .into_iter()
            .map(|initiator| unsafe { self.encapsulate_initiator(initiator) })
            .collect();
        Ok((initiators, values))
    }

    /// Perform a get_targets style memory attribute query
    fn array_query<Endpoint: Copy>(
        &self,
        api: &'static str,
        placeholder: Endpoint,
        mut query: impl FnMut(
            *const RawTopology,
            MemoryAttributeID,
            c_ulong,
            *mut c_uint,
            *mut Endpoint,
            *mut u64,
        ) -> c_int,
    ) -> Result<(Vec<Endpoint>, Vec<u64>), MemoryAttributeQueryError> {
        // Prepare to call hwloc
        let mut nr = 0;
        let mut call_ffi = |nr_mut, endpoint_out, values_out| {
            errors::call_hwloc_int(api, || {
                query(
                    self.topology.as_ptr(),
                    self.id,
                    0,
                    nr_mut,
                    endpoint_out,
                    values_out,
                )
            })
        };

        // Query node count
        let result = call_ffi(&mut nr, ptr::null_mut(), ptr::null_mut())?;
        let len = usize::try_from(nr).expect("Impossible array size from hwloc");

        // Allocate storage and fill arrays
        let mut endpoints = vec![placeholder; len];
        let mut values = vec![0; len];
        let old_nr = nr;
        let result = call_ffi(&mut nr, endpoints.as_mut_ptr(), values.as_mut_ptr())?;
        assert_eq!(old_nr, nr, "Inconsistent node count from hwloc");
        Ok((endpoints, values))
    }

    /// Perform a get_value style memory attribute query
    fn value_query(
        &self,
        api: &'static str,
        query: impl FnOnce(*const RawTopology, MemoryAttributeID, c_ulong, *mut u64) -> c_int,
    ) -> Result<Option<u64>, MemoryAttributeQueryError> {
        let mut value = u64::MAX;
        match errors::call_hwloc_int(api, || {
            query(self.topology.as_ptr(), self.id, 0, &mut value)
        }) {
            Ok(_positive) => Ok(Some(value)),
            Err(
                raw_err @ RawIntError::Errno {
                    errno: Some(errno), ..
                },
            ) => match errno.0 {
                ENOENT => Ok(None),
                _ => Err(MemoryAttributeQueryError::Unexpected(raw_err)),
            },
            Err(raw_err) => Err(MemoryAttributeQueryError::Unexpected(raw_err)),
        }
    }

    /// Encapsulate a *const TopologyObject to a target NUMA node from hwloc
    unsafe fn encapsulate_target_node(
        &self,
        node_ptr: *const TopologyObject,
    ) -> &'topology TopologyObject {
        assert!(!node_ptr.is_null(), "Got null target pointer from hwloc");
        unsafe { &*node_ptr }
    }

    /// Encapsulate an initiator location from hwloc
    unsafe fn encapsulate_initiator(
        &self,
        initiator: RawLocation,
    ) -> MemoryAttributeLocation<'topology> {
        unsafe { MemoryAttributeLocation::from_raw(self.topology, initiator) }
            .expect("Failed to decode location from hwloc")
            .expect("Got null location pointer from hwloc")
    }

    /// Check the initiator argument to some query
    ///
    /// If `is_optional` is true, it is okay not to provide an initiator even
    /// if the memory attribute has flag [`MemoryAttributeFlags::NEED_INITIATOR`].
    fn checked_initiator(
        &self,
        initiator: Option<MemoryAttributeLocation>,
        is_optional: bool,
    ) -> Result<RawLocation, MemoryAttributeQueryError> {
        let is_good = if is_optional {
            self.flags().contains(MemoryAttributeFlags::NEED_INITIATOR) || initiator.is_none()
        } else {
            !(self.flags().contains(MemoryAttributeFlags::NEED_INITIATOR) ^ initiator.is_some())
        };
        is_good
            .then(|| {
                initiator
                    .map(MemoryAttributeLocation::into_raw)
                    .unwrap_or_else(RawLocation::null)
            })
            .ok_or(MemoryAttributeQueryError::BadInitiator)
    }
}

/// Error while querying a memory attribute
#[derive(Copy, Clone, Debug, Error)]
pub enum MemoryAttributeQueryError {
    /// Incorrect `initiator` parameter
    ///
    /// Either an initiator had to be specified and was not specified, or the
    /// requested attribute has no notion of initiator (e.g. Capacity) but an
    /// initiator was specified nonetheless.
    #[error("specified initiator is incorrect for this memory attribute")]
    BadInitiator,

    /// Memory attribute has no initiator
    ///
    /// This error occurs when querying for initiators on attributes that do not
    /// have initiators (e.g. Capacity).
    #[error("requested a memory attribute's initiator, but it has none")]
    NoInitiator,

    /// Unexpected hwloc error
    ///
    /// The hwloc documentation isn't exhaustive about what errors can occur in
    /// general, and new error cases could potentially be added by new hwloc
    /// releases. If we cannot provide a high-level error description, we will
    /// fall back to reporting the raw error from the hwloc API.
    #[error(transparent)]
    Unexpected(#[from] RawIntError),
}

/// Where to measure attributes from
#[doc(alias = "hwloc_location")]
#[doc(alias = "hwloc_location_u")]
#[doc(alias = "hwloc_location_type_e")]
#[derive(Copy, Clone, Debug, Display)]
pub enum MemoryAttributeLocation<'target> {
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
impl<'target> MemoryAttributeLocation<'target> {
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
                Ok(cpuset_opt.map(MemoryAttributeLocation::CpuSet))
            }
            RawLocationType::OBJECT => {
                let object_opt = unsafe { Self::topology_reference(topology, raw.location.object) };
                Ok(object_opt.map(MemoryAttributeLocation::Object))
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
#[derive(Copy, Clone)]
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
                cpuset: ptr::null(),
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
#[derive(Copy, Clone)]
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
        //       [`TargetNumaNodes::All`] as the target NUMA node set.
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
        location: MemoryAttributeLocation<'topology>,

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
    /// These flags are given to [`TopologyEditor::register_memory_attribute()`]
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
    /// Truth that these flags are in a valid state
    pub(crate) fn is_valid(self) -> bool {
        self.contains(Self::HIGHER_IS_BEST) ^ self.contains(Self::LOWER_IS_BEST)
    }
}
