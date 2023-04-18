//! Memory attributes

// Upstream docs:
// - https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs.html
// - https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs__manage.html

#[cfg(doc)]
use crate::topology::support::DiscoverySupport;
use crate::{
    bitmaps::RawBitmap,
    cpu::sets::CpuSet,
    errors::{self, HybridError, NulError, RawHwlocError},
    ffi::{self, LibcString},
    objects::TopologyObject,
    topology::{editor::TopologyEditor, RawTopology, Topology},
};
use bitflags::bitflags;
use derive_more::Display;
use errno::Errno;
use libc::ENOENT;
use std::{
    ffi::{c_int, c_uint, c_ulong, CStr},
    mem::MaybeUninit,
    ptr::{self, NonNull},
};
use thiserror::Error;

/// # Comparing memory node attributes for finding where to allocate on
///
/// Platforms with heterogeneous memory require ways to decide whether a buffer
/// should be allocated on "fast" memory (such as HBM), "normal" memory (DDR) or
/// even "slow" but large-capacity memory (non-volatile memory). These memory
/// nodes are called "Targets" while the CPU accessing them is called the
/// "Initiator". Access performance depends on their locality (NUMA platforms)
/// as well as the intrinsic performance of the targets (heterogeneous platforms).
///
/// The following attributes describe the performance of memory accesses from an
/// Initiator to a memory Target, for instance their latency or bandwidth.
/// Initiators performing these memory accesses are usually some PUs or Cores
/// (described as a CPU set). Hence a Core may choose where to allocate a memory
/// buffer by comparing the attributes of different target memory nodes nearby.
///
/// There are also some attributes that are system-wide. Their value does not
/// depend on a specific initiator performing an access. The memory node
/// Capacity is an example of such attribute without initiator.
///
/// One way to use this API is to start with a cpuset describing the Cores where
/// a program is bound. The best target NUMA node for allocating memory in this
/// program on these Cores may be obtained by passing this cpuset as an
/// initiator to [`MemoryAttribute::best_target()`] with the relevant
/// memory attribute. For instance, if the code is latency limited, use the
/// Latency attribute.
///
/// A more flexible approach consists in getting the list of local NUMA nodes by
/// passing this cpuset to [`Topology::local_numa_nodes()`]. Attribute values
/// for these nodes, if any, may then be obtained with
/// [`MemoryAttribute::value()`] and manually compared with the desired criteria.
///
/// The API also supports specific objects as initiator, but it is currently not
/// used internally by hwloc. Users may for instance use it to provide custom
/// performance values for host memory accesses performed by GPUs.
/// The interface actually also accepts targets that are not NUMA nodes.
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs.html
impl Topology {
    /// Return the identifier of the memory attribute with the given name
    ///
    /// Note that a number of predefined memory attributes have predefined
    /// identifiers and need not be queried by name at runtime, see the
    /// different constructors of [`MemoryAttribute`] for more information.
    ///
    /// # Errors
    ///
    /// - [`NulError`] if `name` contains NUL chars.
    #[doc(alias = "hwloc_memattr_get_by_name")]
    pub fn memory_attribute_named(
        &self,
        name: &str,
    ) -> Result<MemoryAttribute, HybridError<NulError>> {
        let name = LibcString::new(name)?;
        let mut id = MaybeUninit::uninit();
        errors::call_hwloc_int_normal("hwloc_memattr_get_by_name", || unsafe {
            ffi::hwloc_memattr_get_by_name(self.as_ptr(), name.borrow(), id.as_mut_ptr())
        })
        .map_err(HybridError::Hwloc)?;
        Ok(MemoryAttribute::wrap(self, unsafe { id.assume_init() }))
    }

    /// Return an array of local NUMA nodes
    ///
    /// If `target` is given as a `TopologyObject`, its CPU set is used to
    /// find NUMA nodes with the corresponding locality. If the object does not
    /// have a CPU set (e.g. I/O object), the CPU parent (where the I/O object
    /// is attached) is used.
    ///
    /// Some of these NUMA nodes may not have any memory attribute values and
    /// hence not be reported as actual targets in other functions.
    ///
    /// When an object CPU set is given as locality, for instance a Package, and
    /// when `flags` contains both [`LocalNUMANodeFlags::LARGER_LOCALITY`] and
    /// [`LocalNUMANodeFlags::SMALLER_LOCALITY`], the returned array corresponds
    /// to the nodeset of that object.
    #[doc(alias = "hwloc_get_local_numanode_objs")]
    pub fn local_numa_nodes(
        &self,
        target: TargetNumaNodes,
    ) -> Result<Vec<&TopologyObject>, RawHwlocError> {
        // Prepare to call hwloc
        let (location, flags) = target.into_raw_params();
        let mut nr = 0;
        let call_ffi = |nr_mut, out_ptr| {
            errors::call_hwloc_int_normal("hwloc_get_local_numanode_objs", || unsafe {
                ffi::hwloc_get_local_numanode_objs(
                    self.as_ptr(),
                    &location,
                    nr_mut,
                    out_ptr,
                    flags.bits(),
                )
            })
        };

        // Query node count
        call_ffi(&mut nr, ptr::null_mut())?;
        let len = usize::try_from(nr).expect("Impossible node count from hwloc");

        // Allocate storage and fill node list
        let mut out = vec![ptr::null(); len];
        let old_nr = nr;
        call_ffi(&mut nr, out.as_mut_ptr())?;
        assert_eq!(old_nr, nr, "Inconsistent node count from hwloc");

        // Translate node pointers into node references
        Ok(out
            .into_iter()
            .map(|ptr| {
                assert!(!ptr.is_null(), "Invalid NUMA node pointer from hwloc");
                unsafe { &*ptr }
            })
            .collect())
    }
}

/// # Managing memory attributes
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs__manage.html
impl<'topology> TopologyEditor<'topology> {
    /// Register a new memory attribute
    ///
    /// # Panics
    ///
    /// - `name` contains NUL chars
    #[doc(alias = "hwloc_memattr_register")]
    pub fn register_memory_attribute<'name>(
        &mut self,
        name: &'name str,
        flags: MemoryAttributeFlags,
    ) -> Result<MemoryAttributeBuilder<'_, 'topology>, HybridError<MemoryAttributeRegisterError>>
    {
        if !flags.is_valid() {
            return Err(MemoryAttributeRegisterError::BadFlags(flags).into());
        }
        let name = match LibcString::new(name) {
            Ok(name) => name,
            Err(NulError) => return Err(MemoryAttributeRegisterError::NameContainsNul.into()),
        };
        let mut id = MemoryAttributeID::default();
        errors::call_hwloc_int_normal("hwloc_memattr_register", || unsafe {
            ffi::hwloc_memattr_register(
                self.topology_mut_ptr(),
                name.borrow(),
                flags.bits(),
                &mut id,
            )
        })
        .map_err(HybridError::Hwloc)?;
        Ok(MemoryAttributeBuilder {
            editor: self,
            flags,
            id,
        })
    }
}

/// Error returned when trying to create an memory attribute
#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
pub enum MemoryAttributeRegisterError {
    /// Specified flags are not correct
    ///
    /// You must specify exactly one of [`MemoryAttributeFlags::HIGHER_IS_BEST`]
    /// and [`MemoryAttributeFlags::LOWER_IS_BEST`].
    #[error("flags {0:?} do not contain exactly one of the _IS_BEST flags")]
    BadFlags(MemoryAttributeFlags),

    /// Provided `name` contains NUL chars
    #[error("provided name contains NUL chars")]
    NameContainsNul,

    /// A memory attribute with this name already exists
    #[error("a memory attribute with this name already exists")]
    AlreadyExists,
}

/// Mechanism to configure a memory attribute
pub struct MemoryAttributeBuilder<'editor, 'topology> {
    editor: &'editor mut TopologyEditor<'topology>,
    flags: MemoryAttributeFlags,
    id: MemoryAttributeID,
}
//
impl MemoryAttributeBuilder<'_, '_> {
    /// Set attribute values for (initiator, target node) pairs
    ///
    /// Initiators should be provided if and only if this memory attribute has
    /// an initiator (flag [`MemoryAttributeFlags::NEED_INITIATOR`] was set at
    /// registration time. In that case, there should be as many initiators as
    /// there are targets and attribute values.
    ///
    /// # Errors
    ///
    /// - [`InitiatorsError`] if initiators are specified for attributes that
    ///   don't have them, are not specified for attributes that have them, or
    ///   if there are more or less initiators than (target, value) pairs.
    #[doc(alias = "hwloc_memattr_set_value")]
    pub fn set_values(
        &mut self,
        find_values: impl FnOnce(
            &Topology,
        ) -> (
            Option<Vec<MemoryAttributeLocation>>,
            Vec<(&TopologyObject, u64)>,
        ),
    ) -> Result<(), HybridError<InitiatorsError>> {
        // Run user callback, validate results for correctness
        let (initiators, targets_and_values) = find_values(self.editor.topology());
        if !(self.flags.contains(MemoryAttributeFlags::NEED_INITIATOR) ^ initiators.is_some()) {
            return Err(InitiatorsError.into());
        }
        let size_ok = match (&initiators, &targets_and_values) {
            (Some(initiators), targets_and_values)
                if initiators.len() == targets_and_values.len() =>
            {
                true
            }
            (None, _) => true,
            _ => false,
        };
        if !size_ok {
            return Err(InitiatorsError.into());
        }

        // Post-process results to fit hwloc and borrow checker expectations
        let initiators = initiators.map(|vec| {
            vec.into_iter()
                .map(MemoryAttributeLocation::into_raw)
                .collect::<Vec<_>>()
        });
        let initiator_ptrs = initiators
            .iter()
            .flatten()
            .map(|initiator_ref| {
                let initiator_ptr: *const RawLocation = initiator_ref;
                initiator_ptr
            })
            .chain(std::iter::repeat_with(ptr::null));
        let target_ptrs_and_values = targets_and_values
            .into_iter()
            .map(|(target_ref, value)| {
                let target_ptr: *const TopologyObject = target_ref;
                (target_ptr, value)
            })
            .collect::<Vec<_>>();

        // Set memory attribute values
        for (initiator_ptr, (target_ptr, value)) in
            initiator_ptrs.zip(target_ptrs_and_values.into_iter())
        {
            errors::call_hwloc_int_normal("hwloc_memattr_set_value", || unsafe {
                ffi::hwloc_memattr_set_value(
                    self.editor.topology_mut_ptr(),
                    self.id,
                    target_ptr,
                    initiator_ptr,
                    0,
                    value,
                )
            })
            .map_err(HybridError::Hwloc)?;
        }
        Ok(())
    }
}

/// Error returned by [`MemoryAttributeBuilder::set_values`] when the
/// `find_values` callback returns an incorrect set of initiators.
///
/// Either an initiator had to be specified and was not specified, or the
/// requested attribute has no notion of initiator (e.g. Capacity) but an
/// initiator was specified nonetheless.
///
/// This error is also emitted if the array of initiators is not sized like
/// the main (target, value) array.
#[derive(Copy, Clone, Debug, Default, Eq, Error, PartialEq)]
#[error("find_values returned an invalid initiator set")]
pub struct InitiatorsError;

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
    #[cfg(feature = "hwloc-2_8_0")]
    const READ_BANDWIDTH: Self = Self(4);
    #[cfg(feature = "hwloc-2_8_0")]
    const WRITE_BANDWIDTH: Self = Self(5);
    const LATENCY: Self = Self(3);
    #[cfg(feature = "hwloc-2_8_0")]
    const READ_LATENCY: Self = Self(6);
    #[cfg(feature = "hwloc-2_8_0")]
    const WRITE_LATENCY: Self = Self(7);
    // NOTE: Add new attributes to methods below and MemoryAttribute constructors

    /// For predefined attributes, flags are known at compile time
    fn static_flags(self) -> Option<MemoryAttributeFlags> {
        let bandwidth_flags =
            Some(MemoryAttributeFlags::HIGHER_IS_BEST | MemoryAttributeFlags::NEED_INITIATOR);
        let latency_flags =
            Some(MemoryAttributeFlags::LOWER_IS_BEST | MemoryAttributeFlags::NEED_INITIATOR);
        match self {
            Self::CAPACITY => Some(MemoryAttributeFlags::HIGHER_IS_BEST),
            Self::LOCALITY => Some(MemoryAttributeFlags::LOWER_IS_BEST),
            #[cfg(feature = "hwloc-2_8_0")]
            Self::BANDWIDTH | Self::READ_BANDWIDTH | Self::WRITE_BANDWIDTH => bandwidth_flags,
            #[cfg(not(feature = "hwloc-2_8_0"))]
            Self::BANDWIDTH => bandwidth_flags,
            #[cfg(feature = "hwloc-2_8_0")]
            Self::LATENCY | Self::READ_LATENCY | Self::WRITE_LATENCY => latency_flags,
            #[cfg(not(feature = "hwloc-2_8_0"))]
            Self::LATENCY => latency_flags,
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
        #[cfg(feature = "hwloc-2_8_0")]
        #[doc(alias = "HWLOC_MEMATTR_ID_READ_BANDWIDTH")]
        READ_BANDWIDTH -> read_bandwidth,

        /// Write bandwidth in MiB/s, as seen from the given initiator location
        #[cfg(feature = "hwloc-2_8_0")]
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
        #[cfg(feature = "hwloc-2_8_0")]
        #[doc(alias = "HWLOC_MEMATTR_ID_READ_LATENCY")]
        READ_LATENCY -> read_latency,

        /// Write latency in nanoseconds, as seen from the given initiator location
        #[cfg(feature = "hwloc-2_8_0")]
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
    pub fn name(&self) -> Result<&CStr, RawHwlocError> {
        let mut name = ptr::null();
        errors::call_hwloc_int_normal("hwloc_memattr_get_name", || unsafe {
            ffi::hwloc_memattr_get_name(self.topology.as_ptr(), self.id, &mut name)
        })?;
        assert!(
            !name.is_null(),
            "Memory attributes should have non-NULL names"
        );
        Ok(unsafe { CStr::from_ptr(name) })
    }

    /// Memory attribute flags
    #[doc(alias = "hwloc_memattr_get_flags")]
    pub fn flags(&self) -> Result<MemoryAttributeFlags, RawHwlocError> {
        let flags = if let Some(flags) = self.id.static_flags() {
            flags
        } else {
            self.dynamic_flags()?
        };
        debug_assert!(flags.is_valid(), "Flags should be valid");
        Ok(flags)
    }

    /// Dynamically query this memory attribute's flags
    fn dynamic_flags(&self) -> Result<MemoryAttributeFlags, RawHwlocError> {
        let mut flags = 0;
        errors::call_hwloc_int_normal("hwloc_memattr_get_flags", || unsafe {
            ffi::hwloc_memattr_get_flags(self.topology.as_ptr(), self.id, &mut flags)
        })?;
        Ok(MemoryAttributeFlags::from_bits_truncate(flags))
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
    ) -> Result<u64, HybridError<MemoryAttributeQueryError>> {
        let initiator = self.checked_initiator(initiator, false)?;
        let mut value = u64::MAX;
        errors::call_hwloc_int_normal("hwloc_memattr_get_value", || unsafe {
            ffi::hwloc_memattr_get_value(
                self.topology.as_ptr(),
                self.id,
                target_node,
                &initiator,
                0,
                &mut value,
            )
        })
        .map_err(HybridError::Hwloc)?;
        Ok(value)
    }

    /// Best target node and associated attribute value, if any, for a given initiator
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
    ///
    /// [BadInitiator]: MemoryAttributeQueryError::BadInitiator
    #[doc(alias = "hwloc_memattr_get_best_target")]
    pub fn best_target(
        &self,
        initiator: Option<MemoryAttributeLocation>,
    ) -> Result<Option<(&'topology TopologyObject, u64)>, HybridError<MemoryAttributeQueryError>>
    {
        let initiator = self.checked_initiator(initiator, false)?;
        let mut best_target = ptr::null();
        let opt = self.get_best(
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
        )?;
        Ok(opt.map(|value| (unsafe { self.encapsulate_target_node(best_target) }, value)))
    }

    /// Best initiator and associated attribute value, if any, for a given target node
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
    ///
    /// [NoInitiator]: MemoryAttributeQueryError::NoInitiator
    #[doc(alias = "hwloc_memattr_get_best_initiator")]
    pub fn best_initiator(
        &self,
        target: &TopologyObject,
    ) -> Result<
        Option<(MemoryAttributeLocation<'topology>, u64)>,
        HybridError<MemoryAttributeQueryError>,
    > {
        // Validate the query
        if !self
            .flags()
            .map_err(HybridError::Hwloc)?
            .contains(MemoryAttributeFlags::NEED_INITIATOR)
        {
            return Err(MemoryAttributeQueryError::NoInitiator.into());
        }

        // Run it
        let mut best_initiator = RawLocation::null();
        let opt = self.get_best(
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
        )?;
        Ok(opt.map(|value| (unsafe { self.encapsulate_initiator(best_initiator) }, value)))
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
    ) -> Result<(Vec<&'topology TopologyObject>, Vec<u64>), HybridError<MemoryAttributeQueryError>>
    {
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
    ) -> Result<(Vec<MemoryAttributeLocation>, Vec<u64>), HybridError<MemoryAttributeQueryError>>
    {
        // Validate the query
        if !self
            .flags()
            .map_err(HybridError::Hwloc)?
            .contains(MemoryAttributeFlags::NEED_INITIATOR)
        {
            return Err(MemoryAttributeQueryError::NoInitiator.into());
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
    ) -> Result<(Vec<Endpoint>, Vec<u64>), HybridError<MemoryAttributeQueryError>> {
        // Prepare to call hwloc
        let mut nr = 0;
        let mut call_ffi = |nr_mut, endpoint_out, values_out| {
            errors::call_hwloc_int_normal(api, || {
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
        call_ffi(&mut nr, ptr::null_mut(), ptr::null_mut()).map_err(HybridError::Hwloc)?;
        let len = usize::try_from(nr).expect("Impossible array size from hwloc");

        // Allocate storage and fill arrays
        let mut endpoints = vec![placeholder; len];
        let mut values = vec![0; len];
        let old_nr = nr;
        call_ffi(&mut nr, endpoints.as_mut_ptr(), values.as_mut_ptr())
            .map_err(HybridError::Hwloc)?;
        assert_eq!(old_nr, nr, "Inconsistent node count from hwloc");
        Ok((endpoints, values))
    }

    /// Perform a get_best_initiator-style memory attribute query
    fn get_best(
        &self,
        api: &'static str,
        query: impl FnOnce(*const RawTopology, MemoryAttributeID, c_ulong, *mut u64) -> c_int,
    ) -> Result<Option<u64>, MemoryAttributeQueryError> {
        let mut value = u64::MAX;
        match errors::call_hwloc_int_normal(api, || {
            query(self.topology.as_ptr(), self.id, 0, &mut value)
        }) {
            Ok(_positive) => Ok(Some(value)),
            Err(RawHwlocError {
                api: _,
                errno: Some(Errno(ENOENT)),
            }) => Ok(None),
            Err(raw_err) => unreachable!("{raw_err}"),
        }
    }

    /// Encapsulate a *const TopologyObject to a target NUMA node from hwloc
    ///
    /// # Safety
    ///
    /// `node_ptr` must originate from the topology
    unsafe fn encapsulate_target_node(
        &self,
        node_ptr: *const TopologyObject,
    ) -> &'topology TopologyObject {
        assert!(!node_ptr.is_null(), "Got null target pointer from hwloc");
        unsafe { &*node_ptr }
    }

    /// Encapsulate an initiator location from hwloc
    ///
    /// # Safety
    ///
    /// `initiator` must originate from the topology
    unsafe fn encapsulate_initiator(
        &self,
        initiator: RawLocation,
    ) -> MemoryAttributeLocation<'topology> {
        unsafe { MemoryAttributeLocation::from_raw(self.topology, initiator) }
            .expect("Failed to decode location from hwloc")
    }

    /// Check the initiator argument to some query
    ///
    /// If `is_optional` is true, it is okay not to provide an initiator even
    /// if the memory attribute has flag [`MemoryAttributeFlags::NEED_INITIATOR`].
    fn checked_initiator(
        &self,
        initiator: Option<MemoryAttributeLocation>,
        is_optional: bool,
    ) -> Result<RawLocation, HybridError<MemoryAttributeQueryError>> {
        let flags = self.flags().map_err(HybridError::Hwloc)?;
        let is_good = if is_optional {
            flags.contains(MemoryAttributeFlags::NEED_INITIATOR) || initiator.is_none()
        } else {
            !(flags.contains(MemoryAttributeFlags::NEED_INITIATOR) ^ initiator.is_some())
        };
        is_good
            .then(|| {
                initiator
                    .map(MemoryAttributeLocation::into_raw)
                    .unwrap_or_else(RawLocation::null)
            })
            .ok_or(MemoryAttributeQueryError::BadInitiator.into())
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
    /// Only use this on RawLocation structs from hwloc topology queries
    unsafe fn from_raw(
        _topology: &'target Topology,
        raw: RawLocation,
    ) -> Result<Self, UnknownLocationType> {
        match raw.ty {
            RawLocationType::CPUSET => unsafe {
                let ptr = NonNull::new(raw.location.cpuset.cast_mut())
                    .expect("Unexpected null CpuSet from hwloc");
                let topology_ref =
                    std::mem::transmute::<&NonNull<RawBitmap>, &'target NonNull<RawBitmap>>(&ptr);
                let cpuset = CpuSet::borrow_from_non_null(topology_ref);
                Ok(MemoryAttributeLocation::CpuSet(cpuset))
            },
            RawLocationType::OBJECT => unsafe {
                let ptr = NonNull::new(raw.location.object.cast_mut())
                    .expect("Unexpected null TopologyObject from hwloc");
                Ok(MemoryAttributeLocation::Object(ptr.as_ref()))
            },
            unknown => Err(UnknownLocationType(unknown.0)),
        }
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
