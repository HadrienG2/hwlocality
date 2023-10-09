//! Building a topology with a custom configuration
//!
//! The hwloc topology building process can be customized, which means that at
//! any given point in time, a topology can either be in a non-built state that
//! only allows for configuration operations, or in a built state that cannot be
//! configured anymore but allows for most library operations.
//!
//! In a time-honored Rust tradition, this binding models this using two
//! different types, one for the topology building process (which uses the
//! familiar builder pattern) and one for the fully built topology. This module
//! is all about implementing the former type.

use super::Topology;
#[cfg(all(doc, feature = "hwloc-2_8_0"))]
use crate::object::TopologyObject;
#[cfg(all(doc, feature = "hwloc-2_5_0"))]
use crate::topology::editor::TopologyEditor;
#[cfg(doc)]
use crate::topology::support::DiscoverySupport;
#[cfg(all(doc, feature = "hwloc-2_3_0"))]
use crate::topology::support::MiscSupport;
use crate::{
    errors::{self, FlagsError, HybridError, NulError, RawHwlocError},
    ffi::string::LibcString,
    object::types::ObjectType,
    path::{self, PathError},
    ProcessId,
};
use bitflags::bitflags;
use derive_more::From;
use errno::Errno;
#[cfg(feature = "hwloc-2_3_0")]
use hwlocality_sys::HWLOC_TOPOLOGY_FLAG_IMPORT_SUPPORT;
use hwlocality_sys::{
    hwloc_topology, hwloc_topology_flags_e, hwloc_type_filter_e,
    HWLOC_TOPOLOGY_FLAG_INCLUDE_DISALLOWED, HWLOC_TOPOLOGY_FLAG_IS_THISSYSTEM,
    HWLOC_TOPOLOGY_FLAG_THISSYSTEM_ALLOWED_RESOURCES, HWLOC_TYPE_FILTER_KEEP_ALL,
    HWLOC_TYPE_FILTER_KEEP_IMPORTANT, HWLOC_TYPE_FILTER_KEEP_NONE,
    HWLOC_TYPE_FILTER_KEEP_STRUCTURE,
};
#[cfg(feature = "hwloc-2_1_0")]
use hwlocality_sys::{hwloc_topology_components_flag_e, HWLOC_TOPOLOGY_COMPONENTS_FLAG_BLACKLIST};
#[cfg(feature = "hwloc-2_5_0")]
use hwlocality_sys::{
    HWLOC_TOPOLOGY_FLAG_DONT_CHANGE_BINDING, HWLOC_TOPOLOGY_FLAG_RESTRICT_TO_CPUBINDING,
    HWLOC_TOPOLOGY_FLAG_RESTRICT_TO_MEMBINDING,
};
#[cfg(feature = "hwloc-2_8_0")]
use hwlocality_sys::{
    HWLOC_TOPOLOGY_FLAG_NO_CPUKINDS, HWLOC_TOPOLOGY_FLAG_NO_DISTANCES,
    HWLOC_TOPOLOGY_FLAG_NO_MEMATTRS,
};
use libc::{EINVAL, ENOSYS};
use num_enum::{IntoPrimitive, TryFromPrimitive};
#[allow(unused)]
#[cfg(test)]
use pretty_assertions::{assert_eq, assert_ne};
use std::{
    path::{Path, PathBuf},
    ptr::NonNull,
};
use thiserror::Error;

/// Mechanism to build a `Topology` with custom configuration
//
// --- Implementation details ---
//
// # Safety
//
// As a type invariant, the inner pointer is assumed to always point to an
// initialized but non-built, non-aliased topology.
#[derive(Debug)]
pub struct TopologyBuilder(NonNull<hwloc_topology>);

/// # Topology building
//
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__creation.html
impl TopologyBuilder {
    /// Start building a [`Topology`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::topology::builder::{TopologyBuilder, BuildFlags};
    /// let flags = BuildFlags::INCLUDE_DISALLOWED;
    /// let topology = TopologyBuilder::new().with_flags(flags)?.build()?;
    /// assert_eq!(topology.build_flags(), flags);
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn new() -> Self {
        let mut topology: *mut hwloc_topology = std::ptr::null_mut();
        // SAFETY: topology is an out-parameter, initial value shouldn't matter
        errors::call_hwloc_int_normal("hwloc_topology_init", || unsafe {
            hwlocality_sys::hwloc_topology_init(&mut topology)
        })
        .expect("Failed to allocate topology");
        Self(NonNull::new(topology).expect("Got null pointer from hwloc_topology_init"))
    }

    /// Load the topology with the previously specified parameters
    ///
    /// The binding of the current thread or process may temporarily change
    /// during this call but it will be restored before it returns.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::topology::{Topology, builder::BuildFlags};
    /// let flags = BuildFlags::INCLUDE_DISALLOWED;
    /// let topology = Topology::builder().with_flags(flags)?.build()?;
    /// assert_eq!(topology.build_flags(), flags);
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_topology_load")]
    pub fn build(mut self) -> Result<Topology, RawHwlocError> {
        // Finalize the topology building
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc_topology pointer is not reexposed to the
        //           TopologyBuilder interface after this operation
        //         - hwloc_topology pointer should be ready for Topology
        //           interface consumption if this operation succeeds
        errors::call_hwloc_int_normal("hwloc_topology_load", || unsafe {
            hwlocality_sys::hwloc_topology_load(self.as_mut_ptr())
        })?;

        // Check topology for correctness in debug builds
        if cfg!(debug_assertions) {
            // SAFETY: - Topology pointer is trusted to be valid after loading
            //         - hwloc ops are trusted not to modify *const parameters
            unsafe { hwlocality_sys::hwloc_topology_check(self.as_ptr()) }
        }

        // Transfer hwloc_topology ownership to a Topology
        let inner = self.0;
        std::mem::forget(self);
        Ok(Topology(inner))
    }
}

/// # Discovery source
///
/// If none of the functions below is called, the default is to detect all the
/// objects of the machine that the caller is allowed to access.
///
/// This default behavior may also be modified through environment variables if
/// the application did not modify it already. Setting `HWLOC_XMLFILE` in the
/// environment enforces the discovery from a XML file as if [`from_xml_file()`]
/// had been called. Setting `HWLOC_SYNTHETIC` enforces a synthetic topology as
/// if [`from_synthetic()`] had been called.
///
/// Finally, the return value of [`Topology::is_this_system()`] can be enforced
/// by setting `HWLOC_THISSYSTEM`.
///
/// [`from_xml_file()`]: TopologyBuilder::from_xml_file()
/// [`from_synthetic()`]: TopologyBuilder::from_synthetic()
//
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__setsource.html
impl TopologyBuilder {
    /// Change which process the topology is viewed from
    ///
    /// On some systems, processes may have different views of the machine, for
    /// instance the set of allowed CPUs. By default, hwloc exposes the view
    /// from the current process. Calling this method permits to make it expose
    /// the topology of the machine from the point of view of another process.
    ///
    /// # Errors
    ///
    /// - [`FromPIDError`] if the topology cannot be configured from this
    ///   process.
    #[doc(alias = "hwloc_topology_set_pid")]
    pub fn from_pid(mut self, pid: ProcessId) -> Result<Self, HybridError<FromPIDError>> {
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - We can't validate a PID (think TOCTOU race), but hwloc is
        //           trusted to be able to handle an invalid PID
        let result = errors::call_hwloc_int_normal("hwloc_topology_set_pid", || unsafe {
            hwlocality_sys::hwloc_topology_set_pid(self.as_mut_ptr(), pid)
        });
        match result {
            Ok(_) => Ok(self),
            Err(RawHwlocError {
                errno: Some(Errno(ENOSYS)),
                ..
            }) => Err(FromPIDError(pid).into()),
            Err(other_err) => Err(HybridError::Hwloc(other_err)),
        }
    }

    /// Read the topology from a synthetic textual description
    ///
    /// Instead of being probed from the host system, topology information will
    /// be read from the given [textual
    /// description](https://hwloc.readthedocs.io/en/v2.9/synthetic.html).
    ///
    /// Setting the environment variable `HWLOC_SYNTHETIC` may also result in
    /// this behavior.
    ///
    /// CPU and memory binding operations will not do anything with this backend.
    ///
    /// # Errors
    ///
    /// - [`ContainsNul`] if `description` contains NUL chars.
    /// - [`Invalid`] if `description` failed hwloc-side validation (most
    ///   likely it is not a valid Synthetic topology description)
    ///
    /// [`ContainsNul`]: StringInputError::ContainsNul
    /// [`Invalid`]: StringInputError::Invalid
    #[doc(alias = "hwloc_topology_set_synthetic")]
    pub fn from_synthetic(mut self, description: &str) -> Result<Self, StringInputError> {
        let description = LibcString::new(description)?;
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - LibcString should yield valid C strings, which we're not
        //           using beyond their intended lifetime
        //         - hwloc ops are trusted not to modify *const parameters
        let result = errors::call_hwloc_int_normal("hwloc_topology_set_synthetic", || unsafe {
            hwlocality_sys::hwloc_topology_set_synthetic(self.as_mut_ptr(), description.borrow())
        });
        match result {
            Ok(_) => Ok(self),
            Err(RawHwlocError {
                errno: Some(Errno(EINVAL)),
                ..
            }) => Err(StringInputError::Invalid),
            Err(other_err) => unreachable!("Unexpected hwloc error: {other_err}"),
        }
    }

    /// Read the topology from an XML description
    ///
    /// Instead of being probed from the host system, topology information will
    /// be read from the given
    /// [XML description](https://hwloc.readthedocs.io/en/v2.9/xml.html).
    ///
    /// CPU and memory binding operations will not to anything with this backend,
    /// unless [`BuildFlags::ASSUME_THIS_SYSTEM`] is set to assert that the
    /// loaded XML file truly matches the underlying system.
    ///
    /// # Errors
    ///
    /// - [`ContainsNul`] if `description` contains NUL chars.
    /// - [`Invalid`] if `description` failed hwloc-side validation (most
    ///   likely it is not a valid XML topology description)
    ///
    /// [`ContainsNul`]: StringInputError::ContainsNul
    /// [`Invalid`]: StringInputError::Invalid
    #[doc(alias = "hwloc_topology_set_xmlbuffer")]
    pub fn from_xml(mut self, xml: &str) -> Result<Self, StringInputError> {
        let xml = LibcString::new(xml)?;
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - LibcString should yield valid C strings, which we're not
        //           using beyond their intended lifetime
        //         - hwloc ops are trusted not to modify *const parameters
        //         - xml string and length are in sync
        let result = errors::call_hwloc_int_normal("hwloc_topology_set_xmlbuffer", || unsafe {
            hwlocality_sys::hwloc_topology_set_xmlbuffer(
                self.as_mut_ptr(),
                xml.borrow(),
                xml.len()
                    .try_into()
                    .expect("XML buffer is too big for hwloc"),
            )
        });
        match result {
            Ok(_) => Ok(self),
            Err(RawHwlocError {
                errno: Some(Errno(EINVAL)),
                ..
            }) => Err(StringInputError::Invalid),
            Err(other_err) => unreachable!("Unexpected hwloc error: {other_err}"),
        }
    }

    /// Read the topology from an XML file
    ///
    /// This works a lot like [`TopologyBuilder::from_xml()`], but takes a file
    /// name as a parameter instead of an XML string. The same effect can be
    /// achieved by setting the `HWLOC_XMLFILE` environment variable.
    ///
    /// The file may have been generated earlier with
    /// [`Topology::export_xml()`] or `lstopo file.xml`.
    ///
    /// # Errors
    ///
    /// - [`BadRustPath(ContainsNul)`] if `path` contains NUL chars.
    /// - [`BadRustPath(NotUnicode)`] if `path` is not valid Unicode.
    /// - [`Invalid`] if `path` fails hwloc-side validation (most likely the
    ///   path does not exist, is not accessible for reading, or the file does
    ///   not context valid XML)
    ///
    /// [`BadRustPath(ContainsNul)`]: PathError::ContainsNul
    /// [`BadRustPath(NotUnicode)`]: PathError::NotUnicode
    /// [`Invalid`]: FileInputError::Invalid
    #[doc(alias = "hwloc_topology_set_xml")]
    pub fn from_xml_file(self, path: impl AsRef<Path>) -> Result<Self, FileInputError> {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized(
            mut self_: TopologyBuilder,
            path: &Path,
        ) -> Result<TopologyBuilder, FileInputError> {
            let path = path::make_hwloc_path(path)?;
            // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type
            //           invariant)
            //         - hwloc ops are trusted to keep *mut parameters in a
            //           valid state unless stated otherwise
            //         - path has been validated for hwloc consumption
            let result = errors::call_hwloc_int_normal("hwloc_topology_set_xml", || unsafe {
                hwlocality_sys::hwloc_topology_set_xml(self_.as_mut_ptr(), path.borrow())
            });
            match result {
                Ok(_) => Ok(self_),
                Err(RawHwlocError {
                    errno: Some(Errno(EINVAL)),
                    ..
                }) => Err(FileInputError::Invalid(PathBuf::from(path.as_str()).into())),
                Err(other_err) => unreachable!("Unexpected hwloc error: {other_err}"),
            }
        }
        polymorphized(self, path.as_ref())
    }

    /// Prevent a discovery component from being used for a topology
    ///
    /// `name` is the name of the discovery component that should not be used
    /// when loading topology topology. The name is a string such as "cuda".
    /// For components with multiple phases, it may also be suffixed with the
    /// name of a phase, for instance "linux:io". A list of components
    /// distributed with hwloc can be found
    /// [in the hwloc
    /// documentation](https://hwloc.readthedocs.io/en/v2.9/plugins.html#plugins_list).
    ///
    /// This may be used to avoid expensive parts of the discovery process. For
    /// instance, CUDA-specific discovery may be expensive and unneeded while
    /// generic I/O discovery could still be useful.
    ///
    /// # Errors
    ///
    /// - [`NulError`] if `name` contains NUL chars.
    #[cfg(feature = "hwloc-2_1_0")]
    #[doc(alias = "hwloc_topology_set_components")]
    pub fn blacklist_component(mut self, name: &str) -> Result<Self, HybridError<NulError>> {
        let name = LibcString::new(name)?;
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - LibcString should yield valid C strings, which we're not
        //           using beyond their intended lifetime
        //         - hwloc ops are trusted not to modify *const parameters
        //         - BLACKLIST is documented to be the only supported flag
        //           currently, and to be mandated
        errors::call_hwloc_int_normal("hwloc_topology_set_components", || unsafe {
            hwlocality_sys::hwloc_topology_set_components(
                self.as_mut_ptr(),
                ComponentsFlags::BLACKLIST.bits(),
                name.borrow(),
            )
        })
        .map_err(HybridError::Hwloc)?;
        Ok(self)
    }
}

/// Attempted to configure the topology from an invalid process ID
#[derive(Copy, Clone, Debug, Default, Error, From, Eq, Hash, PartialEq)]
#[error("can't configure a Topology from process {0}")]
pub struct FromPIDError(pub ProcessId);

/// Invalid text was specified as the topology source
//
// --- Implementation notes ---
//
// Not exposing the data string in this error because it can be arbitrarily
// large and complex, so including it in the error would not clarify anything.
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum StringInputError {
    /// Input string contains NUL chars and hwloc cannot handle that
    #[error("topology data string can't contain the NUL char")]
    ContainsNul,

    /// Hwloc rejected the input string as invalid for the specified input type
    #[error("hwloc rejected the topology data string as invalid")]
    Invalid,
}
//
impl From<NulError> for StringInputError {
    fn from(NulError: NulError) -> Self {
        Self::ContainsNul
    }
}

/// An invalid input file path was specified as the topology source
#[derive(Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum FileInputError {
    /// Rust-side file path is not suitable for hwloc consumption
    #[error(transparent)]
    BadRustPath(#[from] PathError),

    /// Hwloc rejected the file path or the file contents as invalid
    #[error("hwloc rejected topology input file {0} as invalid")]
    Invalid(Box<Path>),
}

#[cfg(feature = "hwloc-2_1_0")]
bitflags! {
    /// Flags to be passed to `hwloc_topology_set_components()`
    #[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
    #[doc(alias = "hwloc_topology_components_flag_e")]
    pub(crate) struct ComponentsFlags: hwloc_topology_components_flag_e {
        /// Blacklist the target component from being used
        const BLACKLIST = HWLOC_TOPOLOGY_COMPONENTS_FLAG_BLACKLIST;
    }
}

/// # Detection configuration and query
//
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__configuration.html
impl TopologyBuilder {
    /// Set topology building flags
    ///
    /// If this function is called multiple times, the last invocation will
    /// erase and replace the set of flags that was previously set.
    ///
    /// # Errors
    ///
    /// - [`Rust(FlagsError)`](FlagsError) if `flags` were found to be
    ///   invalid on the Rust side. You may want to cross-check the
    ///   documentation of [`BuildFlags`] for more information about which
    ///   combinations of flags are considered valid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hwlocality::topology::{Topology, builder::BuildFlags};
    /// let topology = Topology::builder()
    ///                         .with_flags(BuildFlags::ASSUME_THIS_SYSTEM)?
    ///                         .build()?;
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    #[doc(alias = "hwloc_topology_set_flags")]
    pub fn with_flags(
        mut self,
        flags: BuildFlags,
    ) -> Result<Self, HybridError<FlagsError<BuildFlags>>> {
        if !flags.is_valid() {
            return Err(HybridError::Rust(flags.into()));
        }
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - flags have been validated to be correct above
        errors::call_hwloc_int_normal("hwloc_topology_set_flags", || unsafe {
            hwlocality_sys::hwloc_topology_set_flags(self.as_mut_ptr(), flags.bits())
        })
        .map_err(HybridError::Hwloc)?;
        Ok(self)
    }

    /// Check current topology building flags (empty by default)
    pub fn flags(&self) -> BuildFlags {
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted not to modify *const parameters
        let result = BuildFlags::from_bits_truncate(unsafe {
            hwlocality_sys::hwloc_topology_get_flags(self.as_ptr())
        });
        assert!(result.is_valid(), "hwloc should not send out invalid flags");
        result
    }

    /// Set the filtering for the given object type
    ///
    /// # Errors
    ///
    /// - [`CantKeepGroup`] if one attempts to set [`TypeFilter::KeepAll`] for
    ///   [`Group`] objects, which is not allowed by hwloc.
    /// - [`CantIgnore`] if one attempt's to ignore the top- and bottom-level
    ///   [`Machine`], [`PU`] and [`NUMANode`] types.
    /// - [`StructureIrrelevant`] if one attempts to set
    ///   [`TypeFilter::KeepStructure`] for I/O and [`Misc`] objects, for which
    ///   topology structure does not matter.
    ///
    /// [`CantIgnore`]: TypeFilterError::CantIgnore
    /// [`CantKeepGroup`]: TypeFilterError::CantKeepGroup
    /// [`Group`]: ObjectType::Group
    /// [`Machine`]: ObjectType::Machine
    /// [`Misc`]: ObjectType::Misc
    /// [`NUMANode`]: ObjectType::NUMANode
    /// [`PU`]: ObjectType::PU
    /// [`StructureIrrelevant`]: TypeFilterError::StructureIrrelevant
    #[doc(alias = "hwloc_topology_set_type_filter")]
    pub fn with_type_filter(
        mut self,
        ty: ObjectType,
        filter: TypeFilter,
    ) -> Result<Self, HybridError<TypeFilterError>> {
        match (ty, filter) {
            (ObjectType::Group, TypeFilter::KeepAll) => {
                return Err(TypeFilterError::CantKeepGroup.into())
            }
            (_, TypeFilter::KeepNone) => {
                if let ObjectType::Machine | ObjectType::PU | ObjectType::NUMANode = ty {
                    return Err(TypeFilterError::CantIgnore(ty).into());
                }
            }
            (_, TypeFilter::KeepStructure) if ty.is_io() || ty == ObjectType::Misc => {
                return Err(TypeFilterError::StructureIrrelevant.into())
            }
            _ => {}
        }
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - By construction, ObjectType only exposes values that map into
        //           hwloc_obj_type_t values understood by the configured version
        //           of hwloc, and build.rs checks that the active version of
        //           hwloc is not older than that, so into() may only generate
        //           valid hwloc_obj_type_t values for current hwloc
        //         - By construction, only valid type filters can be sent
        errors::call_hwloc_int_normal("hwloc_topology_set_type_filter", || unsafe {
            hwlocality_sys::hwloc_topology_set_type_filter(
                self.as_mut_ptr(),
                ty.into(),
                filter.into(),
            )
        })
        .map_err(HybridError::Hwloc)?;
        Ok(self)
    }

    /// Set the filtering for all object types
    ///
    /// If some types do not support this filtering, they are silently ignored.
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_topology_set_all_types_filter")]
    pub fn with_common_type_filter(mut self, filter: TypeFilter) -> Result<Self, RawHwlocError> {
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - By construction, only valid type filters can be sent
        errors::call_hwloc_int_normal("hwloc_topology_set_all_types_filter", || unsafe {
            hwlocality_sys::hwloc_topology_set_all_types_filter(self.as_mut_ptr(), filter.into())
        })?;
        Ok(self)
    }

    /// Set the filtering for all CPU cache object types
    ///
    /// Memory-side caches are not involved since they are not CPU caches.
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_topology_set_cache_types_filter")]
    pub fn with_cpu_cache_type_filter(mut self, filter: TypeFilter) -> Result<Self, RawHwlocError> {
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - By construction, only valid type filters can be sent
        errors::call_hwloc_int_normal("hwloc_topology_set_cache_types_filter", || unsafe {
            hwlocality_sys::hwloc_topology_set_cache_types_filter(self.as_mut_ptr(), filter.into())
        })?;
        Ok(self)
    }

    /// Set the filtering for all CPU instruction cache object types
    ///
    /// Memory-side caches are not involved since they are not CPU caches.
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_topology_set_icache_types_filter")]
    pub fn with_cpu_icache_type_filter(
        mut self,
        filter: TypeFilter,
    ) -> Result<Self, RawHwlocError> {
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - By construction, only valid type filters can be sent
        errors::call_hwloc_int_normal("hwloc_topology_set_icache_types_filter", || unsafe {
            hwlocality_sys::hwloc_topology_set_icache_types_filter(self.as_mut_ptr(), filter.into())
        })?;
        Ok(self)
    }

    /// Set the filtering for all I/O object types
    ///
    /// # Errors
    ///
    /// - [`StructureIrrelevant`] if one attempts to set
    ///   [`TypeFilter::KeepStructure`], as topology structure does not matter
    ///   for I/O objects.
    ///
    /// [`StructureIrrelevant`]: TypeFilterError::StructureIrrelevant
    #[doc(alias = "hwloc_topology_set_io_types_filter")]
    pub fn with_io_type_filter(
        mut self,
        filter: TypeFilter,
    ) -> Result<Self, HybridError<TypeFilterError>> {
        if filter == TypeFilter::KeepStructure {
            return Err(TypeFilterError::StructureIrrelevant.into());
        }
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - By construction, only valid type filters can be sent
        errors::call_hwloc_int_normal("hwloc_topology_set_io_types_filter", || unsafe {
            hwlocality_sys::hwloc_topology_set_io_types_filter(self.as_mut_ptr(), filter.into())
        })
        .map_err(HybridError::Hwloc)?;
        Ok(self)
    }
}

bitflags! {
    /// Topology building configuration flags
    #[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
    #[doc(alias = "hwloc_topology_flags_e")]
    pub struct BuildFlags: hwloc_topology_flags_e {
        /// Detect the whole system, ignore reservations, include disallowed objects
        ///
        /// Gather all online resources, even if some were disabled by the
        /// administrator. For instance, ignore Linux Cgroup/Cpusets and gather
        /// all processors and memory nodes. However offline PUs and NUMA nodes
        /// are still ignored.
        ///
        /// When this flag is not set, PUs and NUMA nodes that are disallowed
        /// are not added to the topology. Parent objects (package, core, cache,
        /// etc.) are added only if some of their children are allowed. All
        /// existing PUs and NUMA nodes in the topology are allowed.
        /// [`Topology::allowed_cpuset()`] and [`Topology::allowed_nodeset()`]
        /// are equal to the root object cpuset and nodeset.
        ///
        /// When this flag is set, the actual sets of allowed PUs and NUMA nodes
        /// are given by [`Topology::allowed_cpuset()`] and
        /// [`Topology::allowed_nodeset()`]. They may be smaller than the root
        /// object cpuset and nodeset.
        ///
        /// If the current topology is exported to XML and reimported later,
        /// this flag should be set again in the reimported topology so that
        /// disallowed resources are reimported as well.
        ///
        /// What additional objects could be detected with this flag depends on
        /// [`DiscoverySupport::disallowed_pu()`] and
        /// [`DiscoverySupport::disallowed_numa()`], which can be checked after
        /// building the topology.
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_INCLUDE_DISALLOWED")]
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_WHOLE_SYSTEM")]
        const INCLUDE_DISALLOWED = HWLOC_TOPOLOGY_FLAG_INCLUDE_DISALLOWED;

        /// Assume that the selected backend provides the topology for the
        /// system on which we are running
        ///
        /// This forces [`Topology::is_this_system()`] to return true, i.e.
        /// makes hwloc assume that the selected backend provides the topology
        /// for the system on which we are running, even if it is not the
        /// OS-specific backend but the XML backend for instance. This means
        /// making the binding functions actually call the OS-specific system
        /// calls and really do binding, while the XML backend would otherwise
        /// provide empty hooks just returning success.
        ///
        /// Setting the environment variable `HWLOC_THISSYSTEM` may also result
        /// in the same behavior.
        ///
        /// This can be used for efficiency reasons to first detect the topology
        /// once, save it to an XML file, and quickly reload it later through
        /// the XML backend, but still having binding functions actually do bind.
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_IS_THISSYSTEM")]
        const ASSUME_THIS_SYSTEM = HWLOC_TOPOLOGY_FLAG_IS_THISSYSTEM;

        /// Get the set of allowed resources from the local operating system
        /// even if the topology was loaded from XML or synthetic description
        ///
        /// If the topology was loaded from XML or from a synthetic string,
        /// restrict it by applying the current process restrictions such as
        /// Linux Cgroup/Cpuset.
        ///
        /// This is useful when the topology is not loaded directly from the
        /// local machine (e.g. for performance reason) and it comes with all
        /// resources, while the running process is restricted to only parts of
        /// the machine.
        ///
        /// If this flag is set, `ASSUME_THIS_SYSTEM` must also be set, since
        /// the loaded topology must match the underlying machine where
        /// restrictions will be gathered from.
        ///
        /// Setting the environment variable `HWLOC_THISSYSTEM_ALLOWED_RESOURCES`
        /// would result in the same behavior.
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_THISSYSTEM_ALLOWED_RESOURCES")]
        const GET_ALLOWED_RESOURCES_FROM_THIS_SYSTEM = HWLOC_TOPOLOGY_FLAG_THISSYSTEM_ALLOWED_RESOURCES;

        /// Import support from the imported topology
        ///
        /// When importing a XML topology from a remote machine, binding is
        /// disabled by default (see `ASSUME_THIS_SYSTEM`). This disabling is
        /// also marked by putting zeroes in the corresponding supported feature
        /// bits reported by [`Topology::feature_support()`].
        ///
        /// This flag allows you to actually import support bits from the remote
        /// machine. It also sets the [`MiscSupport::imported()`] support flag.
        /// If the imported XML did not contain any support information
        /// (exporter hwloc is too old), this flag is not set.
        ///
        /// Note that these supported features are only relevant for the hwloc
        /// installation that actually exported the XML topology (it may vary
        /// with the operating system, or with how hwloc was compiled).
        ///
        /// Note that setting this flag however does not enable binding for the
        /// locally imported hwloc topology, it only reports what the remote
        /// hwloc and machine support.
        #[cfg(feature = "hwloc-2_3_0")]
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_IMPORT_SUPPORT")]
        const IMPORT_SUPPORT = HWLOC_TOPOLOGY_FLAG_IMPORT_SUPPORT;

        /// Do not consider resources outside of the process CPU binding
        ///
        /// If the binding of the process is limited to a subset of cores,
        /// ignore the other cores during discovery.
        ///
        /// The resulting topology is identical to what a call to
        /// [`TopologyEditor::restrict()`] would generate, but this flag also
        /// prevents hwloc from ever touching other resources during the
        /// discovery.
        ///
        /// This flag especially tells the x86 backend to never temporarily
        /// rebind a thread on any excluded core. This is useful on Windows
        /// because such temporary rebinding can change the process binding.
        /// Another use-case is to avoid cores that would not be able to perform
        /// the hwloc discovery anytime soon because they are busy executing
        /// some high-priority real-time tasks.
        ///
        /// If process CPU binding is not supported, the thread CPU binding is
        /// considered instead if supported, or the flag is ignored.
        ///
        /// This flag requires `ASSUME_THIS_SYSTEM` as well since binding support
        /// is required.
        #[cfg(feature = "hwloc-2_5_0")]
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_RESTRICT_TO_CPUBINDING")]
        const RESTRICT_CPU_TO_THIS_PROCESS = HWLOC_TOPOLOGY_FLAG_RESTRICT_TO_CPUBINDING;

        /// Do not consider resources outside of the process memory binding
        ///
        /// If the binding of the process is limited to a subset of NUMA nodes,
        /// ignore the other NUMA nodes during discovery.
        ///
        /// The resulting topology is identical to what a call to
        /// [`TopologyEditor::restrict()`] would generate, but this flag also
        /// prevents hwloc from ever touching other resources during the
        /// discovery.
        ///
        /// This flag is meant to be used together with
        /// `RESTRICT_CPU_TO_THIS_PROCESS` when both cores and NUMA nodes should
        /// be ignored outside of the process binding.
        ///
        /// If process memory binding is not supported, the thread memory
        /// binding is considered instead if supported, or the flag is ignored.
        ///
        /// This flag requires `ASSUME_THIS_SYSTEM` as well since binding
        /// support is required.
        #[cfg(feature = "hwloc-2_5_0")]
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_RESTRICT_TO_MEMBINDING")]
        const RESTRICT_MEMORY_TO_THIS_PROCESS = HWLOC_TOPOLOGY_FLAG_RESTRICT_TO_MEMBINDING;

        /// Do not ever modify the process or thread binding during discovery
        ///
        /// This flag disables all hwloc discovery steps that require a change
        /// of the process or thread binding. This currently only affects the
        /// x86 backend which gets entirely disabled.
        ///
        /// This is useful when a [`Topology`] is loaded while the application
        /// also creates additional threads or modifies the binding.
        ///
        /// This flag is also a strict way to make sure the process binding will
        /// not change to due thread binding changes on Windows (see
        /// `RESTRICT_CPU_TO_THIS_PROCESS`).
        #[cfg(feature = "hwloc-2_5_0")]
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_DONT_CHANGE_BINDING")]
        const DONT_CHANGE_BINDING = HWLOC_TOPOLOGY_FLAG_DONT_CHANGE_BINDING;

        /// Ignore distance information from the operating system (and from
        /// XML)
        ///
        /// Distances will not be used for grouping [`TopologyObject`]s.
        #[cfg(feature = "hwloc-2_8_0")]
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_NO_DISTANCES")]
        const IGNORE_DISTANCES = HWLOC_TOPOLOGY_FLAG_NO_DISTANCES;

        /// Ignore memory attribues from the operating system (and from XML)
        #[cfg(feature = "hwloc-2_8_0")]
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_NO_MEMATTRS")]
        const IGNORE_MEMORY_ATTRIBUTES = HWLOC_TOPOLOGY_FLAG_NO_MEMATTRS;

        /// Ignore CPU kind information from the operating system (and from
        /// XML)
        #[cfg(feature = "hwloc-2_8_0")]
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_NO_CPUKINDS")]
        const IGNORE_CPU_KINDS = HWLOC_TOPOLOGY_FLAG_NO_CPUKINDS;
    }
}
//
impl BuildFlags {
    /// Truth that these flags are in a valid state
    #[allow(unused_mut, clippy::let_and_return)]
    pub(crate) fn is_valid(self) -> bool {
        let mut valid = self.contains(Self::ASSUME_THIS_SYSTEM)
            || !self.contains(Self::GET_ALLOWED_RESOURCES_FROM_THIS_SYSTEM);
        #[cfg(feature = "hwloc-2_5_0")]
        {
            valid &= self.contains(Self::ASSUME_THIS_SYSTEM)
                || !self.intersects(
                    Self::RESTRICT_CPU_TO_THIS_PROCESS | Self::RESTRICT_MEMORY_TO_THIS_PROCESS,
                )
        }
        valid
    }
}

/// Type filtering flags
///
/// By default...
///
/// - Most objects are kept (`KeepAll`)
/// - Instruction caches, I/O and Misc objects are ignored (`KeepNone`).
/// - Die and Group levels are ignored unless they bring structure (`KeepStructure`).
///
/// Note that group objects are also ignored individually (without the entire
/// level) when they do not bring structure.
#[cfg_attr(test, derive(enum_iterator::Sequence))]
#[derive(Copy, Clone, Debug, Eq, Hash, IntoPrimitive, PartialEq, TryFromPrimitive)]
#[doc(alias = "hwloc_type_filter_e")]
#[repr(i32)]
pub enum TypeFilter {
    /// Keep all objects of this type
    ///
    /// Cannot be set for [`ObjectType::Group`] (groups are designed only to add
    /// more structure to the topology).
    #[doc(alias = "HWLOC_TYPE_FILTER_KEEP_ALL")]
    KeepAll = HWLOC_TYPE_FILTER_KEEP_ALL,

    /// Ignore all objects of this type
    ///
    /// The bottom-level type [`ObjectType::PU`], the [`ObjectType::NUMANode`]
    /// type, and the top-level type [`ObjectType::Machine`] may not be ignored.
    #[doc(alias = "HWLOC_TYPE_FILTER_KEEP_NONE")]
    KeepNone = HWLOC_TYPE_FILTER_KEEP_NONE,

    /// Only ignore objects if their entire level does not bring any structure
    ///
    /// Keep the entire level of objects if at least one of these objects adds
    /// structure to the topology. An object brings structure when it has
    /// multiple children and it is not the only child of its parent.
    ///
    /// If all objects in the level are the only child of their parent, and if
    /// none of them has multiple children, the entire level is removed.
    ///
    /// Cannot be set for I/O and Misc objects since the topology structure does
    /// not matter there.
    #[doc(alias = "HWLOC_TYPE_FILTER_KEEP_STRUCTURE")]
    KeepStructure = HWLOC_TYPE_FILTER_KEEP_STRUCTURE,

    /// Only keep likely-important objects of the given type.
    ///
    /// This is only useful for I/O object types.
    ///
    /// For [`ObjectType::PCIDevice`] and [`ObjectType::OSDevice`], it means that
    /// only objects of major/common kinds are kept (storage, network,
    /// OpenFabrics, CUDA, OpenCL, RSMI, NVML, and displays).
    /// Also, only OS devices directly attached on PCI (e.g. no USB) are reported.
    ///
    /// For [`ObjectType::Bridge`], it means that bridges are kept only if they
    /// have children.
    ///
    /// This flag is equivalent to `KeepAll` for Normal, Memory and Misc types
    /// since they are likely important.
    #[doc(alias = "HWLOC_TYPE_FILTER_KEEP_IMPORTANT")]
    KeepImportant = HWLOC_TYPE_FILTER_KEEP_IMPORTANT,
}

/// Errors that can occur when filtering types
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum TypeFilterError {
    /// Cannot force keeping Group objects with [`TypeFilter::KeepAll`]
    ///
    /// Groups are designed only to add more structure to the topology.
    #[error("can't force hwloc to keep group objects")]
    CantKeepGroup,

    /// Top-level and bottom-level types cannot be ignored
    #[error("can't ignore top- or bottom-level object type {0}")]
    CantIgnore(ObjectType),

    /// Topology structure doesn't matter for I/O and Misc objects
    #[error("topology structure doesn't matter for I/O and Misc objects")]
    StructureIrrelevant,
}
//
impl From<ObjectType> for TypeFilterError {
    fn from(value: ObjectType) -> Self {
        Self::CantIgnore(value)
    }
}

/// # General-purpose internal utilities
impl TopologyBuilder {
    /// Contained hwloc topology pointer (for interaction with hwloc)
    fn as_ptr(&self) -> *const hwloc_topology {
        self.0.as_ptr()
    }

    /// Contained mutable hwloc topology pointer (for interaction with hwloc)
    fn as_mut_ptr(&mut self) -> *mut hwloc_topology {
        self.0.as_ptr()
    }
}

// NOTE: Do not implement AsRef, AsMut, Borrow, etc: the topology isn't built yet

impl Default for TopologyBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for TopologyBuilder {
    fn drop(&mut self) {
        // Check modified topology for correctness in debug builds
        if cfg!(debug_assertions) {
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - hwloc ops are trusted not to modify *const parameters
            unsafe { hwlocality_sys::hwloc_topology_check(self.as_ptr()) }
        }

        // Liberate the topology
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - Safe code can't use the invalidated topology pointer again
        //           after this Drop
        unsafe { hwlocality_sys::hwloc_topology_destroy(self.as_mut_ptr()) }
    }
}

// SAFETY: No internal mutability
unsafe impl Send for TopologyBuilder {}

// SAFETY: No internal mutability
unsafe impl Sync for TopologyBuilder {}

#[cfg(test)]
mod tests {
    use super::*;
    use bitflags::Flags;
    #[allow(unused)]
    use pretty_assertions::{assert_eq, assert_ne};
    use static_assertions::assert_impl_all;
    use std::{
        error::Error,
        fmt::{Binary, Debug, LowerHex, Octal, UpperHex},
        hash::Hash,
        ops::{
            BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Sub, SubAssign,
        },
        panic::{RefUnwindSafe, UnwindSafe},
    };

    // Check that public types in this module keep implementing all expected
    // traits, in the interest of detecting future semver-breaking changes
    assert_impl_all!(BuildFlags:
        Binary, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign,
        Clone, Copy, Debug, Default, Eq, Extend<BuildFlags>, Flags,
        FromIterator<BuildFlags>, Hash, IntoIterator<Item=BuildFlags>,
        LowerHex, Not, Octal, RefUnwindSafe, Send, Sized, Sub, SubAssign, Sync,
        UpperHex, Unpin, UnwindSafe
    );
    assert_impl_all!(FromPIDError:
        Clone, Copy, Debug, Default, Error, Eq, From<ProcessId>, Hash,
        RefUnwindSafe, Send, Sized, Sync, Unpin, UnwindSafe
    );
    assert_impl_all!(StringInputError:
        Clone, Copy, Debug, Error, Eq, From<NulError>, Hash, RefUnwindSafe,
        Send, Sized, Sync, Unpin, UnwindSafe
    );
    assert_impl_all!(TopologyBuilder:
        Debug, Default, RefUnwindSafe, Send, Sized, Sync, Unpin, UnwindSafe
    );
    assert_impl_all!(TypeFilter:
        Clone, Copy, Debug, Eq, Hash, Into<hwloc_type_filter_e>, RefUnwindSafe,
        Send, Sized, Sync, TryFrom<hwloc_type_filter_e>, Unpin, UnwindSafe
    );
    assert_impl_all!(TypeFilterError:
        Clone, Copy, Debug, Error, Eq, Hash, RefUnwindSafe, Send, Sized, Sync,
        Unpin, UnwindSafe
    );
    assert_impl_all!(FileInputError:
        Clone, Debug, Error, Eq, From<PathError>, Hash, RefUnwindSafe,
        Send, Sized, Sync, Unpin, UnwindSafe
    );

    #[test]
    fn default_build() {
        let builder = TopologyBuilder::new();
        //
        assert_eq!(builder.flags(), BuildFlags::default());
        //
        let expected_filter = |object_type| match object_type {
            ObjectType::Group => TypeFilter::KeepStructure,
            #[cfg(feature = "hwloc-2_1_0")]
            ObjectType::Die => {
                // What hwloc claims to do in its docs
                /* TypeFilter::KeepStructure */
                // What hwloc actually does...
                TypeFilter::KeepAll
            }
            ObjectType::Misc => TypeFilter::KeepNone,
            #[cfg(feature = "hwloc-2_1_0")]
            ObjectType::MemCache => TypeFilter::KeepNone,
            ty if ty.is_cpu_instruction_cache() || ty.is_io() => TypeFilter::KeepNone,
            _ => TypeFilter::KeepAll,
        };

        let topology = builder.build().unwrap();
        //
        assert!(topology.is_abi_compatible());
        assert!(topology.is_this_system());
        //
        assert_eq!(topology.build_flags(), BuildFlags::default());
        for object_type in enum_iterator::all::<ObjectType>() {
            assert_eq!(
                topology.type_filter(object_type).unwrap(),
                expected_filter(object_type),
                "Unexpected filtering for objects of type {object_type:?}"
            );
        }
        //
        assert_eq!(topology.allowed_cpuset(), topology.cpuset());
        assert!(topology.complete_cpuset().includes(&topology.cpuset()));
    }
}
