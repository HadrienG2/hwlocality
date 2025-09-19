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
    ffi::{string::LibcString, unknown::UnknownVariant},
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
    hwloc_pid_t, hwloc_topology, hwloc_topology_flags_e, hwloc_type_filter_e,
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
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::{
    fmt::{self, Pointer},
    path::{Path, PathBuf},
    ptr::NonNull,
};
use strum::{EnumCount, EnumIter, FromRepr};
use thiserror::Error;

/// Mechanism to build a [`Topology`] with custom configuration
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
// Upstream docs: https://hwloc.readthedocs.io/en/stable/group__hwlocality__creation.html
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
    /// # Ok::<(), eyre::Report>(())
    /// ```
    pub fn new() -> Self {
        let mut topology: *mut hwloc_topology = std::ptr::null_mut();
        // SAFETY: topology is an out-parameter, initial value shouldn't matter
        errors::call_hwloc_zero_or_minus1("hwloc_topology_init", || unsafe {
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
    /// # Ok::<(), eyre::Report>(())
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
        errors::call_hwloc_zero_or_minus1("hwloc_topology_load", || unsafe {
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
// Upstream docs: https://hwloc.readthedocs.io/en/stable/group__hwlocality__setsource.html
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
    ///
    /// # Panics
    ///
    /// Some operating systems use signed PIDs, and do not support PIDs greater
    /// than `i32::MAX`. This method will panic when passed such an obviously
    /// invalid PID on these operating systems.
    #[doc(alias = "hwloc_topology_set_pid")]
    pub fn from_pid(mut self, pid: ProcessId) -> Result<Self, HybridError<FromPIDError>> {
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - We can't validate a PID (think TOCTOU race), but hwloc is
        //           trusted to be able to handle an invalid PID
        let result = errors::call_hwloc_zero_or_minus1("hwloc_topology_set_pid", || unsafe {
            hwlocality_sys::hwloc_topology_set_pid(
                self.as_mut_ptr(),
                hwloc_pid_t::try_from(pid).expect("shouldn't fail for a valid PID"),
            )
        });
        #[cfg(not(tarpaulin_include))]
        let handle_enosys = || Err(FromPIDError(pid).into());
        match result {
            Ok(()) => Ok(self),
            #[cfg(not(tarpaulin_include))]
            Err(RawHwlocError {
                errno: Some(Errno(ENOSYS)),
                ..
            }) => handle_enosys(),
            #[cfg(not(tarpaulin_include))]
            #[cfg(windows)]
            Err(RawHwlocError { errno: None, .. }) => {
                // As explained in the RawHwlocError documentation, errno values
                // may not correctly propagate from hwloc to hwlocality on
                // Windows. Since there is only one expected errno value here,
                // we'll interpret lack of errno as ENOSYS on Windows.
                handle_enosys()
            }
            Err(other_err) => Err(HybridError::Hwloc(other_err)),
        }
    }

    /// Read the topology from a synthetic textual description
    ///
    /// Instead of being probed from the host system, topology information will
    /// be read from the given [textual
    /// description](https://hwloc.readthedocs.io/en/stable/synthetic.html).
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
        let result = errors::call_hwloc_zero_or_minus1("hwloc_topology_set_synthetic", || unsafe {
            hwlocality_sys::hwloc_topology_set_synthetic(self.as_mut_ptr(), description.borrow())
        });
        match result {
            Ok(()) => Ok(self),
            Err(RawHwlocError {
                errno: Some(Errno(EINVAL)),
                ..
            }) => Err(StringInputError::Invalid),
            #[cfg(windows)]
            Err(RawHwlocError { errno: None, .. }) => {
                // As explained in the RawHwlocError documentation, errno values
                // may not correctly propagate from hwloc to hwlocality on
                // Windows. Since there is only one expected errno value here,
                // we'll interpret lack of errno as EINVAL on Windows.
                Err(StringInputError::Invalid)
            }
            Err(other_err) => unreachable!("Unexpected hwloc error: {other_err}"),
        }
    }

    /// Read the topology from an XML description
    ///
    /// Instead of being probed from the host system, topology information will
    /// be read from the given
    /// [XML description](https://hwloc.readthedocs.io/en/stable/xml.html).
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
        let result = errors::call_hwloc_zero_or_minus1("hwloc_topology_set_xmlbuffer", || unsafe {
            hwlocality_sys::hwloc_topology_set_xmlbuffer(
                self.as_mut_ptr(),
                xml.borrow(),
                xml.len()
                    .try_into()
                    .expect("XML buffer is too big for hwloc"),
            )
        });
        match result {
            Ok(()) => Ok(self),
            Err(RawHwlocError {
                errno: Some(Errno(EINVAL)),
                ..
            }) => Err(StringInputError::Invalid),
            #[cfg(windows)]
            Err(RawHwlocError { errno: None, .. }) => {
                // As explained in the RawHwlocError documentation, errno values
                // may not correctly propagate from hwloc to hwlocality on
                // Windows. Since there is only one expected errno value here,
                // we'll interpret lack of errno as EINVAL on Windows.
                Err(StringInputError::Invalid)
            }
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
            let result = errors::call_hwloc_zero_or_minus1("hwloc_topology_set_xml", || unsafe {
                hwlocality_sys::hwloc_topology_set_xml(self_.as_mut_ptr(), path.borrow())
            });
            let handle_einval =
                || Err(FileInputError::Invalid(PathBuf::from(path.as_str()).into()));
            match result {
                Ok(()) => Ok(self_),
                Err(RawHwlocError {
                    errno: Some(Errno(EINVAL)),
                    ..
                }) => handle_einval(),
                #[cfg(windows)]
                Err(RawHwlocError { errno: None, .. }) => {
                    // As explained in the RawHwlocError documentation, errno values
                    // may not correctly propagate from hwloc to hwlocality on
                    // Windows. Since there is only one expected errno value
                    // here, we'll interpret lack of errno as EINVAL on Windows.
                    handle_einval()
                }
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
    /// documentation](https://hwloc.readthedocs.io/en/stable/plugins.html#plugins_list).
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
    pub fn without_component(mut self, name: &str) -> Result<Self, HybridError<NulError>> {
        let name = LibcString::new(name)?;
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - LibcString should yield valid C strings, which we're not
        //           using beyond their intended lifetime
        //         - hwloc ops are trusted not to modify *const parameters
        //         - BLACKLIST is documented to be the only supported flag
        //           currently, and to be mandated
        errors::call_hwloc_zero_or_minus1("hwloc_topology_set_components", || unsafe {
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

#[cfg(not(tarpaulin_include))]
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
// Upstream docs: https://hwloc.readthedocs.io/en/stable/group__hwlocality__configuration.html
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
    /// # Ok::<(), eyre::Report>(())
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
        errors::call_hwloc_zero_or_minus1("hwloc_topology_set_flags", || unsafe {
            hwlocality_sys::hwloc_topology_set_flags(self.as_mut_ptr(), flags.bits())
        })
        .map_err(HybridError::Hwloc)?;
        Ok(self)
    }

    /// Check current topology building flags (empty by default)
    pub fn flags(&self) -> BuildFlags {
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted not to modify *const parameters
        let result = BuildFlags::from_bits_retain(unsafe {
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
    /// - [`CantIgnore`] if one attempts to ignore the top- and bottom-level
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
        mut filter: TypeFilter,
    ) -> Result<Self, HybridError<TypeFilterError>> {
        if filter == TypeFilter::KeepImportant && !ty.is_io() {
            filter = TypeFilter::KeepAll;
        }
        match (ty, filter) {
            (ObjectType::Group, TypeFilter::KeepAll) => {
                return Err(TypeFilterError::CantKeepGroup.into())
            }
            (ObjectType::Machine | ObjectType::PU | ObjectType::NUMANode, _) => {
                if filter != TypeFilter::KeepAll {
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
        errors::call_hwloc_zero_or_minus1("hwloc_topology_set_type_filter", || unsafe {
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
        errors::call_hwloc_zero_or_minus1("hwloc_topology_set_all_types_filter", || unsafe {
            hwlocality_sys::hwloc_topology_set_all_types_filter(self.as_mut_ptr(), filter.into())
        })?;

        // Workaround for hwloc check assertion failure that shouldn't fail
        if filter == TypeFilter::KeepImportant {
            self = self
                .with_type_filter(ObjectType::Group, TypeFilter::KeepStructure)
                .expect("Known to be a supported combination");
        }

        Ok(self)
    }

    /// Set the filtering for all CPU cache object types
    ///
    /// Memory-side caches are not involved since they are not CPU caches.
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_topology_set_cache_types_filter")]
    pub fn with_cpu_cache_type_filter(
        mut self,
        mut filter: TypeFilter,
    ) -> Result<Self, RawHwlocError> {
        if filter == TypeFilter::KeepImportant {
            filter = TypeFilter::KeepAll
        }
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - By construction, only valid type filters can be sent
        errors::call_hwloc_zero_or_minus1("hwloc_topology_set_cache_types_filter", || unsafe {
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
        mut filter: TypeFilter,
    ) -> Result<Self, RawHwlocError> {
        if filter == TypeFilter::KeepImportant {
            filter = TypeFilter::KeepAll
        }
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - By construction, only valid type filters can be sent
        errors::call_hwloc_zero_or_minus1("hwloc_topology_set_icache_types_filter", || unsafe {
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
        errors::call_hwloc_zero_or_minus1("hwloc_topology_set_io_types_filter", || unsafe {
            hwlocality_sys::hwloc_topology_set_io_types_filter(self.as_mut_ptr(), filter.into())
        })
        .map_err(HybridError::Hwloc)?;
        Ok(self)
    }

    /// Current filtering for the given object type
    #[allow(clippy::missing_errors_doc)]
    pub fn type_filter(&self, ty: ObjectType) -> Result<TypeFilter, RawHwlocError> {
        let mut filter = hwloc_type_filter_e::MAX;
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted not to modify *const parameters
        //         - By construction, ObjectType only exposes values that map into
        //           hwloc_obj_type_t values understood by the configured version
        //           of hwloc, and build.rs checks that the active version of
        //           hwloc is not older than that, so into() may only generate
        //           valid hwloc_obj_type_t values for current hwloc
        //         - filter is an out-parameter, initial value shouldn't matter
        errors::call_hwloc_zero_or_minus1("hwloc_topology_get_type_filter", || unsafe {
            hwlocality_sys::hwloc_topology_get_type_filter(self.as_ptr(), ty.into(), &mut filter)
        })?;
        // SAFETY: filter comes from hwloc_get_type_filter, which didn't fail,
        //         so it should be a type filter value that hwloc accepts to
        //         receive as input.
        Ok(unsafe { TypeFilter::from_hwloc(filter) })
    }
}

#[cfg(not(tarpaulin_include))]
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
        // TODO: If you add more build flags, update is_valid() and the
        //       valid_build_flags() generator in the test suite.
    }
}
//
impl BuildFlags {
    /// Truth that these flags are in a valid state
    #[allow(unused_mut)]
    pub(crate) fn is_valid(self) -> bool {
        let mut need_this_system = Self::GET_ALLOWED_RESOURCES_FROM_THIS_SYSTEM;
        #[cfg(feature = "hwloc-2_5_0")]
        {
            need_this_system
                .insert(Self::RESTRICT_CPU_TO_THIS_PROCESS | Self::RESTRICT_MEMORY_TO_THIS_PROCESS);
        }
        self.contains(Self::ASSUME_THIS_SYSTEM) || !self.intersects(need_this_system)
    }
}
//
crate::impl_arbitrary_for_bitflags!(BuildFlags, hwloc_topology_flags_e);

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
#[derive(Clone, Copy, Debug, EnumCount, EnumIter, Eq, FromRepr, Hash, PartialEq)]
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

    /// Unknown [`hwloc_type_filter_e`] from hwloc
    #[strum(disabled)]
    Unknown(UnknownVariant<hwloc_type_filter_e>) = hwloc_type_filter_e::MAX,
}
//
impl TypeFilter {
    /// Build a `TypeFilter` from an hwloc-originated [`hwloc_type_filter_e`]
    ///
    /// # Safety
    ///
    /// This type normally maintains the invariant that it holds a valid hwloc
    /// input, and safe code relies on this to treat any C representation of
    /// this enum as valid to send to hwloc. Therefore, you must enforce that
    /// either of the following is true:
    ///
    /// - `value` is a known hwloc enum variant or was emitted by hwloc as
    ///   output, and therefore is known/suspected to be a safe hwloc input.
    /// - The output of `from_hwloc` from a `value` that is _not_ a known-good
    ///   hwloc input is never sent to any hwloc API, either directly or via a
    ///   safe `hwlocality` method. This possibility is mainly provided for
    ///   unit testing code and not meant to be used on a larger scale.
    pub(crate) unsafe fn from_hwloc(value: hwloc_type_filter_e) -> Self {
        Self::from_repr(value).unwrap_or(Self::Unknown(UnknownVariant(value)))
    }
}
//
crate::impl_arbitrary_for_sequence!(TypeFilter);
//
impl From<TypeFilter> for hwloc_type_filter_e {
    fn from(value: TypeFilter) -> Self {
        match value {
            TypeFilter::KeepAll => HWLOC_TYPE_FILTER_KEEP_ALL,
            TypeFilter::KeepNone => HWLOC_TYPE_FILTER_KEEP_NONE,
            TypeFilter::KeepStructure => HWLOC_TYPE_FILTER_KEEP_STRUCTURE,
            TypeFilter::KeepImportant => HWLOC_TYPE_FILTER_KEEP_IMPORTANT,
            TypeFilter::Unknown(unknown) => unknown.get(),
        }
    }
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
        // NOTE: Do not call hwloc_topology_check here, calling this function on
        //       a topology that hasn't been loaded yet isn't supported!

        // Liberate the topology
        // SAFETY: - TopologyBuilder is trusted to contain a valid ptr (type invariant)
        //         - Safe code can't use the invalidated topology pointer again
        //           after this Drop
        unsafe { hwlocality_sys::hwloc_topology_destroy(self.as_mut_ptr()) }
    }
}

impl Pointer for TopologyBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <NonNull<hwloc_topology> as Pointer>::fmt(&self.0, f)
    }
}

// SAFETY: No internal mutability
unsafe impl Send for TopologyBuilder {}

// SAFETY: No internal mutability
unsafe impl Sync for TopologyBuilder {}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::{object::TopologyObject, topology::export::xml::XMLExportFlags};
    use bitflags::Flags;
    use proptest::prelude::*;
    #[allow(unused)]
    use similar_asserts::assert_eq;
    use static_assertions::{assert_impl_all, assert_not_impl_any};
    use std::{
        collections::HashSet,
        error::Error,
        fmt::{Binary, Debug, Display, LowerExp, LowerHex, Octal, UpperExp, UpperHex},
        hash::Hash,
        io::{self, Read},
        ops::{
            BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Deref, Not, Sub,
            SubAssign,
        },
        panic::UnwindSafe,
    };
    use strum::IntoEnumIterator;
    use tempfile::NamedTempFile;

    // Check that public types in this module keep implementing all expected
    // traits, in the interest of detecting future semver-breaking changes
    assert_impl_all!(BuildFlags:
        Binary, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign,
        Copy, Debug, Default, Extend<BuildFlags>, Flags,
        FromIterator<BuildFlags>, Hash, IntoIterator<Item=BuildFlags>,
        LowerHex, Not, Octal, Sized, Sub, SubAssign, Sync, UpperHex, Unpin,
        UnwindSafe
    );
    assert_not_impl_any!(BuildFlags:
        Display, Drop, PartialOrd, Pointer, LowerExp, Read, UpperExp,
        fmt::Write, io::Write
    );
    assert_impl_all!(FileInputError:
        Clone, Error, From<PathError>, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(FileInputError:
        Binary, Copy, Default, Deref, Drop, IntoIterator,
        LowerExp, LowerHex, Octal, PartialOrd, Pointer, Read,
        UpperExp, UpperHex, fmt::Write, io::Write
    );
    assert_impl_all!(FromPIDError:
        Copy, Default, Error, From<ProcessId>, Hash, Sized, Sync, Unpin,
        UnwindSafe
    );
    assert_not_impl_any!(FromPIDError:
        Binary, Deref, Drop, IntoIterator,
        LowerExp, LowerHex, Octal, PartialOrd, Pointer, Read,
        UpperExp, UpperHex, fmt::Write, io::Write
    );
    assert_impl_all!(StringInputError:
        Copy, Error, From<NulError>, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(StringInputError:
        Binary, Default, Deref, Drop, IntoIterator,
        LowerExp, LowerHex, Octal, PartialOrd, Pointer, Read,
        UpperExp, UpperHex, fmt::Write, io::Write
    );
    assert_impl_all!(TopologyBuilder:
        Debug, Default, Drop, Pointer, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(TopologyBuilder:
        Binary, Clone, Deref, Display, IntoIterator, LowerExp, LowerHex, Octal,
        PartialEq, Read, ToOwned, UpperExp, UpperHex, fmt::Write, io::Write
    );
    assert_impl_all!(TypeFilter:
        Copy, Debug, Hash, Into<hwloc_type_filter_e>, Sized, Sync,
        Unpin, UnwindSafe
    );
    assert_not_impl_any!(TypeFilter:
        Binary, Default, Deref, Display, Drop, IntoIterator, LowerExp, LowerHex,
        Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write,
        io::Write
    );
    assert_impl_all!(TypeFilterError:
        Copy, Error, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(TypeFilterError:
        Binary, Default, Deref, Drop, IntoIterator,
        LowerExp, LowerHex, Octal, PartialOrd, Pointer, Read,
        UpperExp, UpperHex, fmt::Write, io::Write
    );

    #[allow(clippy::unnecessary_wraps)]
    fn default_type_filter(object_type: ObjectType) -> Result<TypeFilter, TestCaseError> {
        let res = match object_type {
            ObjectType::Group => TypeFilter::KeepStructure,
            ObjectType::Misc => TypeFilter::KeepNone,
            #[cfg(feature = "hwloc-2_1_0")]
            ObjectType::MemCache => TypeFilter::KeepNone,
            ty if ty.is_cpu_instruction_cache() || ty.is_io() => TypeFilter::KeepNone,
            #[cfg(feature = "hwloc-2_1_0")]
            ObjectType::Die => TypeFilter::KeepAll,
            _ => TypeFilter::KeepAll,
        };
        Ok(res)
    }

    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub(crate) enum DataSource {
        ThisSystem,
        Synthetic,
        Xml,
    }

    pub(crate) fn check_topology(
        topology: &Topology,
        data_source: DataSource,
        build_flags: BuildFlags,
        type_filter: impl Fn(ObjectType) -> Result<TypeFilter, TestCaseError>,
    ) -> Result<(), TestCaseError> {
        prop_assert_eq!(format!("{:p}", *topology), format!("{:p}", topology.0));
        prop_assert!(topology.is_abi_compatible());
        prop_assert_eq!(topology.build_flags(), build_flags);
        prop_assert_eq!(
            topology.is_this_system(),
            data_source == DataSource::ThisSystem
                || build_flags.contains(BuildFlags::ASSUME_THIS_SYSTEM)
        );

        for object_type in ObjectType::iter() {
            prop_assert_eq!(
                topology.type_filter(object_type),
                Ok(type_filter(object_type)?),
                "Unexpected filtering for objects of type {}",
                object_type
            );
        }

        if !build_flags.contains(BuildFlags::GET_ALLOWED_RESOURCES_FROM_THIS_SYSTEM)
            || data_source == DataSource::ThisSystem
        {
            if build_flags.contains(BuildFlags::INCLUDE_DISALLOWED) {
                prop_assert!(topology.allowed_cpuset().includes(topology.cpuset()));
                prop_assert!(topology.allowed_nodeset().includes(topology.nodeset()));
            } else {
                prop_assert_eq!(topology.allowed_cpuset(), topology.cpuset());
                prop_assert_eq!(topology.allowed_nodeset(), topology.nodeset());
            }
        }
        prop_assert!(topology.complete_cpuset().includes(topology.cpuset()));
        prop_assert!(topology.complete_nodeset().includes(topology.nodeset()));

        #[cfg(feature = "hwloc-2_3_0")]
        {
            use crate::topology::support::{FeatureSupport, MiscSupport};
            if build_flags.contains(BuildFlags::IMPORT_SUPPORT) && data_source == DataSource::Xml {
                prop_assert!(topology.supports(FeatureSupport::misc, MiscSupport::imported));
            }
        }

        #[cfg(feature = "hwloc-2_8_0")]
        {
            use crate::cpu::kind::NoData;
            if build_flags.contains(BuildFlags::IGNORE_DISTANCES) {
                prop_assert_eq!(
                    topology
                        .distances(None)
                        .map(|distances| distances.is_empty()),
                    Ok(true)
                );
            }
            if build_flags.contains(BuildFlags::IGNORE_CPU_KINDS) && cfg!(not(windows)) {
                prop_assert_eq!(topology.num_cpu_kinds(), Err(NoData));
            }
        }

        Ok(())
    }

    fn check_default_builder(builder: &TopologyBuilder) -> Result<(), TestCaseError> {
        assert_eq!(format!("{:p}", *builder), format!("{:p}", builder.0));
        assert_eq!(builder.flags(), BuildFlags::default());
        for object_type in ObjectType::iter() {
            assert_eq!(
                builder.type_filter(object_type),
                Ok(default_type_filter(object_type)?),
                "Unexpected filtering for objects of type {}",
                object_type
            );
        }
        Ok(())
    }

    /// Test the various hwlocality-exposed ways to get a topology builder and a
    /// built topology in their default state
    #[test]
    fn default() -> Result<(), TestCaseError> {
        let mut default_topologies = vec![Topology::new().unwrap()];
        for default_builder in [
            Topology::builder(),
            TopologyBuilder::new(),
            TopologyBuilder::default(),
        ] {
            check_default_builder(&default_builder)?;
            default_topologies.push(default_builder.build().unwrap());
        }
        for topology in &default_topologies {
            check_topology(
                topology,
                DataSource::ThisSystem,
                BuildFlags::default(),
                default_type_filter,
            )?;
        }
        Ok(())
    }

    /// Set up a [`TopologyBuilder`] with random flags from proptest, if the
    /// flags are right
    /// FIXME: Test more aspects of build flags
    fn builder_with_flags(
        build_flags: BuildFlags,
    ) -> Result<Option<TopologyBuilder>, TestCaseError> {
        let builder = TopologyBuilder::new();
        let builder_opt = if build_flags.is_valid() {
            let builder = builder
                .with_flags(build_flags)
                .expect("Builder should accept valid flags");
            prop_assert_eq!(builder.flags(), build_flags);
            Some(builder)
        } else {
            builder
                .with_flags(build_flags)
                .expect_err("Builder should reject invalid flags");
            None
        };
        Ok(builder_opt)
    }

    /// [`BuildFlags`] that are guaranteed to be valid
    #[allow(unused_mut)]
    fn valid_build_flags() -> impl Strategy<Value = BuildFlags> {
        any::<BuildFlags>().prop_map(|mut flags| {
            let mut need_this_system = BuildFlags::GET_ALLOWED_RESOURCES_FROM_THIS_SYSTEM;
            #[cfg(feature = "hwloc-2_5_0")]
            {
                need_this_system.insert(
                    BuildFlags::RESTRICT_CPU_TO_THIS_PROCESS
                        | BuildFlags::RESTRICT_MEMORY_TO_THIS_PROCESS,
                );
            }
            if flags.intersects(need_this_system) {
                flags.insert(BuildFlags::ASSUME_THIS_SYSTEM);
            }
            assert!(flags.is_valid());
            flags
        })
    }

    /// Shortcut when you only need a single builder with arbitrary build flags
    fn builder_with_valid_flags() -> impl Strategy<Value = TopologyBuilder> {
        valid_build_flags().prop_map(|flags| builder_with_flags(flags).unwrap().unwrap())
    }

    proptest! {
        /// Test that setting build flags works on its own
        #[test]
        fn with_flags(build_flags: BuildFlags) {
            if let Some(builder) = builder_with_flags(build_flags)? {
                let topology = builder.build().unwrap();
                check_topology(
                    &topology,
                    DataSource::ThisSystem,
                    build_flags,
                    default_type_filter,
                )?;
            }
        }

        /// Test that building from this process' PID is the same as using the
        /// default topology building process
        ///
        /// The outcome of building from a different PID is unpredictable, and thus
        /// not suitable for testing. It may fail altogether if the OS forbids us
        /// from querying another PID.
        #[test]
        fn from_pid(build_flags in valid_build_flags()) {
            // Attempt to configure a builder to get data from a certain process
            let builder_from_pid =
                |pid: ProcessId| Ok::<_, TestCaseError>(builder_with_flags(build_flags)?.unwrap().from_pid(pid));

            // Expect readout from a certain pid to fail
            let expect_fail = |pid: ProcessId| {
                match builder_from_pid(pid)? {
                    Ok(builder) => {
                        // Not validating PID early is acceptable due to TOCTOU race
                        builder
                            .build()
                            .expect_err(&format!("Should fail to load topology from PID {pid}"));
                    }
                    Err(HybridError::Rust(FromPIDError(p))) => prop_assert_eq!(p, pid),
                    Err(other) => prop_assert!(false, "Unexpected error while loading topology from PID {pid}: {other}"),
                }
                Ok(())
            };

            // Try building from an invalid PID The fact that it does not error out
            // on Linux was confirmed to be expected by upstream at
            // https://github.com/open-mpi/hwloc/issues/624
            if cfg!(not(target_os = "linux")) {
                expect_fail(ProcessId::try_from(i32::MAX).expect("should be a 'valid' PID"))?;
            }

            // Building from this process' PID should be supported if building from
            // a PID is supported at all.
            let my_pid = std::process::id();

            // Windows and macOS do not seem to allow construction from PID at all
            let topology = if cfg!(any(windows, target_os = "macos")) {
                expect_fail(my_pid)?;
                return Ok(());
            } else {
                builder_from_pid(my_pid)?.unwrap().build().unwrap()
            };

            // Check topology building outcome
            check_topology(
                &topology,
                DataSource::ThisSystem,
                build_flags,
                default_type_filter,
            )?;
        }

        /// Test building from a Synthetic description
        #[test]
        fn from_synthetic(build_flags in valid_build_flags()) {
            // Attempt to configure a builder from a Synthetic string
            let builder_from_synthetic =
                |synthetic: &str| Ok::<_, TestCaseError>(builder_with_flags(build_flags)?.unwrap().from_synthetic(synthetic));

            // Try building from an invalid string with an inner NUL
            prop_assert!(matches!(
                builder_from_synthetic("\0")?,
                Err(StringInputError::ContainsNul)
            ));

            // Try building from an invalid string with unexpected text
            prop_assert!(matches!(
                builder_from_synthetic("ZaLgO")?,
                Err(StringInputError::Invalid)
            ));

            // Example from https://hwloc.readthedocs.io/en/stable/synthetic.html
            let synthetic = "Package:2 NUMANode:3 L2Cache:4 Core:5 PU:6";
            #[allow(clippy::wildcard_enum_match_arm)]
            let expected_object_count = |ty: ObjectType| match ty {
                ObjectType::Machine => 1,
                ObjectType::Package => 2,
                ObjectType::NUMANode | ObjectType::Group => 3 * 2,
                ObjectType::L2Cache => 4 * 3 * 2,
                ObjectType::Core => 5 * 4 * 3 * 2,
                ObjectType::PU => 6 * 5 * 4 * 3 * 2,
                _ => 0,
            };
            let topology = builder_from_synthetic(synthetic)?
                .unwrap()
                .build()
                .unwrap();
            check_topology(
                &topology,
                DataSource::Synthetic,
                build_flags,
                default_type_filter,
            )?;

            // Object counts can't be right if allowed resources are queried from
            // this system, since we're nothing like that synthetic topology
            #[allow(unused_mut)]
            let mut object_removal_flags = BuildFlags::GET_ALLOWED_RESOURCES_FROM_THIS_SYSTEM;
            #[cfg(feature = "hwloc-2_5_0")]
            {
                object_removal_flags |= BuildFlags::RESTRICT_CPU_TO_THIS_PROCESS
                    | BuildFlags::RESTRICT_MEMORY_TO_THIS_PROCESS;
            }
            if !build_flags.intersects(object_removal_flags) {
                for object_type in ObjectType::iter() {
                    prop_assert_eq!(
                        topology.objects_with_type(object_type).count(),
                        expected_object_count(object_type),
                        "Unexpected number of {} objects", object_type
                    );
                }
            }
        }

        /// Test round trip through XML as an XML import test
        #[test]
        fn from_xml(build_flags in valid_build_flags()) {
            // Try building from an invalid XML string
            match builder_with_flags(build_flags)?.unwrap().from_xml("<ZaLgO>") {
                Ok(builder) => {
                    builder
                        .build()
                        .expect_err("Should fail to load topology from invalid XML");
                }
                Err(StringInputError::Invalid) => {}
                Err(other) => prop_assert!(false, "Unexpected error while loading from invalid XML: {other}"),
            }

            // Use a default-built topology as our reference
            let default = builder_with_flags(build_flags)?.unwrap().build().unwrap();
            let check_xml_topology = |topology: &Topology| {
                check_topology(topology, DataSource::Xml, build_flags, default_type_filter)?;

                // There are e number of hwloc features that can cause the
                // topology built from XML to detect less objects than the
                // original topology. Detect them all.
                #[allow(unused_mut)]
                let mut default_is_superset = build_flags.contains(
                    BuildFlags::INCLUDE_DISALLOWED
                ) && build_flags.intersects(
                    BuildFlags::GET_ALLOWED_RESOURCES_FROM_THIS_SYSTEM
                );
                #[cfg(feature = "hwloc-2_5_0")]
                {
                    default_is_superset |= build_flags.intersects(
                        BuildFlags::RESTRICT_CPU_TO_THIS_PROCESS
                        | BuildFlags::RESTRICT_MEMORY_TO_THIS_PROCESS
                    );
                }

                for object_type in ObjectType::iter() {
                    let objects_gpids = |topology: &Topology| {
                        topology
                            .objects_with_type(object_type)
                            .map(TopologyObject::global_persistent_index)
                            .collect::<HashSet<_>>()
                    };
                    let topology_gpids = objects_gpids(topology);
                    let default_gpids = objects_gpids(&default);
                    if default_is_superset {
                        prop_assert!(topology_gpids.is_subset(&default_gpids));
                    } else {
                        prop_assert_eq!(topology_gpids, default_gpids);
                    }
                }
                Ok(())
            };

            // Test round trip through in-memory XML buffer
            {
                let xml = default.export_xml(XMLExportFlags::default()).unwrap();
                let topology = builder_with_flags(build_flags)?
                    .unwrap()
                    .from_xml(&xml)
                    .unwrap()
                    .build()
                    .unwrap();
                check_xml_topology(&topology)?;
            }

            // Test round trip through XML file
            {
                let path = NamedTempFile::new().unwrap().into_temp_path();
                default
                    .export_xml_file(Some(&path), XMLExportFlags::default())
                    .unwrap();
                let topology = builder_with_flags(build_flags)?
                    .unwrap()
                    .from_xml_file(path)
                    .unwrap()
                    .build()
                    .unwrap();
                check_xml_topology(&topology)?;
            }

            // Test invalid XML file load
            {
                let bad_path = NamedTempFile::new().unwrap().into_temp_path();
                let res = builder_with_flags(build_flags)?
                    .unwrap()
                    .from_xml_file(&bad_path);
                // For unknown reasons, hwloc does not always detect that the
                // XML file is empty ahead of time.
                if res.is_err() {
                    prop_assert!(matches!(
                        res,
                        Err(FileInputError::Invalid(path)) if *path == *bad_path,
                    ));
                } else {
                    prop_assert!(res.unwrap().build().is_err());
                }
            }
        }

        /// Add a targeted type filter
        #[test]
        fn with_type_filter(
            builder in builder_with_valid_flags(),
            object_type: ObjectType,
            filter: TypeFilter,
        ) {
            let build_flags = builder.flags();
            let result = builder.with_type_filter(object_type, filter);
            if object_type == ObjectType::Group
                && [TypeFilter::KeepAll, TypeFilter::KeepImportant].contains(&filter)
            {
                prop_assert!(matches!(
                    result,
                    Err(HybridError::Rust(TypeFilterError::CantKeepGroup))
                ));
            } else if [ObjectType::Machine, ObjectType::PU, ObjectType::NUMANode].contains(&object_type)
                && ![TypeFilter::KeepAll, TypeFilter::KeepImportant].contains(&filter)
            {
                prop_assert!(matches!(
                    result,
                    Err(HybridError::Rust(e)) if e == TypeFilterError::from(object_type)
                ));
            } else if filter == TypeFilter::KeepStructure
                && (object_type.is_io() || object_type == ObjectType::Misc)
            {
                prop_assert!(matches!(
                    result,
                    Err(HybridError::Rust(TypeFilterError::StructureIrrelevant))
                ));
            } else {
                let topology = result.unwrap().build().unwrap();
                let predicted_filter = |ty: ObjectType| {
                    if ty == object_type {
                        // Important is equivalent to All for Non-IO objects
                        if filter == TypeFilter::KeepImportant && !ty.is_io() {
                            Ok(TypeFilter::KeepAll)
                        } else {
                            Ok(filter)
                        }
                    } else {
                        default_type_filter(ty)
                    }
                };
                check_topology(
                    &topology,
                    DataSource::ThisSystem,
                    build_flags,
                    predicted_filter,
                )?;
            }
        }

        /// Add a common type filter
        #[test]
        fn with_common_type_filter(builder in builder_with_valid_flags(), filter: TypeFilter) {
            let build_flags = builder.flags();

            let topology = builder
                .with_common_type_filter(filter)
                .unwrap()
                .build()
                .unwrap();
            let predicted_filter = |ty: ObjectType| {
                let filter = if (ty == ObjectType::Group
                    && [TypeFilter::KeepAll, TypeFilter::KeepImportant].contains(&filter))
                    || [ObjectType::Machine, ObjectType::PU, ObjectType::NUMANode].contains(&ty)
                    || (filter == TypeFilter::KeepStructure && (ty.is_io() || ty == ObjectType::Misc))
                {
                    default_type_filter(ty)?
                } else if filter == TypeFilter::KeepImportant && !ty.is_io() {
                    let actual = topology.type_filter(ty).unwrap();
                    prop_assert!([TypeFilter::KeepAll, TypeFilter::KeepImportant].contains(&actual));
                    actual
                } else {
                    filter
                };
                Ok(filter)
            };

            check_topology(
                &topology,
                DataSource::ThisSystem,
                build_flags,
                predicted_filter,
            )?;
        }

        /// Add a CPU cache type filter
        #[test]
        fn with_cpu_cache_type_filter(builder in builder_with_valid_flags(), filter: TypeFilter) {
            let build_flags = builder.flags();

            let topology = builder
                .with_cpu_cache_type_filter(filter)
                .unwrap()
                .build()
                .unwrap();
            let predicted_filter = |ty: ObjectType| {
                if ty.is_cpu_cache() {
                    if filter == TypeFilter::KeepImportant {
                        Ok(TypeFilter::KeepAll)
                    } else {
                        Ok(filter)
                    }
                } else {
                    default_type_filter(ty)
                }
            };

            check_topology(
                &topology,
                DataSource::ThisSystem,
                build_flags,
                predicted_filter,
            )?;
        }

        /// Add a CPU instruction cache type filter
        #[test]
        fn with_cpu_icache_type_filter(builder in builder_with_valid_flags(), filter: TypeFilter) {
            let build_flags = builder.flags();

            let topology =
                builder
                .with_cpu_icache_type_filter(filter)
                .unwrap()
                .build()
                .unwrap();
            let predicted_filter = |ty: ObjectType| {
                if ty.is_cpu_instruction_cache() {
                    if filter == TypeFilter::KeepImportant {
                        Ok(TypeFilter::KeepAll)
                    } else {
                        Ok(filter)
                    }
                } else {
                    default_type_filter(ty)
                }
            };

            check_topology(
                &topology,
                DataSource::ThisSystem,
                build_flags,
                predicted_filter,
            )?;
        }

        /// Add an I/O object type filter
        #[test]
        fn with_io_type_filter(builder in builder_with_valid_flags(), filter: TypeFilter) {
            let build_flags = builder.flags();

            let result = builder.with_io_type_filter(filter);
            if filter == TypeFilter::KeepStructure {
                prop_assert!(matches!(
                    result,
                    Err(HybridError::Rust(TypeFilterError::StructureIrrelevant))
                ));
            } else {
                let topology = result.unwrap().build().unwrap();
                let predicted_filter = |ty: ObjectType| {
                    if ty.is_io() {
                        Ok(filter)
                    } else {
                        default_type_filter(ty)
                    }
                };
                check_topology(
                    &topology,
                    DataSource::ThisSystem,
                    build_flags,
                    predicted_filter,
                )?;
            }
        }

        /// Disable every non-essential component for default discovery
        #[cfg(feature = "hwloc-2_1_0")]
        #[test]
        fn without_components(builder in builder_with_valid_flags()) {
            let build_flags = builder.flags();
            let topology = builder
                .without_component("synthetic")
                .unwrap()
                .without_component("xml")
                .unwrap()
                .build()
                .unwrap();
            check_topology(
                &topology,
                DataSource::ThisSystem,
                build_flags,
                default_type_filter,
            )?;
        }
    }
}
