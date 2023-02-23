//! Topology building

#[cfg(doc)]
use crate::{editor::TopologyEditor, support::MiscSupport};
use crate::{
    ffi::{self, LibcString},
    objects::types::ObjectType,
    ProcessId, RawTopology, Topology,
};
use bitflags::bitflags;
use errno::{errno, Errno};
use libc::{EINVAL, ENOSYS};
use num_enum::{IntoPrimitive, TryFromPrimitive};
use std::{
    ffi::{c_int, c_ulong},
    fmt::Debug,
    path::Path,
    ptr::NonNull,
};
use thiserror::Error;

/// Mechanism to build a `Topology` with custom configuration
#[derive(Debug)]
pub struct TopologyBuilder(NonNull<RawTopology>);

/// # Topology building
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__creation.html
impl TopologyBuilder {
    /// Start building a [`Topology`]
    pub fn new() -> Self {
        let mut topology: *mut RawTopology = std::ptr::null_mut();
        let result = unsafe { ffi::hwloc_topology_init(&mut topology) };
        assert_ne!(result, -1, "Failed to allocate topology");
        assert_eq!(result, 0, "Unexpected hwloc_topology_init result {result}");
        Self(NonNull::new(topology).expect("Got null pointer from hwloc_topology_init"))
    }

    /// Load the topology with the previously specified parameters
    ///
    /// hwloc does not specify how this function can error out, but it usually
    /// sets Errno, hopefully you will find its value insightful...
    pub fn build(mut self) -> Result<Topology, Errno> {
        // Finalize the topology building
        let result = unsafe { ffi::hwloc_topology_load(self.as_mut_ptr()) };
        assert!(
            result == 0 || result == -1,
            "Unexpected hwloc_topology_load result {result} with errno {}",
            errno()
        );

        // If that was successful, transfer RawTopology ownership to a Topology
        if result == 0 {
            let result = Topology(self.0);
            std::mem::forget(self);
            Ok(result)
        } else {
            Err(errno())
        }
    }
}

/// # Discovery source
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__setsource.html
impl TopologyBuilder {
    /// Change which process the topology is viewed from
    ///
    /// On some systems, processes may have different views of the machine, for
    /// instance the set of allowed CPUs. By default, hwloc exposes the view
    /// from the current process. Calling this method permits to make it expose
    /// the topology of the machine from the point of view of another process.
    pub fn from_pid(mut self, pid: ProcessId) -> Result<Self, Unsupported> {
        let result = unsafe { ffi::hwloc_topology_set_pid(self.as_mut_ptr(), pid) };
        match result {
            0 => Ok(self),
            -1 => {
                let errno = errno();
                match errno.0 {
                    ENOSYS => Err(Unsupported),
                    _ => panic!("Unexpected errno {errno}"),
                }
            }
            other => panic!("Unexpected result {other} with errno {}", errno()),
        }
    }

    /// Read the topology from a synthetic textual description
    ///
    /// Instead of being probed from the host system, topology information will
    /// be read from the given
    /// [textual description](https://hwloc.readthedocs.io/en/v2.9/synthetic.html).
    ///
    /// Setting the environment variable `HWLOC_SYNTHETIC` may also result in
    /// this behavior.
    ///
    /// CPU and memory binding operations will be ineffective with this backend.
    pub fn from_synthetic(mut self, description: &str) -> Result<Self, InvalidParameter> {
        let Ok(description) = LibcString::new(description) else { return Err(InvalidParameter) };
        let result =
            unsafe { ffi::hwloc_topology_set_synthetic(self.as_mut_ptr(), description.borrow()) };
        match result {
            0 => Ok(self),
            -1 => {
                let errno = errno();
                match errno.0 {
                    EINVAL => Err(InvalidParameter),
                    _ => panic!("Unexpected errno {errno}"),
                }
            }
            other => panic!("Unexpected result {other} with errno {}", errno()),
        }
    }

    /// Read the topology from an XML description
    ///
    /// Instead of being probed from the host system, topology information will
    /// be read from the given
    /// [XML description](https://hwloc.readthedocs.io/en/v2.9/xml.html).
    ///
    /// CPU and memory binding operations will be ineffective with this backend,
    /// unless [`BuildFlags::ASSUME_THIS_SYSTEM`] is set to assert that the
    /// loaded XML file truly matches the underlying system.
    pub fn from_xml(mut self, xml: impl AsRef<str>) -> Result<Self, InvalidParameter> {
        let Ok(xml) = LibcString::new(xml) else { return Err(InvalidParameter) };
        let result = unsafe {
            ffi::hwloc_topology_set_xmlbuffer(
                self.as_mut_ptr(),
                xml.borrow(),
                xml.len()
                    .try_into()
                    .expect("XML buffer is too big for hwloc"),
            )
        };
        match result {
            0 => Ok(self),
            -1 => {
                let errno = errno();
                match errno.0 {
                    EINVAL => Err(InvalidParameter),
                    _ => panic!("Unexpected errno {errno}"),
                }
            }
            other => panic!("Unexpected result {other} with errno {}", errno()),
        }
    }

    /// Read the topology from an XML file
    ///
    /// This works a lot like [`TopologyBuilder::from_xml()`], but takes a file
    /// name as a parameter instead of an XML string. The same effect can be
    /// achieved by setting the `HWLOC_XMLFILE` environment variable.
    pub fn from_xml_file(mut self, path: impl AsRef<Path>) -> Result<Self, InvalidParameter> {
        let Some(path) = path.as_ref().to_str() else { return Err(InvalidParameter) };
        let Ok(path) = LibcString::new(path) else { return Err(InvalidParameter) };
        let result = unsafe { ffi::hwloc_topology_set_xml(self.as_mut_ptr(), path.borrow()) };
        match result {
            0 => Ok(self),
            -1 => {
                let errno = errno();
                match errno.0 {
                    EINVAL => Err(InvalidParameter),
                    _ => panic!("Unexpected errno {errno}"),
                }
            }
            other => panic!("Unexpected result {other} with errno {}", errno()),
        }
    }

    /// Prevent a discovery component from being used for a topology
    ///
    /// `name` is the name of the discovery component that should not be used
    /// when loading topology topology. The name is a string such as "cuda".
    /// For components with multiple phases, it may also be suffixed with the
    /// name of a phase, for instance "linux:io". A list of components
    /// distributed with hwloc can be found
    /// [in the hwloc documentation](https://hwloc.readthedocs.io/en/v2.9/plugins.html#plugins_list).
    ///
    /// This may be used to avoid expensive parts of the discovery process. For
    /// instance, CUDA-specific discovery may be expensive and unneeded while
    /// generic I/O discovery could still be useful.
    pub fn blacklist_component(mut self, name: &str) -> Result<Self, InvalidParameter> {
        let Ok(name) = LibcString::new(name) else { return Err(InvalidParameter) };
        let result = unsafe {
            ffi::hwloc_topology_set_components(
                self.as_mut_ptr(),
                ComponentsFlags::BLACKLIST.bits(),
                name.borrow(),
            )
        };
        assert!(
            result >= 0,
            "Unexpected result {result} with errno {}",
            errno()
        );
        Ok(self)
    }
}

/// # Detection configuration and query
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__configuration.html
impl TopologyBuilder {
    /// Set topology building flags
    ///
    /// If this function is called multiple times, the last invocation will
    /// erase and replace the set of flags that was previously set.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::{Topology, builder::BuildFlags};
    ///
    /// let topology = Topology::builder()
    ///                         .with_flags(BuildFlags::ASSUME_THIS_SYSTEM).unwrap()
    ///                         .build().unwrap();
    /// ```
    ///
    pub fn with_flags(mut self, flags: BuildFlags) -> Result<Self, InvalidParameter> {
        if !flags.is_valid() {
            return Err(InvalidParameter);
        }
        let result = unsafe { ffi::hwloc_topology_set_flags(self.as_mut_ptr(), flags.bits()) };
        match result {
            0 => Ok(self),
            -1 => {
                let errno = errno();
                match errno.0 {
                    EINVAL => Err(InvalidParameter),
                    _ => panic!("Unexpected errno {errno}"),
                }
            }
            other => panic!("Unexpected result {other} with errno {}", errno()),
        }
    }

    /// Check current topology building flags
    pub fn flags(&self) -> BuildFlags {
        let result =
            BuildFlags::from_bits_truncate(unsafe { ffi::hwloc_topology_get_flags(self.as_ptr()) });
        debug_assert!(result.is_valid());
        result
    }

    /// Set the filtering for the given object type
    pub fn with_type_filter(mut self, ty: ObjectType, filter: TypeFilter) -> Self {
        let result = unsafe {
            ffi::hwloc_topology_set_type_filter(self.as_mut_ptr(), ty.into(), filter.into())
        };
        assert!(
            result >= 0,
            "Unexpected result from hwloc_topology_set_type_filter"
        );
        self
    }

    /// Set the filtering for all object types
    ///
    /// If some types do not support this filtering, they are silently ignored.
    pub fn with_common_type_filter(mut self, filter: TypeFilter) -> Self {
        let result =
            unsafe { ffi::hwloc_topology_set_all_types_filter(self.as_mut_ptr(), filter.into()) };
        assert!(
            result >= 0,
            "Unexpected result from hwloc_topology_set_all_types_filter"
        );
        self
    }

    /// Set the filtering for all CPU cache object types
    ///
    /// Memory-side caches are not involved since they are not CPU caches.
    pub fn with_cache_type_filter(mut self, filter: TypeFilter) -> Self {
        let result =
            unsafe { ffi::hwloc_topology_set_cache_types_filter(self.as_mut_ptr(), filter.into()) };
        assert!(
            result >= 0,
            "Unexpected result from hwloc_topology_set_cache_types_filter"
        );
        self
    }

    /// Set the filtering for all CPU instruction cache object types
    ///
    /// Memory-side caches are not involved since they are not CPU caches.
    pub fn with_icache_type_filter(mut self, filter: TypeFilter) -> Self {
        let result = unsafe {
            ffi::hwloc_topology_set_icache_types_filter(self.as_mut_ptr(), filter.into())
        };
        assert!(
            result >= 0,
            "Unexpected result from hwloc_topology_set_icache_types_filter"
        );
        self
    }

    /// Set the filtering for all I/O object types
    pub fn with_io_type_filter(mut self, filter: TypeFilter) -> Self {
        let result =
            unsafe { ffi::hwloc_topology_set_io_types_filter(self.as_mut_ptr(), filter.into()) };
        assert!(
            result >= 0,
            "Unexpected result from hwloc_topology_set_io_types_filter"
        );
        self
    }

    /// Current filtering for the given object type
    pub fn type_filter(&self, ty: ObjectType) -> TypeFilter {
        let mut filter = RawTypeFilter::MAX;
        let result =
            unsafe { ffi::hwloc_topology_get_type_filter(self.as_ptr(), ty.into(), &mut filter) };
        assert!(
            result >= 0,
            "Unexpected result from hwloc_topology_get_type_filter"
        );
        TypeFilter::try_from(filter).expect("Unexpected type filter from hwloc")
    }
}

/// # General-purpose internal utilities
impl TopologyBuilder {
    /// Returns the contained hwloc topology pointer for interaction with hwloc.
    fn as_ptr(&self) -> *const RawTopology {
        self.0.as_ptr()
    }

    /// Returns the contained hwloc topology pointer for interaction with hwloc.
    fn as_mut_ptr(&mut self) -> *mut RawTopology {
        self.0.as_ptr()
    }
}

impl Default for TopologyBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for TopologyBuilder {
    fn drop(&mut self) {
        unsafe { ffi::hwloc_topology_destroy(self.as_mut_ptr()) }
    }
}

bitflags! {
    /// Topology building configuration flags
    #[repr(C)]
    pub struct BuildFlags: c_ulong {
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
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_INCLUDE_DISALLOWED")]
        const INCLUDE_DISALLOWED = (1<<0);

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
        const ASSUME_THIS_SYSTEM = (1<<1);

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
        const GET_ALLOWED_RESOURCES_FROM_THIS_SYSTEM = (1<<2);

        /// Import support from the imported topology
        ///
        /// When importing a XML topology from a remote machine, binding is
        /// disabled by default (see `ASSUME_THIS_SYSTEM`). This disabling is
        /// also marked by putting zeroes in the corresponding supported feature
        /// bits reported by [`Topology::support()`].
        ///
        /// The flag `IMPORT_SUPPORT` allows you to actually import support bits
        /// from the remote machine. It also sets the [`MiscSupport::imported()`]
        /// support flag. If the imported XML did not contain any support
        /// information (exporter hwloc is too old), this flag is not set.
        ///
        /// Note that these supported features are only relevant for the hwloc
        /// installation that actually exported the XML topology (it may vary
        /// with the operating system, or with how hwloc was compiled).
        ///
        /// Note that setting this flag however does not enable binding for the
        /// locally imported hwloc topology, it only reports what the remote
        /// hwloc and machine support.
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_IMPORT_SUPPORT")]
        const IMPORT_SUPPORT = (1<<3);

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
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_RESTRICT_TO_CPUBINDING")]
        const RESTRICT_CPU_TO_THIS_PROCESS = (1<<4);

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
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_RESTRICT_TO_MEMBINDING")]
        const RESTRICT_MEMORY_TO_THIS_PROCESS = (1<<5);

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
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_DONT_CHANGE_BINDING")]
        const DONT_CHANGE_BINDING = (1<<6);

        /// Ignore distances
        ///
        /// Ignore distance information from the operating systems (and from
        /// XML) and hence do not use distances for grouping.
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_NO_DISTANCES")]
        const IGNORE_DISTANCES = (1<<7);

        /// Ignore memory attributes
        ///
        /// Ignore memory attribues from the operating systems (and from XML).
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_NO_MEMATTRS")]
        const IGNORE_MEMORY_ATTRIBUTES = (1<<8);

        /// Ignore CPU Kinds
        ///
        /// Ignore CPU kind information from the operating systems (and from
        /// XML).
        #[doc(alias = "HWLOC_TOPOLOGY_FLAG_NO_CPUKINDS")]
        const IGNORE_CPU_KINDS = (1<<9);
    }
}
//
impl BuildFlags {
    /// Truth that these flags are in a valid state
    pub(crate) fn is_valid(self) -> bool {
        self.contains(Self::ASSUME_THIS_SYSTEM)
            || !self.intersects(
                Self::GET_ALLOWED_RESOURCES_FROM_THIS_SYSTEM
                    | Self::RESTRICT_CPU_TO_THIS_PROCESS
                    | Self::RESTRICT_MEMORY_TO_THIS_PROCESS,
            )
    }
}
//
impl Default for BuildFlags {
    fn default() -> Self {
        Self::empty()
    }
}

bitflags! {
    /// Flags to be passed to `hwloc_topology_set_components()`
    #[repr(C)]
    pub(crate) struct ComponentsFlags: c_ulong {
        /// Blacklist the target component from being used
        const BLACKLIST = (1<<0);
    }
}

/// Rust mapping of the hwloc_type_filter_e enum
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
///
pub(crate) type RawTypeFilter = c_int;

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
#[repr(i32)]
#[derive(Copy, Clone, Debug, Eq, Hash, IntoPrimitive, PartialEq, TryFromPrimitive)]
pub enum TypeFilter {
    /// Keep all objects of this type
    ///
    /// Cannot be set for [`ObjectType::Group`] (groups are designed only to add
    /// more structure to the topology).
    KeepAll = 0,

    /// Ignore all objects of this type
    ///
    /// The bottom-level type [`ObjectType::PU`], the [`ObjectType::NUMANode`]
    /// type, and the top-level type [`ObjectType::Machine`] may not be ignored.
    KeepNone = 1,

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
    KeepStructure = 2,

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
    KeepImportant = 3,
}

/// Error returned when an invalid parameter was passed
#[derive(Copy, Clone, Debug, Default, Eq, Error, PartialEq)]
#[error("invalid parameter specified")]
pub struct InvalidParameter;

/// Error returned when the platform does not support this feature
#[derive(Copy, Clone, Debug, Default, Eq, Error, PartialEq)]
#[error("platform does not support this feature")]
pub struct Unsupported;
