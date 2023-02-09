//! Topology building
//!
//! - Creation and destruction: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__creation.html
//! - Discovery source: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__setsource.html
//! - Detection configuration and query: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__configuration.html

use crate::{ffi, RawTopology, Topology};
use bitflags::bitflags;
use errno::{errno, Errno};
use std::{ffi::c_ulong, ptr::NonNull};

/// Mechanism to build a `Topology` with custom configuration
pub struct TopologyBuilder(NonNull<RawTopology>);

impl TopologyBuilder {
    /// Start building a `Topology`
    ///
    /// Returns None if hwloc failled to allocate a topology context.
    ///
    pub fn new() -> Option<Self> {
        let mut topology: *mut RawTopology = std::ptr::null_mut();
        let result = unsafe { ffi::hwloc_topology_init(&mut topology) };
        assert!(
            result == 0 || result == -1,
            "Unexpected hwloc_topology_init result {result}"
        );
        (result == 0).then(|| {
            Self(NonNull::new(topology).expect("Got null pointer from hwloc_topology_init"))
        })
    }

    /// Set topology building flags
    ///
    /// If this function is called multiple times, the last invocation will
    /// erase and replace the set of flags that was previously set.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::{Topology, TopologyFlags};
    ///
    /// let topology = Topology::builder().unwrap()
    ///                         .with_flags(TopologyFlags::ASSUME_THIS_SYSTEM).unwrap()
    ///                         .build().unwrap();
    /// ```
    ///
    pub fn with_flags(mut self, flags: TopologyFlags) -> Result<Self, Errno> {
        let result = unsafe { ffi::hwloc_topology_set_flags(self.as_mut_ptr(), flags.bits()) };
        (result >= 0).then_some(self).ok_or_else(errno)
    }

    /// Check current topology building flags
    pub fn flags(&self) -> TopologyFlags {
        TopologyFlags::from_bits(unsafe { ffi::hwloc_topology_get_flags(self.as_ptr()) })
            .expect("Encountered unexpected topology flags")
    }

    /// Load the topology with the previously specified parameters
    pub fn build(mut self) -> Result<Topology, Errno> {
        // Finalize the topology building
        let result = unsafe { ffi::hwloc_topology_load(self.as_mut_ptr()) };
        assert!(
            result == 0 || result == -1,
            "Unexpected hwloc_topology_load result {result}"
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

    /// Returns the contained hwloc topology pointer for interaction with hwloc.
    fn as_ptr(&self) -> *const RawTopology {
        self.0.as_ptr() as *const RawTopology
    }

    /// Returns the contained hwloc topology pointer for interaction with hwloc.
    fn as_mut_ptr(&mut self) -> *mut RawTopology {
        self.0.as_ptr()
    }
}

impl Drop for TopologyBuilder {
    fn drop(&mut self) {
        unsafe { ffi::hwloc_topology_destroy(self.as_mut_ptr()) }
    }
}

bitflags! {
    /// Topology building configuration flags (aka `hwloc_topology_flags_e`)
    #[repr(C)]
    pub struct TopologyFlags: c_ulong {
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
        /// `Topology::allowed_cpuset()` and `Topology::allowed_nodeset()` are
        /// equal to the root object cpuset and nodeset.
        ///
        /// When this flag is set, the actual sets of allowed PUs and NUMA nodes
        /// are given by `Topology::allowed_cpuset()` and
        /// `Topology::allowed_nodeset()`. They may be smaller than the root
        /// object cpuset and nodeset.
        ///
        /// If the current topology is exported to XML and reimported later,
        /// this flag should be set again in the reimported topology so that
        /// disallowed resources are reimported as well.
        const INCLUDE_DISALLOWED = (1<<0);

        /// Assume that the selected backend provides the topology for the
        /// system on which we are running
        ///
        /// This forces hwloc_topology_is_thissystem() to return 1, i.e. makes
        /// hwloc assume that the selected backend provides the topology for the
        /// system on which we are running, even if it is not the OS-specific
        /// backend but the XML backend for instance. This means making the
        /// binding functions actually call the OS-specific system calls and
        /// really do binding, while the XML backend would otherwise provide
        /// empty hooks just returning success.
        ///
        /// Setting the environment variable HWLOC_THISSYSTEM may also result in
        /// the same behavior.
        ///
        /// This can be used for efficiency reasons to first detect the topology
        /// once, save it to an XML file, and quickly reload it later through
        /// the XML backend, but still having binding functions actually do bind.
        const ASSUME_THIS_SYSTEM = (1<<1); // aka HWLOC_TOPOLOGY_FLAG_IS_THISSYSTEM

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
        /// This flag is ignored unless `ASSUME_THIS_SYSTEM` is also set since
        /// the loaded topology must match the underlying machine where
        /// restrictions will be gathered from.
        ///
        /// Setting the environment variable HWLOC_THISSYSTEM_ALLOWED_RESOURCES
        /// would result in the same behavior.
        const GET_ALLOWED_RESOURCES_FROM_THIS_SYSTEM = (1<<2); // aka HWLOC_TOPOLOGY_FLAG_THISSYSTEM_ALLOWED_RESOURCES

        /// Import support from the imported topology
        ///
        /// When importing a XML topology from a remote machine, binding is
        /// disabled by default (see `ASSUME_THIS_SYSTEM`). This disabling is
        /// also marked by putting zeroes in the corresponding supported feature
        /// bits reported by `Topology::support()`.
        ///
        /// The flag `IMPORT_SUPPORT` allows you to actually import support bits
        /// from the remote machine. It also sets the flag imported_support in
        /// the struct hwloc_topology_misc_support array (TODO: adapt to binding).
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
        const IMPORT_SUPPORT = (1<<3);

        /// Do not consider resources outside of the process CPU binding
        ///
        /// If the binding of the process is limited to a subset of cores,
        /// ignore the other cores during discovery.
        ///
        /// The resulting topology is identical to what a call to
        /// hwloc_topology_restrict() (TODO: adapt to binding) would generate,
        /// but this flag also prevents hwloc from ever touching other resources
        /// during the discovery.
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
        /// This flag requires `ASSUME_THIS_SYSTEM as well since binding support
        /// is required.
        const RESTRICT_CPU_TO_THIS_PROCESS = (1<<4); // aka HWLOC_TOPOLOGY_FLAG_RESTRICT_TO_CPUBINDING

        /// Do not consider resources outside of the process memory binding
        ///
        /// If the binding of the process is limited to a subset of NUMA nodes,
        /// ignore the other NUMA nodes during discovery.
        ///
        /// The resulting topology is identical to what a call to
        /// hwloc_topology_restrict() (TODO: adapt to binding) would generate,
        /// but this flag also prevents hwloc from ever touching other resources
        /// during the discovery.
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
        const RESTRICT_MEMORY_TO_THIS_PROCESS = (1<<5); // aka HWLOC_TOPOLOGY_FLAG_RESTRICT_TO_MEMBINDING

        /// Do not ever modify the process or thread binding during discovery
        ///
        /// This flag disables all hwloc discovery steps that require a change
        /// of the process or thread binding. This currently only affects the
        /// x86 backend which gets entirely disabled.
        ///
        /// This is useful when a `Topology` is loaded while the application
        /// also creates additional threads or modifies the binding.
        ///
        /// This flag is also a strict way to make sure the process binding will
        /// not change to due thread binding changes on Windows (see
        /// `RESTRICT_CPU_TO_THIS_PROCESS`).
        const DONT_CHANGE_BINDING = (1<<6);

        /// Ignore distances
        ///
        /// Ignore distance information from the operating systems (and from
        /// XML) and hence do not use distances for grouping.
        const IGNORE_DISTANCES = (1<<7); // aka HWLOC_TOPOLOGY_FLAG_NO_DISTANCES

        /// Ignore memory attributes
        ///
        /// Ignore memory attribues from the operating systems (and from XML).
        const IGNORE_MEMORY_ATTRIBUTES = (1<<8); // aka HWLOC_TOPOLOGY_FLAG_NO_MEMATTRS

        /// Ignore CPU Kinds
        ///
        /// Ignore CPU kind information from the operating systems (and from
        /// XML).
        const IGNORE_CPU_KINDS = (1<<9); // aka HWLOC_TOPOLOGY_FLAG_NO_CPUKINDS
    }
}

impl Default for TopologyFlags {
    fn default() -> Self {
        Self::empty()
    }
}
