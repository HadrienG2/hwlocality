//! Rust Bindings for the Hwloc library
//!
//! This library is a rust binding to the hwloc C library, which provides a portable abstraction
//! of the hierarchical topology of modern architectures, including NUMA memory nodes, sockets,
//! shared caches, cores and simultaneous multithreading.
//!
//! # Usage
//!
//! First, add the following to your `Cargo.toml`:
//!
//! FIXME: This is outdated
//!
//! ```toml
//! [dependencies]
//! hwloc = "0.3.0"
//! ```
//!
//! Here is a quick example which walks the `Topology` and prints it out:
//!
//! ```no_run
//! use hwloc2::Topology;
//!
//! fn main() {
//! 	let topo = Topology::new().unwrap();
//!
//! 	for i in 0..topo.depth() {
//! 		println!("*** Objects at level {}", i);
//!
//! 		for (idx, object) in topo.objects_at_depth(i).iter().enumerate() {
//! 			println!("{}: {}", idx, object);
//! 		}
//! 	}
//! }
//! ```
//!
//! You can also [look at](https://github.com/daschl/hwloc-rs/tree/master/examples)
//! more examples, if you want to run them check out the next section below.
//!
//! # Running Examples
//! The library ships with examples, and to run them you need to clone the repository
//! and then run them through `cargo run --example=`.
//!
//! ```bash
//! $ git clone https://github.com/daschl/hwloc-rs.git
//! $ cd hwloc-rs
//! ```
//!
//! To run an example (which will download the dependencies and build it) you can
//! use `cargo run -example=`:
//!
//! ```bash
//! $ cargo run --example=walk_tree
//!    Compiling libc v0.2.3
//!    ...
//!    Compiling hwloc v0.2.0 (file:///vagrant/hwloc-rs)
//!      Running `target/debug/examples/walk_tree`
//! *** Printing overall tree
//! Machine (490MB): #0
//!  Socket (): #0
//!   L2d (6144KB): #4294967295
//!    L1d (32KB): #4294967295
//!     Core (): #0
//!      PU (): #0
//!   L1d (32KB): #4294967295
//!     Core (): #1
//!      PU (): #1
//! ```
//!
//! # License
//! This project uses the MIT license, please see the
//! [LICENSE](https://github.com/daschl/hwloc-rs/blob/master/LICENSE) file for more
//! information.

// TODO: Remove this once the crate is in a better shape
#![allow(dead_code)]

pub mod bitmap;
pub mod depth;
mod ffi;
pub mod objects;
pub mod support;

use self::{
    bitmap::CpuSet,
    depth::{Depth, DepthError, DepthResult, RawDepth},
    objects::{
        types::{ObjectType, RawObjectType},
        TopologyObject,
    },
    support::TopologySupport,
};
use bitflags::bitflags;
use errno::{errno, Errno};
use libc::c_ulong;
use num_enum::TryFromPrimitiveError;
use std::{
    convert::TryInto,
    marker::{PhantomData, PhantomPinned},
    ptr::NonNull,
};

/// Indicate at runtime which hwloc API version was used at build time.
/// This number is updated to (X<<16)+(Y<<8)+Z when a new release X.Y.Z
/// actually modifies the API.
///
/// Users may check for available features at build time using this number
pub fn get_api_version() -> u32 {
    unsafe { ffi::hwloc_get_api_version() as u32 }
}

/// Opaque topology struct
///
/// Represents the private `hwloc_topology_s` type that `hwloc_topology_t` API
/// pointers map to.
#[repr(C)]
pub(crate) struct RawTopology {
    _data: [u8; 0],
    _marker: PhantomData<(*mut u8, PhantomPinned)>,
}

pub struct Topology(NonNull<RawTopology>);

impl Topology {
    // ### FIXME: Not refactored yet ###

    /// Creates a new Topology.
    ///
    /// If no further customization is needed on init, this method
    /// represents the main entry point. A topology is returned
    /// which contains the logical representation of the physical
    /// hardware.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::Topology;
    ///
    /// let topology = Topology::new().unwrap();
    /// ```
    ///
    pub fn new() -> Result<Topology, Errno> {
        let builder = TopologyBuilder::new().expect("Failed to allocate topology");
        builder.build()
    }

    /// Prepare to create a Topology with custom configuration
    pub fn builder() -> Option<TopologyBuilder> {
        TopologyBuilder::new()
    }

    /// Retrieve the topology support
    ///
    /// This documents which hwloc features are supported by the current
    /// topology on the current machine
    pub fn support(&self) -> &TopologySupport {
        let ptr = unsafe { ffi::hwloc_topology_get_support(self.as_ptr()) };
        assert!(
            !ptr.is_null(),
            "Got null pointer from hwloc_topology_get_support"
        );
        // This is correct because the output reference will be bound the the
        // lifetime of &self by the borrow checker.
        unsafe { &*ptr }
    }

    /// Flags that were used to build this topology
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::{Topology,TopologyFlag};
    ///
    /// let default_topology = Topology::new().unwrap();
    /// assert_eq!(0, default_topology.flags().len());
    ///
    /// let topology_with_flags = Topology::with_flags(vec![TopologyFlag::IsThisSystem]).unwrap();
    /// assert_eq!(vec![TopologyFlag::IsThisSystem], topology_with_flags.flags());
    /// ```
    pub fn build_flags(&self) -> TopologyFlags {
        TopologyFlags::from_bits(unsafe { ffi::hwloc_topology_get_flags(self.as_ptr()) })
            .expect("Encountered unexpected topology flags")
    }

    // === Object levels, depths and types: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__levels.html ===

    /// Full depth of the topology.
    ///
    /// In practice, the full depth of the topology equals the depth of the
    /// `ObjectType::PU` plus one.
    ///
    /// The full topology depth is useful to know if one needs to manually
    /// traverse the complete topology.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::Topology;
    ///
    /// let topology = Topology::new().unwrap();
    /// assert!(topology.depth() > 0);
    /// ```
    pub fn depth(&self) -> u32 {
        unsafe { ffi::hwloc_topology_get_depth(self.as_ptr()) }
            .try_into()
            .expect("Got unexpected depth from hwloc_topology_get_depth")
    }

    /// Depth of parents where memory objects are attached
    pub fn memory_parents_depth(&self) -> DepthResult {
        Depth::try_from(unsafe { ffi::hwloc_get_memory_parents_depth(self.as_ptr()) })
    }

    /// Depth for the given `ObjectType`
    ///
    /// # Errors
    ///
    /// This will return `Err(DepthError::None)` if no object of this type
    /// is present or if the OS doesn't provide this kind of information. If a
    /// similar type is acceptable, consider using `depth_of_below_for_type()`
    /// or `depth_or_above_for_type()` instead.
    ///
    /// You will also get `Err(DepthError::Multiple)` if objects of this type
    /// exist at multiple depths.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::{Topology,ObjectType};
    ///
    /// let topology = Topology::new().unwrap();
    ///
    /// let machine_depth = topology.depth_for_type(ObjectType::Machine).unwrap();
    /// let pu_depth = topology.depth_for_type(ObjectType::PU).unwrap();
    /// assert!(machine_depth < pu_depth);
    /// ```
    ///
    pub fn depth_for_type(&self, object_type: ObjectType) -> DepthResult {
        Depth::try_from(unsafe { ffi::hwloc_get_type_depth(self.as_ptr(), object_type.into()) })
    }

    /// Depth for the given `ObjectType` or below
    ///
    /// If no object of this type is present on the underlying architecture, the
    /// function returns the depth of the first "present" object typically found
    /// inside `object_type`.
    ///
    /// # Errors
    ///
    /// This function is only meaningful for normal object types.
    ///
    /// You will get `Err(DepthError::Multiple)` if objects of this type or
    /// higher-depth types exist at multiple depths.
    pub fn depth_or_below_for_type(&self, object_type: ObjectType) -> DepthResult {
        assert!(
            object_type.is_normal(),
            "This is only meaningful for normal objects"
        );
        match self.depth_for_type(object_type) {
            Ok(d) => Ok(d),
            Err(DepthError::None) => {
                let pu_depth = self.depth_for_type(ObjectType::PU)?.assert_normal();
                for depth in (0..pu_depth).rev() {
                    if self
                        .type_at_depth(depth.into())
                        .expect("Depths above PU depth should exist")
                        < object_type
                    {
                        return Ok(Depth::Normal(depth + 1));
                    }
                }
                Err(DepthError::None)
            }
            Err(e) => Err(e),
        }
    }

    /// Depth for the given `ObjectType` or above
    ///
    /// If no object of this type is present on the underlying architecture, the
    /// function returns the depth of the first "present" object typically
    /// containing `object_type`.
    ///
    /// This function is only meaningful for normal object types.
    pub fn depth_or_above_for_type(&self, object_type: ObjectType) -> DepthResult {
        assert!(
            object_type.is_normal(),
            "This is only meaningful for normal objects"
        );
        match self.depth_for_type(object_type) {
            Ok(d) => Ok(d),
            Err(DepthError::None) => {
                for depth in (0..self.depth()).rev() {
                    if self
                        .type_at_depth(depth.into())
                        .expect("Depths above bottom depth should exist")
                        > object_type
                    {
                        return Ok(Depth::Normal(depth - 1));
                    }
                }
                Err(DepthError::None)
            }
            Err(e) => Err(e),
        }
    }

    /// `ObjectType` at the given depth.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::{Topology,ObjectType};
    ///
    /// let topology = Topology::new().unwrap();
    ///
    /// // Load depth for PU to assert against
    /// let pu_depth = topology.depth_for_type(ObjectType::PU).unwrap();
    /// // Retrieve the type for the given depth
    /// assert_eq!(ObjectType::PU, topology.type_at_depth(pu_depth));
    /// ```
    ///
    pub fn type_at_depth(&self, depth: Depth) -> Option<ObjectType> {
        if let Depth::Normal(depth) = depth {
            if depth >= self.depth() {
                return None;
            }
        }
        match unsafe { ffi::hwloc_get_depth_type(self.as_ptr(), depth.into()) }.try_into() {
            Ok(depth) => Some(depth),
            Err(TryFromPrimitiveError {
                number: RawObjectType::MAX,
            }) => None,
            Err(unknown) => unreachable!("Got unknown object type {unknown}"),
        }
    }

    /// Number of objects at the given depth.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::Topology;
    ///
    /// let topology = Topology::new().unwrap();
    ///
    /// let topo_depth = topology.depth();
    /// assert!(topology.size_at_depth(topo_depth - 1) > 0);
    /// ```
    ///
    pub fn size_at_depth(&self, depth: Depth) -> u32 {
        unsafe { ffi::hwloc_get_nbobjs_by_depth(self.as_ptr(), depth.into()) }
    }

    /// `TopologyObject` at the root of the topology.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::{Topology,TopologyObject};
    ///
    /// let topology = Topology::new().unwrap();
    ///
    /// assert_eq!(topology.type_at_root(), topology.object_at_root().object_type());
    /// ```
    pub fn root_object(&self) -> &TopologyObject {
        self.objects_at_depth(0.into())
            .next()
            .expect("Root object should exist")
    }

    /// `TopologyObjects` with the given `ObjectType`.
    ///
    /// Like its hwloc equivalent, this operation is currently implemented using
    /// `depth_for_type()` and will fail for object types where `depth_for_type`
    /// is not defined.
    pub fn objects_with_type(
        &self,
        object_type: ObjectType,
    ) -> impl Iterator<Item = &TopologyObject> {
        let depth = self
            .depth_for_type(object_type)
            .expect("Type should exist at some depth");
        self.objects_at_depth(depth)
    }

    /// `TopologyObject`s at the given depth.
    pub fn objects_at_depth(&self, depth: Depth) -> impl Iterator<Item = &TopologyObject> {
        let size = self.size_at_depth(depth);
        let depth = RawDepth::from(depth);
        (0..size).map(move |idx| {
            let ptr = unsafe { ffi::hwloc_get_obj_by_depth(self.as_ptr(), depth, idx) };
            assert!(
                !ptr.is_null(),
                "Got null pointer from hwloc_get_obj_by_depth"
            );
            unsafe { &*ptr }
        })
    }

    // ### FIXME: Not refactored yet ###

    /// Binds the current process or thread on CPUs given in the `CpuSet`.
    pub fn set_cpubind(&mut self, set: &CpuSet, flags: CpuBindFlags) -> Result<(), CpuBindError> {
        let result =
            unsafe { ffi::hwloc_set_cpubind(self.as_mut_ptr(), set.as_ptr(), flags.bits()) };

        match result {
            r if r < 0 => {
                let e = errno();
                Err(CpuBindError::Generic(e.0, format!("{e}")))
            }
            _ => Ok(()),
        }
    }

    /// Get current process or thread binding.
    pub fn get_cpubind(&self, flags: CpuBindFlags) -> Option<CpuSet> {
        let mut cpuset = CpuSet::new();
        let res =
            unsafe { ffi::hwloc_get_cpubind(self.as_ptr(), cpuset.as_mut_ptr(), flags.bits()) };
        if res >= 0 {
            Some(cpuset)
        } else {
            None
        }
    }

    /// Binds a process (identified by its `pid`) on CPUs identified by the given `CpuSet`.
    pub fn set_cpubind_for_process(
        &mut self,
        pid: pid_t,
        set: &CpuSet,
        flags: CpuBindFlags,
    ) -> Result<(), CpuBindError> {
        let result = unsafe {
            ffi::hwloc_set_proc_cpubind(self.as_mut_ptr(), pid, set.as_ptr(), flags.bits())
        };

        match result {
            r if r < 0 => {
                let e = errno();
                Err(CpuBindError::Generic(e.0, format!("{e}")))
            }
            _ => Ok(()),
        }
    }

    /// Get the current physical binding of a process, identified by its `pid`.
    pub fn get_cpubind_for_process(&self, pid: pid_t, flags: CpuBindFlags) -> Option<CpuSet> {
        let mut cpuset = CpuSet::new();
        let res = unsafe {
            ffi::hwloc_get_proc_cpubind(self.as_ptr(), pid, cpuset.as_mut_ptr(), flags.bits())
        };
        if res >= 0 {
            Some(cpuset)
        } else {
            None
        }
    }

    /// Bind a thread (by its `tid`) on CPUs given in through the `CpuSet`.
    pub fn set_cpubind_for_thread(
        &mut self,
        tid: pthread_t,
        set: &CpuSet,
        flags: CpuBindFlags,
    ) -> Result<(), CpuBindError> {
        let result = unsafe {
            ffi::hwloc_set_thread_cpubind(self.as_mut_ptr(), tid, set.as_ptr(), flags.bits())
        };

        match result {
            r if r < 0 => {
                let e = errno();
                Err(CpuBindError::Generic(e.0, format!("{e}")))
            }
            _ => Ok(()),
        }
    }

    /// Get the current physical binding of thread `tid`.
    pub fn get_cpubind_for_thread(&self, tid: pthread_t, flags: CpuBindFlags) -> Option<CpuSet> {
        let mut cpuset = CpuSet::new();
        let res = unsafe {
            ffi::hwloc_get_thread_cpubind(self.as_ptr(), tid, cpuset.as_mut_ptr(), flags.bits())
        };
        if res >= 0 {
            Some(cpuset)
        } else {
            None
        }
    }

    /// Get the last physical CPU where the current process or thread ran.
    ///
    /// The operating system may move some tasks from one processor
    /// to another at any time according to their binding,
    /// so this function may return something that is already
    /// outdated.
    ///
    /// Flags can include either `CPUBIND_PROCESS` or `CPUBIND_THREAD` to
    /// specify whether the query should be for the whole process (union of all CPUs
    /// on which all threads are running), or only the current thread. If the
    /// process is single-threaded, flags can be set to zero to let hwloc use
    /// whichever method is available on the underlying OS.
    pub fn get_cpu_location(&self, flags: CpuBindFlags) -> Option<CpuSet> {
        let mut cpuset = CpuSet::new();
        let res = unsafe {
            ffi::hwloc_get_last_cpu_location(self.as_ptr(), cpuset.as_mut_ptr(), flags.bits())
        };
        if res >= 0 {
            Some(cpuset)
        } else {
            None
        }
    }

    /// Get the last physical CPU where a process ran.
    ///
    /// The operating system may move some tasks from one processor to another at any
    /// time according to their binding, so this function may return something that is
    /// already outdated.
    pub fn get_cpu_location_for_process(&self, pid: pid_t, flags: CpuBindFlags) -> Option<CpuSet> {
        let mut cpuset = CpuSet::new();
        let res = unsafe {
            ffi::hwloc_get_proc_last_cpu_location(
                self.as_ptr(),
                pid,
                cpuset.as_mut_ptr(),
                flags.bits(),
            )
        };
        if res >= 0 {
            Some(cpuset)
        } else {
            None
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

impl Drop for Topology {
    fn drop(&mut self) {
        unsafe { ffi::hwloc_topology_destroy(self.as_mut_ptr()) }
    }
}

unsafe impl Send for Topology {}
unsafe impl Sync for Topology {}

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
    /// use hwloc2::{Topology, TopologyFlag};
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
        let result = unsafe { ffi::hwloc_topology_load(self.as_mut_ptr()) };
        assert!(
            result == 0 || result == -1,
            "Unexpected hwloc_topology_load result {result}"
        );
        (result == 0).then_some(Topology(self.0)).ok_or_else(errno)
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
    /// Flags to be set onto a topology context during setup
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

// ### FIXME: Tidy up the following mess ###

#[allow(non_camel_case_types)]
#[cfg(target_os = "windows")]
pub type pthread_t = winapi::winnt::HANDLE;
#[allow(non_camel_case_types)]
#[cfg(target_os = "windows")]
pub type pid_t = winapi::minwindef::DWORD;
#[allow(non_camel_case_types)]
#[cfg(not(target_os = "windows"))]
pub type pthread_t = libc::pthread_t;
#[allow(non_camel_case_types)]
#[cfg(not(target_os = "windows"))]
pub type pid_t = libc::pid_t;

bitflags! {
    /// Process/Thread binding flags.
    ///
    /// These bit flags can be used to refine the binding policy.
    ///
    /// The default (Process) is to bind the current process, assumed to be
    /// single-threaded, in a non-strict way.  This is the most portable
    /// way to bind as all operating systems usually provide it.
    ///
    /// **Note:** Not all systems support all kinds of binding.
    ///
    /// The following flags (constants) are available:
    ///
    /// - **CPUBIND_PROCESS:** Bind all threads of the current (possibly) multithreaded process.
    /// - **CPUBIND_THREAD:** Bind current thread of current process.
    /// - **CPUBIND_STRICT:** Request for strict binding from the OS.
    /// - **CPUBIND_NO_MEMBIND:** Avoid any effect on memory binding.
    #[repr(C)]
    pub struct CpuBindFlags: i32 {
        /// Bind all threads of the current (possibly) multithreaded process.
        const CPUBIND_PROCESS = (1<<0);
        /// Bind current thread of current process.
        const CPUBIND_THREAD  = (1<<1);
        /// Request for strict binding from the OS.
        const CPUBIND_STRICT = (1<<2);
        /// Avoid any effect on memory binding.
        const CPUBIND_NO_MEMBIND = (1<<3);
    }
}

#[derive(Debug)]
pub enum CpuBindError {
    Generic(i32, String),
}

// FIXME: Should not be bitflags, there's nothing flag-y about it
bitflags! {
    #[repr(C)]
    pub struct MemBindPolicy: i32 {
        /// Reset the memory allocation policy to the system default. Depending on the operating
        /// system, this may correspond to MEMBIND_FIRSTTOUCH (Linux), or MEMBIND_BIND (AIX,
        /// HP-UX, OSF, Solaris, Windows).
        const MEMBIND_DEFAULT = 0;
        /// Allocate memory but do not immediately bind it to a specific locality. Instead,
        /// each page in the allocation is bound only when it is first touched. Pages are
        /// individually bound to the local NUMA node of the first thread that touches it. If
        /// there is not enough memory on the node, allocation may be done in the specified
        /// cpuset before allocating on other nodes.
        const MEMBIND_FIRSTTOUCH = 1;
        /// Allocate memory on the specified nodes.
        const MEMBIND_BIND = 2;
        /// Allocate memory on the given nodes in an interleaved / round-robin manner.
        /// The precise layout of the memory across multiple NUMA nodes is OS/system specific.
        /// Interleaving can be useful when threads distributed across the specified NUMA nodes
        /// will all be accessing the whole memory range concurrently, since the interleave will
        /// then balance the memory references.
        const MEMBIND_INTERLEAVE = 3;
        /// For each page bound with this policy, by next time it is touched (and next time
        /// only), it is moved from its current location to the local NUMA node of the thread
        /// where the memory reference occurred (if it needs to be moved at all).
        const MEMBIND_NEXTTOUCH = 4;
        /// Returned by get_membind() functions when multiple threads or parts of a memory
        /// area have differing memory binding policies.
        const MEMBIND_MIXED = -1;
    }
}

// FIXME: Should not be a Rust enum
#[repr(C)]
pub enum TypeFilter {
    /// Keep all objects of this type
    KeepAll = 0,
    /// Ignore all objects of this type
    KeepNone = 1,
    /// Only ignore objects if their entire level does not bring any structure
    KeepStructure = 2,
    /// Only keep ilkely-important objects of the given type
    KeepImportant = 3,
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn should_set_and_get_flags() {
        let topo = Topology::builder()
            .unwrap()
            .with_flags(
                TopologyFlags::INCLUDE_DISALLOWED
                    | TopologyFlags::GET_ALLOWED_RESOURCES_FROM_THIS_SYSTEM,
            )
            .unwrap()
            .build()
            .unwrap();
        assert_eq!(
            TopologyFlags::INCLUDE_DISALLOWED
                | TopologyFlags::GET_ALLOWED_RESOURCES_FROM_THIS_SYSTEM,
            topo.build_flags()
        );
    }

    #[test]
    fn should_get_topology_depth() {
        let topo = Topology::new().unwrap();
        assert!(topo.depth() > 0);
    }

    #[test]
    fn should_match_types_and_their_depth() {
        let topo = Topology::new().unwrap();

        let pu_depth = topo.depth_for_type(ObjectType::PU).unwrap();
        assert!(pu_depth.assert_normal() > 0);
        assert_eq!(Some(ObjectType::PU), topo.type_at_depth(pu_depth));
    }

    #[test]
    fn should_get_nbobjs_by_depth() {
        let topo = Topology::new().unwrap();
        assert!(topo.size_at_depth(1.into()) > 0);
    }

    #[test]
    fn should_get_root_object() {
        let topo = Topology::new().unwrap();

        let root_obj = topo.root_object();
        assert_eq!(ObjectType::Machine, root_obj.object_type());
        assert!(root_obj.total_memory() > 0);
        assert_eq!(Depth::Normal(0), root_obj.depth());
        assert_eq!(0, root_obj.logical_index());
        println!("{root_obj}");
        assert!(root_obj.first_normal_child().is_some());
        assert!(root_obj.last_normal_child().is_some());
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn should_support_cpu_binding_on_linux() {
        let topo = Topology::new().unwrap();

        assert!(topo.support().cpu().set_current_process());
        assert!(topo.support().cpu().set_current_thread());
    }

    #[test]
    #[cfg(target_os = "freebsd")]
    fn should_support_cpu_binding_on_freebsd() {
        let topo = Topology::new().unwrap();

        assert!(topo.support().cpu().set_current_process());
        assert!(topo.support().cpu().set_current_thread());
    }

    #[test]
    #[cfg(target_os = "macos")]
    fn should_not_support_cpu_binding_on_macos() {
        let topo = Topology::new().unwrap();

        assert_eq!(false, topo.support().cpu().set_current_process());
        assert_eq!(false, topo.support().cpu().set_current_thread());
    }

    #[test]
    fn should_produce_cpubind_bitflags() {
        assert_eq!("1", format!("{:b}", CpuBindFlags::CPUBIND_PROCESS.bits()));
        assert_eq!("10", format!("{:b}", CpuBindFlags::CPUBIND_THREAD.bits()));
        assert_eq!("100", format!("{:b}", CpuBindFlags::CPUBIND_STRICT.bits()));
        assert_eq!(
            "101",
            format!(
                "{:b}",
                (CpuBindFlags::CPUBIND_STRICT | CpuBindFlags::CPUBIND_PROCESS).bits()
            )
        );
    }
}
