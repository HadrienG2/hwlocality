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
//! ```toml
//! [dependencies]
//! hwloc2 = "2.2.0"
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
//! 		for (idx, object) in topo.objects_at_depth(i.into()).enumerate() {
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

pub mod bitmap;
pub mod builder;
pub mod cpu;
pub mod depth;
mod ffi;
pub mod memory;
pub mod objects;
pub mod support;

use crate::{ffi::hwloc_get_membind, memory::RawMemoryBindingPolicy};

use self::{
    bitmap::{CpuSet, RawBitmap},
    builder::{BuildFlags, TopologyBuilder},
    cpu::{CpuBindingError, CpuBindingFlags},
    depth::{Depth, DepthError, DepthResult, RawDepth},
    objects::{
        types::{ObjectType, RawObjectType},
        TopologyObject,
    },
    support::TopologySupport,
};
use bitmap::Bitmap;
use errno::{errno, Errno};
use libc::EINVAL;
use memory::{
    Bytes, MemoryBindingFlags, MemoryBindingPolicy, MemoryBindingQueryError,
    MemoryBindingSetupError,
};
use num_enum::TryFromPrimitiveError;
use std::{
    convert::TryInto,
    marker::{PhantomData, PhantomPinned},
    mem::MaybeUninit,
    ptr::NonNull,
};

#[cfg(target_os = "windows")]
/// Thread identifier
pub type ThreadID = winapi::winnt::HANDLE;
#[cfg(target_os = "windows")]
/// Process identifier
pub type ProcessID = winapi::minwindef::DWORD;
#[cfg(not(target_os = "windows"))]
/// Thread identifier
pub type ThreadID = libc::pthread_t;
#[cfg(not(target_os = "windows"))]
/// Process identifier
pub type ProcessID = libc::pid_t;

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

/// Main entry point to the hwloc API
pub struct Topology(NonNull<RawTopology>);

impl Topology {
    // === Topology building: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__creation.html ===

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
        TopologyBuilder::new().build()
    }

    /// Prepare to create a Topology with custom configuration
    pub fn builder() -> TopologyBuilder {
        TopologyBuilder::new()
    }

    /// Check that this topology is compatible with the current hwloc library
    ///
    /// This is useful when using the same topology structure (in memory) in
    /// different libraries that may use different hwloc installations (for
    /// instance if one library embeds a specific version of hwloc, while
    /// another library uses a default system-wide hwloc installation).
    ///
    /// If all libraries/programs use the same hwloc installation, this function
    /// always returns success.
    pub fn is_abi_compatible(&self) -> bool {
        let result = unsafe { ffi::hwloc_topology_abi_check(self.as_ptr()) };
        match result {
            0 => true,
            -1 => {
                let errno = errno();
                assert_eq!(errno.0, EINVAL, "Unexpected errno from hwloc {errno}");
                false
            }
            other => unreachable!("Unexpected hwloc return value {other}"),
        }
    }

    // === Topology Detection Configuration and Query: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__configuration.html ===

    /// Flags that were used to build this topology
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::{Topology, builder::BuildFlags};
    ///
    /// let default_topology = Topology::new().unwrap();
    /// assert_eq!(BuildFlags::empty(), default_topology.build_flags());
    ///
    /// let topology_with_flags =
    ///     Topology::builder()
    ///         .with_flags(BuildFlags::ASSUME_THIS_SYSTEM).unwrap()
    ///         .build().unwrap();
    /// assert_eq!(
    ///     BuildFlags::ASSUME_THIS_SYSTEM,
    ///     topology_with_flags.build_flags()
    /// );
    /// ```
    pub fn build_flags(&self) -> BuildFlags {
        BuildFlags::from_bits(unsafe { ffi::hwloc_topology_get_flags(self.as_ptr()) })
            .expect("Encountered unexpected topology flags")
    }

    /// Supported hwloc features with this topology on this machine
    ///
    /// This is the information that one gets via the `hwloc-info --support` CLI.
    ///
    /// The reported features are what the current topology supports on the
    /// current machine. If the topology was exported to XML from another
    /// machine and later imported here, support still describes what is
    /// supported for this imported topology after import. By default, binding
    /// will be reported as unsupported in this case (see
    /// `BuildFlags::ASSUME_THIS_SYSTEM`).
    ///
    /// `BuildFlags::IMPORT_SUPPORT` may be used during topology building to
    /// report the supported features of the original remote machine instead. If
    /// it was successfully imported, `MiscSupport::imported()` will be set.
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
    /// You will get `Err(DepthError::Multiple)` if objects of this type
    /// exist at multiple depths.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::{Topology, objects::types::ObjectType};
    ///
    /// let topology = Topology::new().unwrap();
    ///
    /// let machine_depth = topology.depth_for_type(ObjectType::Machine).unwrap();
    /// let pu_depth = topology.depth_for_type(ObjectType::PU).unwrap();
    /// assert!(machine_depth.assume_normal() < pu_depth.assume_normal());
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
    /// exist at multiple depths.
    pub fn depth_or_below_for_type(&self, object_type: ObjectType) -> DepthResult {
        assert!(
            object_type.is_normal(),
            "This is only meaningful for normal objects"
        );
        match self.depth_for_type(object_type) {
            Ok(d) => Ok(d),
            Err(DepthError::None) => {
                let pu_depth = self
                    .depth_for_type(ObjectType::PU)
                    .expect("PU objects should be present")
                    .assume_normal();
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
    /// # Errors
    ///
    /// This function is only meaningful for normal object types.
    ///
    /// You will get `Err(DepthError::Multiple)` if objects of this type or
    /// exist at multiple depths.
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
    /// use hwloc2::{Topology, objects::types::ObjectType};
    ///
    /// let topology = Topology::new().unwrap();
    ///
    /// // Load depth for PU to assert against
    /// let pu_depth = topology.depth_for_type(ObjectType::PU).unwrap();
    /// // Retrieve the type for the given depth
    /// assert_eq!(ObjectType::PU, topology.type_at_depth(pu_depth).unwrap());
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
    /// assert!(topology.size_at_depth((topo_depth - 1).into()) > 0);
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
    /// use hwloc2::Topology;
    ///
    /// let topology = Topology::new().unwrap();
    ///
    /// assert_eq!(
    ///     topology.type_at_depth(0.into()).unwrap(),
    ///     topology.root_object().object_type()
    /// );
    /// ```
    pub fn root_object(&self) -> &TopologyObject {
        self.objects_at_depth(0.into())
            .next()
            .expect("Root object should exist")
    }

    /// `TopologyObjects` with the given `ObjectType`.
    pub fn objects_with_type(&self, object_type: ObjectType) -> Vec<&TopologyObject> {
        match self.depth_for_type(object_type) {
            Ok(depth) => {
                // Fast path where the type only exists at one depth
                self.objects_at_depth(depth).collect()
            }
            Err(DepthError::None) => Vec::new(),
            Err(DepthError::Multiple) => {
                // Slow path where all depths must be probed
                let mut result = Vec::new();
                for depth in 0..self.depth() {
                    let depth = Depth::from(depth);
                    if self.type_at_depth(depth).expect("Depth should exist") == object_type {
                        result.extend(self.objects_at_depth(depth));
                    }
                }
                result
            }
            Err(e @ DepthError::Unknown(_)) => panic!("{e}"),
        }
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

    // === CPU binding: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpubinding.html ===

    /// Binds the current process or thread on given CPUs
    ///
    /// Some operating systems only support binding threads or processes to a
    /// single PU. Others allow binding to larger sets such as entire Cores or
    /// Packages or even random sets of individual PUs. In such operating
    /// systems, the scheduler is free to run the task on one of these PU, then
    /// migrate it to another PU, etc. It is often useful to call `singlify()`
    /// on the target CPU set before passing it to the binding function to avoid
    /// these expensive migrations. See the documentation of
    /// `Bitmap::singlify()` for details.
    ///
    /// Some operating systems do not provide all hwloc-supported mechanisms to
    /// bind processes, threads, etc. `Topology::support()` may be used to query
    /// about the actual CPU binding support in the currently used operating
    /// system.
    ///
    /// By default, when the requested binding operation is not available, hwloc
    /// will go for a similar binding operation (with side-effects, smaller
    /// binding set, etc). You can inhibit this with `CpuBindingFlags::STRICT`.
    ///
    /// To unbind, just call the binding function with either a full cpuset or a
    /// cpuset equal to the system cpuset.
    ///
    /// On some operating systems, CPU binding may have effects on memory
    /// binding, see `CpuBindingFlags::NO_MEMORY_BINDING`.
    ///
    /// Running lstopo --top or hwloc-ps can be a very convenient tool to check
    /// how binding actually happened.
    pub fn bind_cpu(&self, set: &CpuSet, flags: CpuBindingFlags) -> Result<(), CpuBindingError> {
        let result = unsafe { ffi::hwloc_set_cpubind(self.as_ptr(), set.as_ptr(), flags.bits()) };
        cpu::result(result, ())
    }

    /// Get current process or thread CPU binding
    pub fn cpu_binding(&self, flags: CpuBindingFlags) -> Result<CpuSet, CpuBindingError> {
        let mut cpuset = CpuSet::new();
        let result =
            unsafe { ffi::hwloc_get_cpubind(self.as_ptr(), cpuset.as_mut_ptr(), flags.bits()) };
        cpu::result(result, cpuset)
    }

    /// Binds a process (identified by its `pid`) on given CPUs
    ///
    /// See `bind_cpu()` for more informations.
    pub fn bind_process_cpu(
        &self,
        pid: ProcessID,
        set: &CpuSet,
        flags: CpuBindingFlags,
    ) -> Result<(), CpuBindingError> {
        let result =
            unsafe { ffi::hwloc_set_proc_cpubind(self.as_ptr(), pid, set.as_ptr(), flags.bits()) };
        cpu::result(result, ())
    }

    /// Get the current physical binding of a process, identified by its `pid`.
    pub fn process_cpu_binding(
        &self,
        pid: ProcessID,
        flags: CpuBindingFlags,
    ) -> Result<CpuSet, CpuBindingError> {
        let mut cpuset = CpuSet::new();
        let result = unsafe {
            ffi::hwloc_get_proc_cpubind(self.as_ptr(), pid, cpuset.as_mut_ptr(), flags.bits())
        };
        cpu::result(result, cpuset)
    }

    /// Bind a thread (by its `tid`) on given CPUs
    ///
    /// See `bind_cpu()` for more informations.
    pub fn bind_thread_cpu(
        &self,
        tid: ThreadID,
        set: &CpuSet,
        flags: CpuBindingFlags,
    ) -> Result<(), CpuBindingError> {
        let result = unsafe {
            ffi::hwloc_set_thread_cpubind(self.as_ptr(), tid, set.as_ptr(), flags.bits())
        };
        cpu::result(result, ())
    }

    /// Get the current physical binding of thread `tid`.
    pub fn thread_cpu_binding(
        &self,
        tid: ThreadID,
        flags: CpuBindingFlags,
    ) -> Result<CpuSet, CpuBindingError> {
        let mut cpuset = CpuSet::new();
        let result = unsafe {
            ffi::hwloc_get_thread_cpubind(self.as_ptr(), tid, cpuset.as_mut_ptr(), flags.bits())
        };
        cpu::result(result, cpuset)
    }

    /// Get the last physical CPUs where the current process or thread ran
    ///
    /// The operating system may move some tasks from one processor
    /// to another at any time according to their binding,
    /// so this function may return something that is already
    /// outdated.
    ///
    /// Flags can include either `PROCESS` or `THREAD` to specify whether the
    /// query should be for the whole process (union of all CPUs on which all
    /// threads are running), or only the current thread. If the process is
    /// single-threaded, flags can be set to empty() to let hwloc use whichever
    /// method is available on the underlying OS.
    pub fn last_cpu_location(&self, flags: CpuBindingFlags) -> Result<CpuSet, CpuBindingError> {
        let mut cpuset = CpuSet::new();
        let result = unsafe {
            ffi::hwloc_get_last_cpu_location(self.as_ptr(), cpuset.as_mut_ptr(), flags.bits())
        };
        cpu::result(result, cpuset)
    }

    /// Get the last physical CPU where a process ran.
    ///
    /// The operating system may move some tasks from one processor to another
    /// at any time according to their binding, so this function may return
    /// something that is already outdated.
    pub fn last_process_cpu_location(
        &self,
        pid: ProcessID,
        flags: CpuBindingFlags,
    ) -> Result<CpuSet, CpuBindingError> {
        let mut cpuset = CpuSet::new();
        let result = unsafe {
            ffi::hwloc_get_proc_last_cpu_location(
                self.as_ptr(),
                pid,
                cpuset.as_mut_ptr(),
                flags.bits(),
            )
        };
        cpu::result(result, cpuset)
    }

    // === Memory binding: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__membinding.html ===

    /// Allocate some memory
    ///
    /// This is equivalent to `malloc()`, except that it tries to allocated
    /// page-aligned memory from the OS.
    pub fn allocate_memory(&self, len: usize) -> Option<Bytes> {
        unsafe { Bytes::wrap(self, ffi::hwloc_alloc(self.as_ptr(), len), len) }
    }

    /// Allocate some memory on NUMA nodes specified by `set` and `flags`
    ///
    /// If the `BY_NODE_SET` flag is set (which is the default), `set` is
    /// interpreted as a `NodeSet`. Otherwise, it is interpreted as a `CpuSet`.
    /// Binding by `NodeSet` is preferred because some NUMA memory nodes are not
    /// attached to CPUs, and thus cannot be bound by `CpuSet`.
    ///
    /// If you do not care about changing the binding of the current process or
    /// thread, you can maximize portability by using `binding_allocate_memory()`.
    pub fn allocate_bound_memory(
        &self,
        len: usize,
        set: &Bitmap,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<Bytes, MemoryBindingSetupError> {
        unsafe {
            let base =
                ffi::hwloc_alloc_membind(self.as_ptr(), len, set.as_ptr(), policy.into(), flags);
            Bytes::wrap(self, base, len).ok_or_else(MemoryBindingSetupError::from_errno)
        }
    }

    /// Allocate some memory on NUMA nodes specified by `set` and `flags`,
    /// possibly rebinding current process or thread if needed
    ///
    /// This works like `allocate_bound_memory()` unless the allocation fails,
    /// in which case he current process or thread memory binding policy is
    /// changed before retrying.
    ///
    /// Allocating memory that matches the current process/thread configuration
    /// is supported on more operating systems, so this is the most portable way
    /// to obtain a bound memory buffer.
    pub fn binding_allocate_memory(
        &self,
        len: usize,
        set: &Bitmap,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<Bytes, MemoryBindingSetupError> {
        // Try allocate_bound_memory first
        if let Ok(bytes) = self.allocate_bound_memory(len, set, policy, flags) {
            return Ok(bytes);
        }

        // If that doesn't work, try binding the current process
        self.bind_memory(Some((set, policy)), flags)?;

        // If that succeeds, try allocating more memory
        let mut bytes = self
            .allocate_memory(len)
            .ok_or(MemoryBindingSetupError::AllocationFailed)?;

        // Depending on policy, we may or may not need to touch the memory to
        // enforce the binding
        match policy {
            MemoryBindingPolicy::FirstTouch | MemoryBindingPolicy::NextTouch => {}
            MemoryBindingPolicy::Bind | MemoryBindingPolicy::Interleave => {
                for b in &mut bytes[..] {
                    *b = MaybeUninit::new(0);
                }
            }
        }
        Ok(bytes)
    }

    /// Set the default memory binding policy of the current process or thread
    /// to prefer the NUMA node(s) specified by `config` and `flags`.
    ///
    /// If `config` is set to None, the memory allocation policy is reset to the
    /// system default. Depending on the operating system, this may correspond
    /// to `FirstTouch` (Linux, FreeBSD) or `Bind` (AIX, HP-UX, Solaris, Windows).
    ///
    /// If neither `MemoryBindingFlags::PROCESS` nor `MemoryBindingFlags::THREAD`
    /// is specified, the current process is assumed to be single-threaded. This
    /// is the most portable form as it permits hwloc to use either
    /// process-based OS functions or thread-based OS functions, depending on
    /// which are available.
    ///
    /// If the `BY_NODE_SET` flag is set (which is the default), the `Bitmap` is
    /// interpreted as a `NodeSet`. Otherwise, it is interpreted as a `CpuSet`.
    /// Binding by `NodeSet` is preferred because some NUMA memory nodes are not
    /// attached to CPUs, and thus cannot be bound by `CpuSet`.
    pub fn bind_memory(
        &self,
        config: Option<(&Bitmap, MemoryBindingPolicy)>,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingSetupError> {
        // TODO: Generalize to all binding actions
        let (set, policy) = Self::decode_binding_config(config);
        let result = unsafe { ffi::hwloc_set_membind(self.as_ptr(), set, policy, flags) };
        memory::setup_result(result)
    }

    /// Query the default memory binding policy and physical locality of the
    /// current process or thread
    ///
    /// Passing the `MemoryBindingFlags::PROCESS` flag specifies that the query
    /// target is the current policies and nodesets for all the threads in the
    /// current process. Passing `THREAD` instead specifies that the query
    /// target is the current policy and nodeset for only the thread invoking
    /// this function.
    ///
    /// If neither of these flags are passed (which is the most portable
    /// method), the process is assumed to be single threaded. This allows hwloc
    /// to use either process-based OS functions or thread-based OS functions,
    /// depending on which are available.
    ///
    /// `MemoryBindingFlags::STRICT` is only meaningful when `PROCESS` is also
    /// specified. In this case, hwloc will check the default memory policies
    /// and nodesets for all threads in the process. If they are not identical,
    /// `Err(MemoryBindingQueryError::MixedResults)` is returned. Otherwise, the
    /// shared configuration is returned.
    ///
    /// Otherwise, if `MemoryBindingFlags::PROCESS` is specified and `STRICT` is
    /// not specified, the default set from each thread is logically OR'ed
    /// together. If all threads' default policies are the same, that shared
    /// policy is returned, otherwise no policy is returned.
    ///
    /// In the `MemoryBindingFlags::THREAD` case (or when neither `PROCESS` or
    /// `THREAD` is specified), there is only one set and policy, they are returned.
    ///
    /// If `MemoryBindingFlags::BY_NODE_SET` is specified (which is the default),
    /// a `NodeSet` is returned, otherwise a `CpuSet` is returned. You should
    /// prefer `NodeSet`s whenever possible because some NUMA nodes may not be
    /// attached to CPUs and thus be skipped from `CpuSet`s.
    pub fn memory_binding(
        &self,
        flags: MemoryBindingFlags,
    ) -> Result<(Bitmap, Option<MemoryBindingPolicy>), MemoryBindingQueryError> {
        // TODO: Generalize to all binding queries
        let mut set = Bitmap::new();
        let mut raw_policy = 0;
        let result =
            unsafe { hwloc_get_membind(self.as_ptr(), set.as_mut_ptr(), &mut raw_policy, flags) };
        memory::query_result_lazy(result, move || {
            let policy = match MemoryBindingPolicy::try_from(raw_policy) {
                Ok(policy) => Some(policy),
                Err(TryFromPrimitiveError { number: -1 }) => None,
                Err(TryFromPrimitiveError { number }) => {
                    panic!("Got unexpected memory policy #{number}")
                }
            };
            (set, policy)
        })
    }

    /* TODO:
                #[must_use]
                pub(crate) fn hwloc_set_proc_membind(
                    topology: *const RawTopology,
                    pid: ProcessID,
                    set: *const RawBitmap,
                    policy: RawMemoryBindingPolicy,
                    flags: MemoryBindingFlags,
                ) -> c_int;
                #[must_use]
                pub(crate) fn hwloc_get_proc_membind(
                    topology: *const RawTopology,
                    pid: ProcessID,
                    set: *mut RawBitmap,
                    policy: *mut RawMemoryBindingPolicy,
                    flags: MemoryBindingFlags,
                ) -> c_int;
                #[must_use]
                pub(crate) fn hwloc_set_area_membind(
                    topology: *const RawTopology,
                    addr: *const c_void,
                    len: size_t,
                    set: *const RawBitmap,
                    policy: RawMemoryBindingPolicy,
                    flags: MemoryBindingFlags,
                ) -> c_int;
                #[must_use]
                pub(crate) fn hwloc_get_area_membind(
                    topology: *const RawTopology,
                    addr: *const c_void,
                    len: size_t,
                    set: *mut RawBitmap,
                    policy: *mut RawMemoryBindingPolicy,
                    flags: MemoryBindingFlags,
                ) -> c_int;
                #[must_use]
                pub(crate) fn hwloc_get_area_memlocation(
                    topology: *const RawTopology,
                    addr: *const c_void,
                    len: size_t,
                    set: *mut RawBitmap,
                    flags: MemoryBindingFlags,
                ) -> c_int;
    */

    /// Decode a memory binding configuration
    fn decode_binding_config(
        config: Option<(&Bitmap, MemoryBindingPolicy)>,
    ) -> (*const RawBitmap, RawMemoryBindingPolicy) {
        if let Some((set, policy)) = config {
            (set.as_ptr(), policy.into())
        } else {
            (std::ptr::null(), 0)
        }
    }

    // === General-purpose internal utilities ===

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

impl Clone for Topology {
    fn clone(&self) -> Self {
        let mut clone = std::ptr::null_mut();
        let result = unsafe { ffi::hwloc_topology_dup(&mut clone, self.as_ptr()) };
        assert!(result >= 0, "Topology clone failed with error {result}");
        Self(NonNull::new(clone).expect("Got null pointer from hwloc_topology_dup"))
    }
}

unsafe impl Send for Topology {}
unsafe impl Sync for Topology {}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn should_set_and_get_flags() {
        let topo = Topology::builder()
            .with_flags(
                BuildFlags::INCLUDE_DISALLOWED | BuildFlags::GET_ALLOWED_RESOURCES_FROM_THIS_SYSTEM,
            )
            .unwrap()
            .build()
            .unwrap();
        assert_eq!(
            BuildFlags::INCLUDE_DISALLOWED | BuildFlags::GET_ALLOWED_RESOURCES_FROM_THIS_SYSTEM,
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
        assert!(pu_depth.assume_normal() > 0);
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
    fn should_produce_cpubind_bitflags() {
        assert_eq!("1", format!("{:b}", CpuBindingFlags::PROCESS.bits()));
        assert_eq!("10", format!("{:b}", CpuBindingFlags::THREAD.bits()));
        assert_eq!("100", format!("{:b}", CpuBindingFlags::STRICT.bits()));
        assert_eq!(
            "101",
            format!(
                "{:b}",
                (CpuBindingFlags::STRICT | CpuBindingFlags::PROCESS).bits()
            )
        );
    }
}
