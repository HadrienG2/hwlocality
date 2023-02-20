#![doc = include_str!("../README.md")]

pub mod bitmap;
pub mod builder;
pub mod cache;
pub mod cpu;
pub mod depth;
pub mod editor;
pub(crate) mod ffi;
pub mod memory;
pub mod objects;
pub mod support;

#[cfg(doc)]
use self::support::MiscSupport;
use self::{
    bitmap::{Bitmap, BitmapKind, CpuSet, NodeSet, RawBitmap, SpecializedBitmap},
    builder::{BuildFlags, RawTypeFilter, TopologyBuilder, TypeFilter},
    cache::CPUCacheStats,
    cpu::{CpuBindingError, CpuBindingFlags},
    depth::{Depth, DepthError, DepthResult, RawDepth},
    editor::TopologyEditor,
    ffi::LibcString,
    memory::{
        Bytes, MemoryBindingFlags, MemoryBindingPolicy, MemoryBindingQueryError,
        MemoryBindingSetupError, RawMemoryBindingPolicy,
    },
    objects::{
        attributes::ObjectAttributes,
        types::{CacheType, ObjectType, RawObjectType},
        TopologyObject,
    },
    support::TopologySupport,
};
use bitflags::bitflags;
use errno::{errno, Errno};
use libc::EINVAL;
use num_enum::TryFromPrimitiveError;
use std::{
    convert::TryInto,
    ffi::{c_char, c_int, c_ulong, c_void},
    iter::FusedIterator,
    marker::{PhantomData, PhantomPinned},
    mem::MaybeUninit,
    panic::{AssertUnwindSafe, UnwindSafe},
    ptr::{self, NonNull},
};

#[cfg(target_os = "windows")]
/// Thread identifier
pub type ThreadId = windows_sys::Win32::Foundation::HANDLE;
#[cfg(target_os = "windows")]
/// Process identifier
pub type ProcessId = u32;
#[cfg(not(target_os = "windows"))]
/// Thread identifier
pub type ThreadId = libc::pthread_t;
#[cfg(not(target_os = "windows"))]
/// Process identifier
pub type ProcessId = libc::pid_t;

/// Indicate at runtime which hwloc API version was used at build time.
/// This number is updated to (X<<16)+(Y<<8)+Z when a new release X.Y.Z
/// actually modifies the API.
///
/// Users may check for available features at build time using this number
pub fn get_api_version() -> u32 {
    unsafe { ffi::hwloc_get_api_version() }
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
///
/// A `Topology` contains everything hwloc knows about the hardware and software
/// structure of a system. It can be used to query the system topology and to
/// bind threads and processes to hardware CPU cores and NUMA nodes.
///
/// Since there are **many** things you can do with a `Topology`, the API is
/// broken down into sections roughly following the structure of the upstream
/// hwloc documentation:
///
/// - [Topology building](#topology-building)
/// - [Object levels, depths and types](#object-levels-depths-and-types)
/// - [CPU cache statistics](#cpu-cache-statistics)
/// - [CPU binding](#cpu-binding)
/// - [Memory binding](#memory-binding)
/// - [Modifying a loaded topology](#modifying-a-loaded-topology)
/// - [Finding objects inside a CPU set](#finding-objects-inside-a-cpu-set)
/// - [Finding objects covering at least a CPU set](#finding-objects-covering-at-least-a-cpu-set)
/// - [Finding other objects](#finding-other-objects)
/// - [Distributing items over a topology](#distributing-items-over-a-topology)
#[derive(Debug)]
pub struct Topology(NonNull<RawTopology>);

/// # Topology building
//
// Upstream docs:
// - Creation: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__creation.html
// - Build queries: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__configuration.html
impl Topology {
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

    /// Was the topology built using the system running this program?
    ///
    /// It may not have been if, for instance, it was built using another
    /// file-system root or loaded from a synthetic or XML textual description.
    pub fn is_this_system(&self) -> bool {
        let result = unsafe { ffi::hwloc_topology_is_thissystem(self.as_ptr()) };
        assert!(
            result == 0 || result == 1,
            "Unexpected result from hwloc_topology_is_thissystem"
        );
        result == 1
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
    /// [`BuildFlags::ASSUME_THIS_SYSTEM`].
    ///
    /// [`BuildFlags::IMPORT_SUPPORT`] may be used during topology building to
    /// report the supported features of the original remote machine instead. If
    /// it was successfully imported, [`MiscSupport::imported()`] will be set.
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

    /// Filtering that was applied for the given object type
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

/// # Object levels, depths and types
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__levels.html
impl Topology {
    /// Full depth of the topology.
    ///
    /// In practice, the full depth of the topology equals the depth of the
    /// [`ObjectType::PU`] plus one.
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

    /// Depth for the given [`ObjectType`]
    ///
    /// # Errors
    ///
    /// This will return Err([`DepthError::None`]) if no object of this type
    /// is present or if the OS doesn't provide this kind of information. If a
    /// similar type is acceptable, consider using
    /// [`depth_or_below_for_type()`](#method.depth_or_below_for_type)
    /// or [`depth_or_above_for_type()`](#method.depth_or_above_for_type) instead.
    ///
    /// You will get Err([`DepthError::Multiple`]) if objects of this type
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

    /// Depth for the given [`ObjectType`] or below
    ///
    /// If no object of this type is present on the underlying architecture, the
    /// function returns the depth of the first present object typically found
    /// inside `object_type`.
    ///
    /// # Errors
    ///
    /// This function is only meaningful for normal object types.
    ///
    /// You will get Err([`DepthError::Multiple`]) if objects of this type or
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

    /// Depth for the given [`ObjectType`] or above
    ///
    /// If no object of this type is present on the underlying architecture, the
    /// function returns the depth of the first present object typically
    /// containing `object_type`.
    ///
    /// # Errors
    ///
    /// This function is only meaningful for normal object types.
    ///
    /// You will get Err([`DepthError::Multiple`]) if objects of this type or
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

    /// Depth for the given cache type and level
    ///
    /// Return the depth of the topology level that contains cache objects whose
    /// attributes match `cache_level` and `cache_type`.
    ///
    /// This function is similar to calling [`Topology::depth_for_type()`] with
    /// the corresponding type such as [`ObjectType::L1iCache`], except that it
    /// may also return a unified cache when looking for an instruction cache.
    ///
    /// If `cache_type` is `None`, it is ignored and multiple levels may match.
    /// The function returns either the depth of a uniquely matching level or
    /// Err([`DepthError::Multiple`]).
    ///
    /// If `cache_type` is Some([`CacheType::Unified`]), the depth of the unique
    /// matching unified cache level is returned.
    ///
    /// If `cache_type` is Some([`CacheType::Data`]) or
    /// Some([`CacheType::Instruction`]), either a matching cache, or a
    /// unified cache is returned.
    ///
    /// # Errors
    ///
    /// - If no cache level matches, Err([`DepthError::None`]) is returned.
    /// - If multiple cache levels match, Err([`DepthError::Multiple`]) is
    ///   returned. This can only happen if `cache_type` is `None`.
    pub fn depth_for_cache(&self, cache_level: u32, cache_type: Option<CacheType>) -> DepthResult {
        let mut result = Err(DepthError::None);
        for depth in 0..self.depth() {
            // Cache level and type are homogeneous across a depth level so we
            // only need to look at one object
            for obj in self.objects_at_depth(depth.into()).take(1) {
                // Is this a cache?
                if let Some(ObjectAttributes::Cache(cache)) = obj.attributes() {
                    // Check cache level
                    if cache.depth() != cache_level {
                        continue;
                    }

                    // Check cache type if instructed to do so
                    if let Some(cache_type) = cache_type {
                        if cache.cache_type() == cache_type
                            || cache.cache_type() == CacheType::Unified
                        {
                            // If both cache type + level are specified, then
                            // multiple matches cannot occur: stop here.
                            return Ok(depth.into());
                        } else {
                            continue;
                        }
                    } else {
                        // Without a cache type check, multiple matches may occur
                        match result {
                            Err(DepthError::None) => result = Ok(depth.into()),
                            Ok(_) => {
                                return Err(DepthError::Multiple);
                            }
                            Err(DepthError::Multiple) => {
                                unreachable!("Setting this triggers a loop break")
                            }
                            Err(DepthError::Unknown(_)) => {
                                unreachable!("This value is never set")
                            }
                        }
                    }
                }
            }
        }
        result
    }

    /// [`ObjectType`] at the given depth.
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

    /// [`TopologyObject`] at the root of the topology.
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

    /// [`TopologyObject`]s with the given [`ObjectType`].
    ///
    /// If you know that objects of this type should only appear at a single
    /// depth (which is true of most object types with the notable exception of
    /// Group), you can avoid allocating a `Vec` by probing said depth like this:
    ///
    /// ```
    /// # fn main() -> anyhow::Result<()> {
    /// #     let topology = hwloc2::Topology::new().unwrap();
    /// #     let object_type = hwloc2::objects::types::ObjectType::PU;
    /// topology.objects_at_depth(topology.depth_for_type(object_type)?)
    /// #     ; Ok(())
    /// # }
    /// ```
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

    /// [`TopologyObject`]s at the given depth.
    pub fn objects_at_depth(
        &self,
        depth: Depth,
    ) -> impl Iterator<Item = &TopologyObject>
           + Clone
           + DoubleEndedIterator
           + ExactSizeIterator
           + FusedIterator {
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
}

/// # CPU cache statistics
impl Topology {
    /// Compute high-level CPU cache statistics
    ///
    /// These statistics can be used in scenarios where you're not yet ready for
    /// full locality-aware scheduling but just want to make sure that your code
    /// will use CPU caches sensibly no matter which CPU core it's running on.
    ///
    /// This API is unique to the Rust hwloc bindings.
    pub fn cpu_cache_stats(&self) -> CPUCacheStats {
        CPUCacheStats::new(self)
    }
}

/// # CPU binding
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpubinding.html
impl Topology {
    /// Binds the current process or thread on given CPUs
    ///
    /// Some operating systems only support binding threads or processes to a
    /// single PU. Others allow binding to larger sets such as entire Cores or
    /// Packages or even random sets of individual PUs. In such operating
    /// systems, the scheduler is free to run the task on one of these PU, then
    /// migrate it to another PU, etc. It is often useful to call `singlify()`
    /// on the target CPU set before passing it to the binding function to avoid
    /// these expensive migrations. See the documentation of
    /// [`Bitmap::singlify()`] for details.
    ///
    /// Some operating systems do not provide all hwloc-supported mechanisms to
    /// bind processes, threads, etc. [`Topology::support()`] may be used to
    /// query about the actual CPU binding support in the currently used
    /// operating system.
    ///
    /// By default, when the requested binding operation is not available, hwloc
    /// will go for a similar binding operation (with side-effects, smaller
    /// binding set, etc). You can inhibit this with [`CpuBindingFlags::STRICT`].
    ///
    /// To unbind, just call the binding function with either a full cpuset or a
    /// cpuset equal to the system cpuset.
    ///
    /// On some operating systems, CPU binding may have effects on memory
    /// binding, see [`CpuBindingFlags::NO_MEMORY_BINDING`].
    ///
    /// Running `lstopo --top` or `hwloc-ps` can be a very convenient tool to
    /// check how binding actually happened.
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
    /// See [`Topology::bind_cpu()`] for more informations.
    pub fn bind_process_cpu(
        &self,
        pid: ProcessId,
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
        pid: ProcessId,
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
    /// See [`Topology::bind_cpu()`] for more informations.
    pub fn bind_thread_cpu(
        &self,
        tid: ThreadId,
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
        tid: ThreadId,
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
    /// `flags` can include either [`CpuBindingFlags::PROCESS`] or
    /// [`CpuBindingFlags::THREAD`] to specify whether the query should be for
    /// the whole process (union of all CPUs on which all threads are running),
    /// or only the current thread. If the process is single-threaded, `flags`
    /// can be left empty to let hwloc use whichever method is available on the
    /// underlying OS, which increases portability.
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
        pid: ProcessId,
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
}

/// # Memory binding
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__membinding.html
impl Topology {
    /// Allocate some memory
    ///
    /// This is equivalent to [`libc::malloc()`], except that it tries to
    /// allocate page-aligned memory from the OS.
    pub fn allocate_memory(&self, len: usize) -> Option<Bytes> {
        unsafe { Bytes::wrap(self, ffi::hwloc_alloc(self.as_ptr(), len), len) }
    }

    /// Allocate some memory on NUMA nodes specified by `set`
    ///
    /// Memory can be bound by either [`CpuSet`] or [`NodeSet`]. Binding by
    /// [`NodeSet`] is preferred because some NUMA memory nodes are not attached
    /// to CPUs, and thus cannot be bound by [`CpuSet`].
    ///
    /// If you do not care about changing the binding of the current process or
    /// thread, you can maximize portability by using
    /// [`Topology::binding_allocate_memory()`] instead.
    pub fn allocate_bound_memory<Set: SpecializedBitmap>(
        &self,
        len: usize,
        set: &Set,
        policy: MemoryBindingPolicy,
        mut flags: MemoryBindingFlags,
    ) -> Result<Bytes, MemoryBindingSetupError> {
        Self::adjust_flags_for::<Set>(&mut flags);
        unsafe {
            let base = ffi::hwloc_alloc_membind(
                self.as_ptr(),
                len,
                set.as_ref().as_ptr(),
                policy.into(),
                flags,
            );
            Bytes::wrap(self, base, len).ok_or_else(MemoryBindingSetupError::from_errno)
        }
    }

    /// Allocate some memory on NUMA nodes specified by `set` and `flags`,
    /// possibly rebinding current process or thread if needed
    ///
    /// This works like [`Topology::allocate_bound_memory()`] unless the
    /// allocation fails, in which case hwloc will attempt to change the current
    /// process or thread memory binding policy as directed instead before
    /// retrying the allocation.
    ///
    /// Allocating memory that matches the current process/thread configuration
    /// is supported on more operating systems, so this is the most portable way
    /// to obtain a bound memory buffer.
    pub fn binding_allocate_memory<Set: SpecializedBitmap>(
        &self,
        len: usize,
        set: &Set,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<Bytes, MemoryBindingSetupError> {
        // Try allocate_bound_memory first
        if let Ok(bytes) = self.allocate_bound_memory(len, set, policy, flags) {
            return Ok(bytes);
        }

        // If that doesn't work, try binding the current process
        self.bind_memory(set, policy, flags)?;

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
    /// to prefer the NUMA node(s) specified by `set`.
    ///
    /// If neither [`MemoryBindingFlags::PROCESS`] nor
    /// [`MemoryBindingFlags::THREAD`] is specified, the current process is
    /// assumed to be single-threaded. This is the most portable form as it
    /// permits hwloc to use either process-based OS functions or thread-based
    /// OS functions, depending on which are available.
    ///
    /// Memory can be bound by either [`CpuSet`] or [`NodeSet`]. Binding by
    /// [`NodeSet`] is preferred because some NUMA memory nodes are not attached
    /// to CPUs, and thus cannot be bound by [`CpuSet`].
    pub fn bind_memory<Set: SpecializedBitmap>(
        &self,
        set: &Set,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingSetupError> {
        self.bind_memory_impl(set, policy, flags, |topology, set, policy, flags| unsafe {
            ffi::hwloc_set_membind(topology, set, policy, flags)
        })
    }

    /// Reset the memory allocation policy of the current process or thread to
    /// the system default
    ///
    /// Depending on the operating system, this may correspond to
    /// [`MemoryBindingPolicy::FirstTouch`] (Linux, FreeBSD) or
    /// [`MemoryBindingPolicy::Bind`] (AIX, HP-UX, Solaris, Windows).
    ///
    /// If neither [`MemoryBindingFlags::PROCESS`] nor
    /// [`MemoryBindingFlags::THREAD`] is specified, the current process is
    /// assumed to be single-threaded. This is the most portable form as it
    /// permits hwloc to use either process-based OS functions or thread-based
    /// OS functions, depending on which are available.
    pub fn unbind_memory(&self, flags: MemoryBindingFlags) -> Result<(), MemoryBindingSetupError> {
        self.unbind_memory_impl(flags, |topology, set, policy, flags| unsafe {
            ffi::hwloc_set_membind(topology, set, policy, flags)
        })
    }

    /// Query the default memory binding policy and physical locality of the
    /// current process or thread
    ///
    /// Passing the [`MemoryBindingFlags::PROCESS`] flag specifies that the
    /// query target is the current policies and nodesets for all the threads
    /// in the current process. Passing [`MemoryBindingFlags::THREAD`] instead
    /// specifies that the query target is the current policy and nodeset for
    /// only the thread invoking this function.
    ///
    /// If neither of these flags are passed (which is the most portable
    /// method), the process is assumed to be single threaded. This allows hwloc
    /// to use either process-based OS functions or thread-based OS functions,
    /// depending on which are available.
    ///
    /// [`MemoryBindingFlags::STRICT`] is only meaningful when
    /// `PROCESS` is also specified. In this case, hwloc will check the default
    /// memory policies and nodesets for all threads in the process. If they are
    /// not identical, Err([`MemoryBindingQueryError::MixedResults`]) is
    /// returned. Otherwise, the shared configuration is returned.
    ///
    /// Otherwise, if `PROCESS` is specified and `STRICT` is not specified, the
    /// default sets from each thread are logically OR'ed together. If all
    /// threads' default policies are the same, that shared policy is returned,
    /// otherwise no policy is returned.
    ///
    /// In the `THREAD` case (or when neither `PROCESS` nor `THREAD` is
    /// specified), there is only one set and policy, they are returned.
    ///
    /// Bindings can be queried as [`CpuSet`] or [`NodeSet`]. Querying by
    /// [`NodeSet`] is preferred because some NUMA memory nodes are not attached
    /// to CPUs, and thus cannot be bound by [`CpuSet`].
    pub fn memory_binding<Set: SpecializedBitmap>(
        &self,
        flags: MemoryBindingFlags,
    ) -> Result<(Set, Option<MemoryBindingPolicy>), MemoryBindingQueryError> {
        self.memory_binding_impl(flags, |topology, set, policy, flags| unsafe {
            ffi::hwloc_get_membind(topology, set, policy, flags)
        })
    }

    /// Set the default memory binding policy of the specified process to prefer
    /// the NUMA node(s) specified by `set`.
    ///
    /// Memory can be bound by either [`CpuSet`] or [`NodeSet`]. Binding by
    /// [`NodeSet`] is preferred because some NUMA memory nodes are not attached
    /// to CPUs, and thus cannot be bound by [`CpuSet`].
    pub fn bind_process_memory<Set: SpecializedBitmap>(
        &self,
        pid: ProcessId,
        set: &Set,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingSetupError> {
        self.bind_memory_impl(set, policy, flags, |topology, set, policy, flags| unsafe {
            ffi::hwloc_set_proc_membind(topology, pid, set, policy, flags)
        })
    }

    /// Reset the memory allocation policy of the specified process to the
    /// system default
    ///
    /// Depending on the operating system, this may correspond to
    /// [`MemoryBindingPolicy::FirstTouch`] (Linux, FreeBSD) or
    /// [`MemoryBindingPolicy::Bind`] (AIX, HP-UX, Solaris, Windows).
    pub fn unbind_process_memory(
        &self,
        pid: ProcessId,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingSetupError> {
        self.unbind_memory_impl(flags, |topology, set, policy, flags| unsafe {
            ffi::hwloc_set_proc_membind(topology, pid, set, policy, flags)
        })
    }

    /// Query the default memory binding policy and physical locality of the
    /// specified process
    ///
    /// Passing the [`MemoryBindingFlags::PROCESS`] flag specifies that the
    /// query target is the current policies and nodesets for all the threads in
    /// the current process. If `PROCESS` is not specified (which is the most
    /// portable method), the process is assumed to be single threaded. This
    /// allows hwloc to use either process-based OS functions or thread-based OS
    /// functions, depending on which are available.
    ///
    /// Note that it does not make sense to pass [`MemoryBindingFlags::THREAD`]
    /// to this function.
    ///
    /// If [`MemoryBindingFlags::STRICT`] is specified, hwloc will check the
    /// default memory policies and nodesets for all threads in the process. If
    /// they are not identical, Err([`MemoryBindingQueryError::MixedResults`])
    /// is returned. Otherwise, the shared configuration is returned.
    ///
    /// If `STRICT` is not specified, the default set from each thread is
    /// logically OR'ed together. If all threads' default policies are the same,
    /// that shared policy is returned, otherwise no policy is returned.
    ///
    /// Bindings can be queried as [`CpuSet`] or [`NodeSet`]. Querying by
    /// [`NodeSet`] is preferred because some NUMA memory nodes are not attached
    /// to CPUs, and thus cannot be bound by [`CpuSet`].
    pub fn process_memory_binding<Set: SpecializedBitmap>(
        &self,
        pid: ProcessId,
        flags: MemoryBindingFlags,
    ) -> Result<(Set, Option<MemoryBindingPolicy>), MemoryBindingQueryError> {
        self.memory_binding_impl(flags, |topology, set, policy, flags| unsafe {
            ffi::hwloc_get_proc_membind(topology, pid, set, policy, flags)
        })
    }

    /// Bind the memory identified by `target` to the NUMA node(s) specified by
    /// `set`
    ///
    /// Beware that only the memory directly targeted by the `target` reference
    /// will be covered. So for example, you cannot pass in an `&Vec<T>` and
    /// expect the Vec's contents to be covered, instead you must pass in the
    /// `&[T]` corresponding to the Vec's contents as `&vec[..]`. You may want
    /// to manually specify the `Target` type via turbofish to make sure that
    /// you don't get tripped up by references of references like `&&[T]`.
    ///
    /// Memory can be bound by either [`CpuSet`] or [`NodeSet`]. Binding by
    /// [`NodeSet`] is preferred because some NUMA memory nodes are not attached
    /// to CPUs, and thus cannot be bound by [`CpuSet`].
    pub fn bind_memory_area<Target: ?Sized, Set: SpecializedBitmap>(
        &self,
        target: &Target,
        set: &Set,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingSetupError> {
        self.bind_memory_impl(set, policy, flags, |topology, set, policy, flags| unsafe {
            ffi::hwloc_set_area_membind(
                topology,
                target as *const _ as *const c_void,
                std::mem::size_of_val(target),
                set,
                policy,
                flags,
            )
        })
    }

    /// Reset the memory allocation policy of the memory identified by `target`
    /// to the system default
    ///
    /// Depending on the operating system, this may correspond to
    /// [`MemoryBindingPolicy::FirstTouch`] (Linux, FreeBSD) or
    /// [`MemoryBindingPolicy::Bind`] (AIX, HP-UX, Solaris, Windows).
    ///
    /// Beware that only the memory directly targeted by the `target` reference
    /// will be covered. So for example, you cannot pass in an `&Vec<T>` and
    /// expect the Vec's contents to be covered, instead you must pass in the
    /// `&[T]` corresponding to the Vec's contents as `&vec[..]`. You may want
    /// to manually specify the `Target` type via turbofish to make sure that
    /// you don't get tripped up by references of references like `&&[T]`.
    pub fn unbind_memory_area<Target: ?Sized>(
        &self,
        target: &Target,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingSetupError> {
        self.unbind_memory_impl(flags, |topology, set, policy, flags| unsafe {
            ffi::hwloc_set_area_membind(
                topology,
                target as *const _ as *const c_void,
                std::mem::size_of_val(target),
                set,
                policy,
                flags,
            )
        })
    }

    /// Query the memory binding policy and physical locality of the
    /// memory identified by `target`
    ///
    /// Beware that only the memory directly targeted by the `target` reference
    /// will be covered. So for example, you cannot pass in an `&Vec<T>` and
    /// expect the Vec's contents to be covered, instead you must pass in the
    /// `&[T]` corresponding to the Vec's contents as `&vec[..]`. You may want
    /// to manually specify the `Target` type via turbofish to make sure that
    /// you don't get tripped up by references of references like `&&[T]`.
    ///
    /// If [`MemoryBindingFlags::STRICT`] is specified, hwloc will check the
    /// default memory policies and nodesets for all memory pages covered by
    /// `target`. If these are not identical,
    /// Err([`MemoryBindingQueryError::MixedResults`]) is returned. Otherwise,
    /// the shared configuration is returned.
    ///
    /// If `STRICT` is not specified, the union of all NUMA nodes containing
    /// pages in the address range is calculated. If all pages in the target
    /// have the same policy, it is returned, otherwise no policy is returned.
    ///
    /// Bindings can be queried as [`CpuSet`] or [`NodeSet`]. Querying by
    /// [`NodeSet`] is preferred because some NUMA memory nodes are not attached
    /// to CPUs, and thus cannot be bound by [`CpuSet`].
    pub fn area_memory_binding<Target: ?Sized, Set: SpecializedBitmap>(
        &self,
        target: &Target,
        flags: MemoryBindingFlags,
    ) -> Result<(Set, Option<MemoryBindingPolicy>), MemoryBindingQueryError> {
        assert!(
            std::mem::size_of_val(target) > 0,
            "Zero-sized target covers no memory!"
        );
        self.memory_binding_impl(flags, |topology, set, policy, flags| unsafe {
            ffi::hwloc_get_area_membind(
                topology,
                target as *const _ as *const c_void,
                std::mem::size_of_val(target),
                set,
                policy,
                flags,
            )
        })
    }

    /// Get the NUMA nodes where the memory identified by `target` is physically
    /// allocated
    ///
    /// Beware that only the memory directly targeted by the `target` reference
    /// will be covered. So for example, you cannot pass in an `&Vec<T>` and
    /// expect the Vec's contents to be covered, instead you must pass in the
    /// `&[T]` corresponding to the Vec's contents as `&vec[..]`. You may want
    /// to manually specify the `Target` type via turbofish to make sure that
    /// you don't get tripped up by references of references like `&&[T]`.
    ///
    /// If pages spread to multiple nodes, it is not specified whether they
    /// spread equitably, or whether most of them are on a single node, etc.
    ///
    /// The operating system may move memory pages from one processor to another
    /// at any time according to their binding, so this function may return
    /// something that is already outdated.
    ///
    /// Bindings can be queried as [`CpuSet`] or [`NodeSet`]. Querying by
    /// [`NodeSet`] is preferred because some NUMA memory nodes are not attached
    /// to CPUs, and thus cannot be bound by [`CpuSet`].
    pub fn area_memory_location<Target: ?Sized, Set: SpecializedBitmap>(
        &self,
        target: &Target,
        flags: MemoryBindingFlags,
    ) -> Result<Set, MemoryBindingQueryError> {
        self.memory_binding_impl(flags, |topology, set, policy, flags| unsafe {
            *policy = -1;
            ffi::hwloc_get_area_memlocation(
                topology,
                target as *const _ as *const c_void,
                std::mem::size_of_val(target),
                set,
                flags,
            )
        })
        .map(|(set, _policy)| set)
    }

    /// Adjust binding flags for a certain kind of Set
    fn adjust_flags_for<Set: SpecializedBitmap>(flags: &mut MemoryBindingFlags) {
        match Set::BITMAP_KIND {
            BitmapKind::CpuSet => flags.remove(MemoryBindingFlags::BY_NODE_SET),
            BitmapKind::NodeSet => flags.insert(MemoryBindingFlags::BY_NODE_SET),
        }
    }

    /// Call an hwloc memory binding function to bind some memory
    fn bind_memory_impl<Set: SpecializedBitmap>(
        &self,
        set: &Set,
        policy: MemoryBindingPolicy,
        mut flags: MemoryBindingFlags,
        set_membind_like: impl FnOnce(
            *const RawTopology,
            *const RawBitmap,
            RawMemoryBindingPolicy,
            MemoryBindingFlags,
        ) -> c_int,
    ) -> Result<(), MemoryBindingSetupError> {
        Self::adjust_flags_for::<Set>(&mut flags);
        let result = set_membind_like(self.as_ptr(), set.as_ref().as_ptr(), policy.into(), flags);
        memory::setup_result(result)
    }

    /// Call an hwloc memory binding function to unbind some memory
    fn unbind_memory_impl(
        &self,
        flags: MemoryBindingFlags,
        set_membind_like: impl FnOnce(
            *const RawTopology,
            *const RawBitmap,
            RawMemoryBindingPolicy,
            MemoryBindingFlags,
        ) -> c_int,
    ) -> Result<(), MemoryBindingSetupError> {
        let result = set_membind_like(self.as_ptr(), ptr::null(), 0, flags);
        memory::setup_result(result)
    }

    /// Call an hwloc memory binding query function
    fn memory_binding_impl<Set: SpecializedBitmap>(
        &self,
        mut flags: MemoryBindingFlags,
        get_membind_like: impl FnOnce(
            *const RawTopology,
            *mut RawBitmap,
            *mut RawMemoryBindingPolicy,
            MemoryBindingFlags,
        ) -> c_int,
    ) -> Result<(Set, Option<MemoryBindingPolicy>), MemoryBindingQueryError> {
        let mut set = Bitmap::new();
        let mut raw_policy = 0;
        Self::adjust_flags_for::<Set>(&mut flags);
        let result = get_membind_like(self.as_ptr(), set.as_mut_ptr(), &mut raw_policy, flags);
        memory::query_result_lazy(result, move || {
            let policy = match MemoryBindingPolicy::try_from(raw_policy) {
                Ok(policy) => Some(policy),
                Err(TryFromPrimitiveError { number: -1 }) => None,
                Err(TryFromPrimitiveError { number }) => {
                    panic!("Got unexpected memory policy #{number}")
                }
            };
            (set.into(), policy)
        })
    }
}

/// # Modifying a loaded `Topology`
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__tinker.html
impl Topology {
    /// Modify this topology
    ///
    /// hwloc employs lazy caching patterns that do not interact well with
    /// Rust's shared XOR mutable aliasing model. This API lets you safely
    /// modify the active `Topology` through a [`TopologyEditor`] proxy object,
    /// with the guarantee that by the time `Topology::edit()` returns, the
    /// `Topology` will be back in a state where it is safe to use `&self` again.
    pub fn edit<R>(&mut self, edit: impl UnwindSafe + FnOnce(&mut TopologyEditor) -> R) -> R {
        // Set up topology editing
        let mut editor = TopologyEditor::new(self);
        let mut editor = AssertUnwindSafe(&mut editor);

        // Run the user-provided edit callback, catching panics
        let result = std::panic::catch_unwind(move || edit(&mut editor));

        // Force eager evaluation of all caches
        self.refresh();

        // Return user callback result or resume unwinding as appropriate
        match result {
            Ok(result) => result,
            Err(e) => std::panic::resume_unwind(e),
        }
    }

    /// Force eager evaluation of all lazily evaluated caches in preparation for
    /// using or exposing &self
    ///
    /// Abort if this fails as we must not let an invalid `Topology` state
    /// escape, not even via unwinding, as that would result in undefined
    /// behavior (mutation which the compiler assumes will not happen).
    pub(crate) fn refresh(&mut self) {
        let refresh_result = unsafe { ffi::hwloc_topology_refresh(self.as_mut_ptr()) };
        if refresh_result < 0 {
            eprintln!("Topology stuck in a state that violates Rust aliasing rules, must abort");
            std::process::abort();
        }
    }
}

/// # Finding objects inside a CPU set
//
// This is inspired by the upstream functionality described at
// https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__find__inside.html
// but the code had to be ported to Rust as most C code is inline and thus
// cannot be called from Rust, and the only function that's not inline does not
// fit Rust's design (assumes caller has allocated large enough storage with no
// way to tell what is large enough)
impl Topology {
    /// Enumerate the largest objects included in the given cpuset `set`
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set).
    ///
    /// In the common case where `set` is a subset of the root cpuset, this
    /// operation can be more efficiently performed by using
    /// `coarsest_cpuset_partition()`.
    pub fn largest_objects_inside_cpuset(
        &self,
        set: CpuSet,
    ) -> impl Iterator<Item = &TopologyObject> + FusedIterator {
        LargestObjectsInsideCpuSet {
            topology: self,
            set,
        }
    }

    /// Get the largest objects exactly covering the given cpuset `set`
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set).
    ///
    /// # Panics
    ///
    /// If the requested cpuset is not a subset of the root cpuset, we can't
    /// find children covering the indices outside of the root cpuset
    pub fn coarsest_cpuset_partition(&self, set: &CpuSet) -> Vec<&TopologyObject> {
        // Make sure each set index actually maps into a hardware PU
        let root = self.root_object();
        assert!(
            set.includes(root.cpuset().expect("Root should have a CPU set")),
            "Requested set has indices outside the root cpuset"
        );

        // Start recursion
        let mut result = Vec::new();
        let mut cpusets = Vec::new();
        fn process_object<'a>(
            parent: &'a TopologyObject,
            set: &CpuSet,
            result: &mut Vec<&'a TopologyObject>,
            cpusets: &mut Vec<CpuSet>,
        ) {
            // If the current object does not have a cpuset, ignore it
            let Some(parent_cpuset) = parent.cpuset() else { return };

            // If it exactly covers the target cpuset, we're done
            if parent_cpuset == set {
                result.push(parent);
                return;
            }

            // Otherwise, look for children that cover the target cpuset
            let mut subset = cpusets.pop().unwrap_or_default();
            for child in parent.normal_children() {
                // Ignore children without a cpuset, or with a cpuset that
                // doesn't intersect the target cpuset
                let Some(child_cpuset) = child.cpuset() else { continue };
                if !child_cpuset.intersects(set) {
                    continue;
                }

                // Split out the cpuset part corresponding to this child and recurse
                subset.copy_from(set);
                subset &= child_cpuset;
                process_object(child, &subset, result, cpusets);
            }
            cpusets.push(subset);
        }
        process_object(root, set, &mut result, &mut cpusets);
        result
    }

    /// Enumerate objects included in the given cpuset `set` at a certain depth
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set). Therefore, an empty iterator will
    /// always be returned for I/O or Misc depths as those objects have no cpusets.
    pub fn objects_inside_cpuset_at_depth<'result>(
        &'result self,
        set: &'result CpuSet,
        depth: Depth,
    ) -> impl Iterator<Item = &TopologyObject> + Clone + DoubleEndedIterator + FusedIterator + 'result
    {
        self.objects_at_depth(depth)
            .filter(|object| object.is_inside_cpuset(set))
    }

    /// Get objects included in the given cpuset `set` with a certain type
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set). Therefore, an empty Vec will
    /// always be returned for I/O or Misc objects as they don't have cpusets.
    ///
    /// If you know that objects of this type should only appear at a single
    /// depth (which is true of most object types with the notable exception of
    /// Group), you can avoid allocating a `Vec` by probing said depth like this:
    ///
    /// ```
    /// # fn main() -> anyhow::Result<()> {
    /// #     let topology = hwloc2::Topology::new().unwrap();
    /// #     let object_type = hwloc2::objects::types::ObjectType::PU;
    /// #     let set = hwloc2::bitmap::CpuSet::new();
    /// topology.objects_inside_cpuset_at_depth(&set, topology.depth_for_type(object_type)?)
    /// #     ; Ok(())
    /// # }
    /// ```
    pub fn objects_inside_cpuset_with_type(
        &self,
        set: &CpuSet,
        object_type: ObjectType,
    ) -> Vec<&TopologyObject> {
        let mut objects = self.objects_with_type(object_type);
        objects.retain(|object| object.is_inside_cpuset(set));
        objects
    }

    /// Get the first largest object included in the given cpuset `set`
    ///
    /// Returns the first object that is included in `set` and whose parent is
    /// not, in descending depth and children iteration order.
    ///
    /// This is convenient for iterating over all largest objects within a CPU
    /// set by doing a loop getting the first largest object and clearing its
    /// CPU set from the remaining CPU set. This very pattern is exposed by
    /// the `largest_objects_inside_cpuset` method, which is why this method is
    /// not publicly exposed.
    ///
    /// That being said, if the cpuset is a strict subset of the root cpuset of
    /// this `Topology`, the work may be more efficiently done by
    /// `largest_cpuset_partition()`, which only needs to walk the topology
    /// tree once.
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set).
    fn first_largest_object_inside_cpuset(&self, set: &CpuSet) -> Option<&TopologyObject> {
        // If root object doesn't intersect this CPU set then no child will
        let root = self.root_object();
        let root_cpuset = root.cpuset().expect("Root should have a CPU set");
        if !root_cpuset.intersects(set) {
            return None;
        }

        // Walk the topoogy tree until we find an object included into set
        let mut parent = root;
        let mut parent_cpuset = root_cpuset;
        while !set.includes(&parent_cpuset) {
            // While the object intersects without being included, look at children
            let old_parent = parent;
            for child in parent.normal_children() {
                if let Some(child_cpuset) = child.cpuset() {
                    // This child intersects, make it the new parent and recurse
                    if set.intersects(&child_cpuset) {
                        parent = child;
                        parent_cpuset = child_cpuset;
                    }
                }
            }
            assert!(
                !ptr::eq(parent, old_parent),
                "This should not happen because...\n\
                - The root intersects, so it has at least one index from the set\n\
                - The lowest-level children are PUs, which have only one index set,\
                  so one of them should pass the includes() test"
            );
        }
        Some(parent)
    }
}

/// Iterator over largest objects inside a cpuset
#[derive(Clone, Debug)]
struct LargestObjectsInsideCpuSet<'topology> {
    topology: &'topology Topology,
    set: CpuSet,
}
//
impl<'topology> Iterator for LargestObjectsInsideCpuSet<'topology> {
    type Item = &'topology TopologyObject;

    fn next(&mut self) -> Option<Self::Item> {
        let object = self
            .topology
            .first_largest_object_inside_cpuset(&self.set)?;
        let object_cpuset = object
            .cpuset()
            .expect("Output of first_largest_object_inside_cpuset should have a cpuset");
        self.set.and_not_assign(&object_cpuset);
        Some(object)
    }
}
//
impl FusedIterator for LargestObjectsInsideCpuSet<'_> {}

/// # Finding objects covering at least a CPU set
//
// This is inspired by the upstream functionality described at
// https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__find__covering.html
// but the code had to be ported to Rust because it's inline
impl Topology {
    /// Get the lowest object covering at least the given cpuset `set`
    ///
    /// No object is considered to cover the empty cpuset, therefore such a
    /// request will always return None, as if a set going outside of the root
    /// cpuset were passed as input.
    pub fn smallest_object_covering_cpuset(&self, set: &CpuSet) -> Option<&TopologyObject> {
        let root = self.root_object();
        if !root.covers_cpuset(set) || set.is_empty() {
            return None;
        }
        let mut parent = root;
        while let Some(child) = parent.normal_child_covering_cpuset(set) {
            parent = child;
        }
        Some(parent)
    }

    /// Get the first data (or unified) cache covering the given cpuset
    pub fn first_cache_covering_cpuset(&self, set: &CpuSet) -> Option<&TopologyObject> {
        let first_obj = self.smallest_object_covering_cpuset(set)?;
        std::iter::once(first_obj)
            .chain(first_obj.ancestors())
            .find(|obj| obj.object_type().is_cpu_data_cache())
    }

    /// Enumerate objects covering the given cpuset `set` at a certain depth
    ///
    /// Objects are not considered to cover the empty CPU set (otherwise a list
    /// of all objects would be returned). Therefore, an empty iterator will
    /// always be returned for I/O or Misc depths as those objects have no cpusets.
    pub fn objects_covering_cpuset_at_depth<'result>(
        &'result self,
        set: &'result CpuSet,
        depth: Depth,
    ) -> impl Iterator<Item = &TopologyObject> + Clone + DoubleEndedIterator + FusedIterator + 'result
    {
        self.objects_at_depth(depth)
            .filter(|object| object.covers_cpuset(set))
    }

    /// Get objects covering the given cpuset `set` with a certain type
    ///
    /// Objects are not considered to cover the empty CPU set (otherwise a list
    /// of all objects would be returned). Therefore, an empty iterator will
    /// always be returned for I/O or Misc depths as those objects have no cpusets.
    ///
    /// If you know that objects of this type should only appear at a single
    /// depth (which is true of most object types with the notable exception of
    /// Group), you can avoid allocating a `Vec` by probing said depth like this:
    ///
    /// ```
    /// # fn main() -> anyhow::Result<()> {
    /// #     let topology = hwloc2::Topology::new().unwrap();
    /// #     let object_type = hwloc2::objects::types::ObjectType::PU;
    /// #     let set = hwloc2::bitmap::CpuSet::new();
    /// topology.objects_covering_cpuset_at_depth(&set, topology.depth_for_type(object_type)?)
    /// #     ; Ok(())
    /// # }
    /// ```
    pub fn objects_covering_cpuset_with_type(
        &self,
        set: &CpuSet,
        object_type: ObjectType,
    ) -> Vec<&TopologyObject> {
        let mut objects = self.objects_with_type(object_type);
        objects.retain(|object| object.covers_cpuset(set));
        objects
    }
}

/// # Finding other objects
//
// This is inspired by the upstream functionality described at
// https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__find__misc.html
// but the code had to be ported to Rust because it's inline
impl Topology {
    /// Get the object of type [`ObjectType::PU`] with the specified OS index
    ///
    /// If you want to convert an entire CPU set into the PU objects it
    /// contains, using `pus_from_cpuset` will be more efficient than repeatedly
    /// calling this function with every OS index from the CpuSet.
    pub fn pu_with_os_index(&self, os_index: u32) -> Option<&TopologyObject> {
        self.objs_and_os_indices(ObjectType::PU)
            .find_map(|(pu, pu_os_index)| (pu_os_index == os_index).then_some(pu))
    }

    /// Get the objects of type [`ObjectType::PU`] covered by the specified cpuset
    pub fn pus_from_cpuset<'result>(
        &'result self,
        cpuset: &'result CpuSet,
    ) -> impl Iterator<Item = &TopologyObject> + Clone + DoubleEndedIterator + FusedIterator + 'result
    {
        self.objs_and_os_indices(ObjectType::PU)
            .filter_map(|(pu, os_index)| cpuset.is_set(os_index).then_some(pu))
    }

    /// Get the object of type [`ObjectType::NUMANode`] with the specified OS index
    ///
    /// If you want to convert an entire NodeSet into the NUMANode objects it
    /// contains, using `nodes_from_cpuset` will be more efficient than repeatedly
    /// calling this function with every OS index from the NodeSet.
    pub fn node_with_os_index(&self, os_index: u32) -> Option<&TopologyObject> {
        self.objs_and_os_indices(ObjectType::NUMANode)
            .find_map(|(node, node_os_index)| (node_os_index == os_index).then_some(node))
    }

    /// Get the objects of type [`ObjectType::NUMANode`] covered by the specified nodeset
    pub fn nodes_from_nodeset<'result>(
        &'result self,
        nodeset: &'result NodeSet,
    ) -> impl Iterator<Item = &TopologyObject> + Clone + DoubleEndedIterator + FusedIterator + 'result
    {
        self.objs_and_os_indices(ObjectType::NUMANode)
            .filter_map(|(node, os_index)| nodeset.is_set(os_index).then_some(node))
    }

    /// Get a list of `(&TopologyObject, OS index)` tuples for an `ObjectType`
    /// that is guaranteed to appear only at one depth of the topology and to
    /// have an OS index.
    ///
    /// # Panics
    ///
    /// Will panic if the object type appears at more than one depth or do not
    /// have an OS index.
    fn objs_and_os_indices(
        &self,
        ty: ObjectType,
    ) -> impl Iterator<Item = (&TopologyObject, u32)>
           + Clone
           + DoubleEndedIterator
           + ExactSizeIterator
           + FusedIterator {
        self.objects_at_depth(
            self.depth_for_type(ty)
                .expect("These objects should only appear at a single depth"),
        )
        .map(|obj| {
            (
                obj,
                obj.os_index()
                    .expect("These objects should have an OS index"),
            )
        })
    }

    /// Enumerate objects at the same depth as `obj`, but with increasing
    /// physical distance (i.e. from increasingly higher common ancestors in the
    /// topology tree)
    ///
    /// # Panics
    ///
    /// `obj` must have a cpuset, otherwise this function will panic.
    pub fn closest_objects<'result>(
        &'result self,
        obj: &'result TopologyObject,
    ) -> impl Iterator<Item = &TopologyObject> + Clone + 'result {
        // Track which CPUs map into objects we don't want to report
        // (current object or already reported object)
        let mut known_cpuset = obj.cpuset().expect("Target object must have a cpuset");

        // Assert that an object has a cpuset, return both
        fn obj_and_cpuset<'obj>(
            obj: &'obj TopologyObject,
            error: &str,
        ) -> (&'obj TopologyObject, &'obj CpuSet) {
            (obj, obj.cpuset().expect(error))
        }

        // Find the first ancestor of an object that knows about more objects
        // than that object (if any), and return it along with its cpuset
        fn find_larger_parent<'obj>(
            known_obj: &'obj TopologyObject,
            known_cpuset: &CpuSet,
        ) -> Option<(&'obj TopologyObject, &'obj CpuSet)> {
            known_obj
                .ancestors()
                .map(|ancestor| {
                    obj_and_cpuset(
                        ancestor,
                        "Ancestors of an obj with a cpuset should have a cpuset",
                    )
                })
                .find(|&(_ancestor, ancestor_cpuset)| ancestor_cpuset != known_cpuset)
        }
        let mut ancestor_and_cpuset = find_larger_parent(&obj, &known_cpuset);

        // Prepare to jointly iterate over cousins and their cpusets
        let cousins_and_cpusets = self
            .objects_at_depth(obj.depth())
            .map(|cousin| {
                obj_and_cpuset(
                    cousin,
                    "Cousins of an obj with a cpuset should have a cpuset",
                )
            })
            .collect::<Vec<_>>();
        let mut cousin_idx = 0;

        // Emit the final iterator
        std::iter::from_fn(move || {
            loop {
                // Look for a cousin that is part of ancestor_cpuset but not known_cpuset
                let (ancestor, ancestor_cpuset) = ancestor_and_cpuset?;
                while let Some((cousin, cousin_cpuset)) = cousins_and_cpusets.get(cousin_idx) {
                    cousin_idx += 1;
                    if ancestor_cpuset.includes(cousin_cpuset)
                        && !known_cpuset.includes(cousin_cpuset)
                    {
                        return Some(*cousin);
                    }
                }

                // We ran out of cousins, go up one ancestor level or end
                // iteration if we reached the top of the tree.
                let known_obj = ancestor;
                known_cpuset = ancestor_cpuset;
                let (ancestor, ancestor_cpuset) = find_larger_parent(&known_obj, &known_cpuset)?;
                ancestor_and_cpuset = Some((ancestor, ancestor_cpuset));
                cousin_idx = 0;
            }
        })
    }

    /// Find an object via a parent->child chain specified by types and indices
    ///
    /// For example, if called with `&[(NUMANode, 0), (Package, 1), (Core, 2)]`,
    /// this will return the third core object below the second package below
    /// the first NUMA node.
    ///
    /// # Panics
    ///
    /// All objects must have a cpuset, otherwise this function will panic.
    pub fn object_by_type_index_path(
        &self,
        path: &[(ObjectType, usize)],
    ) -> Option<&TopologyObject> {
        let mut obj = self.root_object();
        for &(ty, idx) in path {
            // Check out cpuset
            let cpuset = obj
                .cpuset()
                .expect("All objects in path should have a cpuset");

            // Avoid allocation in common case where ty only appears at one depth
            if let Ok(depth) = self.depth_for_type(ty) {
                obj = self
                    .objects_inside_cpuset_at_depth(cpuset, depth)
                    .nth(idx)?;
            } else {
                obj = self.objects_inside_cpuset_with_type(cpuset, ty).get(idx)?;
            }
        }
        Some(obj)
    }

    /// Find an object of a different type with the same locality
    ///
    /// If the source object src is a normal or memory type, this function
    /// returns an object of type type with same CPU and node sets, either below
    /// or above in the hierarchy.
    ///
    /// If the source object src is a PCI or an OS device within a PCI device,
    /// the function may either return that PCI device, or another OS device in
    /// the same PCI parent. This may for instance be useful for converting
    /// between OS devices such as "nvml0" or "rsmi1" used in distance
    /// structures into the the PCI device, or the CUDA or OpenCL OS device that
    /// correspond to the same physical card.
    ///
    /// If specified, parameter `subtype` restricts the search to objects whose
    /// [`TopologyObject::subtype()`] attribute exists and is equal to `subtype`
    /// (case-insensitively), for instance "OpenCL" or "CUDA".
    ///
    /// If specified, parameter `name_prefix` restricts the search to objects
    /// whose [`TopologyObject::name()`] attribute exists and starts with
    /// `name_prefix` (case-insensitively), for instance "rsmi" for matching
    /// "rsmi0".
    ///
    /// If multiple objects match, the first one is returned.
    ///
    /// This function will not walk the hierarchy across bridges since the PCI
    /// locality may become different. This function cannot also convert between
    /// normal/memory objects and I/O or Misc objects.
    ///
    /// If no matching object could be found, or if the source object and target
    /// type are incompatible, `None` will be returned.
    ///
    /// # Panics
    ///
    /// If a string with inner NUL chars is passed as `subtype` or `name_prefix`.
    pub fn object_with_same_locality(
        &self,
        src: &TopologyObject,
        ty: ObjectType,
        subtype: Option<&str>,
        name_prefix: Option<&str>,
    ) -> Option<&TopologyObject> {
        let to_libc = |s: &str| LibcString::new(s).expect("Can't pass NUL char to hwloc");
        let subtype = subtype.map(to_libc);
        let name_prefix = name_prefix.map(to_libc);
        let borrow_pchar = |opt: &Option<LibcString>| -> *const c_char {
            opt.as_ref().map(|s| s.borrow()).unwrap_or(ptr::null())
        };
        let ptr = unsafe {
            ffi::hwloc_get_obj_with_same_locality(
                self.as_ptr(),
                src,
                ty.into(),
                borrow_pchar(&subtype),
                borrow_pchar(&name_prefix),
                0,
            )
        };
        (!ptr.is_null()).then(|| unsafe { &*ptr })
    }
}

/// # Distributing items over a topology
//
// Inspired by https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__distribute.html,
// but the inline header implementation had to be rewritten in Rust.
impl Topology {
    /// Distribute `num_sets` items over the topology under `roots`
    ///
    /// This function will return `num_sets` cpusets recursively distributed
    /// linearly over the topology, under objects `roots`.
    ///
    /// To distribute over the entire topology, just pass `&[self.root_object()]`
    /// as the `roots` parameter.
    ///
    /// If there is no depth limit, which is achieved by setting `max_depth` to
    /// `u32::MAX`, the distribution is done down to the depth where there is
    /// only one CPU to distribute, which is similar to the following bitmap
    /// manipulation...
    ///
    /// ```
    /// # let topology = Topology::new().unwrap();
    /// # let roots = &[topology.root_object()];
    /// let cpusets =
    ///     roots.iter()
    ///         .flat_map(|root| root.cpuset().unwrap_or_else(CpuSet::new()))
    ///         .map(|idx| CpuSet::from(idx))
    ///         .collect::<Vec<_>>();
    /// ```
    ///
    /// ...except the cpusets will be returned in hwloc's logical index order,
    /// not in OS index order, so neighbouring cpusets in the output Vec are
    /// adjacent in the hardware topology and have a high chance of sharing
    /// resources like L3 caches.
    ///
    /// By setting the `max_depth` parameter to a lower limit, one can ensure
    /// that once the desired depth is reached or passed, distribution stops and
    /// one copy of the associated cpuset is returned per CPU core inside the
    /// cpuset at that depth.
    ///
    /// A typical use of this function is to distribute n threads over a
    /// machine, giving each of them as much private cache as possible and
    /// keeping them locally in number order.
    ///
    /// The caller may typically want to also call `Bitmap::singlify()`
    /// before binding a thread so that it does not move at all.
    ///
    /// # Panics
    ///
    /// Root objects should have a CPU set, this function will panic if that is
    /// not the case.
    pub fn distribute_cpusets(
        &self,
        roots: &[&TopologyObject],
        num_sets: usize,
        max_depth: u32,
        flags: DistributeFlags,
    ) -> Vec<CpuSet> {
        /* /// Recursive implementation of `distribute_cpusets`
        fn recurse(
            roots: impl Iterator<Item = &TopologyObject> + Clone,
            num_sets: usize,
            max_depth: u32,
            flags: DistributeFlags,
            result: &mut Vec<CpuSet>
        ) */
    }
}

bitflags! {
    /// Flags to be given to [`Topology::distributed_cpuset()`]
    #[repr(C)]
    pub struct DistributeFlags: c_ulong {
        /// Distribute in reverse order, starting from the last objects
        const REVERSE = (1<<0);
    }
}

// # General-purpose internal utilities
impl Topology {
    /// Returns the contained hwloc topology pointer for interaction with hwloc.
    fn as_ptr(&self) -> *const RawTopology {
        self.0.as_ptr()
    }

    /// Returns the contained hwloc topology pointer for interaction with hwloc.
    pub(crate) fn as_mut_ptr(&mut self) -> *mut RawTopology {
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
        let mut clone = ptr::null_mut();
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
