//! Memory binding

use crate::{
    bitmaps::{Bitmap, BitmapKind, RawBitmap, SpecializedBitmap},
    errors::{self, FlagsError, RawHwlocError},
    ffi,
    memory::{self, nodesets::NodeSet},
    topology::{RawTopology, Topology},
    ProcessId,
};
#[cfg(doc)]
use crate::{cpu::cpusets::CpuSet, topology::support::MemoryBindingSupport};
use bitflags::bitflags;
use derive_more::Display;
use errno::{errno, Errno};
use libc::{ENOMEM, ENOSYS, EXDEV};
use num_enum::{IntoPrimitive, TryFromPrimitive, TryFromPrimitiveError};
use std::{
    borrow::{Borrow, BorrowMut},
    ffi::{c_int, c_void},
    fmt::{self, Debug, Display},
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
};
use thiserror::Error;

/// # Memory binding
///
/// Memory binding can be done three ways:
///
/// - Explicit memory allocation through [`allocate_bound_memory()`] and friends:
///   the binding will have effect on the memory allocated by these functions.
/// - Implicit memory binding through process/thread binding policy through
///   [`bind_memory()`] and friends: the binding will be applied to subsequent
///   memory allocations by the target process/thread.
/// - Migration of existing memory ranges through [`bind_memory_area()`] and
///   friends: already-allocated data will be migrated to the target NUMA
///   nodes.
///
/// Not all operating systems support all three ways.
/// [`Topology::feature_support()`] may be used to query about the actual memory
/// binding support in the currently used operating system. Individual memory
/// binding functions will clarify which support flags they require. The most
/// portable operation, where usable, is [`binding_allocate_memory()`].
///
/// By default, when the requested binding operation is not available, hwloc
/// will go for a similar binding operation (with side-effects, smaller
/// binding set, etc). You can inhibit this with flag [`STRICT`], at the
/// expense of reducing portability across operating systems.
///
/// Memory can be bound by [`CpuSet`] or [`NodeSet`], but memory binding by
/// CPU set cannot work for CPU-less NUMA memory nodes. Binding by node set
/// should therefore be preferred whenever possible.
///
/// You should specify one of the [`ASSUME_SINGLE_THREAD`], [`THREAD`] and
/// [`PROCESS`] flags (listed in order of decreasing portability) when using any
/// of the functions that target a process, but some functions may only support
/// a subset of these flags.
///
/// On some operating systems, memory binding affects CPU binding. You can avoid
/// this at the cost of reducing portability by specifying the
/// [`NO_CPU_BINDING`] flag.
///
/// [`allocate_bound_memory()`]: Topology::allocate_bound_memory()
/// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
/// [`bind_memory_area()`]: Topology::bind_memory_area()
/// [`bind_memory()`]: Topology::bind_memory()
/// [`binding_allocate_memory()`]: Topology::binding_allocate_memory()
/// [`NO_CPU_BINDING`]: MemoryBindingFlags::NO_CPU_BINDING
/// [`PROCESS`]: MemoryBindingFlags::PROCESS
/// [`STRICT`]: MemoryBindingFlags::STRICT
/// [`THREAD`]: MemoryBindingFlags::THREAD
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__membinding.html
impl Topology {
    /// Allocate some memory
    ///
    /// This is equivalent to [`libc::malloc()`], except that it tries to
    /// allocate page-aligned memory from the OS.
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot allocate page-aligned memory
    /// - [`AllocationFailed`] if memory allocation failed
    ///
    /// [`AllocationFailed`]: MemoryBindingError::AllocationFailed
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_alloc")]
    pub fn allocate_memory(&self, len: usize) -> Result<Bytes, MemoryAllocationError<NodeSet>> {
        self.allocate_memory_impl(len)
    }

    /// Like allocate_memory, but polymorphic on Set
    fn allocate_memory_impl<Set: SpecializedBitmap>(
        &self,
        len: usize,
    ) -> Result<Bytes, MemoryAllocationError<Set>> {
        memory::binding::call_hwloc_allocate("hwloc_alloc", None, || unsafe {
            ffi::hwloc_alloc(self.as_ptr(), len)
        })
        .map(|base| unsafe { Bytes::wrap(self, base, len) })
    }

    /// Allocate some memory on NUMA nodes specified by `set`
    ///
    /// If you do not care about changing the binding of the current process or
    /// thread, you can maximize portability by using
    /// [`Topology::binding_allocate_memory()`] instead.
    ///
    /// Memory can be bound by either [`CpuSet`] or [`NodeSet`]. Binding by
    /// [`NodeSet`] is preferred because some NUMA memory nodes are not attached
    /// to CPUs, and thus cannot be bound by [`CpuSet`].
    ///
    /// Flags [`ASSUME_SINGLE_THREAD`], [`PROCESS`], [`THREAD`] and [`MIGRATE`]
    /// should not be used with this function.
    ///
    /// Requires [`MemoryBindingSupport::alloc()`].
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot allocate bound memory with the
    ///   requested policy
    /// - [`BadFlags`] if one of the flags [`MIGRATE`], [`PROCESS`] and
    ///   [`THREAD`] is specified
    /// - [`BadSet`] if the system can't bind memory to that CPU/node set
    /// - [`AllocationFailed`] if memory allocation failed
    ///
    /// [`AllocationFailed`]: MemoryBindingError::AllocationFailed
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadSet`]: MemoryBindingError::BadSet
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_alloc_membind")]
    pub fn allocate_bound_memory<Set: SpecializedBitmap>(
        &self,
        len: usize,
        set: &Set,
        policy: MemoryBindingPolicy,
        mut flags: MemoryBindingFlags,
    ) -> Result<Bytes, MemoryAllocationError<Set>> {
        Self::adjust_flags_for::<Set>(&mut flags);
        if !flags.is_valid(MemoryBoundObject::Area, MemoryBindingOperation::Allocate) {
            return Err(MemoryAllocationError::BadFlags(flags.into()));
        }
        memory::binding::call_hwloc_allocate("hwloc_alloc_membind", Some(set), || unsafe {
            ffi::hwloc_alloc_membind(
                self.as_ptr(),
                len,
                set.as_ref().as_ptr(),
                policy.into(),
                flags.bits(),
            )
        })
        .map(|base| unsafe { Bytes::wrap(self, base, len) })
    }

    /// Allocate some memory on NUMA nodes specified by `set` and `flags`,
    /// possibly rebinding current process or thread if needed
    ///
    /// This works like [`Topology::allocate_bound_memory()`] unless the
    /// allocation fails, in which case hwloc will attempt to change the current
    /// process or thread memory binding policy as directed instead before
    /// performing a normal allocation.
    ///
    /// Allocating memory that matches the current process/thread configuration
    /// is supported on more operating systems, so this is the most portable way
    /// to obtain a bound memory buffer.
    ///
    /// You should specify one of the [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and
    /// [`THREAD`] flags when using this function.
    ///
    /// Requires either [`MemoryBindingSupport::alloc()`], or one of
    /// [`MemoryBindingSupport::set_current_process()`] and
    /// [`MemoryBindingSupport::set_current_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system can neither allocate bound memory
    ///   nor rebind the current thread/process with the requested policy
    /// - [`BadFlags`] if flags [`PROCESS`] and [`THREAD`] were both specified
    /// - [`BadSet`] if the system can't bind memory to that CPU/node set
    /// - [`AllocationFailed`] if memory allocation failed
    ///
    /// [`AllocationFailed`]: MemoryBindingError::AllocationFailed
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadSet`]: MemoryBindingError::BadSet
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_alloc_membind_policy")]
    pub fn binding_allocate_memory<Set: SpecializedBitmap>(
        &self,
        len: usize,
        set: &Set,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<Bytes, MemoryAllocationError<Set>> {
        // Try allocate_bound_memory first
        if let Ok(bytes) = self.allocate_bound_memory(len, set, policy, flags) {
            return Ok(bytes);
        }

        // If that doesn't work, try binding the current process
        self.bind_memory(set, policy, flags)?;

        // If that succeeds, try allocating more memory
        let mut bytes = self.allocate_memory_impl(len)?;

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
    /// Memory can be bound by either [`CpuSet`] or [`NodeSet`]. Binding by
    /// [`NodeSet`] is preferred because some NUMA memory nodes are not attached
    /// to CPUs, and thus cannot be bound by [`CpuSet`].
    ///
    /// You should specify one of the [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and
    /// [`THREAD`] flags when using this function.
    ///
    /// Requires [`MemoryBindingSupport::set_current_process()`] or
    /// [`MemoryBindingSupport::set_current_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot bind the current
    ///   thread/process with the requested policy
    /// - [`BadFlags`] if flags [`PROCESS`] and [`THREAD`] were both specified
    /// - [`BadSet`] if the system can't bind memory to that CPU/node set
    ///
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadSet`]: MemoryBindingError::BadSet
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_set_membind")]
    pub fn bind_memory<Set: SpecializedBitmap>(
        &self,
        set: &Set,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingError<Set>> {
        self.bind_memory_impl(
            "hwloc_set_membind",
            set,
            policy,
            flags,
            MemoryBoundObject::ThisProgram,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_set_membind(topology, set, policy, flags)
            },
        )
    }

    /// Reset the memory allocation policy of the current process or thread to
    /// the system default
    ///
    /// Depending on the operating system, this may correspond to
    /// [`MemoryBindingPolicy::FirstTouch`] (Linux, FreeBSD) or
    /// [`MemoryBindingPolicy::Bind`] (AIX, HP-UX, Solaris, Windows).
    ///
    /// You should specify one of the [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and
    /// [`THREAD`] flags when using this function, but the [`STRICT`] and
    /// [`MIGRATE`] flags should **not** be used with this function.
    ///
    /// Requires [`MemoryBindingSupport::set_current_process()`] or
    /// [`MemoryBindingSupport::set_current_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot unbind the current thread/process
    /// - [`BadFlags`] if one of flags [`STRICT`] and [`MIGRATE`] was specified,
    ///   or if flags [`PROCESS`] and [`THREAD`] were both specified
    ///
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "HWLOC_MEMBIND_DEFAULT")]
    pub fn unbind_memory(
        &self,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingError<NodeSet>> {
        self.unbind_memory_impl(
            "hwloc_set_membind",
            flags,
            MemoryBoundObject::ThisProgram,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_set_membind(topology, set, policy, flags)
            },
        )
    }

    /// Query the default memory binding policy and physical locality of the
    /// current process or thread
    ///
    /// You should specify one of the [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and
    /// [`THREAD`] flags when using this function. However, flags [`MIGRATE`]
    /// and [`NO_CPU_BINDING`] should **not** be used with this function.
    ///
    /// The [`STRICT`] flag is only meaningful when [`PROCESS`] is also
    /// specified. In this case, hwloc will check the default memory policies
    /// and nodesets for all threads in the process. If they are not identical,
    /// Err([`MixedResults`]) is returned. Otherwise,
    /// the shared configuration is returned.
    ///
    /// Otherwise, if [`PROCESS`] is specified and [`STRICT`] is not specified,
    /// the default sets from each thread are logically OR'ed together. If all
    /// threads' default policies are the same, that shared policy is returned,
    /// otherwise no policy is returned.
    ///
    /// In the [`THREAD`] and [`ASSUME_SINGLE_THREAD`] case, there is only one
    /// set and policy, they are returned.
    ///
    /// Bindings can be queried as [`CpuSet`] or [`NodeSet`]. Querying by
    /// [`NodeSet`] is preferred because some NUMA memory nodes are not attached
    /// to CPUs, and thus cannot be bound by [`CpuSet`].
    ///
    /// Requires [`MemoryBindingSupport::get_current_process()`] or
    /// [`MemoryBindingSupport::get_current_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot query the current thread/process
    ///   binding
    /// - [`BadFlags`] if one of flags [`MIGRATE`] and [`NO_CPU_BINDING`] was
    ///   specified, if flags [`PROCESS`] and [`THREAD`] were both specified,
    ///   or if flag [`STRICT`] was specified without [`PROCESS`]
    /// - [`MixedResults`] if flags [`STRICT`] and [`PROCESS`] were specified
    ///   and memory binding is inhomogeneous across threads in the process
    ///
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`MixedResults`]: MemoryBindingError::MixedResults
    /// [`NO_CPU_BINDING`]: MemoryBindingFlags::NO_CPU_BINDING
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_get_membind")]
    pub fn memory_binding<Set: SpecializedBitmap>(
        &self,
        flags: MemoryBindingFlags,
    ) -> Result<(Set, Option<MemoryBindingPolicy>), MemoryBindingError<Set>> {
        self.memory_binding_impl(
            "hwloc_get_membind",
            flags,
            MemoryBoundObject::ThisProgram,
            MemoryBindingOperation::GetBinding,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_get_membind(topology, set, policy, flags)
            },
        )
    }

    /// Set the default memory binding policy of the specified process to prefer
    /// the NUMA node(s) specified by `set`.
    ///
    /// See also [`Topology::bind_memory()`] for general semantics, except this
    /// function requires [`MemoryBindingSupport::set_process()`].
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot bind the specified
    ///   thread/process with the requested policy
    /// - [`BadFlags`] if flags [`PROCESS`] and [`THREAD`] were both specified
    /// - [`BadSet`] if the system can't bind memory to that CPU/node set
    ///
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadSet`]: MemoryBindingError::BadSet
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_set_proc_membind")]
    pub fn bind_process_memory<Set: SpecializedBitmap>(
        &self,
        pid: ProcessId,
        set: &Set,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingError<Set>> {
        self.bind_memory_impl(
            "hwloc_set_proc_membind",
            set,
            policy,
            flags,
            MemoryBoundObject::Process,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_set_proc_membind(topology, pid, set, policy, flags)
            },
        )
    }

    /// Reset the memory allocation policy of the specified process to the
    /// system default
    ///
    /// See also [`Topology::unbind_memory()`] for general semantics, except
    /// this function requires [`MemoryBindingSupport::set_process()`].
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot unbind the specified
    ///   thread/process
    /// - [`BadFlags`] if one of flags [`STRICT`] and [`MIGRATE`] was specified,
    ///   or if flags [`PROCESS`] and [`THREAD`] were both specified
    ///
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    pub fn unbind_process_memory(
        &self,
        pid: ProcessId,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingError<NodeSet>> {
        self.unbind_memory_impl(
            "hwloc_set_proc_membind",
            flags,
            MemoryBoundObject::Process,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_set_proc_membind(topology, pid, set, policy, flags)
            },
        )
    }

    /// Query the default memory binding policy and physical locality of the
    /// specified process
    ///
    /// See [`Topology::memory_binding()`] for general semantics, except this
    /// function requires [`MemoryBindingSupport::get_process()`].
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot query the specified
    ///   thread/process' binding
    /// - [`BadFlags`] if one of flags [`MIGRATE`] and [`NO_CPU_BINDING`] was
    ///   specified, if flags [`PROCESS`] and [`THREAD`] were both specified,
    ///   or if flag [`STRICT`] was specified without [`PROCESS`]
    /// - [`MixedResults`] if flags [`STRICT`] and [`PROCESS`] were specified
    ///   and memory binding is inhomogeneous across threads in the process
    ///
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`MixedResults`]: MemoryBindingError::MixedResults
    /// [`NO_CPU_BINDING`]: MemoryBindingFlags::NO_CPU_BINDING
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_get_proc_membind")]
    pub fn process_memory_binding<Set: SpecializedBitmap>(
        &self,
        pid: ProcessId,
        flags: MemoryBindingFlags,
    ) -> Result<(Set, Option<MemoryBindingPolicy>), MemoryBindingError<Set>> {
        self.memory_binding_impl(
            "hwloc_get_proc_membind",
            flags,
            MemoryBoundObject::Process,
            MemoryBindingOperation::GetBinding,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_get_proc_membind(topology, pid, set, policy, flags)
            },
        )
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
    /// See also [`Topology::bind_memory()`] for general semantics, except the
    /// [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and [`THREAD`] flags should not be
    /// used with this function, and it requires
    /// [`MemoryBindingSupport::set_area()`].
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot bind the specified memory area
    ///   with the requested policy
    /// - [`BadFlags`] if one of flags [`PROCESS`] and [`THREAD`] was specified
    /// - [`BadSet`] if the system can't bind memory to that CPU/node set
    /// - [`BadTarget`] if `target` is a zero-sized object
    ///
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadSet`]: MemoryBindingError::BadSet
    /// [`BadTarget`]: MemoryBindingError::BadTarget
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_set_area_membind")]
    pub fn bind_memory_area<Target: ?Sized, Set: SpecializedBitmap>(
        &self,
        target: &Target,
        set: &Set,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingError<Set>> {
        let target_size = std::mem::size_of_val(target);
        if target_size == 0 {
            return Err(MemoryBindingError::BadTarget);
        }
        let target_ptr: *const Target = target;
        self.bind_memory_impl(
            "hwloc_set_area_membind",
            set,
            policy,
            flags,
            MemoryBoundObject::Area,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_set_area_membind(
                    topology,
                    target_ptr.cast::<c_void>(),
                    target_size,
                    set,
                    policy,
                    flags,
                )
            },
        )
    }

    /// Reset the memory allocation policy of the memory identified by `target`
    /// to the system default
    ///
    /// The warning about `Target` coverage in the documentation of
    /// [`Topology::bind_memory_area()`] also applies here.
    ///
    /// See also [`Topology::unbind_memory()`] for general semantics, except the
    /// [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and [`THREAD`] flags should not be
    /// used with this function, and it requires
    /// [`MemoryBindingSupport::set_area()`].
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot unbind the specified memory area
    /// - [`BadFlags`] if one of flags [`PROCESS`], [`THREAD`], [`STRICT`]
    ///   and [`MIGRATE`] was specified
    /// - [`BadTarget`] if `target` is a zero-sized object
    ///
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadTarget`]: MemoryBindingError::BadTarget
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    pub fn unbind_memory_area<Target: ?Sized>(
        &self,
        target: &Target,
        flags: MemoryBindingFlags,
    ) -> Result<(), MemoryBindingError<NodeSet>> {
        let target_size = std::mem::size_of_val(target);
        if target_size == 0 {
            return Err(MemoryBindingError::BadTarget);
        }
        let target_ptr: *const Target = target;
        self.unbind_memory_impl(
            "hwloc_set_area_membind",
            flags,
            MemoryBoundObject::Area,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_set_area_membind(
                    topology,
                    target_ptr.cast::<c_void>(),
                    target_size,
                    set,
                    policy,
                    flags,
                )
            },
        )
    }

    /// Query the memory binding policy and physical locality of the
    /// memory identified by `target`
    ///
    /// The warning about `Target` coverage in the documentation of
    /// [`Topology::bind_memory_area()`] also applies here.
    ///
    /// If the [`STRICT`] flag is specified, hwloc will check the default memory
    /// policies and nodesets for all memory pages covered by `target`. If these
    /// are not identical,
    /// Err([`MixedResults`]) is returned. Otherwise,
    /// the shared configuration is returned.
    ///
    /// If [`STRICT`] is not specified, the union of all NUMA nodes containing
    /// pages in the address range is calculated. If all pages in the target
    /// have the same policy, it is returned, otherwise no policy is returned.
    ///
    /// See also [`Topology::memory_binding()`] for general semantics, except...
    ///
    /// - The [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and [`THREAD`] flags should
    ///   not be used with this function
    /// - As mentioned above, [`STRICT`] has a specific meaning in the context
    ///   of this function.
    /// - This function requires [`MemoryBindingSupport::get_area()`].
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot query the specified
    ///   memory area's binding
    /// - [`BadFlags`] if one of flags [`PROCESS`], [`THREAD`], [`MIGRATE`]
    ///   and [`NO_CPU_BINDING`] was specified
    /// - [`BadTarget`] if `target` is a zero-sized object
    /// - [`MixedResults`] if flags [`STRICT`] and [`PROCESS`] were specified
    ///   and memory binding is inhomogeneous across target memory pages
    ///
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadTarget`]: MemoryBindingError::BadTarget
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`MixedResults`]: MemoryBindingError::MixedResults
    /// [`NO_CPU_BINDING`]: MemoryBindingFlags::NO_CPU_BINDING
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_get_area_membind")]
    pub fn area_memory_binding<Target: ?Sized, Set: SpecializedBitmap>(
        &self,
        target: &Target,
        flags: MemoryBindingFlags,
    ) -> Result<(Set, Option<MemoryBindingPolicy>), MemoryBindingError<Set>> {
        let target_size = std::mem::size_of_val(target);
        if target_size == 0 {
            return Err(MemoryBindingError::BadTarget);
        }
        let target_ptr: *const Target = target;
        self.memory_binding_impl(
            "hwloc_get_area_membind",
            flags,
            MemoryBoundObject::Area,
            MemoryBindingOperation::GetBinding,
            |topology, set, policy, flags| unsafe {
                ffi::hwloc_get_area_membind(
                    topology,
                    target_ptr.cast::<c_void>(),
                    target_size,
                    set,
                    policy,
                    flags,
                )
            },
        )
    }

    /// Get the NUMA nodes where the memory identified by `target` is physically
    /// allocated
    ///
    /// The warning about `Target` coverage in the documentation of
    /// [`Topology::bind_memory_area()`] also applies here.
    ///
    /// If pages spread to multiple nodes, it is not specified whether they
    /// spread equitably, or whether most of them are on a single node, etc.
    ///
    /// The operating system may move memory pages from one processor to another
    /// at any time according to their binding, so this function may return
    /// something that is already outdated.
    ///
    /// See also [`Topology::memory_binding()`] for general semantics, except
    /// the [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and [`THREAD`] flags should
    /// not be used with this function, and it requires
    /// [`MemoryBindingSupport::get_area_memory_location()`].
    ///
    /// # Errors
    ///
    /// - [`Unsupported`] if the system cannot query the specified
    ///   memory area's location
    /// - [`BadFlags`] if one of flags [`PROCESS`], [`THREAD`], [`MIGRATE`]
    ///   and [`NO_CPU_BINDING`] was specified
    /// - [`BadTarget`] if `target` is a zero-sized object
    /// - [`MixedResults`] if flags [`STRICT`] and [`PROCESS`] were specified
    ///   and memory binding is inhomogeneous across target memory pages
    ///
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadTarget`]: MemoryBindingError::BadTarget
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`MixedResults`]: MemoryBindingError::MixedResults
    /// [`NO_CPU_BINDING`]: MemoryBindingFlags::NO_CPU_BINDING
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_get_area_memlocation")]
    pub fn area_memory_location<Target: ?Sized, Set: SpecializedBitmap>(
        &self,
        target: &Target,
        flags: MemoryBindingFlags,
    ) -> Result<Set, MemoryBindingError<Set>> {
        let target_size = std::mem::size_of_val(target);
        if target_size == 0 {
            return Err(MemoryBindingError::BadTarget);
        }
        let target_ptr: *const Target = target;
        self.memory_binding_impl(
            "hwloc_get_area_memlocation",
            flags,
            MemoryBoundObject::ThisProgram,
            MemoryBindingOperation::GetLastLocation,
            |topology, set, policy, flags| unsafe {
                *policy = -1;
                ffi::hwloc_get_area_memlocation(
                    topology,
                    target_ptr.cast::<c_void>(),
                    target_size,
                    set,
                    flags,
                )
            },
        )
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
        api: &'static str,
        set: &Set,
        policy: MemoryBindingPolicy,
        mut flags: MemoryBindingFlags,
        target: MemoryBoundObject,
        set_membind_like: impl FnOnce(
            *const RawTopology,
            *const RawBitmap,
            RawMemoryBindingPolicy,
            c_int,
        ) -> c_int,
    ) -> Result<(), MemoryBindingError<Set>> {
        let operation = MemoryBindingOperation::Bind;
        Self::adjust_flags_for::<Set>(&mut flags);
        if !flags.is_valid(target, operation) {
            return Err(MemoryBindingError::BadFlags(flags.into()));
        }
        memory::binding::call_hwloc_int(api, target, operation, Some(set), || {
            set_membind_like(
                self.as_ptr(),
                set.as_ref().as_ptr(),
                policy.into(),
                flags.bits(),
            )
        })
    }

    /// Call an hwloc memory binding function to unbind some memory
    fn unbind_memory_impl(
        &self,
        api: &'static str,
        flags: MemoryBindingFlags,
        target: MemoryBoundObject,
        set_membind_like: impl FnOnce(
            *const RawTopology,
            *const RawBitmap,
            RawMemoryBindingPolicy,
            c_int,
        ) -> c_int,
    ) -> Result<(), MemoryBindingError<NodeSet>> {
        let operation = MemoryBindingOperation::Unbind;
        if !flags.is_valid(target, operation) {
            return Err(MemoryBindingError::BadFlags(flags.into()));
        }
        memory::binding::call_hwloc_int(api, target, operation, None, || {
            set_membind_like(self.as_ptr(), ptr::null(), 0, flags.bits())
        })
    }

    /// Call an hwloc memory binding query function
    fn memory_binding_impl<Set: SpecializedBitmap>(
        &self,
        api: &'static str,
        mut flags: MemoryBindingFlags,
        target: MemoryBoundObject,
        operation: MemoryBindingOperation,
        get_membind_like: impl FnOnce(
            *const RawTopology,
            *mut RawBitmap,
            *mut RawMemoryBindingPolicy,
            c_int,
        ) -> c_int,
    ) -> Result<(Set, Option<MemoryBindingPolicy>), MemoryBindingError<Set>> {
        Self::adjust_flags_for::<Set>(&mut flags);
        if !flags.is_valid(target, operation) {
            return Err(MemoryBindingError::BadFlags(flags.into()));
        }
        let mut set = Bitmap::new();
        let mut raw_policy = 0;
        memory::binding::call_hwloc_int(api, target, operation, None, || {
            get_membind_like(
                self.as_ptr(),
                set.as_mut_ptr(),
                &mut raw_policy,
                flags.bits(),
            )
        })
        .map(|()| {
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

bitflags! {
    /// Memory binding flags.
    ///
    /// These bit flags can be used to refine the binding policy. All flags can
    /// be OR'ed together with the exception of `ASSUME_SINGLE_THREAD`, `THREAD`
    /// and `PROCESS`, of which at most one must be specified. The most portable
    /// option is `ASSUME_SINGLE_THREAD`, when it is applicable.
    ///
    /// Not all systems support all kinds of binding,
    /// [`Topology::feature_support()`] may be used to query the
    /// actual memory binding support in the currently used operating system.
    #[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
    #[doc(alias = "hwloc_membind_flags_t")]
    #[repr(C)]
    pub struct MemoryBindingFlags: c_int {
        /// Assume that the target process is single threaded
        ///
        /// This lets hwloc pick between thread and process binding for
        /// increased portability.
        ///
        /// This is mutually exclusive with `PROCESS` and `THREAD`.
        const ASSUME_SINGLE_THREAD = 0;

        /// Set policy for all threads of the specified process
        ///
        /// This is mutually exclusive with `ASSUME_SINGLE_THREAD` and `PROCESS`.
        #[doc(alias = "HWLOC_MEMBIND_PROCESS")]
        const PROCESS = (1<<0);

        /// Set policy for a specific thread of the specified process
        ///
        /// This is mutually exclusive with `ASSUME_SINGLE_THREAD` and `THREAD`.
        #[doc(alias = "HWLOC_MEMBIND_THREAD")]
        const THREAD = (1<<1);

        /// Request strict binding from the OS
        ///
        /// If this flag is set, a binding function will fail if the binding can
        /// not be guaranteed or completely enforced. Otherwise, hwloc will
        /// attempt to achieve an approximation of the requested binding (e.g.
        /// targeting more or less threads and NUMA nodes).
        ///
        /// This flag has slightly different meanings depending on which
        /// function it is used with.
        #[doc(alias = "HWLOC_MEMBIND_STRICT")]
        const STRICT = (1<<2);

        /// Migrate existing allocated memory
        ///
        /// If the memory cannot be migrated and the `STRICT` flag is set, an
        /// error will be returned.
        ///
        /// This flag is only meaningful on operations that bind memory.
        ///
        /// Requires [`MemoryBindingSupport::migrate()`].
        #[doc(alias = "HWLOC_MEMBIND_MIGRATE")]
        const MIGRATE = (1<<3);

        /// Avoid any effect on CPU binding
        ///
        /// On some operating systems, some underlying memory binding
        /// functions also bind the application to the corresponding CPU(s).
        /// Using this flag will cause hwloc to avoid using OS functions that
        /// could potentially affect CPU bindings.
        ///
        /// Note, however, that using this flag may reduce hwloc's overall
        /// memory binding support.
        #[doc(alias = "HWLOC_MEMBIND_NOCPUBIND")]
        const NO_CPU_BINDING = (1<<4);

        /// Consider the bitmap argument as a nodeset.
        ///
        /// The bitmap argument is considered a nodeset if this flag is given,
        /// or a cpuset otherwise by default.
        ///
        /// Memory binding by CPU set cannot work for CPU-less NUMA memory nodes.
        /// Binding by nodeset should therefore be preferred whenever possible.
        //
        // NOTE: This flag is automatically set by the implementation
        #[doc(hidden)]
        #[doc(alias = "HWLOC_MEMBIND_BYNODESET")]
        const BY_NODE_SET = (1<<5);
    }
}
//
impl MemoryBindingFlags {
    /// Truth that these flags are in a valid state
    pub(crate) fn is_valid(
        self,
        target: MemoryBoundObject,
        operation: MemoryBindingOperation,
    ) -> bool {
        // Intrinsically incompatible flag combination
        if self.contains(Self::PROCESS | Self::THREAD) {
            return false;
        }

        // Support for PROCESS and THREAD
        let good_for_target = match target {
            MemoryBoundObject::Area => !self.intersects(Self::PROCESS | Self::THREAD),
            MemoryBoundObject::Process => !self.contains(Self::THREAD),
            MemoryBoundObject::ThisProgram => true,
        };

        // Support fo STRICT, MIGRATE and NO_CPU_BINDING
        good_for_target
            && match operation {
                MemoryBindingOperation::GetLastLocation => {
                    !self.intersects(Self::STRICT | Self::MIGRATE | Self::NO_CPU_BINDING)
                }
                MemoryBindingOperation::GetBinding => {
                    if self.intersects(Self::MIGRATE | Self::NO_CPU_BINDING) {
                        return false;
                    }
                    match target {
                        MemoryBoundObject::Area | MemoryBoundObject::Process => true,
                        MemoryBoundObject::ThisProgram => {
                            !self.contains(Self::STRICT) || self.contains(Self::PROCESS)
                        }
                    }
                }
                MemoryBindingOperation::Unbind => !self.intersects(Self::STRICT | Self::MIGRATE),
                MemoryBindingOperation::Allocate => !self.contains(Self::MIGRATE),
                MemoryBindingOperation::Bind => true,
            }
    }
}
//
// NOTE: No default because user must consciously think about the need for PROCESS
//
/// Object that is being bound to particular NUMA nodes
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum MemoryBoundObject {
    /// A process, identified by its PID
    Process,

    /// A range of memory adresses, identified by a reference
    Area,

    /// The currently running program
    ThisProgram,
}
//
impl Display for MemoryBoundObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let display = match self {
            Self::Process => "the target process",
            Self::Area => "the target location",
            Self::ThisProgram => "the current process/thread",
        };
        f.pad(display)
    }
}
//
/// Binding operation
#[derive(Copy, Clone, Debug, Display, Eq, Hash, PartialEq)]
pub(crate) enum MemoryBindingOperation {
    GetBinding,
    Bind,
    Unbind,
    Allocate,
    GetLastLocation,
}

/// Rust mapping of the hwloc_membind_policy_t enum
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
pub(crate) type RawMemoryBindingPolicy = c_int;

/// Memory binding policy.
///
/// Not all systems support all kinds of binding.
/// [`Topology::feature_support()`] may be used to query the
/// actual memory binding support in the currently used operating system.
#[derive(
    Copy, Clone, Debug, Default, Display, Eq, Hash, IntoPrimitive, PartialEq, TryFromPrimitive,
)]
#[doc(alias = "hwloc_membind_policy_t")]
#[repr(i32)]
pub enum MemoryBindingPolicy {
    /// Allocate each memory page individually on the local NUMA
    /// node of the thread that touches it
    ///
    /// The given nodeset should usually be [`Topology::nodeset()`]
    /// so that the touching thread may run and allocate on any node in the
    /// system.
    ///
    /// On AIX, if the nodeset is smaller, pages are allocated locally (if the
    /// local node is in the nodeset) or from a random non-local node (otherwise).
    ///
    /// Requires [`MemoryBindingSupport::first_touch()`].
    #[doc(alias = "HWLOC_MEMBIND_FIRSTTOUCH")]
    FirstTouch = 1,

    /// Allocate memory on the specified nodes (most portable option)
    ///
    /// Requires [`MemoryBindingSupport::bind()`].
    #[default]
    #[doc(alias = "HWLOC_MEMBIND_BIND")]
    Bind = 2,

    /// Allocate memory on the given nodes in an interleaved round-robin manner
    ///
    /// The precise layout of the memory across multiple NUMA nodes is OS/system
    /// specific.
    ///
    /// Interleaving can be useful when threads distributed across the specified
    /// NUMA nodes will all be accessing the whole memory range concurrently,
    /// since the interleave will then balance the memory references.
    ///
    /// Requires [`MemoryBindingSupport::interleave()`].
    #[doc(alias = "HWLOC_MEMBIND_INTERLEAVE")]
    Interleave = 3,

    /// Migrate pages on next touch
    ///
    /// For each page bound with this policy, by next time it is touched (and
    /// next time only), it is moved from its current location to the local NUMA
    /// node of the thread where the memory reference occurred (if it needs to
    /// be moved at all).
    ///
    /// Requires [`MemoryBindingSupport::next_touch()`].
    #[doc(alias = "HWLOC_MEMBIND_NEXTTOUCH")]
    NextTouch = 4,
}

/// Errors that can occur when binding memory to NUMA nodes, querying bindings,
/// or allocating (possibly bound) memory
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum MemoryBindingError<Set: SpecializedBitmap> {
    /// The system does not support the specified action or policy
    ///
    /// For example, some systems only allow binding memory on a per-thread
    /// basis, whereas other systems only allow binding memory for all threads
    /// in a process.
    ///
    /// This error might not be reported if [`MemoryBindingFlags::STRICT`] is
    /// not set. Instead, the implementation is allowed to try to use a slightly
    /// different operation (with side-effects, binding more objects, etc.) when
    /// the requested operation is not exactly supported.
    #[error("requested memory binding action or policy is not supported")]
    Unsupported,

    /// Requested memory binding flags are not valid in this context
    ///
    /// Not all memory binding flag combinations make sense, either in isolation
    /// or in the context of a particular binding function. Please cross-check
    /// the documentation of [`MemoryBindingFlags`] and the function you were
    /// trying to call for more information.
    #[error(transparent)]
    BadFlags(FlagsError<MemoryBindingFlags>),

    /// Cannot bind to the target CPU or node set
    ///
    /// Operating systems can have various restrictions here, e.g. can only bind
    /// to NUMA node.
    ///
    /// This error should only be reported when trying to set memory bindings.
    ///
    /// This error might not be reported if [`MemoryBindingFlags::STRICT`] is
    /// not set. Instead, the implementation is allowed to try using a smaller
    /// or larger set to make the operation succeed.
    #[error("cannot bind {0} to {1}")]
    BadSet(MemoryBoundObject, Set),

    /// Cannot query the memory location of zero-sized target
    #[error("cannot query the memory location of zero-sized target")]
    BadTarget,

    /// Memory allocation failed even before trying to bind
    ///
    /// This error may only be returned by [`Topology::allocate_bound_memory()`]
    /// and [`Topology::binding_allocate_memory()`].
    #[error("failed to allocate memory")]
    AllocationFailed,

    /// Memory policies and nodesets vary from one thread to another
    ///
    /// This error is returned when querying a process' memory bindings with the
    /// flags [`PROCESS`] and [`STRICT`] specified. It means that the default
    /// memory policies and nodesets are not homogeneous across all threads of
    /// the target process.
    ///
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    #[error("binding varies from one thread of the process to another")]
    #[doc(alias = "HWLOC_MEMBIND_MIXED")]
    MixedResults,
}
//
impl<Set: SpecializedBitmap> From<MemoryBindingFlags> for MemoryBindingError<Set> {
    fn from(value: MemoryBindingFlags) -> Self {
        Self::BadFlags(value.into())
    }
}

/// Call an hwloc API that is about manipulating memory bindings and translate
/// known errors into higher-level `MemoryBindingError`s.
///
/// Validating flags is left up to the caller, to avoid allocating result
/// objects when it can be proved upfront that the request is invalid.
pub(crate) fn call_hwloc_int<Set: SpecializedBitmap>(
    api: &'static str,
    object: MemoryBoundObject,
    operation: MemoryBindingOperation,
    set: Option<&Set>,
    ffi: impl FnOnce() -> c_int,
) -> Result<(), MemoryBindingError<Set>> {
    match errors::call_hwloc_int_normal(api, ffi) {
        Ok(_) => Ok(()),
        Err(RawHwlocError { errno, .. }) => Err(decode_errno(
            object,
            operation,
            set,
            errno.expect("Unexpected hwloc error without errno"),
        )
        .expect("Unexpected errno value")),
    }
}

/// Errors that can occur when allocating memory
pub type MemoryAllocationError<Set> = MemoryBindingError<Set>;

/// Call an hwloc API that allocates (possibly bound) memory and translate
/// known errors into higher-level `MemoryBindingError`s.
///
/// Validating flags is left up to the caller, to avoid allocating result
/// objects when it can be proved upfront that the request is invalid.
pub(crate) fn call_hwloc_allocate<Set: SpecializedBitmap>(
    api: &'static str,
    set: Option<&Set>,
    ffi: impl FnOnce() -> *mut c_void,
) -> Result<NonNull<c_void>, MemoryAllocationError<Set>> {
    errors::call_hwloc_ptr_mut(api, ffi).map_err(|raw_err| {
        decode_errno(
            MemoryBoundObject::Area,
            MemoryBindingOperation::Allocate,
            set,
            raw_err.errno.expect("Unexpected hwloc error without errno"),
        )
        .expect("Unexpected errno value")
    })
}

/// Translating hwloc errno into high-level errors
fn decode_errno<Set: SpecializedBitmap>(
    object: MemoryBoundObject,
    operation: MemoryBindingOperation,
    set: Option<&Set>,
    errno: Errno,
) -> Option<MemoryBindingError<Set>> {
    match errno.0 {
        ENOSYS => Some(MemoryBindingError::Unsupported),
        EXDEV => match operation {
            MemoryBindingOperation::Bind | MemoryBindingOperation::Allocate => {
                Some(MemoryBindingError::BadSet(
                    object,
                    set.expect("This error should only be observed on commands that set bindings")
                        .clone(),
                ))
            }
            MemoryBindingOperation::GetBinding | MemoryBindingOperation::GetLastLocation => {
                Some(MemoryBindingError::MixedResults)
            }
            MemoryBindingOperation::Unbind => {
                unreachable!("The empty set should always be considered valid")
            }
        },
        ENOMEM => Some(MemoryBindingError::AllocationFailed),
        _ => None,
    }
}

/// Bytes allocated through hwloc
///
/// This behaves like a `Box<[MaybeUninit<u8>]>` and will similarly
/// automatically liberate the allocated memory when it goes out of scope.
pub struct Bytes<'topology> {
    /// Underlying hwloc topology
    topology: &'topology Topology,

    /// Previously allocated data pointer
    data: NonNull<[MaybeUninit<u8>]>,
}

impl<'topology> Bytes<'topology> {
    /// Wrap an hwloc allocation
    pub(crate) unsafe fn wrap(
        topology: &'topology Topology,
        base: NonNull<c_void>,
        len: usize,
    ) -> Self {
        let base = base.as_ptr().cast::<MaybeUninit<u8>>();
        let data = std::ptr::slice_from_raw_parts_mut(base, len);
        Self {
            topology,
            data: NonNull::new_unchecked(data),
        }
    }
}

impl AsRef<[MaybeUninit<u8>]> for Bytes<'_> {
    fn as_ref(&self) -> &[MaybeUninit<u8>] {
        unsafe { self.data.as_ref() }
    }
}

impl AsMut<[MaybeUninit<u8>]> for Bytes<'_> {
    fn as_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        unsafe { self.data.as_mut() }
    }
}

impl Borrow<[MaybeUninit<u8>]> for Bytes<'_> {
    fn borrow(&self) -> &[MaybeUninit<u8>] {
        self.as_ref()
    }
}

impl BorrowMut<[MaybeUninit<u8>]> for Bytes<'_> {
    fn borrow_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.as_mut()
    }
}

impl Debug for Bytes<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(self.as_ref(), f)
    }
}

impl Deref for Bytes<'_> {
    type Target = [MaybeUninit<u8>];

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl DerefMut for Bytes<'_> {
    fn deref_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.as_mut()
    }
}

impl Drop for Bytes<'_> {
    #[doc(alias = "hwloc_free")]
    fn drop(&mut self) {
        let addr = self.data.as_ptr().cast::<c_void>();
        let len = self.data.len();
        let result = unsafe { ffi::hwloc_free(self.topology.as_ptr(), addr, len) };
        assert_eq!(
            result,
            0,
            "Got unexpected result from hwloc_free with errno {}",
            errno()
        );
    }
}
