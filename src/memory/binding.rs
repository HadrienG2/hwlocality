//! Memory binding
//!
//! This module is all about checking and changing the binding of memory
//! allocations to hardware NUMA nodes.
//!
//! Most of this module's functionality is exposed via [methods of the Topology
//! struct](../../topology/struct.Topology.html#memory-binding). The module
//! itself only hosts type definitions that are related to this functionality.

use crate::{
    bitmap::{Bitmap, BitmapKind, SpecializedBitmap, SpecializedBitmapRef},
    errors::{self, FlagsError, HybridError, RawHwlocError},
    ffi::unknown::UnknownVariant,
    memory::nodeset::NodeSet,
    topology::Topology,
    ProcessId,
};
#[cfg(doc)]
use crate::{cpu::cpuset::CpuSet, topology::support::MemoryBindingSupport};
use bitflags::bitflags;
use derive_more::Display;
use errno::Errno;
#[cfg(feature = "hwloc-2_11_0")]
use hwlocality_sys::HWLOC_MEMBIND_WEIGHTED_INTERLEAVE;
use hwlocality_sys::{
    hwloc_bitmap_t, hwloc_const_bitmap_t, hwloc_const_topology_t, hwloc_membind_flags_t,
    hwloc_membind_policy_t, hwloc_pid_t, HWLOC_MEMBIND_BIND, HWLOC_MEMBIND_BYNODESET,
    HWLOC_MEMBIND_DEFAULT, HWLOC_MEMBIND_FIRSTTOUCH, HWLOC_MEMBIND_INTERLEAVE,
    HWLOC_MEMBIND_MIGRATE, HWLOC_MEMBIND_MIXED, HWLOC_MEMBIND_NEXTTOUCH, HWLOC_MEMBIND_NOCPUBIND,
    HWLOC_MEMBIND_PROCESS, HWLOC_MEMBIND_STRICT, HWLOC_MEMBIND_THREAD,
};
use libc::{ENOMEM, ENOSYS, EXDEV};
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::{
    borrow::{Borrow, BorrowMut},
    ffi::{c_int, c_void},
    fmt::{self, Debug, Display},
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};
use strum::{EnumCount, EnumIter, FromRepr};
use thiserror::Error;

/// # Memory binding
///
/// Memory binding can be done three ways:
///
/// - Explicit memory allocation through [`allocate_bound_memory()`] and friends:
///   the binding will have effect on the memory allocated by these methods.
/// - Implicit memory binding via process/thread binding through
///   [`bind_memory()`] and friends: unless [`MIGRATE`] is also used, the
///   binding will only apply to subsequent memory allocations by the target
///   process/thread.
/// - Migration of existing memory ranges through [`bind_memory_area()`] and
///   friends: already-allocated data will be migrated to the target NUMA
///   nodes.
///
/// Not all operating systems support all three ways.
/// [`Topology::feature_support()`] may be used to query about the actual memory
/// binding support in the currently used operating system. Individual memory
/// binding methods will clarify which support flags they require. The most
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
/// You should specify one of the [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and
/// [`THREAD`] flags (the former being best for portability) when using any of
/// the methods that target a process, but some methods may only support a
/// subset of these flags.
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
/// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
/// [`NO_CPU_BINDING`]: MemoryBindingFlags::NO_CPU_BINDING
/// [`PROCESS`]: MemoryBindingFlags::PROCESS
/// [`STRICT`]: MemoryBindingFlags::STRICT
/// [`THREAD`]: MemoryBindingFlags::THREAD
//
// --- Implementation details ---
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
    /// - [`AllocationFailed`] if memory allocation failed
    /// - [`Unsupported`] if the system cannot allocate page-aligned memory or
    ///   if more than `isize::MAX` bytes of memory are requested
    ///
    /// [`AllocationFailed`]: MemoryBindingError::AllocationFailed
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_alloc")]
    pub fn allocate_memory(
        &self,
        len: usize,
    ) -> Result<Bytes<'_>, HybridError<MemoryAllocationError<NodeSet>>> {
        self.allocate_memory_generic(len)
    }

    /// Like [`allocate_memory()`], but generic over `Set`
    ///
    /// [`allocate_memory`]: Topology::allocate_memory
    fn allocate_memory_generic<Set: SpecializedBitmap>(
        &self,
        len: usize,
    ) -> Result<Bytes<'_>, HybridError<MemoryAllocationError<Set>>> {
        // SAFETY: - hwloc_alloc is accepted by definition
        //         - FFI is guaranteed to be passed valid (topology, len)
        unsafe {
            self.allocate_memory_impl("hwloc_alloc", &|| None, len, |topology, len| {
                hwlocality_sys::hwloc_alloc(topology, len)
            })
        }
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
    /// Binding target flags [`ASSUME_SINGLE_THREAD`], [`PROCESS`],
    /// [`THREAD`] and [`MIGRATE`] should not be used with this method.
    ///
    /// Requires [`MemoryBindingSupport::allocate_bound()`].
    ///
    /// # Errors
    ///
    /// - [`AllocationFailed`] if memory allocation failed
    /// - [`BadFlags`] if binding target flags were specified
    /// - [`BadSet`] if the system can't bind memory to that CPU/node set
    /// - [`Unsupported`] if the system cannot allocate bound memory with the
    ///   requested policy or if more than `isize::MAX` bytes of memory are
    ///   requested
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
    pub fn allocate_bound_memory<SetRef: SpecializedBitmapRef>(
        &self,
        len: usize,
        set: SetRef,
        policy: MemoryBindingPolicy,
        original_flags: MemoryBindingFlags,
    ) -> Result<Bytes<'_>, HybridError<MemoryAllocationError<SetRef::Owned>>> {
        // Detect invalid binding sets
        let object = MemoryBoundObject::Area;
        if !self.is_valid_binding_set(&*set) {
            return Err(MemoryBindingError::BadSet(object, set.to_owned()).into());
        }

        // Adjust flags for target set type and detect problems with them
        let flags = Self::adjust_flags_for::<SetRef::Owned>(original_flags);
        let Some(flags) = flags.validate(object, MemoryBindingOperation::Allocate) else {
            return Err(MemoryBindingError::BadFlags(original_flags.into()).into());
        };

        // Perform the memory allocation
        // SAFETY: - Bitmap is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted not to modify *const parameters
        //         - hwloc_alloc_membind with set, policy and flags
        //           arguments curried away behaves like hwloc_alloc
        //         - FFI is guaranteed to be passed valid (topology, len)
        //         - All user-visible policies are accepted by hwloc
        //         - flags are validated to be correct
        unsafe {
            self.allocate_memory_impl(
                "hwloc_alloc_membind",
                &|| Some(set.to_owned()),
                len,
                |topology, len| {
                    hwlocality_sys::hwloc_alloc_membind(
                        topology,
                        len,
                        set.as_bitmap_ref().as_ptr(),
                        policy.into(),
                        flags.bits(),
                    )
                },
            )
        }
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
    /// You must specify exactly one of the [`ASSUME_SINGLE_THREAD`],
    /// [`PROCESS`] and [`THREAD`] binding target flags when using this method.
    ///
    /// Requires either [`MemoryBindingSupport::allocate_bound()`], or one of
    /// [`MemoryBindingSupport::set_current_process()`] and
    /// [`MemoryBindingSupport::set_current_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`AllocationFailed`] if memory allocation failed
    /// - [`BadFlags`] if the number of specified binding target flags is not
    ///   exactly one
    /// - [`BadSet`] if the system can't bind memory to that CPU/node set
    /// - [`Unsupported`] if the system can neither allocate bound memory nor
    ///   rebind the current thread/process with the requested policy or if more
    ///   than `isize::MAX` bytes of memory are requested
    ///
    /// [`AllocationFailed`]: MemoryBindingError::AllocationFailed
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadSet`]: MemoryBindingError::BadSet
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_alloc_membind_policy")]
    pub fn binding_allocate_memory<SetRef: SpecializedBitmapRef>(
        &self,
        len: usize,
        set: SetRef,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<Bytes<'_>, HybridError<MemoryAllocationError<SetRef::Owned>>> {
        // Reject invalid flags first
        if flags
            .validate(MemoryBoundObject::ThisProgram, MemoryBindingOperation::Bind)
            .is_none()
        {
            return Err(MemoryBindingError::BadFlags(flags.into()).into());
        }

        // Try to allocate_bound_memory first
        let set: &SetRef::Owned = &set;
        let flags_wo_target = flags.difference(
            MemoryBindingFlags::ASSUME_SINGLE_THREAD
                | MemoryBindingFlags::PROCESS
                | MemoryBindingFlags::THREAD
                | MemoryBindingFlags::MIGRATE,
        );
        if let Ok(bytes) = self.allocate_bound_memory(len, set, policy, flags_wo_target) {
            return Ok(bytes);
        }

        // If that doesn't work, try binding the current process
        self.bind_memory(set, policy, flags)?;

        // If that succeeds, try allocating more memory
        let mut bytes = self.allocate_memory_generic::<SetRef::Owned>(len)?;

        // Depending on policy, we may or may not need to touch the memory to
        // enforce the binding
        match policy {
            // Nothing to do, user expects first/next-touch lazy behavior
            MemoryBindingPolicy::FirstTouch | MemoryBindingPolicy::NextTouch => {}

            // All other cases expect eager binding, which may require touching
            // to enforce. That's also what we do when we don't know.
            MemoryBindingPolicy::Bind
            | MemoryBindingPolicy::Interleave
            | MemoryBindingPolicy::Unknown(_) => {
                bytes.fill(MaybeUninit::new(0));
            }
            #[cfg(feature = "hwloc-2_11_0")]
            MemoryBindingPolicy::WeightedInterleave => {
                bytes.fill(MaybeUninit::new(0));
            }
        }
        Ok(bytes)
    }

    /// Set the default memory binding policy of the current process or thread
    /// to prefer the NUMA node(s) specified by `set`
    ///
    /// By default, only future allocations by the process/thread will be bound
    /// to the target NUMA node. You can attempt to migrate existing allocations
    /// using the [`MIGRATE`] flag, at the expense of reducing portability.
    ///
    /// Memory can be bound by either [`CpuSet`] or [`NodeSet`]. Binding by
    /// [`NodeSet`] is preferred because some NUMA memory nodes are not attached
    /// to CPUs, and thus cannot be bound by [`CpuSet`].
    ///
    /// You must specify exactly one of the [`ASSUME_SINGLE_THREAD`],
    /// [`PROCESS`] and [`THREAD`] binding target flags when using this method.
    ///
    /// Requires [`MemoryBindingSupport::set_current_process()`] or
    /// [`MemoryBindingSupport::set_current_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`BadFlags`] if the number of specified binding target flags is not
    ///   exactly one
    /// - [`BadSet`] if the system can't bind memory to that CPU/node set
    /// - [`Unsupported`] if the system cannot bind the current
    ///   thread/process with the requested policy
    ///
    /// [`ASSUME_SINGLE_THREAD`]: MemoryBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadSet`]: MemoryBindingError::BadSet
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_set_membind")]
    pub fn bind_memory<SetRef: SpecializedBitmapRef>(
        &self,
        set: SetRef,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<(), HybridError<MemoryBindingError<SetRef::Owned>>> {
        // SAFETY: - ThisProgram is the correct target for this FFI
        //         - hwloc_set_membind is accepted by definition
        //         - FFI is guaranteed to be passed valid (topology,
        //           out set, out policy, flags)
        unsafe {
            self.bind_memory_impl(
                "hwloc_set_membind",
                &set,
                policy,
                flags,
                MemoryBoundObject::ThisProgram,
                |topology, set, policy, flags| {
                    hwlocality_sys::hwloc_set_membind(topology, set, policy, flags)
                },
            )
        }
    }

    /// Reset the memory allocation policy of the current process or thread to
    /// the system default
    ///
    /// Depending on the operating system, this may correspond to
    /// [`MemoryBindingPolicy::FirstTouch`] (Linux, FreeBSD) or
    /// [`MemoryBindingPolicy::Bind`] (AIX, HP-UX, Solaris, Windows).
    ///
    /// You must specify exactly one of the [`ASSUME_SINGLE_THREAD`],
    /// [`PROCESS`] and [`THREAD`] binding target flags when using this method,
    /// but the [`STRICT`] and [`MIGRATE`] flags should **not** be used with
    /// this method.
    ///
    /// Requires [`MemoryBindingSupport::set_current_process()`] or
    /// [`MemoryBindingSupport::set_current_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`BadFlags`] if one of flags [`STRICT`] and [`MIGRATE`] was specified,
    ///   or if the number of specified binding target flags is not exactly
    ///   one
    /// - [`Unsupported`] if the system cannot unbind the current thread/process
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
    ) -> Result<(), HybridError<MemoryBindingError<NodeSet>>> {
        // SAFETY: - ThisProgram is the correct target for this FFI
        //         - hwloc_set_membind is accepted by definition
        //         - FFI is guaranteed to be passed valid (topology,
        //           out set, out policy, flags)
        unsafe {
            self.unbind_memory_impl(
                "hwloc_set_membind",
                flags,
                MemoryBoundObject::ThisProgram,
                |topology, set, policy, flags| {
                    hwlocality_sys::hwloc_set_membind(topology, set, policy, flags)
                },
            )
        }
    }

    /// Query the default memory binding policy and physical locality of the
    /// current process or thread
    ///
    /// You must specify one of the [`ASSUME_SINGLE_THREAD`], [`PROCESS`] and
    /// [`THREAD`] binding target flags when using this method. However, flags
    /// [`MIGRATE`] and [`NO_CPU_BINDING`] should **not** be used with this
    /// method.
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
    /// - [`BadFlags`] if one of flags [`MIGRATE`] and [`NO_CPU_BINDING`] was
    ///   specified, if flag [`STRICT`] was specified without [`PROCESS`], or
    ///   if the number of specified binding target flags is not exactly one
    /// - [`MixedResults`] if flags [`STRICT`] and [`PROCESS`] were specified
    ///   and memory binding is inhomogeneous across threads in the process
    /// - [`Unsupported`] if the system cannot query the current thread/process
    ///   binding
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
    ) -> Result<(Set, Option<MemoryBindingPolicy>), HybridError<MemoryBindingError<Set>>> {
        // SAFETY: - ThisProgram is the correct target for this FFI
        //         - GetBinding is the correct operation for this FFI
        //         - hwloc_get_membind is accepted by definition
        //         - FFI is guaranteed to be passed valid (topology,
        //           out set, out policy, flags)
        unsafe {
            self.memory_binding_impl(
                "hwloc_get_membind",
                flags,
                MemoryBoundObject::ThisProgram,
                MemoryBindingOperation::GetBinding,
                |topology, set, policy, flags| {
                    hwlocality_sys::hwloc_get_membind(topology, set, policy, flags)
                },
            )
        }
    }

    /// Set the default memory binding policy of the specified process to prefer
    /// the NUMA node(s) specified by `set`.
    ///
    /// See also [`Topology::bind_memory()`] for general semantics, except
    /// binding target flag [`THREAD`] should not be used with this method, and
    /// it requires [`MemoryBindingSupport::set_process()`].
    ///
    /// # Errors
    ///
    /// - [`BadFlags`] if flag [`THREAD`] was specified, or if the number of
    ///   specified binding target flags is not exactly one
    /// - [`BadSet`] if the system can't bind memory to that CPU/node set
    /// - [`Unsupported`] if the system cannot bind the specified
    ///   thread/process with the requested policy
    ///
    /// # Panics
    ///
    /// Some operating systems use signed PIDs, and do not support PIDs greater
    /// than `i32::MAX`. This method will panic when passed such an obviously
    /// invalid PID on these operating systems.
    ///
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadSet`]: MemoryBindingError::BadSet
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_set_proc_membind")]
    pub fn bind_process_memory<SetRef: SpecializedBitmapRef>(
        &self,
        pid: ProcessId,
        set: SetRef,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<(), HybridError<MemoryBindingError<SetRef::Owned>>> {
        // SAFETY: - Process is the correct target for this FFI
        //         - hwloc_set_proc_membind with pid argument curried away
        //           behaves like hwloc_set_membind
        //         - FFI is guaranteed to be passed valid (topology,
        //           set, policy, flags)
        //         - PID cannot be validated (think TOCTOU), but hwloc should be
        //           able to handle an invalid PID
        unsafe {
            self.bind_memory_impl(
                "hwloc_set_proc_membind",
                &set,
                policy,
                flags,
                MemoryBoundObject::Process(pid),
                |topology, set, policy, flags| {
                    hwlocality_sys::hwloc_set_proc_membind(
                        topology,
                        hwloc_pid_t::try_from(pid).expect("shouldn't fail for a valid PID"),
                        set,
                        policy,
                        flags,
                    )
                },
            )
        }
    }

    /// Reset the memory allocation policy of the specified process to the
    /// system default
    ///
    /// See also [`Topology::unbind_memory()`] for general semantics, except
    /// binding target flag [`THREAD`] should not be used with this method, and
    /// it requires [`MemoryBindingSupport::set_process()`].
    ///
    /// # Errors
    ///
    /// - [`BadFlags`] if one of flags [`MIGRATE`], [`STRICT`] and [`THREAD`]
    ///   was specified,  or if the number of specified binding target flags is
    ///   not exactly one
    /// - [`Unsupported`] if the system cannot unbind the specified
    ///   thread/process
    ///
    /// # Panics
    ///
    /// Some operating systems use signed PIDs, and do not support PIDs greater
    /// than `i32::MAX`. This method will panic when passed such an obviously
    /// invalid PID on these operating systems.
    ///
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`THREAD`]: MemoryBindingFlags::THREAD
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    pub fn unbind_process_memory(
        &self,
        pid: ProcessId,
        flags: MemoryBindingFlags,
    ) -> Result<(), HybridError<MemoryBindingError<NodeSet>>> {
        // SAFETY: - Process is the correct target for this FFI
        //         - hwloc_set_proc_membind with pid argument curried away
        //           behaves like hwloc_set_membind
        //         - FFI is guaranteed to be passed valid (topology,
        //           set, policy, flags)
        //         - PID cannot be validated (think TOCTOU), but hwloc should be
        //           able to handle an invalid PID
        unsafe {
            self.unbind_memory_impl(
                "hwloc_set_proc_membind",
                flags,
                MemoryBoundObject::Process(pid),
                |topology, set, policy, flags| {
                    hwlocality_sys::hwloc_set_proc_membind(
                        topology,
                        hwloc_pid_t::try_from(pid).expect("shouldn't fail for a valid PID"),
                        set,
                        policy,
                        flags,
                    )
                },
            )
        }
    }

    /// Query the default memory binding policy and physical locality of the
    /// specified process
    ///
    /// See [`Topology::memory_binding()`] for general semantics, except binding
    /// target flag [`THREAD`] should not be used with this method, and it
    /// requires [`MemoryBindingSupport::get_process()`].
    ///
    /// # Errors
    ///
    /// - [`BadFlags`] if one of flags [`MIGRATE`], [`NO_CPU_BINDING`] and
    ///   [`THREAD`] was specified, if flag [`STRICT`] was specified without
    ///   [`PROCESS`], or if the number of specified binding target flags is
    ///   not exactly one
    /// - [`MixedResults`] if flags [`STRICT`] and [`PROCESS`] were specified
    ///   and memory binding is inhomogeneous across threads in the process
    /// - [`Unsupported`] if the system cannot query the specified
    ///   thread/process' binding
    ///
    /// # Panics
    ///
    /// Some operating systems use signed PIDs, and do not support PIDs greater
    /// than `i32::MAX`. This method will panic when passed such an obviously
    /// invalid PID on these operating systems.
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
    ) -> Result<(Set, Option<MemoryBindingPolicy>), HybridError<MemoryBindingError<Set>>> {
        // SAFETY: - Process is the correct target for this FFI
        //         - GetBinding is the correct operation for this FFI
        //         - hwloc_get_proc_membind with pid argument curried away
        //           behaves like hwloc_get_membind
        //         - FFI is guaranteed to be passed valid (topology,
        //           out set, out policy, flags)
        //         - PID cannot be validated (think TOCTOU), but hwloc should be
        //           able to handle an invalid PID
        unsafe {
            self.memory_binding_impl(
                "hwloc_get_proc_membind",
                flags,
                MemoryBoundObject::Process(pid),
                MemoryBindingOperation::GetBinding,
                |topology, set, policy, flags| {
                    hwlocality_sys::hwloc_get_proc_membind(
                        topology,
                        hwloc_pid_t::try_from(pid).expect("shouldn't fail for a valid PID"),
                        set,
                        policy,
                        flags,
                    )
                },
            )
        }
    }

    /// Bind the memory identified by `target` to the NUMA node(s) specified by
    /// `set`
    ///
    /// Beware that only the memory directly targeted by the `target` reference
    /// will be covered. So for example, you cannot pass in an `&Vec<T>` and
    /// expect the Vec's contents to be covered, instead you must pass in the
    /// `&[T]` corresponding to the Vec's contents as `&vec[..]`. You may also
    /// want to manually specify the `Target` type via turbofish to make sure
    /// that you don't get tripped up by references of references like `&&[T]`.
    ///
    /// See also [`Topology::bind_memory()`] for general semantics, except
    /// binding target flags should not be used with this method, and it
    /// requires [`MemoryBindingSupport::set_area()`].
    ///
    /// # Errors
    ///
    /// - [`BadFlags`] if a binding target flag was specified
    /// - [`BadSet`] if the system can't bind memory to that CPU/node set
    /// - [`Unsupported`] if the system cannot bind the specified memory area
    ///   with the requested policy
    ///
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadSet`]: MemoryBindingError::BadSet
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_set_area_membind")]
    pub fn bind_memory_area<Target: ?Sized, SetRef: SpecializedBitmapRef>(
        &self,
        target: &Target,
        set: SetRef,
        policy: MemoryBindingPolicy,
        flags: MemoryBindingFlags,
    ) -> Result<(), HybridError<MemoryBindingError<SetRef::Owned>>> {
        let target_size = std::mem::size_of_val(target);
        if target_size == 0 {
            return Ok(());
        }
        let target_ptr: *const Target = target;
        // SAFETY: - Area is the correct target for this FFI
        //         - hwloc_set_area_membind with target_ptr and target_size
        //           arguments curried away behaves like hwloc_set_membind
        //         - FFI is guaranteed to be passed valid (topology,
        //           set, policy, flags)
        //         - target_ptr is valid as it originates from a & reference
        //         - target_size has been checked not to be zero
        unsafe {
            self.bind_memory_impl(
                "hwloc_set_area_membind",
                &set,
                policy,
                flags,
                MemoryBoundObject::Area,
                |topology, set, policy, flags| {
                    hwlocality_sys::hwloc_set_area_membind(
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
    }

    /// Reset the memory allocation policy of the memory identified by `target`
    /// to the system default
    ///
    /// The warning about `Target` coverage in the documentation of
    /// [`Topology::bind_memory_area()`] also applies here.
    ///
    /// See also [`Topology::unbind_memory()`] for general semantics, except
    /// binding target flags should not be used with this method, and it
    /// requires[`MemoryBindingSupport::set_area()`].
    ///
    /// # Errors
    ///
    /// - [`BadFlags`] if one of flags [`MIGRATE`] and [`STRICT`] was specified,
    ///   or if a binding target flag was specified.
    /// - [`Unsupported`] if the system cannot unbind the specified memory area
    ///
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    pub fn unbind_memory_area<Target: ?Sized>(
        &self,
        target: &Target,
        flags: MemoryBindingFlags,
    ) -> Result<(), HybridError<MemoryBindingError<NodeSet>>> {
        let target_size = std::mem::size_of_val(target);
        if target_size == 0 {
            return Ok(());
        }
        let target_ptr: *const Target = target;
        // SAFETY: - Area is the correct target for this FFI
        //         - hwloc_set_area_membind with target_ptr and target_size
        //           arguments curried away behaves like hwloc_set_membind
        //         - FFI is guaranteed to be passed valid (topology,
        //           set, policy, flags)
        //         - target_ptr is valid as it originates from a & reference
        //         - target_size has been checked not to be zero
        unsafe {
            self.unbind_memory_impl(
                "hwloc_set_area_membind",
                flags,
                MemoryBoundObject::Area,
                |topology, set, policy, flags| {
                    hwlocality_sys::hwloc_set_area_membind(
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
    /// - Binding target flags should not be used with this method
    /// - As mentioned above, [`STRICT`] has a specific meaning in the context
    ///   of this method.
    /// - This method requires [`MemoryBindingSupport::get_area()`].
    ///
    /// # Errors
    ///
    /// - [`BadFlags`] if one of flags [`MIGRATE`] and [`NO_CPU_BINDING`] was
    ///   specified, or if a binding target flag was specified.
    /// - [`BadArea`] if `target` is a zero-sized object
    /// - [`MixedResults`] if flag [`STRICT`] was specified and memory binding
    ///   is inhomogeneous across target memory pages
    /// - [`Unsupported`] if the system cannot query the specified
    ///   memory area's binding
    ///
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadArea`]: MemoryBindingError::BadArea
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`MixedResults`]: MemoryBindingError::MixedResults
    /// [`NO_CPU_BINDING`]: MemoryBindingFlags::NO_CPU_BINDING
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_get_area_membind")]
    pub fn area_memory_binding<Target: ?Sized, Set: SpecializedBitmap>(
        &self,
        target: &Target,
        flags: MemoryBindingFlags,
    ) -> Result<(Set, Option<MemoryBindingPolicy>), HybridError<MemoryBindingError<Set>>> {
        let target_size = std::mem::size_of_val(target);
        if target_size == 0 {
            return Err(MemoryBindingError::BadArea.into());
        }
        let target_ptr: *const Target = target;
        // SAFETY: - Area is the correct target for this FFI
        //         - GetBinding is the correct operation for this FFI
        //         - hwloc_get_area_membind with target_ptr and target_size
        //           arguments curried away behaves like hwloc_get_membind
        //         - FFI is guaranteed to be passed valid (topology,
        //           out set, out policy, flags)
        //         - target_ptr is valid as it originates from a & reference
        //         - target_size has been checked not to be zero
        unsafe {
            self.memory_binding_impl(
                "hwloc_get_area_membind",
                flags,
                MemoryBoundObject::Area,
                MemoryBindingOperation::GetBinding,
                |topology, set, policy, flags| {
                    hwlocality_sys::hwloc_get_area_membind(
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
    /// at any time according to their binding, so this method may return
    /// something that is already outdated.
    ///
    /// See also [`Topology::memory_binding()`] for general semantics, except
    /// binding target flags should not be used with this method, and it
    /// requires [`MemoryBindingSupport::get_area_memory_location()`].
    ///
    /// # Errors
    ///
    /// - [`BadFlags`] if one of flags [`MIGRATE`] and [`NO_CPU_BINDING`] was
    ///   specified, or if a binding target flag was specified.
    /// - [`BadArea`] if `target` is a zero-sized object
    /// - [`MixedResults`] if flag [`STRICT`] was specified and memory binding
    ///   is inhomogeneous across target memory pages
    /// - [`Unsupported`] if the system cannot query the specified
    ///   memory area's location
    ///
    /// [`BadFlags`]: MemoryBindingError::BadFlags
    /// [`BadArea`]: MemoryBindingError::BadArea
    /// [`MIGRATE`]: MemoryBindingFlags::MIGRATE
    /// [`MixedResults`]: MemoryBindingError::MixedResults
    /// [`NO_CPU_BINDING`]: MemoryBindingFlags::NO_CPU_BINDING
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    /// [`Unsupported`]: MemoryBindingError::Unsupported
    #[doc(alias = "hwloc_get_area_memlocation")]
    pub fn area_memory_location<Target: ?Sized, Set: SpecializedBitmap>(
        &self,
        target: &Target,
        flags: MemoryBindingFlags,
    ) -> Result<Set, HybridError<MemoryBindingError<Set>>> {
        let target_size = std::mem::size_of_val(target);
        if target_size == 0 {
            return Err(MemoryBindingError::BadArea.into());
        }
        let target_ptr: *const Target = target;
        // SAFETY: - ThisProgram is the correct target for this FFI
        //         - GetLastLocation is the correct operation for this FFI
        //         - hwloc_get_area_memlocation with target_ptr and target_size
        //           arguments curried away and policy placeholder'd behaves
        //           like hwloc_get_membind
        //         - FFI is guaranteed to be passed valid (topology,
        //           out set, out policy, flags)
        //         - target_ptr is valid as it originates from a & reference
        //         - target_size has been checked not to be zero
        unsafe {
            self.memory_binding_impl(
                "hwloc_get_area_memlocation",
                flags,
                MemoryBoundObject::Area,
                MemoryBindingOperation::GetLastLocation,
                |topology, set, policy, flags| {
                    *policy = -1;
                    hwlocality_sys::hwloc_get_area_memlocation(
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
    }

    /// Truth that a certain [`CpuSet`] or [`NodeSet`] **certainly** cannot be
    /// used to bind a process/thread to CPU/memory resources
    ///
    /// This check is used to weed out blatantly incorrect requests without even
    /// trying to call hwloc, thus bypassing hwloc's finnicky error handling.
    pub(crate) fn is_valid_binding_set<Set: SpecializedBitmap>(&self, set: &Set) -> bool {
        // It is never legal to bind a process/thread to an empty resource set
        let set = set.as_bitmap_ref();
        if set.is_empty() {
            return false;
        }

        // Resources indices outside the topology's complete set are never valid
        match Set::BITMAP_KIND {
            BitmapKind::CpuSet => self.allowed_cpuset().as_bitmap_ref().includes(set),
            BitmapKind::NodeSet => self.allowed_nodeset().as_bitmap_ref().includes(set),
        }
    }

    /// Adjust binding flags for a certain kind of Set
    fn adjust_flags_for<Set: SpecializedBitmap>(
        mut flags: MemoryBindingFlags,
    ) -> MemoryBindingFlags {
        match Set::BITMAP_KIND {
            BitmapKind::CpuSet => flags.remove(MemoryBindingFlags::BY_NODE_SET),
            BitmapKind::NodeSet => flags.insert(MemoryBindingFlags::BY_NODE_SET),
        }
        flags
    }

    /// Binding for `hwloc_alloc`-like functions
    ///
    /// # Safety
    ///
    /// - `ffi` should have semantics analogous to `hwloc_alloc`
    /// - If so, this is guaranteed to call `ffi` with a valid (topology, size)
    ///   tuple
    unsafe fn allocate_memory_impl<Set: SpecializedBitmap>(
        &self,
        api: &'static str,
        clone_set: &dyn Fn() -> Option<Set>,
        len: usize,
        ffi: impl FnOnce(hwloc_const_topology_t, usize) -> *mut c_void,
    ) -> Result<Bytes<'_>, HybridError<MemoryBindingError<Set>>> {
        if len > isize::MAX as usize {
            Err(MemoryAllocationError::Unsupported.into())
        } else if len > 0 {
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - hwloc ops are trusted not to modify *const parameters
            //         - len was checked to be nonzero above
            errors::call_hwloc_ptr_mut(api, || ffi(self.as_ptr(), len))
                .map_err(|raw_err| {
                    decode_errno(
                        MemoryBoundObject::Area,
                        MemoryBindingOperation::Allocate,
                        clone_set,
                        raw_err.errno,
                    )
                    .map_or_else(|| HybridError::Hwloc(raw_err), HybridError::Rust)
                })
                // SAFETY: If hwloc allocation successfully returns, this is
                //         assumed to be a valid allocation pointer
                .map(|base| unsafe { Bytes::wrap(self, base, len) })
        } else {
            // SAFETY: Bytes accepts any pointer for zero-sized allocations
            Ok(unsafe { Bytes::wrap(self, NonNull::dangling(), 0) })
        }
    }

    /// Memory-binding interface for `hwloc_set_membind`-like functions
    ///
    /// # Safety
    ///
    /// - `ffi` should have semantics analogous to `hwloc_set_membind`
    /// - `target` should accurately reflect the target which this function
    ///   is applied to, for flags validation purposes
    /// - If all of the above is true, this is guaranteed to only call `ffi`
    ///   with a valid (topology, bitmap, policy, flags) tuple
    unsafe fn bind_memory_impl<Set: SpecializedBitmap>(
        &self,
        api: &'static str,
        set: &Set,
        policy: MemoryBindingPolicy,
        original_flags: MemoryBindingFlags,
        target: MemoryBoundObject,
        ffi: impl FnOnce(
            hwloc_const_topology_t,
            hwloc_const_bitmap_t,
            hwloc_membind_policy_t,
            hwloc_membind_flags_t,
        ) -> c_int,
    ) -> Result<(), HybridError<MemoryBindingError<Set>>> {
        // Detect invalid binding sets
        if !self.is_valid_binding_set(set) {
            return Err(MemoryBindingError::BadSet(target, set.to_owned()).into());
        }

        // Adjust flags for target set type and detect problems with them
        let operation = MemoryBindingOperation::Bind;
        let flags = Self::adjust_flags_for::<Set>(original_flags);
        let Some(flags) = flags.validate(target, operation) else {
            return Err(MemoryBindingError::BadFlags(original_flags.into()).into());
        };

        // Perform the memory binding operation
        call_hwloc_int(api, target, operation, &|| Some(set.clone()), || {
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - Bitmap is trusted to contain a valid ptr (type invariant)
            //         - hwloc ops are trusted not to modify *const parameters
            //         - All user-visible policies are accepted by hwloc
            //         - flags should be valid if target is valid
            ffi(
                self.as_ptr(),
                set.as_bitmap_ref().as_ptr(),
                policy.into(),
                flags.bits(),
            )
        })
    }

    /// Memory-unbinding interface for `hwloc_set_membind`-like functions
    ///
    /// # Safety
    ///
    /// - `ffi` should have semantics analogous to `hwloc_set_membind`
    /// - `target` should accurately reflect the target which this function
    ///   is applied to, for flags validation purposes
    /// - If all of the above is true, this is guaranteed to only call `ffi`
    ///   with a valid (topology, bitmap, policy, flags) tuple
    unsafe fn unbind_memory_impl(
        &self,
        api: &'static str,
        flags: MemoryBindingFlags,
        target: MemoryBoundObject,
        ffi: impl FnOnce(
            hwloc_const_topology_t,
            hwloc_const_bitmap_t,
            hwloc_membind_policy_t,
            hwloc_membind_flags_t,
        ) -> c_int,
    ) -> Result<(), HybridError<MemoryBindingError<NodeSet>>> {
        let operation = MemoryBindingOperation::Unbind;
        let Some(flags) = flags.validate(target, operation) else {
            return Err(MemoryBindingError::BadFlags(flags.into()).into());
        };
        call_hwloc_int::<NodeSet>(api, target, operation, &|| None, || {
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - hwloc ops are trusted not to modify *const parameters
            //         - Passing any valid set and the default policy is an
            //           hwloc-accepted way to reset the binding policy
            //         - All user-visible policies are accepted by hwloc
            //         - flags should be valid if target is valid
            ffi(
                self.as_ptr(),
                self.nodeset().as_ptr(),
                HWLOC_MEMBIND_DEFAULT,
                flags.bits(),
            )
        })
    }

    /// Binding for `hwloc_get_membind`-like functions
    ///
    /// # Safety
    ///
    /// - `ffi` should have semantics analogous to `hwloc_get_membind`
    /// - `target` should accurately reflect the target which this function
    ///   is applied to, for flags validation purposes
    /// - `operation` should accurately reflect the kind of operation being
    ///   performed, for flags validation purposes
    /// - If all of the above is true, this is guaranteed to only call `ffi`
    ///   with a valid (topology, out bitmap, out policy, flags) tuple
    unsafe fn memory_binding_impl<Set: SpecializedBitmap>(
        &self,
        api: &'static str,
        original_flags: MemoryBindingFlags,
        target: MemoryBoundObject,
        operation: MemoryBindingOperation,
        ffi: impl FnOnce(
            hwloc_const_topology_t,
            hwloc_bitmap_t,
            *mut hwloc_membind_policy_t,
            hwloc_membind_flags_t,
        ) -> c_int,
    ) -> Result<(Set, Option<MemoryBindingPolicy>), HybridError<MemoryBindingError<Set>>> {
        let flags = Self::adjust_flags_for::<Set>(original_flags);
        let Some(flags) = flags.validate(target, operation) else {
            return Err(MemoryBindingError::BadFlags(original_flags.into()).into());
        };
        let mut set = Bitmap::new();
        let mut raw_policy = hwloc_membind_policy_t::MAX;
        call_hwloc_int::<Set>(api, target, operation, &|| None, || {
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - Bitmap is trusted to contain a valid ptr (type invariant)
            //         - hwloc ops are trusted not to modify *const parameters
            //         - hwloc ops are trusted to keep *mut parameters in a
            //           valid state unless stated otherwise
            //         - As a pure out parameter, policy shouldn't be read by hwloc
            //         - flags should be valid if target & operation are valid
            ffi(
                self.as_ptr(),
                set.as_mut_ptr(),
                &mut raw_policy,
                flags.bits(),
            )
        })
        .map(|()| {
            /// Polymorphized version of policy check (avoids generics bloat)
            ///
            /// # Safety
            ///
            /// `raw_policy` must come from hwloc
            unsafe fn check_policy(
                raw_policy: hwloc_membind_policy_t,
            ) -> Option<MemoryBindingPolicy> {
                #[allow(clippy::wildcard_enum_match_arm)]
                // SAFETY: Per function precondition
                match unsafe { MemoryBindingPolicy::from_hwloc(raw_policy) } {
                    MemoryBindingPolicy::Unknown(UnknownVariant(HWLOC_MEMBIND_MIXED)) => None,
                    MemoryBindingPolicy::Unknown(UnknownVariant(err)) if err < 0 => {
                        panic!("Got unexpected negative memory policy #{err}")
                    }
                    policy => Some(policy),
                }
            }
            // SAFETY: If control reaches this point, the hwloc function
            //         returned with a success status, which means it should
            //         have set `raw_policy` to a value value.
            (set.into(), unsafe { check_policy(raw_policy) })
        })
    }
}

#[cfg(not(tarpaulin_include))]
bitflags! {
    /// Memory binding flags.
    ///
    /// These bit flags can be used to refine the binding policy. All flags can
    /// be OR'ed together with the exception of the binding target flags
    /// `ASSUME_SINGLE_THREAD`, `THREAD` and `PROCESS`, of which at most one
    /// must be specified. The most portable option is `ASSUME_SINGLE_THREAD`,
    /// when it is applicable.
    ///
    /// When using one of the methods that target a process, you must use
    /// exactly one of these flags. The most portable option is
    /// `ASSUME_SINGLE_THREAD`, when it is applicable. These
    /// flags must not be used with any other method.
    ///
    /// Individual memory binding methods may not support all of these flags.
    /// Please check the documentation of the [memory binding
    /// method](../../topology/struct.Topology.html#memory-binding) that you are
    /// calling for more information.
    #[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
    #[doc(alias = "hwloc_membind_flags_t")]
    pub struct MemoryBindingFlags: hwloc_membind_flags_t {
        /// Assume that the target process is single threaded
        ///
        /// This lets hwloc pick between thread and process binding for
        /// increased portability.
        ///
        /// This is mutually exclusive with `PROCESS` and `THREAD`.
        //
        // --- Implementation details ---
        //
        // This is not an actual hwloc flag, it is only used to detect
        // incompatible configurations and must be cleared before invoking
        // hwloc. validate() will clear the flag for you.
        const ASSUME_SINGLE_THREAD = 1 << (hwloc_membind_flags_t::BITS - 2);

        /// Apply command to all threads of the specified process
        ///
        /// This is mutually exclusive with `ASSUME_SINGLE_THREAD` and `THREAD`.
        #[doc(alias = "HWLOC_MEMBIND_PROCESS")]
        const PROCESS = HWLOC_MEMBIND_PROCESS;

        /// Apply command to the current thread of the current process
        ///
        /// This is mutually exclusive with `ASSUME_SINGLE_THREAD` and `PROCESS`.
        #[doc(alias = "HWLOC_MEMBIND_THREAD")]
        const THREAD = HWLOC_MEMBIND_THREAD;

        /// Request strict binding from the OS
        ///
        /// If this flag is set, a binding method will fail if the binding can
        /// not be guaranteed or completely enforced. Otherwise, hwloc will
        /// attempt to achieve an approximation of the requested binding (e.g.
        /// targeting more or less threads and NUMA nodes).
        ///
        /// This flag has slightly different meanings depending on which
        /// method it is used with.
        #[doc(alias = "HWLOC_MEMBIND_STRICT")]
        const STRICT = HWLOC_MEMBIND_STRICT;

        /// Migrate existing allocated memory
        ///
        /// If the memory cannot be migrated and the `STRICT` flag is set, an
        /// error will be returned.
        ///
        /// This flag is only meaningful on operations that bind memory.
        ///
        /// Requires [`MemoryBindingSupport::migrate_flag()`].
        #[doc(alias = "HWLOC_MEMBIND_MIGRATE")]
        const MIGRATE = HWLOC_MEMBIND_MIGRATE;

        /// Avoid any effect on CPU binding
        ///
        /// On some operating systems, some underlying memory binding
        /// methods also bind the application to the corresponding CPU(s).
        /// Using this flag will cause hwloc to avoid using OS functions that
        /// could potentially affect CPU bindings.
        ///
        /// Note, however, that using this flag may reduce hwloc's overall
        /// memory binding support.
        #[doc(alias = "HWLOC_MEMBIND_NOCPUBIND")]
        const NO_CPU_BINDING = HWLOC_MEMBIND_NOCPUBIND;

        /// Consider the bitmap argument as a nodeset.
        ///
        /// The bitmap argument is considered a nodeset if this flag is given,
        /// or a cpuset otherwise by default.
        ///
        /// Memory binding by CPU set cannot work for CPU-less NUMA memory nodes.
        /// Binding by nodeset should therefore be preferred whenever possible.
        //
        // --- Implementation details ---
        //
        // This flag does not need to be visible as it is automatically set and
        // cleared by the implementation as appropriate.
        #[doc(hidden)]
        #[doc(alias = "HWLOC_MEMBIND_BYNODESET")]
        const BY_NODE_SET = HWLOC_MEMBIND_BYNODESET;
    }
}
//
impl MemoryBindingFlags {
    /// Truth that these flags are in a valid state
    pub(crate) fn validate(
        mut self,
        target: MemoryBoundObject,
        operation: MemoryBindingOperation,
    ) -> Option<Self> {
        // Target flags should always be specified for operations that target
        // the current process, for other operations they are assumed not to be
        // accepted unless the hwloc docs say otherwise
        let num_target_flags = (self & (Self::PROCESS | Self::THREAD | Self::ASSUME_SINGLE_THREAD))
            .bits()
            .count_ones();
        let expected_num_target_flags = match target {
            MemoryBoundObject::ThisProgram => 1,
            MemoryBoundObject::Area => 0,
            MemoryBoundObject::Process(_) => match operation {
                MemoryBindingOperation::Bind | MemoryBindingOperation::Unbind => 0,
                MemoryBindingOperation::GetBinding | MemoryBindingOperation::GetLastLocation => 1,
                MemoryBindingOperation::Allocate => unreachable!(),
            },
        };
        if num_target_flags != expected_num_target_flags {
            return None;
        }

        // The THREAD flag should only be used for the current process
        if target != MemoryBoundObject::ThisProgram && self.contains(Self::THREAD) {
            return None;
        }

        // Operation-specific considerations
        match operation {
            MemoryBindingOperation::GetLastLocation => {
                if self.intersects(Self::STRICT | Self::MIGRATE | Self::NO_CPU_BINDING) {
                    return None;
                }
            }
            MemoryBindingOperation::GetBinding => {
                if self.intersects(Self::MIGRATE | Self::NO_CPU_BINDING) {
                    return None;
                }
                match target {
                    MemoryBoundObject::Area | MemoryBoundObject::Process(_) => {}
                    MemoryBoundObject::ThisProgram => {
                        if self.contains(Self::STRICT) && !self.contains(Self::PROCESS) {
                            return None;
                        }
                    }
                }
            }
            MemoryBindingOperation::Unbind => {
                if self.intersects(Self::STRICT | Self::MIGRATE) {
                    return None;
                }
            }
            MemoryBindingOperation::Allocate => {
                if self.contains(Self::MIGRATE) {
                    return None;
                }
            }
            MemoryBindingOperation::Bind => {
                if target == MemoryBoundObject::Area && self.contains(Self::MIGRATE) {
                    return None;
                }
            }
        }

        // Clear virtual ASSUME_SINGLE_THREAD flag, which served its purpose
        self.remove(Self::ASSUME_SINGLE_THREAD);
        Some(self)
    }
}
//
crate::impl_arbitrary_for_bitflags!(MemoryBindingFlags, hwloc_membind_flags_t);
//
// NOTE: No default because user must consciously think about the need for PROCESS

/// Object that is being bound to particular NUMA nodes
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum MemoryBoundObject {
    /// A process, identified by its PID
    Process(ProcessId),

    /// A range of memory adresses, identified by a reference
    Area,

    /// The currently running program
    ThisProgram,
}
//
#[cfg(any(test, feature = "proptest"))]
impl proptest::prelude::Arbitrary for MemoryBoundObject {
    type Parameters = ();
    type Strategy = proptest::strategy::TupleUnion<(
        proptest::strategy::WA<proptest::strategy::Just<Self>>,
        proptest::strategy::WA<proptest::strategy::Just<Self>>,
        proptest::strategy::WA<
            proptest::strategy::Map<
                <ProcessId as proptest::arbitrary::Arbitrary>::Strategy,
                fn(ProcessId) -> Self,
            >,
        >,
    )>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        use proptest::prelude::*;
        prop_oneof![
            1 => Just(Self::ThisProgram),
            1 => Just(Self::Area),
            3 => any::<ProcessId>().prop_map(Self::Process)
        ]
    }
}
//
impl Display for MemoryBoundObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let display = match self {
            Self::Process(pid) => format!("the process with PID {pid}"),
            Self::Area => "the target location".to_owned(),
            Self::ThisProgram => "the current process/thread".to_owned(),
        };
        f.pad(&display)
    }
}
//
impl From<ProcessId> for MemoryBoundObject {
    fn from(value: ProcessId) -> Self {
        Self::Process(value)
    }
}

/// Binding operation
#[derive(Copy, Clone, Debug, Display, EnumCount, EnumIter, Eq, Hash, PartialEq)]
pub(crate) enum MemoryBindingOperation {
    /// Allocate memory
    Allocate,

    /// Bind memory to some NUMA nodes
    Bind,

    /// Query the current binding of some memory
    GetBinding,

    /// Query on which NUMA node(s) memory was last resident
    GetLastLocation,

    /// Un-bind memory
    Unbind,
}
//
crate::impl_arbitrary_for_sequence!(MemoryBindingOperation);

/// Memory binding policy
///
/// Not all systems support all kinds of binding.
/// [`Topology::feature_support()`] may be used to query the actual memory
/// binding support in the currently used operating system.
#[derive(
    Copy, Clone, Debug, Default, Display, EnumCount, EnumIter, Eq, FromRepr, Hash, PartialEq,
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
    /// Requires [`MemoryBindingSupport::first_touch_policy()`].
    #[doc(alias = "HWLOC_MEMBIND_FIRSTTOUCH")]
    FirstTouch = HWLOC_MEMBIND_FIRSTTOUCH,

    /// Allocate memory on the specified nodes (most portable option)
    ///
    /// The actual behavior may slightly vary between operating systems,
    /// especially when (some of) the requested nodes are full. On Linux, by
    /// default, the `MPOL_PREFERRED_MANY` (or `MPOL_PREFERRED`) policy is used.
    /// However, if the [`STRICT`] flag is also given, the Linux `MPOL_BIND`
    /// policy is rather used.
    ///
    /// Requires [`MemoryBindingSupport::bind_policy()`].
    ///
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    #[default]
    #[doc(alias = "HWLOC_MEMBIND_BIND")]
    Bind = HWLOC_MEMBIND_BIND,

    /// Allocate memory on the given nodes in an interleaved round-robin manner
    ///
    /// The precise layout of the memory across multiple NUMA nodes is OS/system
    /// specific.
    ///
    /// Interleaving can be useful when threads distributed across the specified
    /// NUMA nodes will all be accessing the whole memory range concurrently,
    /// since the interleave will then balance the memory references.
    ///
    /// Requires [`MemoryBindingSupport::interleave_policy()`].
    #[doc(alias = "HWLOC_MEMBIND_INTERLEAVE")]
    Interleave = HWLOC_MEMBIND_INTERLEAVE,

    /// Allocate memory on the given nodes in an interleaved / weighted manner.
    ///
    /// The precise layout of the memory across multiple NUMA nodes is OS/system
    /// specific.
    ///
    /// Weighted interleaving can be useful when threads distributed across the
    /// specified NUMA nodes with different bandwidth capabilities will all be
    /// accessing the whole memory range concurrently, since the interleave will
    /// then balance the memory references.
    ///
    /// Requires [`MemoryBindingSupport::weighted_interleave_policy()`].
    #[cfg(feature = "hwloc-2_11_0")]
    #[doc(alias = "HWLOC_MEMBIND_WEIGHTED_INTERLEAVE")]
    WeightedInterleave = HWLOC_MEMBIND_WEIGHTED_INTERLEAVE,

    /// Migrate pages on next touch
    ///
    /// For each page bound with this policy, by next time it is touched (and
    /// next time only), it is moved from its current location to the local NUMA
    /// node of the thread where the memory reference occurred (if it needs to
    /// be moved at all).
    ///
    /// Requires [`MemoryBindingSupport::next_touch_policy()`].
    #[doc(alias = "HWLOC_MEMBIND_NEXTTOUCH")]
    NextTouch = HWLOC_MEMBIND_NEXTTOUCH,

    /// Unknown [`hwloc_membind_policy_t`] from hwloc
    #[strum(disabled)]
    Unknown(UnknownVariant<hwloc_membind_policy_t>) = hwloc_membind_policy_t::MAX,
}
//
impl MemoryBindingPolicy {
    /// Build a `MemoryBindingPolicy` from an hwloc-originated [`hwloc_membind_policy_t`]
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
    pub(crate) unsafe fn from_hwloc(value: hwloc_membind_policy_t) -> Self {
        Self::from_repr(value).unwrap_or(Self::Unknown(UnknownVariant(value)))
    }
}
//
crate::impl_arbitrary_for_sequence!(MemoryBindingPolicy);
//
impl From<MemoryBindingPolicy> for hwloc_membind_policy_t {
    fn from(value: MemoryBindingPolicy) -> Self {
        match value {
            MemoryBindingPolicy::FirstTouch => HWLOC_MEMBIND_FIRSTTOUCH,
            MemoryBindingPolicy::Bind => HWLOC_MEMBIND_BIND,
            MemoryBindingPolicy::Interleave => HWLOC_MEMBIND_INTERLEAVE,
            #[cfg(feature = "hwloc-2_11_0")]
            MemoryBindingPolicy::WeightedInterleave => HWLOC_MEMBIND_WEIGHTED_INTERLEAVE,
            MemoryBindingPolicy::NextTouch => HWLOC_MEMBIND_NEXTTOUCH,
            MemoryBindingPolicy::Unknown(unknown) => unknown.0,
        }
    }
}

/// Errors that can occur when binding memory to NUMA nodes, querying bindings,
/// or allocating (possibly bound) memory
#[derive(Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum MemoryBindingError<Set: SpecializedBitmap> {
    /// Memory allocation failed even before trying to bind
    ///
    /// This error may only be returned by [`Topology`] methods that allocate
    /// memory (recognizable by the fact that they all return [`Bytes`]).
    #[error("failed to allocate memory")]
    AllocationFailed,

    /// Requested memory binding flags are not valid in this context
    ///
    /// Not all memory binding flag combinations make sense, either in isolation
    /// or in the context of a particular binding method. Please cross-check
    /// the documentation of [`MemoryBindingFlags`] and the method you were
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
    #[error("cannot bind memory of {0} to {1}")]
    BadSet(MemoryBoundObject, Set),

    /// Cannot query the memory binding of a zero-sized memory region
    ///
    /// Since the target memory region contains no bytes, the memory binding of
    /// these absent bytes cannot be queried from the OS.
    ///
    /// Note that in contrast, attempting to _set_ the memory binding of a
    /// zero-sized memory region will succeed, but have no effect.
    #[error("cannot query the memory location of a zero-sized target")]
    BadArea,

    /// Memory policies and nodesets vary from one thread to another
    ///
    /// This error is returned when querying a process' memory bindings with the
    /// flags [`PROCESS`] and [`STRICT`] specified. It means that the default
    /// memory policies and nodesets are not homogeneous across all threads of
    /// the target process.
    ///
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    #[error("memory binding varies from one thread of the process to another")]
    #[doc(alias = "HWLOC_MEMBIND_MIXED")]
    MixedResults,

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
    #[error("requested memory binding action or policy isn't supported")]
    Unsupported,

    /// An error occured, but we don't know which one
    ///
    /// This may only happen on Windows. On this operating system, there are
    /// multiple versions of the standard library (called the C Run-Times or
    /// CRTs), and it is very easy to end up in a situation where your program
    /// links against a different CRT than your hwloc build, which breaks
    /// errno-based error reporting among other things.
    #[cfg(windows)]
    #[error("an unknown error occured")]
    Unknown,
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
    clone_set: &dyn Fn() -> Option<Set>,
    ffi: impl FnOnce() -> c_int,
) -> Result<(), HybridError<MemoryBindingError<Set>>> {
    match errors::call_hwloc_zero_or_minus1(api, ffi) {
        Ok(()) => Ok(()),
        Err(e @ RawHwlocError { errno, .. }) => {
            Err(decode_errno(object, operation, clone_set, errno)
                .map_or_else(|| HybridError::Hwloc(e), HybridError::Rust))
        }
    }
}

/// Errors that can occur when allocating memory
pub type MemoryAllocationError<Set> = MemoryBindingError<Set>;

/// Translating hwloc errno into high-level errors
fn decode_errno<Set: SpecializedBitmap>(
    object: MemoryBoundObject,
    operation: MemoryBindingOperation,
    clone_set: &dyn Fn() -> Option<Set>,
    errno: Option<Errno>,
) -> Option<MemoryBindingError<Set>> {
    match errno {
        Some(Errno(ENOSYS)) => Some(MemoryBindingError::Unsupported),
        Some(Errno(EXDEV)) => match operation {
            MemoryBindingOperation::Bind | MemoryBindingOperation::Allocate => {
                Some(MemoryBindingError::BadSet(
                    object,
                    clone_set()
                        .expect("This error should only be observed on commands that set bindings"),
                ))
            }
            MemoryBindingOperation::GetBinding | MemoryBindingOperation::GetLastLocation => {
                Some(MemoryBindingError::MixedResults)
            }
            MemoryBindingOperation::Unbind => {
                unreachable!("The empty set should always be considered valid")
            }
        },
        Some(Errno(ENOMEM)) => Some(MemoryBindingError::AllocationFailed),
        #[cfg(windows)]
        // Work around CRT mismatch issues on Windows, which break errno
        None => Some(MemoryBindingError::Unknown),
        _ => None,
    }
}

/// Bytes allocated through hwloc
///
/// This behaves like a `Box<[MaybeUninit<u8>]>` and will similarly
/// automatically liberate the allocated memory when it goes out of scope.
//
// --- Implementation details ---
//
// # Safety
//
// - If the size is nonzero, `data` is an owned (valid, non-aliased)
//   hwloc-originated allocation from `topology`, with correct size metadata,
//   that should be freed on Drop
// - If the size is zero, `data` is a zero-sized slice with a dangling base
//   pointer, that should not be freed on Drop
pub struct Bytes<'topology> {
    /// Underlying hwloc topology
    topology: &'topology Topology,

    /// Previously allocated data pointer
    data: NonNull<[MaybeUninit<u8>]>,
}
//
impl<'topology> Bytes<'topology> {
    /// Wrap an hwloc allocation
    ///
    /// # Panics
    ///
    /// Panics if the slice covers more than `isize::MAX` bytes, as this is not
    /// supported by Rust.
    ///
    /// # Safety
    ///
    /// If the size is nonzero, `base` must originate from an hwloc memory
    /// allocation function that was called on `topology` for `size` bytes.
    unsafe fn wrap(topology: &'topology Topology, base: NonNull<c_void>, size: usize) -> Self {
        isize::try_from(size).expect("Unsupported allocation size");
        Self {
            topology,
            data: NonNull::slice_from_raw_parts(base.cast::<MaybeUninit<u8>>(), size),
        }
    }
}
//
impl AsRef<[MaybeUninit<u8>]> for Bytes<'_> {
    fn as_ref(&self) -> &[MaybeUninit<u8>] {
        // SAFETY: Per type invariant
        unsafe { self.data.as_ref() }
    }
}
//
impl AsMut<[MaybeUninit<u8>]> for Bytes<'_> {
    fn as_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        // SAFETY: Per type invariant
        unsafe { self.data.as_mut() }
    }
}
//
impl Borrow<[MaybeUninit<u8>]> for Bytes<'_> {
    fn borrow(&self) -> &[MaybeUninit<u8>] {
        self.as_ref()
    }
}
//
impl BorrowMut<[MaybeUninit<u8>]> for Bytes<'_> {
    fn borrow_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.as_mut()
    }
}
//
impl Debug for Bytes<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(self.as_ref(), f)
    }
}
//
impl Deref for Bytes<'_> {
    type Target = [MaybeUninit<u8>];

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}
//
impl DerefMut for Bytes<'_> {
    fn deref_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.as_mut()
    }
}
//
impl Drop for Bytes<'_> {
    #[allow(clippy::print_stderr)]
    #[doc(alias = "hwloc_free")]
    fn drop(&mut self) {
        let len = self.data.len();
        if len > 0 {
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - self.data is trusted to be valid (type invariant)
            //         - hwloc ops are trusted not to modify *const parameters
            //         - Bytes will not be usable again after Drop
            let result = errors::call_hwloc_zero_or_minus1("hwloc_free", || unsafe {
                hwlocality_sys::hwloc_free(
                    self.topology.as_ptr(),
                    self.data.as_ptr().cast::<c_void>(),
                    len,
                )
            });
            if let Err(e) = result {
                // Cannot panic in Drop
                eprintln!("ERROR: Failed to liberate hwloc allocation ({e}).",);
            }
        }
    }
}
//
// SAFETY: Exposes no internal mutability
unsafe impl Send for Bytes<'_> {}
//
// SAFETY: Exposes no internal mutability
unsafe impl Sync for Bytes<'_> {}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    #[allow(unused)]
    use similar_asserts::assert_eq;

    // Most of the functionality in this module must be tested in the
    // single_threaded integration test because of ASSUME_SINGLE_THREAD, but
    // some things can be tested here.

    proptest! {
        #[test]
        fn display_membound_object(
            obj: MemoryBoundObject,
        ) {
            let display = obj.to_string();
            match obj {
                MemoryBoundObject::Process(pid) => {
                    let expected_pid = format!("PID {pid}");
                    prop_assert!(display.contains("process"));
                    prop_assert!(display.contains(&expected_pid));
                }
                MemoryBoundObject::ThisProgram => {
                    prop_assert!(display.contains("current process/thread"));
                }
                MemoryBoundObject::Area => {}
            }
        }

        #[test]
        fn pid_to_membound(pid: ProcessId) {
            let obj = MemoryBoundObject::from(pid);
            prop_assert_eq!(obj, MemoryBoundObject::Process(pid));
        }
    }
}
