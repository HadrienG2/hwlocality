//! CPU binding
//!
//! This module is all about checking and changing the binding of threads and
//! processes to hardware CPU cores.
//!
//! Most of this module's functionality is exposed via [methods of the Topology
//! struct](../../topology/struct.Topology.html#cpu-binding). The module itself
//! only hosts type definitions that are related to this functionality.

#[cfg(doc)]
use crate::{bitmap::Bitmap, object::types::ObjectType, topology::support::CpuBindingSupport};
use crate::{
    cpu::cpuset::CpuSet,
    errors::{self, FlagsError, HybridError, RawHwlocError},
    topology::Topology,
    ProcessId, ThreadId,
};
use bitflags::bitflags;
use derive_more::Display;
use hwlocality_sys::{
    hwloc_const_cpuset_t, hwloc_const_topology_t, hwloc_cpubind_flags_t, hwloc_cpuset_t,
    HWLOC_CPUBIND_NOMEMBIND, HWLOC_CPUBIND_PROCESS, HWLOC_CPUBIND_STRICT, HWLOC_CPUBIND_THREAD,
};
use libc::{ENOSYS, EXDEV};
#[allow(unused)]
#[cfg(test)]
use pretty_assertions::{assert_eq, assert_ne};
use std::{
    borrow::Borrow,
    ffi::{c_int, c_uint},
    fmt::Display,
};
use thiserror::Error;

/// # CPU binding
///
/// Some operating systems do not provide all hwloc-supported mechanisms to bind
/// processes, threads, etc. [`Topology::feature_support()`] may be used to
/// query about the actual CPU binding support in the currently used operating
/// system. The documentation of individual CPU binding methods will clarify
/// which support flags they require.
///
/// By default, when the requested binding operation is not available, hwloc
/// will go for a similar binding operation (with side-effects, smaller
/// binding set, etc). You can inhibit this with flag [`STRICT`], at the
/// expense of reducing portability across operating systems.
///
/// [`STRICT`]: CpuBindingFlags::STRICT
//
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpubinding.html
impl Topology {
    /// Binds the current process or thread on given CPUs
    ///
    /// Some operating systems only support binding threads or processes to a
    /// single [`PU`]. Others allow binding to larger sets such as entire
    /// [`Core`]s or [`Package`]s or even random sets of individual [`PU`]s. In
    /// such operating systems, the scheduler is free to run the task on one of
    /// these PU, then migrate it to another [`PU`], etc. It is often useful to
    /// call [`singlify()`] on the target CPU set before passing it to the
    /// binding method to avoid these expensive migrations.
    ///
    /// To unbind, just call the binding method with either a full cpuset or a
    /// cpuset equal to the system cpuset.
    ///
    /// You must specify exactly one of the [`ASSUME_SINGLE_THREAD`],
    /// [`THREAD`] and [`PROCESS`] binding target flags (listed in order of
    /// decreasing portability) when using this method.
    ///
    /// On some operating systems, CPU binding may have effects on memory
    /// binding, you can forbid this with flag [`NO_MEMORY_BINDING`].
    ///
    /// Running `lstopo --top` or `hwloc-ps` can be a very convenient tool to
    /// check how binding actually happened.
    ///
    /// Requires [`CpuBindingSupport::set_current_process()`] or
    /// [`CpuBindingSupport::set_current_thread()`] depending on flags.
    ///
    /// See also [the top-level CPU binding CPU
    /// documentation](../../topology/struct.Topology.html#cpu-binding).
    ///
    /// # Errors
    ///
    /// - [`BadCpuSet`] if it is not possible to bind the current process/thread
    ///   to the requested CPU set, specifically
    /// - [`BadFlags`] if the number of specified binding target flags is not
    ///   exactly one
    /// - [`BadObject(ThisProgram)`] if it is not possible to bind the current
    ///   process/thread to CPUs, generally speaking
    ///
    /// [`ASSUME_SINGLE_THREAD`]: CpuBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadCpuSet`]: CpuBindingError::BadCpuSet
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ThisProgram)`]: CpuBindingError::BadObject
    /// [`Core`]: ObjectType::Core
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`Package`]: ObjectType::Package
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`PU`]: ObjectType::PU
    /// [`THREAD`]: CpuBindingFlags::THREAD
    /// [`singlify()`]: Bitmap::singlify()
    #[doc(alias = "hwloc_set_cpubind")]
    pub fn bind_cpu(
        &self,
        set: impl Borrow<CpuSet>,
        flags: CpuBindingFlags,
    ) -> Result<(), CpuBindingError> {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized(
            self_: &Topology,
            set: &CpuSet,
            flags: CpuBindingFlags,
        ) -> Result<(), CpuBindingError> {
            // SAFETY: - ThisProgram is the correct target for this operation
            //         - hwloc_set_cpubind is accepted by definition
            //         - FFI is guaranteed to be passed valid (topology, cpuset, flags)
            let res = unsafe {
                self_.bind_cpu_impl(
                    set,
                    flags,
                    CpuBoundObject::ThisProgram,
                    "hwloc_set_cpubind",
                    |topology, cpuset, flags| {
                        hwlocality_sys::hwloc_set_cpubind(topology, cpuset, flags)
                    },
                )
            };
            match res {
                Ok(()) => Ok(()),
                Err(HybridError::Rust(e)) => Err(e),
                Err(HybridError::Hwloc(e)) => unreachable!("Unexpected hwloc error: {e}"),
            }
        }
        polymorphized(self, set.borrow(), flags)
    }

    /// Get the current process or thread CPU binding
    ///
    /// You must specify exactly one of the [`ASSUME_SINGLE_THREAD`],
    /// [`THREAD`] and [`PROCESS`] binding target flags (listed in order of
    /// decreasing portability) when using this method.
    ///
    /// Flag [`NO_MEMORY_BINDING`] should not be used with this method.
    ///
    /// Requires [`CpuBindingSupport::get_current_process()`] or
    /// [`CpuBindingSupport::get_current_thread()`] depending on flags.
    ///
    /// See also [the top-level CPU binding CPU
    /// documentation](../../topology/struct.Topology.html#cpu-binding).
    ///
    /// # Errors
    ///
    /// - [`BadFlags`] if flag [`NO_MEMORY_BINDING`] was specified or if the
    ///   number of binding target flags is not exactly one
    /// - [`BadObject(ThisProgram)`] if it is not possible to query the CPU
    ///   binding of the current process/thread
    ///
    /// [`ASSUME_SINGLE_THREAD`]: CpuBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ThisProgram)`]: CpuBindingError::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[doc(alias = "hwloc_get_cpubind")]
    pub fn cpu_binding(
        &self,
        flags: CpuBindingFlags,
    ) -> Result<CpuSet, HybridError<CpuBindingError>> {
        // SAFETY: - ThisProgram is the correct target for this operation
        //         - hwloc_get_cpubind is accepted by definition
        //         - FFI is guaranteed to be passed valid (topology, cpuset, flags)
        unsafe {
            self.cpu_binding_impl(
                flags,
                CpuBoundObject::ThisProgram,
                "hwloc_get_cpubind",
                |topology, cpuset, flags| {
                    hwlocality_sys::hwloc_get_cpubind(topology, cpuset, flags)
                },
            )
        }
    }

    /// Binds a process (identified by its `pid`) on given CPUs
    ///
    /// As a special case on Linux, if a tid (thread ID) is supplied instead of
    /// a pid (process ID) and flag [`THREAD`] is specified, the specified
    /// thread is bound. Otherwise, flag [`THREAD`] should not be used with this
    /// method.
    ///
    /// See also [`Topology::bind_cpu()`] for more informations, except binding
    /// target flags other than [`THREAD`] should not be used with this method,
    /// and it requires [`CpuBindingSupport::set_process()`] or
    /// [`CpuBindingSupport::set_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`BadCpuSet`] if it is not possible to bind the target process/thread
    ///   to the requested CPU set, specifically
    /// - [`BadFlags`] if flag [`THREAD`] was specified on an operating system
    ///   other than Linux, or if any other binding target flag was specified
    /// - [`BadObject(ProcessOrThread)`] if it is not possible to bind the
    ///   target process/thread to CPUs, generally speaking
    ///
    /// [`BadCpuSet`]: CpuBindingError::BadCpuSet
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ProcessOrThread)`]: CpuBindingError::BadObject
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[doc(alias = "hwloc_set_proc_cpubind")]
    pub fn bind_process_cpu(
        &self,
        pid: ProcessId,
        set: impl Borrow<CpuSet>,
        flags: CpuBindingFlags,
    ) -> Result<(), HybridError<CpuBindingError>> {
        // SAFETY: - ProcessOrThread is the correct target for this operation
        //         - hwloc_set_proc_cpubind with pid argument curried away
        //           behaves like hwloc_set_cpubind
        //         - FFI is guaranteed to be passed valid (topology, cpuset, flags)
        //         - PID cannot be validated (think TOCTOU), but hwloc should be
        //           able to handle an invalid PID
        unsafe {
            self.bind_cpu_impl(
                set.borrow(),
                flags,
                CpuBoundObject::ProcessOrThread(pid),
                "hwloc_set_proc_cpubind",
                |topology, cpuset, flags| {
                    hwlocality_sys::hwloc_set_proc_cpubind(topology, pid, cpuset, flags)
                },
            )
        }
    }

    /// Get the current physical binding of a process, identified by its `pid`
    ///
    /// As a special case on Linux, if a tid (thread ID) is supplied instead of
    /// a pid (process ID) and flag [`THREAD`] is specified, the binding of the
    /// specified thread is returned. Otherwise, flag [`THREAD`] should not be
    /// used with this method.
    ///
    /// See [`Topology::cpu_binding()`] for more informations, except binding
    /// target flags other than [`THREAD`] should not be used with this method,
    /// and it requires [`CpuBindingSupport::get_process()`] or
    /// [`CpuBindingSupport::get_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`BadFlags`] if one of the  [`NO_MEMORY_BINDING`] was specified, if
    ///   flag [`THREAD`] was specified on an operating system other than Linux,
    ///   or if any other binding target flag was specified
    /// - [`BadObject(ProcessOrThread)`] if it is not possible to query the CPU
    ///   binding of the target process/thread
    ///
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ProcessOrThread)`]: CpuBindingError::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[doc(alias = "hwloc_get_proc_cpubind")]
    pub fn process_cpu_binding(
        &self,
        pid: ProcessId,
        flags: CpuBindingFlags,
    ) -> Result<CpuSet, HybridError<CpuBindingError>> {
        // SAFETY: - ProcessOrThread is the correct target for this operation
        //         - hwloc_get_proc_cpubind with pid argument curried away
        //           behaves like hwloc_get_cpubind
        //         - FFI is guaranteed to be passed valid (topology, cpuset, flags)
        //         - PID cannot be validated (think TOCTOU), but hwloc should be
        //           able to handle an invalid PID
        unsafe {
            self.cpu_binding_impl(
                flags,
                CpuBoundObject::ProcessOrThread(pid),
                "hwloc_get_proc_cpubind",
                |topology, cpuset, flags| {
                    hwlocality_sys::hwloc_get_proc_cpubind(topology, pid, cpuset, flags)
                },
            )
        }
    }

    /// Bind a thread, identified by its `tid`, on the given CPUs
    ///
    /// See [`Topology::bind_cpu()`] for more informations, except binding
    /// target flags should not be used with this method, and it always
    /// requires [`CpuBindingSupport::set_thread()`].
    ///
    /// # Errors
    ///
    /// - [`BadCpuSet`] if it is not possible to bind the target thread to the
    ///   requested CPU set, specifically
    /// - [`BadFlags`] if a binding target flag was specified
    /// - [`BadObject(Thread)`] if it is not possible to bind the target thread
    ///   to CPUs, generally speaking
    ///
    /// [`BadCpuSet`]: CpuBindingError::BadCpuSet
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(Thread)`]: CpuBindingError::BadObject
    #[doc(alias = "hwloc_set_thread_cpubind")]
    pub fn bind_thread_cpu(
        &self,
        tid: ThreadId,
        set: impl Borrow<CpuSet>,
        flags: CpuBindingFlags,
    ) -> Result<(), HybridError<CpuBindingError>> {
        // SAFETY: - Thread is the correct target for this operation
        //         - hwloc_set_thread_cpubind with tid argument curried away
        //           behaves like hwloc_set_cpubind
        //         - FFI is guaranteed to be passed valid (topology, cpuset, flags)
        //         - TID cannot be validated (think TOCTOU), but hwloc should be
        //           able to handle an invalid TID
        unsafe {
            self.bind_cpu_impl(
                set.borrow(),
                flags,
                CpuBoundObject::Thread(tid),
                "hwloc_set_thread_cpubind",
                |topology, cpuset, flags| {
                    hwlocality_sys::hwloc_set_thread_cpubind(topology, tid, cpuset, flags)
                },
            )
        }
    }

    /// Get the current physical binding of thread `tid`
    ///
    /// Flags [`STRICT`], [`NO_MEMORY_BINDING`] and binding target flags should
    /// not be used with this method.
    ///
    /// See [`Topology::cpu_binding()`] for more informations, except binding
    /// target flags should not be used with this method, and it requires
    /// [`CpuBindingSupport::get_thread()`].
    ///
    /// # Errors
    ///
    /// - [`BadFlags`] if at least one of flags [`STRICT`] and
    ///   [`NO_MEMORY_BINDING`] or a binding target flag was specified
    /// - [`BadObject(Thread)`] if it is not possible to query the CPU
    ///   binding of the target thread
    ///
    /// [`ASSUME_SINGLE_THREAD`]: CpuBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(Thread)`]: CpuBindingError::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`STRICT`]: CpuBindingFlags::STRICT
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[doc(alias = "hwloc_get_thread_cpubind")]
    pub fn thread_cpu_binding(
        &self,
        tid: ThreadId,
        flags: CpuBindingFlags,
    ) -> Result<CpuSet, HybridError<CpuBindingError>> {
        // SAFETY: - Thread is the correct target for this operation
        //         - hwloc_get_thread_cpubind with tid argument curried away
        //           behaves like hwloc_get_cpubind
        //         - FFI is guaranteed to be passed valid (topology, cpuset, flags)
        //         - TID cannot be validated (think TOCTOU), but hwloc should be
        //           able to handle an invalid TID
        unsafe {
            self.cpu_binding_impl(
                flags,
                CpuBoundObject::Thread(tid),
                "hwloc_get_thread_cpubind",
                |topology, cpuset, flags| {
                    hwlocality_sys::hwloc_get_thread_cpubind(topology, tid, cpuset, flags)
                },
            )
        }
    }

    /// Get the last physical CPUs where the current process or thread ran
    ///
    /// The operating system may move some tasks from one processor
    /// to another at any time according to their binding,
    /// so this method may return something that is already
    /// outdated.
    ///
    /// You must specify exactly one of the [`ASSUME_SINGLE_THREAD`],
    /// [`THREAD`] and [`PROCESS`] binding target flags (listed in order of
    /// decreasing portability) when using this method.
    ///
    /// Flags [`NO_MEMORY_BINDING`] and [`STRICT`] should not be used with this
    /// method.
    ///
    /// Requires [`CpuBindingSupport::get_current_process_last_cpu_location()`]
    /// or [`CpuBindingSupport::get_current_thread_last_cpu_location()`]
    /// depending on flags.
    ///
    /// See also [the top-level CPU binding CPU
    /// documentation](../../topology/struct.Topology.html#cpu-binding).
    ///
    /// # Errors
    ///
    /// - [`BadFlags`] if one of flags [`NO_MEMORY_BINDING`] and [`STRICT`] was
    ///   specified, or if the number of binding target flags is not exactly
    ///   one
    /// - [`BadObject(ThisProgram)`] if it is not possible to query the CPU
    ///   location of the current process/thread
    ///
    /// [`ASSUME_SINGLE_THREAD`]: CpuBindingFlags::ASSUME_SINGLE_THREAD
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ThisProgram)`]: CpuBindingError::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`STRICT`]: CpuBindingFlags::STRICT
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[doc(alias = "hwloc_get_last_cpu_location")]
    pub fn last_cpu_location(
        &self,
        flags: CpuBindingFlags,
    ) -> Result<CpuSet, HybridError<CpuBindingError>> {
        // SAFETY: - ThisProgram is the correct target for this operation
        //         - hwloc_get_last_cpu_location is accepted by definition
        //         - FFI is guaranteed to be passed valid (topology, cpuset, flags)
        unsafe {
            self.last_cpu_location_impl(
                flags,
                CpuBoundObject::ThisProgram,
                "hwloc_get_last_cpu_location",
                |topology, cpuset, flags| {
                    hwlocality_sys::hwloc_get_last_cpu_location(topology, cpuset, flags)
                },
            )
        }
    }

    /// Get the last physical CPU where a process ran.
    ///
    /// As a special case on Linux, if a tid (thread ID) is supplied instead of
    /// a pid (process ID) and flag [`THREAD`] is specified, the last cpu
    /// location of the specified thread is returned. Otherwise, flag [`THREAD`]
    /// should not be used with this method.
    ///
    /// See [`Topology::last_cpu_location()`] for more informations, except
    /// binding target flags other than [`THREAD`] should not be used with this
    /// method, and it requires
    /// [`CpuBindingSupport::get_process_last_cpu_location()`].
    ///
    /// # Errors
    ///
    /// - [`BadFlags`] if one of flags [`NO_MEMORY_BINDING`] and [`STRICT`] was
    ///   specified, if flag [`THREAD`] was specified on an operating system
    ///   other than Linux, or if any other binding target flag was specified
    /// - [`BadObject(ProcessOrThread)`] if it is not possible to query the CPU
    ///   binding of the target process/thread
    ///
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ProcessOrThread)`]: CpuBindingError::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`STRICT`]: CpuBindingFlags::STRICT
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[doc(alias = "hwloc_get_proc_last_cpu_location")]
    pub fn last_process_cpu_location(
        &self,
        pid: ProcessId,
        flags: CpuBindingFlags,
    ) -> Result<CpuSet, HybridError<CpuBindingError>> {
        // SAFETY: - ProcessOrThread is the correct target for this operation
        //         - hwloc_get_proc_last_cpu_location with pid argument curried
        //           away behaves like hwloc_get_last_cpu_location
        //         - FFI is guaranteed to be passed valid (topology, cpuset, flags)
        //         - PID cannot be validated (think TOCTOU), but hwloc should be
        //           able to handle an invalid PID
        unsafe {
            self.last_cpu_location_impl(
                flags,
                CpuBoundObject::ProcessOrThread(pid),
                "hwloc_get_proc_last_cpu_location",
                |topology, cpuset, flags| {
                    hwlocality_sys::hwloc_get_proc_last_cpu_location(topology, pid, cpuset, flags)
                },
            )
        }
    }

    /// Binding for `hwloc_set_cpubind`-like functions
    ///
    /// # Safety
    ///
    /// - `ffi` should have semantics analogous to `hwloc_set_cpubind`
    /// - `target` should accurately reflect the target which this function
    ///   is applied to, for flags validation purposes
    /// - If all of the above is true, this is guaranteed to only call `ffi`
    ///   with a valid (topology, bitmap, flags) tuple
    unsafe fn bind_cpu_impl(
        &self,
        set: &CpuSet,
        flags: CpuBindingFlags,
        target: CpuBoundObject,
        api: &'static str,
        ffi: impl FnOnce(hwloc_const_topology_t, hwloc_const_cpuset_t, hwloc_cpubind_flags_t) -> c_int,
    ) -> Result<(), HybridError<CpuBindingError>> {
        let Some(flags) = flags.validate(target, CpuBindingOperation::SetBinding) else {
            return Err(CpuBindingError::from(flags).into());
        };
        call_hwloc(api, target, Some(set), || {
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - Bitmap is trusted to contain a valid ptr (type invariant)
            //         - hwloc ops are trusted not to modify *const parameters
            //         - flags should be valid if target is valid
            ffi(self.as_ptr(), set.as_ptr(), flags.bits())
        })
    }

    /// Binding for `hwloc_get_cpubind`-like functions
    ///
    /// # Safety
    ///
    /// - `ffi` should have semantics analogous to `hwloc_get_cpubind`
    /// - `target` should accurately reflect the target which this function
    ///   is applied to, for flags validation purposes
    /// - If all of the above is true, this is guaranteed to only call `ffi`
    ///   with a valid (topology, out bitmap, flags) tuple
    unsafe fn cpu_binding_impl(
        &self,
        flags: CpuBindingFlags,
        target: CpuBoundObject,
        api: &'static str,
        ffi: impl FnOnce(hwloc_const_topology_t, hwloc_cpuset_t, hwloc_cpubind_flags_t) -> c_int,
    ) -> Result<CpuSet, HybridError<CpuBindingError>> {
        // SAFETY: - GetBinding is the valid operation tag for this FFI
        //         - Rest is per function precondition
        unsafe { self.get_cpuset(flags, target, CpuBindingOperation::GetBinding, api, ffi) }
    }

    /// Binding for `hwloc_get_last_cpu_location`-like functions
    ///
    /// # Safety
    ///
    /// - `ffi` should have semantics analogous to `hwloc_get_last_cpu_location`
    /// - `target` should accurately reflect the target which this function
    ///   is applied to, for flags validation purposes
    /// - If all of the above is true, this is guaranteed to only call `ffi`
    ///   with a valid (topology, out bitmap, flags) tuple
    unsafe fn last_cpu_location_impl(
        &self,
        flags: CpuBindingFlags,
        target: CpuBoundObject,
        api: &'static str,
        ffi: impl FnOnce(hwloc_const_topology_t, hwloc_cpuset_t, hwloc_cpubind_flags_t) -> c_int,
    ) -> Result<CpuSet, HybridError<CpuBindingError>> {
        // SAFETY: - GetLastLocation is the valid operation tag for this FFI
        //         - Rest is per function precondition
        unsafe {
            self.get_cpuset(
                flags,
                target,
                CpuBindingOperation::GetLastLocation,
                api,
                ffi,
            )
        }
    }

    /// Binding for all functions that get CPU bindings & locations
    ///
    /// # Safety
    ///
    /// - `ffi` should have semantics analogous to `hwloc_get_cpubind` and
    ///   `hwloc_get_last_cpu_location`
    /// - `target` should accurately reflect the target which this function
    ///   is applied to, for flags validation purposes
    /// - `operation` should accurately reflect the kind of operation being
    ///   performed, for flags validation purposes
    /// - If all of the above is true, this is guaranteed to only call `ffi`
    ///   with a valid (topology, out bitmap, flags) tuple
    unsafe fn get_cpuset(
        &self,
        flags: CpuBindingFlags,
        target: CpuBoundObject,
        operation: CpuBindingOperation,
        api: &'static str,
        ffi: impl FnOnce(hwloc_const_topology_t, hwloc_cpuset_t, hwloc_cpubind_flags_t) -> c_int,
    ) -> Result<CpuSet, HybridError<CpuBindingError>> {
        let Some(flags) = flags.validate(target, operation) else {
            return Err(CpuBindingError::from(flags).into());
        };
        let mut cpuset = CpuSet::new();
        call_hwloc(api, target, None, || {
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - Bitmap is trusted to contain a valid ptr (type invariant)
            //         - hwloc ops are trusted not to modify *const parameters
            //         - hwloc ops are trusted to keep *mut parameters in a
            //           valid state unless stated otherwise
            //         - flags should be valid if target & operation are valid
            ffi(self.as_ptr(), cpuset.as_mut_ptr(), flags.bits())
        })
        .map(|()| cpuset)
    }
}

bitflags! {
    /// Process/Thread binding flags
    ///
    /// These bit flags can be used to refine the binding policy. All flags can
    /// be OR'ed together with the exception of the binding targets flags
    /// `ASSUME_SINGLE_THREAD`, `THREAD` and `PROCESS`, which are mutually
    /// exclusive.
    ///
    /// When using one of the methods that target the active process, you must
    /// use exactly one of these flags. The most portable binding targets are
    /// `ASSUME_SINGLE_THREAD`, `THREAD` and `PROCESS`, in this order. These
    /// flags must generally not be used with any other method, except on
    /// Linux where flag `THREAD` can also be used to turn process-binding
    /// methods into thread-binding methods.
    ///
    /// Individual CPU binding methods may not support all of these flags.
    /// Please check the documentation of the [cpu binding
    /// method](../../topology/struct.Topology.html#cpu-binding) that you are
    /// calling for more information.
    #[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
    #[doc(alias = "hwloc_cpubind_flags_t")]
    pub struct CpuBindingFlags: hwloc_cpubind_flags_t {
        /// Assume that the current process is single threaded
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
        const ASSUME_SINGLE_THREAD = 1 << (hwloc_cpubind_flags_t::BITS - 2);

        /// Bind the current thread of the current process
        ///
        /// This is the second most portable option where `ASSUME_SINGLE_THREAD`
        /// is inapplicable.
        ///
        /// On Linux, this flag can also be used to turn process-binding
        /// methods into thread-binding methods.
        ///
        /// This is mutually exclusive with `ASSUME_SINGLE_THREAD` and `PROCESS`.
        #[doc(alias = "HWLOC_CPUBIND_THREAD")]
        const THREAD  = HWLOC_CPUBIND_THREAD;

        /// Bind all threads of the current process
        ///
        /// This is mutually exclusive with `ASSUME_SINGLE_THREAD` and `THREAD`.
        #[doc(alias = "HWLOC_CPUBIND_PROCESS")]
        const PROCESS = HWLOC_CPUBIND_PROCESS;

        /// Request for strict binding from the OS
        ///
        /// By default, when the designated CPUs are all busy while other CPUs
        /// are idle, operating systems may execute the thread/process on those
        /// other CPUs instead of the designated CPUs, to let them progress
        /// anyway. Strict binding means that the thread/process will _never_
        /// execute on other CPUs than the designated CPUs, even when those are
        /// busy with other tasks and other CPUs are idle.
        ///
        /// Depending on the operating system, strict binding may not be
        /// possible (e.g. the OS does not implement it) or not allowed (e.g.
        /// for an administrative reasons), and the binding method will fail
        /// in that case.
        ///
        /// When retrieving the binding of a process, this flag checks whether
        /// all its threads actually have the same binding. If the flag is not
        /// given, the binding of each thread will be accumulated.
        ///
        /// This flag should not be used when retrieving the binding of a
        /// thread or the CPU location of a process.
        #[doc(alias = "HWLOC_CPUBIND_STRICT")]
        const STRICT = HWLOC_CPUBIND_STRICT;

        /// Avoid any effect on memory binding
        ///
        /// On some operating systems, some CPU binding method would also bind
        /// the memory on the corresponding NUMA node. It is often not a
        /// problem for the application, but if it is, setting this flag will
        /// make hwloc avoid using OS functions that would also bind memory.
        /// This will however reduce the support of CPU bindings, i.e.
        /// potentially result in the binding method erroring out with a
        /// [`CpuBindingError`].
        ///
        /// This flag should only be used with methods that set the CPU
        /// binding.
        #[doc(alias = "HWLOC_CPUBIND_NOMEMBIND")]
        const NO_MEMORY_BINDING = HWLOC_CPUBIND_NOMEMBIND;
    }
}
//
// NOTE: No Default because user must consciously think about the need for
//       PROCESS vs ASSUME_SINGLE_THREAD.
//
impl CpuBindingFlags {
    /// Check that these flags are in a valid state, emit validated flags free
    /// of [`ASSUME_SINGLE_THREAD`] and ready for hwloc consumption.
    ///
    /// [`ASSUME_SINGLE_THREAD`]: CpuBindingFlags::ASSUME_SINGLE_THREAD
    pub(crate) fn validate(
        mut self,
        target: CpuBoundObject,
        operation: CpuBindingOperation,
    ) -> Option<Self> {
        // THREAD can only be specified on process binding methods on Linux,
        // to turn them into thread binding methods.
        let is_linux_thread_special_case =
            self.contains(Self::THREAD) && matches!(target, CpuBoundObject::ProcessOrThread(_));
        if is_linux_thread_special_case && cfg!(not(target_os = "linux")) {
            return None;
        }

        // Must use exactly one target flag when targeting the active process,
        // and none otherwise, except for the special case discussed above.
        let num_target_flags = (self & (Self::PROCESS | Self::THREAD | Self::ASSUME_SINGLE_THREAD))
            .bits()
            .count_ones();
        if (num_target_flags != u32::from(target == CpuBoundObject::ThisProgram))
            && !(is_linux_thread_special_case && num_target_flags == 1)
        {
            return None;
        }

        // Operation-specific considerations
        match operation {
            CpuBindingOperation::GetLastLocation => {
                if self.intersects(Self::STRICT | Self::NO_MEMORY_BINDING) {
                    return None;
                }
            }
            CpuBindingOperation::SetBinding => {}
            CpuBindingOperation::GetBinding => {
                if (self.contains(Self::STRICT) && matches!(target, CpuBoundObject::Thread(_)))
                    || self.contains(Self::NO_MEMORY_BINDING)
                {
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
#[cfg(any(test, feature = "quickcheck"))]
impl quickcheck::Arbitrary for CpuBindingFlags {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        Self::from_bits_truncate(hwloc_cpubind_flags_t::arbitrary(g))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let self_copy = *self;
        Box::new(self.into_iter().map(move |value| self_copy ^ value))
    }
}

/// Object that is being bound to particular CPUs
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum CpuBoundObject {
    /// A process, identified by its PID, or possibly a thread on Linux
    ProcessOrThread(ProcessId),

    /// A thread, identified by its TID
    Thread(ThreadId),

    /// The currently running program
    ThisProgram,
}
//
impl Display for CpuBoundObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let display = match self {
            Self::ProcessOrThread(id) => {
                if cfg!(linux) {
                    format!("the process/thread with ID {id}")
                } else {
                    format!("the process with PID {id}")
                }
            }
            Self::Thread(id) => format!("the thread with TID {id}"),
            Self::ThisProgram => "the current process/thread".to_owned(),
        };
        f.pad(&display)
    }
}

/// Operation on that object's CPU binding
#[derive(Copy, Clone, Debug, Display, Eq, Hash, PartialEq)]
pub(crate) enum CpuBindingOperation {
    /// `hwloc_get_cpubind()`-like operation
    GetBinding,

    /// `hwloc_set_cpubind()`-like operation
    SetBinding,

    /// `hwloc_get_last_cpu_location()`-like operation
    GetLastLocation,
}

/// Errors that can occur when manipulating process/thread CPU bindings
#[derive(Clone, Debug, Error, Eq, PartialEq)]
pub enum CpuBindingError {
    /// Cannot query or set CPU bindings for this kind of object
    ///
    /// This error might not be reported if [`CpuBindingFlags::STRICT`] is not
    /// set. Instead, the implementation is allowed to try to use a slightly
    /// different operation (with side-effects, larger object, etc.) when the
    /// requested operation is not exactly supported.
    #[error("cannot query or set the CPU binding of {0}")]
    BadObject(CpuBoundObject),

    /// Requested CPU binding flags are not valid in this context
    ///
    /// Not all CPU binding flag combinations make sense, either in isolation or
    /// in the context of a particular binding method. Please cross-check the
    /// documentation of [`CpuBindingFlags`] as well as that of the method
    /// you were trying to call for more information.
    #[error(transparent)]
    BadFlags(#[from] FlagsError<CpuBindingFlags>),

    /// Cannot bind the requested object to the target cpu set
    ///
    /// Operating systems can have various restrictions here, e.g. can only bind
    /// to one CPU, one NUMA node, etc.
    ///
    /// This error should only be reported when trying to set CPU bindings.
    ///
    /// This error might not be reported if [`CpuBindingFlags::STRICT`] is not
    /// set. Instead, the implementation is allowed to try to use a slightly
    /// different operation (with side-effects, smaller binding set, etc.) when
    /// the requested operation is not exactly supported.
    #[error("cannot change the CPU binding of {0} to {1}")]
    BadCpuSet(CpuBoundObject, CpuSet),
}
//
impl From<CpuBindingFlags> for CpuBindingError {
    fn from(value: CpuBindingFlags) -> Self {
        Self::BadFlags(value.into())
    }
}
//
impl From<CpuBoundObject> for CpuBindingError {
    fn from(value: CpuBoundObject) -> Self {
        Self::BadObject(value)
    }
}

/// Call an hwloc API that is about getting or setting CPU bindings, translate
/// known errors into higher-level `CpuBindingError`s.
///
/// Validating flags is left up to the caller, to avoid allocating result
/// objects when it can be proven upfront that the request is invalid.
pub(crate) fn call_hwloc(
    api: &'static str,
    object: CpuBoundObject,
    cpuset: Option<&CpuSet>,
    ffi: impl FnOnce() -> c_int,
) -> Result<(), HybridError<CpuBindingError>> {
    /// Polymorphized version of result translation (avoids generics code bloat)
    fn translate_result(
        object: CpuBoundObject,
        cpuset: Option<&CpuSet>,
        raw_result: Result<c_uint, RawHwlocError>,
    ) -> Result<(), HybridError<CpuBindingError>> {
        match raw_result {
            Ok(_positive) => Ok(()),
            Err(
                raw_err @ RawHwlocError {
                    errno: Some(errno), ..
                },
            ) => match errno.0 {
                // Using errno documentation from
                // https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpubinding.html
                ENOSYS => Err(CpuBindingError::BadObject(object).into()),
                EXDEV => Err(CpuBindingError::BadCpuSet(
                    object,
                    cpuset
                        .expect("This error should only be observed on commands that bind to CPUs")
                        .clone(),
                )
                .into()),
                _ => Err(HybridError::Hwloc(raw_err)),
            },
            Err(raw_err) => Err(HybridError::Hwloc(raw_err)),
        }
    }
    translate_result(object, cpuset, errors::call_hwloc_int_normal(api, ffi))
}
