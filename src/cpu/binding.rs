//! CPU binding

// Main docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpubinding.html

#[cfg(doc)]
use crate::{bitmaps::Bitmap, support::CpuBindingSupport};
use crate::{
    bitmaps::{CpuSet, RawBitmap},
    cpu,
    errors::{self, FlagsError, RawIntError},
    ffi, ProcessId, RawTopology, ThreadId, Topology,
};
use bitflags::bitflags;
use derive_more::Display;
use libc::{ENOSYS, EXDEV};
use std::{ffi::c_int, fmt::Display};
use thiserror::Error;

/// # CPU binding
///
/// Some operating systems do not provide all hwloc-supported mechanisms to bind
/// processes, threads, etc. [`Topology::feature_support()`] may be used to
/// query about the actual CPU binding support in the currently used operating
/// system. Individual CPU binding functions will clarify which support flags
/// they require.
///
/// You should specify one of the [`ASSUME_SINGLE_THREAD`], [`THREAD`] and
/// [`PROCESS`] flags (listed in order of decreasing portability) when using any
/// of the functions that target a process, but some functions may only support
/// a subset of these flags.
///
/// [`ASSUME_SINGLE_THREAD`]: CpuBindingFlags::ASSUME_SINGLE_THREAD
/// [`PROCESS`]: CpuBindingFlags::PROCESS
/// [`singlify()`]: Bitmap::singlify()
/// [`THREAD`]: CpuBindingFlags::THREAD
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
    /// By default, when the requested binding operation is not available, hwloc
    /// will go for a similar binding operation (with side-effects, smaller
    /// binding set, etc). You can inhibit this with flag [`STRICT`], at the
    /// expense of reducing portability across operating systems.
    ///
    /// To unbind, just call the binding function with either a full cpuset or a
    /// cpuset equal to the system cpuset.
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
    /// # Errors
    ///
    /// - [`BadObject(ThisProgram)`] if it is not possible to bind the current
    ///   process/thread to CPUs, generally speaking.
    /// - [`BadCpuSet`] if it is not possible to bind the current process/thread
    ///   to the requested CPU set, specifically.
    /// - [`BadFlags`] if flags [`PROCESS`] and [`THREAD`] were both specified.
    ///
    /// [`BadCpuSet`]: CpuBindingError::BadCpuSet
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ThisProgram)`]: CpuBindingError::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`STRICT`]: CpuBindingFlags::STRICT
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[doc(alias = "hwloc_set_cpubind")]
    pub fn bind_cpu(&self, set: &CpuSet, flags: CpuBindingFlags) -> Result<(), CpuBindingError> {
        self.bind_cpu_impl(
            set,
            flags,
            CpuBoundObject::ThisProgram,
            "hwloc_set_cpubind",
            |topology, cpuset, flags| unsafe { ffi::hwloc_set_cpubind(topology, cpuset, flags) },
        )
    }

    /// Get the current process or thread CPU binding
    ///
    /// Flag [`NO_MEMORY_BINDING`] should not be used with this function.
    ///
    /// Requires [`CpuBindingSupport::get_current_process()`] or
    /// [`CpuBindingSupport::get_current_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`BadObject(ThisProgram)`] if it is not possible to query the CPU
    ///   binding of the current process/thread.
    /// - [`BadFlags`] if flag [`NO_MEMORY_BINDING`] was specified or if
    ///   flags [`PROCESS`] and [`THREAD`] were both specified.
    ///
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ThisProgram)`]: CpuBindingError::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[doc(alias = "hwloc_get_cpubind")]
    pub fn cpu_binding(&self, flags: CpuBindingFlags) -> Result<CpuSet, CpuBindingError> {
        self.cpu_binding_impl(
            flags,
            CpuBoundObject::ThisProgram,
            "hwloc_get_cpubind",
            |topology, cpuset, flags| unsafe { ffi::hwloc_get_cpubind(topology, cpuset, flags) },
        )
    }

    /// Binds a process (identified by its `pid`) on given CPUs
    ///
    /// As a special case on Linux, if a tid (thread ID) is supplied instead of
    /// a pid (process ID) and flag [`THREAD`] is specified, the specified
    /// thread is bound. Otherwise, flag [`THREAD`] should not be used with this
    /// function.
    ///
    /// See [`Topology::bind_cpu()`] for more informations, except this
    /// requires [`CpuBindingSupport::set_process()`] or
    /// [`CpuBindingSupport::set_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`BadObject(ProcessOrThread)`] if it is not possible to bind the
    ///   target process/thread to CPUs, generally speaking.
    /// - [`BadCpuSet`] if it is not possible to bind the target process/thread
    ///   to the requested CPU set, specifically.
    /// - [`BadFlags`] if flag [`THREAD`] was specified on an operating system
    ///   other than Linux, or if flags [`PROCESS`] and [`THREAD`] were both
    ///   specified.
    ///
    /// [`BadCpuSet`]: CpuBindingError::BadCpuSet
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ProcessOrThread)`]: CpuBindingError::BadObject
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[doc(alias = "hwloc_set_proc_cpubind")]
    pub fn bind_process_cpu(
        &self,
        pid: ProcessId,
        set: &CpuSet,
        flags: CpuBindingFlags,
    ) -> Result<(), CpuBindingError> {
        self.bind_cpu_impl(
            set,
            flags,
            CpuBoundObject::ProcessOrThread,
            "hwloc_set_proc_cpubind",
            |topology, cpuset, flags| unsafe {
                ffi::hwloc_set_proc_cpubind(topology, pid, cpuset, flags)
            },
        )
    }

    /// Get the current physical binding of a process, identified by its `pid`
    ///
    /// As a special case on Linux, if a tid (thread ID) is supplied instead of
    /// a pid (process ID) and flag [`THREAD`] is specified, the binding of the
    /// specified thread is returned. Otherwise, flag [`THREAD`] should not be
    /// used with this function.
    ///
    /// Flag [`NO_MEMORY_BINDING`] should not be used with this function.
    ///
    /// Requires [`CpuBindingSupport::get_process()`] or
    /// [`CpuBindingSupport::get_thread()`] depending on flags.
    ///
    /// # Errors
    ///
    /// - [`BadObject(ProcessOrThread)`] if it is not possible to query the CPU
    ///   binding of the target process/thread.
    /// - [`BadFlags`] if flag [`NO_MEMORY_BINDING`] was specified, if flag
    ///   [`THREAD`] was specified on an operating system other than Linux, or
    ///   if flags [`PROCESS`] and [`THREAD`] were both specified.
    ///
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ProcessOrThread)`]: CpuBindingError::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[doc(alias = "hwloc_get_proc_cpubind")]
    pub fn process_cpu_binding(
        &self,
        pid: ProcessId,
        flags: CpuBindingFlags,
    ) -> Result<CpuSet, CpuBindingError> {
        self.cpu_binding_impl(
            flags,
            CpuBoundObject::ProcessOrThread,
            "hwloc_get_proc_cpubind",
            |topology, cpuset, flags| unsafe {
                ffi::hwloc_get_proc_cpubind(topology, pid, cpuset, flags)
            },
        )
    }

    /// Bind a thread, identified by its `tid`, on the given CPUs
    ///
    /// Flag [`PROCESS`] should not be used with this function.
    ///
    /// See [`Topology::bind_cpu()`] for more informations, except this always
    /// requires [`CpuBindingSupport::set_thread()`].
    ///
    /// # Errors
    ///
    /// - [`BadObject(Thread)`] if it is not possible to bind the target thread
    ///   to CPUs, generally speaking.
    /// - [`BadCpuSet`] if it is not possible to bind the target thread to the
    ///   requested CPU set, specifically.
    /// - [`BadFlags`] if flag [`PROCESS`] was specified.
    ///
    /// [`BadCpuSet`]: CpuBindingError::BadCpuSet
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(Thread)`]: CpuBindingError::BadObject
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    #[doc(alias = "hwloc_set_thread_cpubind")]
    pub fn bind_thread_cpu(
        &self,
        tid: ThreadId,
        set: &CpuSet,
        flags: CpuBindingFlags,
    ) -> Result<(), CpuBindingError> {
        self.bind_cpu_impl(
            set,
            flags,
            CpuBoundObject::Thread,
            "hwloc_set_thread_cpubind",
            |topology, cpuset, flags| unsafe {
                ffi::hwloc_set_thread_cpubind(topology, tid, cpuset, flags)
            },
        )
    }

    /// Get the current physical binding of thread `tid`
    ///
    /// Flags [`PROCESS`], [`STRICT`] and [`NO_MEMORY_BINDING`] should not be
    /// used with this function.
    ///
    /// Requires [`CpuBindingSupport::get_thread()`].
    ///
    /// # Errors
    ///
    /// - [`BadObject(Thread)`] if it is not possible to query the CPU
    ///   binding of the target thread.
    /// - [`BadFlags`] if at least one of the flags [`PROCESS`], [`STRICT`] and
    ///   [`NO_MEMORY_BINDING`] was specified.
    ///
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(Thread)`]: CpuBindingError::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`STRICT`]: CpuBindingFlags::STRICT
    #[doc(alias = "hwloc_get_thread_cpubind")]
    pub fn thread_cpu_binding(
        &self,
        tid: ThreadId,
        flags: CpuBindingFlags,
    ) -> Result<CpuSet, CpuBindingError> {
        self.cpu_binding_impl(
            flags,
            CpuBoundObject::Thread,
            "hwloc_get_thread_cpubind",
            |topology, cpuset, flags| unsafe {
                ffi::hwloc_get_thread_cpubind(topology, tid, cpuset, flags)
            },
        )
    }

    /// Get the last physical CPUs where the current process or thread ran
    ///
    /// The operating system may move some tasks from one processor
    /// to another at any time according to their binding,
    /// so this function may return something that is already
    /// outdated.
    ///
    /// Flag [`NO_MEMORY_BINDING`] should not be used with this function.
    ///
    /// Requires [`CpuBindingSupport::get_current_process_last_cpu_location()`]
    /// or [`CpuBindingSupport::get_current_thread_last_cpu_location()`]
    /// depending on flags.
    ///
    /// # Errors
    ///
    /// - [`BadObject(ThisProgram)`] if it is not possible to query the CPU
    ///   location of the current process/thread.
    /// - [`BadFlags`] if flag [`NO_MEMORY_BINDING`] was specified or if
    ///   flags [`PROCESS`] and [`THREAD`] were both specified.
    ///
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ThisProgram)`]: CpuBindingError::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[doc(alias = "hwloc_get_last_cpu_location")]
    pub fn last_cpu_location(&self, flags: CpuBindingFlags) -> Result<CpuSet, CpuBindingError> {
        self.last_cpu_location_impl(
            flags,
            CpuBoundObject::ThisProgram,
            "hwloc_get_last_cpu_location",
            |topology, cpuset, flags| unsafe {
                ffi::hwloc_get_last_cpu_location(topology, cpuset, flags)
            },
        )
    }

    /// Get the last physical CPU where a process ran.
    ///
    /// The operating system may move some tasks from one processor to another
    /// at any time according to their binding, so this function may return
    /// something that is already outdated.
    ///
    /// As a special case on Linux, if a tid (thread ID) is supplied instead of
    /// a pid (process ID) and flag [`THREAD`] is specified, the last cpu
    /// location of the specified thread is returned. Otherwise, flag [`THREAD`]
    /// should not be used with this function.
    ///
    /// Flag [`NO_MEMORY_BINDING`] should not be used with this function.
    ///
    /// Requires [`CpuBindingSupport::get_process_last_cpu_location()`].
    ///
    /// # Errors
    ///
    /// - [`BadObject(ProcessOrThread)`] if it is not possible to query the CPU
    ///   binding of the target process/thread.
    /// - [`BadFlags`] if flag [`NO_MEMORY_BINDING`] was specified, if flag
    ///   [`THREAD`] was specified on an operating system other than Linux, or
    ///   if flags [`PROCESS`] and [`THREAD`] were both specified.
    ///
    /// [`BadFlags`]: CpuBindingError::BadFlags
    /// [`BadObject(ProcessOrThread)`]: CpuBindingError::BadObject
    /// [`NO_MEMORY_BINDING`]: CpuBindingFlags::NO_MEMORY_BINDING
    /// [`PROCESS`]: CpuBindingFlags::PROCESS
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[doc(alias = "hwloc_get_proc_last_cpu_location")]
    pub fn last_process_cpu_location(
        &self,
        pid: ProcessId,
        flags: CpuBindingFlags,
    ) -> Result<CpuSet, CpuBindingError> {
        self.last_cpu_location_impl(
            flags,
            CpuBoundObject::ProcessOrThread,
            "hwloc_get_proc_last_cpu_location",
            |topology, cpuset, flags| unsafe {
                ffi::hwloc_get_proc_last_cpu_location(topology, pid, cpuset, flags)
            },
        )
    }

    /// Binding for set_cpubind style functions
    fn bind_cpu_impl(
        &self,
        set: &CpuSet,
        flags: CpuBindingFlags,
        target: CpuBoundObject,
        api: &'static str,
        ffi: impl FnOnce(*const RawTopology, *const RawBitmap, c_int) -> c_int,
    ) -> Result<(), CpuBindingError> {
        if !flags.is_valid(target, CpuBindingOperation::SetBinding) {
            return Err(CpuBindingError::BadFlags(flags.into()));
        }
        cpu::binding::call_hwloc(api, target, Some(set), || {
            ffi(self.as_ptr(), set.as_ptr(), flags.bits() as i32)
        })
    }

    /// Binding for get_cpubind style functions
    fn cpu_binding_impl(
        &self,
        flags: CpuBindingFlags,
        target: CpuBoundObject,
        api: &'static str,
        ffi: impl FnOnce(*const RawTopology, *mut RawBitmap, c_int) -> c_int,
    ) -> Result<CpuSet, CpuBindingError> {
        self.get_cpuset(flags, target, CpuBindingOperation::GetBinding, api, ffi)
    }

    /// Binding for get_last_cpu_location style functions
    fn last_cpu_location_impl(
        &self,
        flags: CpuBindingFlags,
        target: CpuBoundObject,
        api: &'static str,
        ffi: impl FnOnce(*const RawTopology, *mut RawBitmap, c_int) -> c_int,
    ) -> Result<CpuSet, CpuBindingError> {
        self.get_cpuset(
            flags,
            target,
            CpuBindingOperation::GetLastLocation,
            api,
            ffi,
        )
    }

    /// Binding for all functions that get CPU bindings
    fn get_cpuset(
        &self,
        flags: CpuBindingFlags,
        target: CpuBoundObject,
        operation: CpuBindingOperation,
        api: &'static str,
        ffi: impl FnOnce(*const RawTopology, *mut RawBitmap, c_int) -> c_int,
    ) -> Result<CpuSet, CpuBindingError> {
        if !flags.is_valid(target, operation) {
            return Err(CpuBindingError::BadFlags(flags.into()));
        }
        let mut cpuset = CpuSet::new();
        cpu::binding::call_hwloc(api, target, None, || {
            ffi(self.as_ptr(), cpuset.as_mut_ptr(), flags.bits() as i32)
        })
        .map(|()| cpuset)
    }
}

bitflags! {
    /// Process/Thread binding flags.
    ///
    /// These bit flags can be used to refine the binding policy. All flags can
    /// be OR'ed together with the exception of `ASSUME_SINGLE_THREAD`, `THREAD`
    /// and `PROCESS`, of which exactly one must be specified.
    ///
    /// The most portable binding targets are `ASSUME_SINGLE_THREAD`, `THREAD`
    /// and `PROCESS`, in this order.
    ///
    /// Not all systems support all kinds of binding,
    /// [`Topology::feature_support()`] may be used to query the
    /// actual CPU binding support in the currently used operating system.
    #[repr(C)]
    pub struct CpuBindingFlags: u32 {
        /// Assume that the target process is single threaded
        ///
        /// This lets hwloc pick between thread and process binding for
        /// increased portability.
        ///
        /// This is mutually exclusive with `PROCESS` and `THREAD`.
        const ASSUME_SINGLE_THREAD = 0;

        /// Bind current thread of target process
        ///
        /// This is the second most portable option where `ASSUME_SINGLE_THREAD`
        /// is inapplicable.
        ///
        /// This is mutually exclusive with `ASSUME_SINGLE_THREAD` and `PROCESS`.
        const THREAD  = (1<<1);

        /// Bind all threads of the target process
        ///
        /// This is mutually exclusive with `ASSUME_SINGLE_THREAD` and `THREAD`.
        const PROCESS = (1<<0);

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
        /// for an administrative reasons), and the binding function will fail
        /// in that case.
        ///
        /// When retrieving the binding of a process, this flag checks whether
        /// all its threads actually have the same binding. If the flag is not
        /// given, the binding of each thread will be accumulated.
        ///
        /// This flag is meaningless when retrieving the binding of a thread.
        const STRICT = (1<<2);

        /// Avoid any effect on memory binding
        ///
        /// On some operating systems, some CPU binding function would also bind
        /// the memory on the corresponding NUMA node. It is often not a problem
        /// for the application, but if it is, setting this flag will make hwloc
        /// avoid using OS functions that would also bind memory. This will
        /// however reduce the support of CPU bindings, i.e. potentially
        /// result in the binding function erroring out with
        /// [`CpuBindingError::Unsupported`].
        ///
        /// This flag is only meaningful when used with functions that set the
        /// CPU binding. It is ignored when used with functions that get CPU
        /// binding information.
        const NO_MEMORY_BINDING = (1<<3);
    }
}
//
// NOTE: No Default because user must consciously think about need for PROCESS
//
impl CpuBindingFlags {
    /// Truth that these flags are in a valid state
    pub(crate) fn is_valid(self, target: CpuBoundObject, operation: CpuBindingOperation) -> bool {
        if self.contains(Self::PROCESS | Self::THREAD) {
            return false;
        }
        if self.contains(Self::PROCESS) && target == CpuBoundObject::Thread {
            return false;
        }
        if self.contains(Self::THREAD)
            && target == CpuBoundObject::ProcessOrThread
            && cfg!(not(target_os = "linux"))
        {
            return false;
        }
        match operation {
            CpuBindingOperation::GetLastLocation => {
                !self.intersects(Self::STRICT | Self::NO_MEMORY_BINDING)
            }
            CpuBindingOperation::SetBinding => true,
            CpuBindingOperation::GetBinding => {
                if self.contains(Self::STRICT) && target == CpuBoundObject::Thread {
                    return false;
                }
                !self.contains(Self::NO_MEMORY_BINDING)
            }
        }
    }
}
//
/// Object that is being bound to particular CPUs
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum CpuBoundObject {
    /// A process, identified by its PID, or possibly a thread on Linux
    ProcessOrThread,

    /// A thread, identified by its TID
    Thread,

    /// The currently running program
    ThisProgram,
}
//
impl Display for CpuBoundObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let display = match self {
            Self::ProcessOrThread => "the target process/thread",
            Self::Thread => "the target thread",
            Self::ThisProgram => "the current process/thread",
        };
        write!(f, "{display}")
    }
}
//
/// Operation on that object's CPU binding
#[derive(Copy, Clone, Debug, Display, Eq, Hash, PartialEq)]
pub(crate) enum CpuBindingOperation {
    GetBinding,
    SetBinding,
    GetLastLocation,
}

/// Errors that can occur when binding processes or threads to CPUSets
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
    /// in the context of a particular binding function. Please cross-check the
    /// documentation of [`CpuBindingFlags`] and the function you were trying to
    /// call for more information.
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
    #[error("cannot bind {0} to {1}")]
    BadCpuSet(CpuBoundObject, CpuSet),

    /// Unexpected hwloc error
    ///
    /// The hwloc documentation isn't exhaustive about what errors can occur in
    /// general, and new error cases could potentially be added by new hwloc
    /// releases. If we can't provide a high-level error description, we will
    /// fall back to reporting the raw error from the hwloc API.
    #[error(transparent)]
    Unexpected(#[from] RawIntError),
}

/// Call an hwloc API that is about getting or setting CPU bindings, translate
/// known errors into higher-level `CpuBindingError`s.
///
/// Validating flags is left up to the caller, to avoid allocating result
/// objects when it can be proved upfront that the request is invalid.
pub(crate) fn call_hwloc(
    api: &'static str,
    object: CpuBoundObject,
    cpuset: Option<&CpuSet>,
    ffi: impl FnOnce() -> c_int,
) -> Result<(), CpuBindingError> {
    match errors::call_hwloc_int(api, ffi) {
        Ok(_positive) => Ok(()),
        Err(
            raw_err @ RawIntError::Errno {
                errno: Some(errno), ..
            },
        ) => match errno.0 {
            ENOSYS => Err(CpuBindingError::BadObject(object)),
            EXDEV => Err(CpuBindingError::BadCpuSet(
                object,
                cpuset
                    .expect("This error should only be observed on commands that bind to CPUs")
                    .clone(),
            )),
            _ => Err(CpuBindingError::Unexpected(raw_err)),
        },
        Err(raw_err) => Err(CpuBindingError::Unexpected(raw_err)),
    }
}
