//! CPU binding

// Main docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpubinding.html

use bitflags::bitflags;
use derive_more::Display;
use libc::{ENOSYS, EXDEV};
use std::{ffi::c_int, fmt::Display};
use thiserror::Error;

use crate::{
    bitmaps::CpuSet,
    errors::{self, FlagsError, RawIntError},
};

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
