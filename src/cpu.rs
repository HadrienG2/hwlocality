//! CPU binding

// Main docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpubinding.html

use bitflags::bitflags;
use errno::{errno, Errno};
use libc::{ENOSYS, EXDEV};
use thiserror::Error;

bitflags! {
    /// Process/Thread binding flags.
    ///
    /// These bit flags can be used to refine the binding policy.
    ///
    /// The default (`PROCESS`) is to bind the current process, assumed to be
    /// single-threaded, in a non-strict way.  This is the most portable
    /// way to bind as all operating systems usually provide it.
    ///
    /// For multi-threaded processes, `THREAD` should be used instead as the
    /// most portable option.
    ///
    /// **Note:** Not all systems support all kinds of binding.
    #[repr(C)]
    pub struct CpuBindingFlags: u32 {
        /// Bind all threads of the current (possibly) multithreaded process
        const PROCESS = (1<<0);

        /// Bind current thread of current process
        const THREAD  = (1<<1);

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

impl Default for CpuBindingFlags {
    fn default() -> Self {
        Self::empty()
    }
}

/// Errors that can occur when binding processes or threads to CPUSets
#[derive(Copy, Clone, Debug, Error, Eq, PartialEq)]
pub enum CpuBindingError {
    /// Action is not supported
    ///
    /// This error might not be reported if [`CpuBindingFlags::STRICT`] is not
    /// set. Instead, the implementation is allowed to try to use a slightly
    /// different operation (with side-effects, smaller binding set, etc.) when
    /// the requested operation is not exactly supported.
    #[error("action is not supported")]
    Unsupported,

    /// Binding cannot be enforced
    ///
    /// This error might not be reported if [`CpuBindingFlags::STRICT`] is not
    /// set. Instead, the implementation is allowed to try to use a slightly
    /// different operation (with side-effects, smaller binding set, etc.) when
    /// the requested operation is not exactly supported.
    #[error("binding cannot be enforced")]
    Ineffective,

    /// Unexpected errno value
    #[error("unexpected errno value {0}")]
    UnexpectedErrno(Errno),

    /// Unexpected binding function result
    #[error("unexpected binding function result {0} with errno {1}")]
    UnexpectedResult(i32, Errno),
}

/// CPU binding result builder
pub(crate) fn result<T>(result: i32, ok: T) -> Result<T, CpuBindingError> {
    match result {
        x if x >= 0 => Ok(ok),
        -1 => Err({
            let errno = errno();
            match errno.0 {
                ENOSYS => CpuBindingError::Unsupported,
                EXDEV => CpuBindingError::Ineffective,
                _ => CpuBindingError::UnexpectedErrno(errno),
            }
        }),
        negative => Err(CpuBindingError::UnexpectedResult(negative, errno())),
    }
}
