//! Errors emitted from multiple points of the crate which do not belong elsewhere

use errno::Errno;
use std::{
    error::Error,
    ffi::{c_int, c_uint},
    fmt::Debug,
    ptr::NonNull,
};
use thiserror::Error;

/// Do something with errno checking
///
/// Call a user-provided callback, which tells if symptoms of a C-side error
/// were observed. If so, check for appearance of nonzero errno values and
/// report them.
///
/// When this function returns, errno is back to the state where it was before
/// the user callback was invoked.
fn check_errno<R>(callback: impl FnOnce() -> (R, bool)) -> (R, Option<Errno>) {
    let old_errno = errno::errno();
    errno::set_errno(Errno(0));

    let (result, should_check_errno) = callback();

    let mut new_errno = None;
    if should_check_errno {
        let errno = errno::errno();
        if errno != Errno(0) {
            new_errno = Some(errno);
        }
    }
    errno::set_errno(old_errno);

    (result, new_errno)
}

/// Raw error emitted by hwloc functions returning int
///
/// This is a last-resort error type that is emitted when the error handling
/// semantics of hwloc APIs are undocumented, and either they couldn't be easily
/// guessed from the source code or our guess became invalid as hwloc evolved.
///
/// It this happens, we assume the convention, followed by most hwloc API entry
/// points, that the function you are calling should return -1 and optionally
/// set errno when an error occurs.
///
/// Unknown positive return values are considered to indicate success, and
/// unknown negative return values are considered to indicate failure.
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum RawIntError {
    /// An hwloc API returned -1 and we observed this errno value, which may or
    /// may not have been set by hwloc.
    #[error("got -1 from {api} with errno {errno:?} (hopefully from hwloc)")]
    Errno {
        api: &'static str,
        errno: Option<Errno>,
    },

    /// An hwloc API returned an unexpected integer, and we observed the
    /// specified errno value which is unlikely to have been set by hwloc
    #[error("got {result} from {api} with errno {errno:?} (most likely NOT from hwloc)")]
    ReturnValue {
        api: &'static str,
        result: c_int,
        errno: Option<Errno>,
    },
}
//
/// Call an hwloc entry point that returns int and post-process its result
pub(crate) fn call_hwloc_int(
    api: &'static str,
    call: impl FnOnce() -> c_int,
) -> Result<c_uint, RawIntError> {
    let (result, errno) = check_errno(|| {
        let result = call();
        (result, result < 0)
    });
    match result {
        success if success >= 0 => Ok(c_uint::try_from(success).expect("Can't fail if >= 0")),
        -1 => Err(RawIntError::Errno { api, errno }),
        _ => Err(RawIntError::ReturnValue { api, result, errno }),
    }
}

/// Raw error emitted by hwloc functions returning pointers that should be
/// non-null
///
/// This is a last-resort error type that is emitted when the error handling
/// semantics of hwloc APIs are undocumented, and either they couldn't be easily
/// guessed from the source code or our guess became invalid as hwloc evolved.
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
#[error(
    "got unexpected null pointer from hwloc API {api} with errno {errno:?} (hopefully from hwloc)"
)]
pub struct RawNullError {
    pub api: &'static str,
    pub errno: Option<Errno>,
}
//
/// Call an hwloc entry point that returns a *const T that should not be null
/// and post-process its result
pub(crate) fn call_hwloc_ptr_mut<T>(
    api: &'static str,
    call: impl FnOnce() -> *mut T,
) -> Result<NonNull<T>, RawNullError> {
    let (result, errno) = check_errno(|| {
        let result = call();
        (result, result.is_null())
    });
    if let Some(ptr) = NonNull::new(result) {
        Ok(ptr)
    } else {
        Err(RawNullError { api, errno })
    }
}
//
/// Call an hwloc entry point that returns a *mut T that should not be null and
/// post-process its result
pub(crate) fn call_hwloc_ptr<T>(
    api: &'static str,
    call: impl FnOnce() -> *const T,
) -> Result<NonNull<T>, RawNullError> {
    call_hwloc_ptr_mut(api, || call() as *mut T)
}

/// Requested string contains the NUL char
///
/// hwloc, like most C APIs, cannot handle strings with inner NULs.
#[derive(Copy, Clone, Debug, Default, Error, Eq, Hash, PartialEq)]
#[error("string cannot be used by hwloc, it contains the NUL char")]
pub struct NulError;

/// An invalid parameter was passed to a function
#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
pub enum ParameterError<RustError: Error> {
    /// Rust-side validation failed
    #[error(transparent)]
    RustSide(#[from] RustError),

    /// Hwloc-side validation failed
    #[error("hwloc-side parameter validation failed")]
    HwlocSide,
}

/// An invalid set of flags was passed to a function
///
/// Many hwloc APIs only accept particular combinations of flags. You may want
/// to cross-check the documentation of the flags type and that of the function
/// you were trying to call for more information.
#[derive(Copy, Clone, Debug, Default, Error, Eq, Hash, PartialEq)]
#[error("flags {0:?} are not valid for this operation")]
pub struct FlagsError<Flags: Debug>(Flags);
//
impl<Flags: Debug> From<Flags> for FlagsError<Flags> {
    fn from(value: Flags) -> Self {
        Self(value)
    }
}

/// Error returned when the platform does not support the requested operation
///
/// This can be a general statement, or it may be contextual to a particular set
/// of parameters (e.g. you cannot query a specific ProcessID because you don't
/// have permission to do so).
#[derive(Copy, Clone, Debug, Default, Eq, Error, PartialEq)]
#[error("platform does not support this operation")]
pub struct UnsupportedError;
