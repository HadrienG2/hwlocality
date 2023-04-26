//! Shared error handling

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

/// Raw error emitted by hwloc functions that follow the usual convention
///
/// Hwloc APIs almost always error out by returning -1 if they return an
/// integer, or a null pointer if they return a pointer.
///
/// They may additionally change the value of errno to report additional detail
/// about what happened.
///
/// If no additional detail is provided by the hwloc documentation, we will
/// assume this error handling convention and report errors using the present
/// struct. Where possible errno values are clarified in the hwloc docs, we will
/// assume they are the only errors that can occur, translate them into a
/// higher-level Rust errors and panic if another errno value is observed.
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
#[error("hwloc API {api} errored out with errno {errno:?}")]
pub struct RawHwlocError {
    /// Hwloc entry point that failed
    pub api: &'static str,

    /// Observed errno value, if non-zero
    pub errno: Option<Errno>,
}

/// Call an hwloc entry point that returns a `*mut T` that should not be null
pub(crate) fn call_hwloc_ptr_mut<T>(
    api: &'static str,
    call: impl FnOnce() -> *mut T,
) -> Result<NonNull<T>, RawHwlocError> {
    let (result, errno) = check_errno(|| {
        let result = call();
        (result, result.is_null())
    });
    if let Some(ptr) = NonNull::new(result) {
        Ok(ptr)
    } else {
        Err(RawHwlocError { api, errno })
    }
}
//
/// Call an hwloc entry point that returns a `*const T` that should not be null
pub(crate) fn call_hwloc_ptr<T>(
    api: &'static str,
    call: impl FnOnce() -> *const T,
) -> Result<NonNull<T>, RawHwlocError> {
    call_hwloc_ptr_mut(api, || call().cast_mut())
}
//
/// Call an hwloc entry point that returns an `int` where -1 signals failure
///
/// This behavior is followed by almost every hwloc API, though unfortunately
/// there are a couple of exception.
pub(crate) fn call_hwloc_int_normal(
    api: &'static str,
    call: impl FnOnce() -> c_int,
) -> Result<c_uint, RawHwlocError> {
    match call_hwloc_int_raw(api, call) {
        Ok(positive) => Ok(positive),
        Err(RawNegIntError {
            api,
            result: -1,
            errno,
        }) => Err(RawHwlocError { api, errno }),
        Err(other_err) => unreachable!("{other_err}"),
    }
}

/// Raw error emitted by hwloc functions that returns a negative int on failure
///
/// A few hwloc functions (most prominently topology diffing) return negative
/// integer values other than -1 when erroring out. This error type is an
/// extension of [`RawHwlocError`] that allows you to catch and process those
/// negative return values.
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
#[error("hwloc API {api} errored out with result {result} and errno {errno:?}")]
pub(crate) struct RawNegIntError {
    /// Hwloc entry point that failed
    pub api: &'static str,

    /// Return value (may not be positive)
    pub result: c_int,

    /// Observed errno value, if non-zero
    pub errno: Option<Errno>,
}
//
/// Call an hwloc entry point that returns int and post-process its result
pub(crate) fn call_hwloc_int_raw(
    api: &'static str,
    call: impl FnOnce() -> c_int,
) -> Result<c_uint, RawNegIntError> {
    let (result, errno) = check_errno(|| {
        let result = call();
        (result, result < 0)
    });
    match result {
        success if success >= 0 => Ok(c_uint::try_from(success).expect("Can't fail if >= 0")),
        result => Err(RawNegIntError { api, result, errno }),
    }
}

/// A function errored out either on the Rust or hwloc side
///
/// This is typically used for functions which have known failure modes on the
/// Rust side (e.g. takes a string input that must not contain NUL chars), but
/// whose hwloc-side error reporting policy is undocumented.
///
/// If the hwloc documentation contains a list of failure modes, we normally
/// assume that list to be exhaustive and return a pure Rust error type,
/// panicking if another hwloc error is observed.
#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
pub enum HybridError<RustError: Error> {
    /// An error was caught on the Rust side
    #[error(transparent)]
    Rust(#[from] RustError),

    /// An error was caught on the hwloc side
    #[error(transparent)]
    // Unfortunately, this type cannot implement both #[from] RustError and
    // #[from] RawHwlocError as rustc rightly complains that nothing prevents
    // RustError to be RawHwlocError at the type system level.
    //
    // I choose to implement for RustError because that type has unbounded
    // complexity and thus benefits the most from it.
    Hwloc(RawHwlocError),
}

/// Requested string contains the NUL char
///
/// hwloc, like most C APIs, cannot handle strings with inner NULs.
#[derive(Copy, Clone, Debug, Default, Error, Eq, Hash, PartialEq)]
#[error("string cannot be used by hwloc, it contains the NUL char")]
pub struct NulError;

/// A method was passed an invalid parameter
#[derive(Copy, Clone, Debug, Default, Eq, Error, Hash, PartialEq)]
#[error("parameter {0:?} is not valid for this operation")]
pub struct ParameterError<Parameter: Debug>(Parameter);
//
impl<Parameter: Debug> From<Parameter> for ParameterError<Parameter> {
    fn from(value: Parameter) -> Self {
        Self(value)
    }
}

/// An invalid set of flags was passed to a function
///
/// Many hwloc APIs only accept particular combinations of flags. You may want
/// to cross-check the documentation of the flags type and that of the function
/// you were trying to call for more information.
pub type FlagsError<Flags> = ParameterError<Flags>;

/// Error returned when the platform does not support the requested operation
///
/// This can be a general statement, or it may be contextual to a particular set
/// of parameters (e.g. you cannot query a specific ProcessID because you don't
/// have permission to do so).
#[derive(Copy, Clone, Debug, Default, Eq, Error, PartialEq)]
#[error("platform does not support this operation")]
pub struct UnsupportedError;
