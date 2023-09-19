//! Generic error handling primitives
//!
//! While we do not shy away from using context-specific error types that
//! provide higher-quality error messages, for some common patterns we do emit
//! generic error types, which are implemented in this module.
//
// At the implementation level, this is also the place where all the low-level
// handling of hwloc errors is implemented.

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
#[error("hwloc API {api} failed with errno {errno:?}")]
pub struct RawHwlocError {
    /// Hwloc entry point that failed
    pub api: &'static str,

    /// Observed errno value, if errno was set
    pub errno: Option<Errno>,
}

/// Call an hwloc entry point that returns a `*mut T` that should not be null
///
/// # Errors
///
/// See the documentation of `call` to know when the entry point can error out
pub(crate) fn call_hwloc_ptr_mut<T>(
    api: &'static str,
    call: impl FnOnce() -> *mut T,
) -> Result<NonNull<T>, RawHwlocError> {
    let (result, errno) = check_errno(|| {
        let result = call();
        (result, result.is_null())
    });
    NonNull::new(result).ok_or(RawHwlocError { api, errno })
}

/// Call an hwloc entry point that returns a `*const T` that should not be null
///
/// # Errors
///
/// See the documentation of `call` to know when the entry point can error out
pub(crate) fn call_hwloc_ptr<T>(
    api: &'static str,
    call: impl FnOnce() -> *const T,
) -> Result<NonNull<T>, RawHwlocError> {
    call_hwloc_ptr_mut(api, || call().cast_mut())
}

/// Call an hwloc entry point that returns an `int` where -1 signals failure
///
/// This behavior is followed by almost every hwloc API, though unfortunately
/// there are a couple of exception.
///
/// # Errors
///
/// See the documentation of `call` to know when the entry point can error out
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
        Err(other_err) => unreachable!("Unexpected hwloc error: {other_err}"),
    }
}

/// Call an hwloc entry point that returns an `int` with standard boolean values
/// (1 if true, 0 if false)
pub(crate) fn call_hwloc_bool(
    api: &'static str,
    call: impl FnOnce() -> c_int,
) -> Result<bool, RawHwlocError> {
    match call_hwloc_int_normal(api, call) {
        Ok(1) => Ok(true),
        Ok(0) => Ok(false),
        Ok(other) => unreachable!("Got unexpected boolean value {other} from {api}"),
        Err(e) => Err(e),
    }
}

/// Raw error emitted by hwloc functions that returns a negative int on failure
///
/// A few hwloc functions (most prominently topology diffing) return negative
/// integer values other than -1 when erroring out. This error type is an
/// extension of [`RawHwlocError`] that allows you to catch and process those
/// negative return values.
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
#[error("hwloc API {api} failed with result {result} and errno {errno:?}")]
pub(crate) struct RawNegIntError {
    /// Hwloc entry point that failed
    pub(crate) api: &'static str,

    /// Return value (may not be positive)
    pub(crate) result: c_int,

    /// Observed errno value, if errno was set
    pub(crate) errno: Option<Errno>,
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
    c_uint::try_from(result).map_err(|_| RawNegIntError { api, result, errno })
}

/// A function errored out either on the Rust or hwloc side
///
/// This is typically used for functions which have known failure modes on the
/// Rust side (e.g. takes a string input that must not contain NUL chars), but
/// whose hwloc-side error reporting policy is undocumented or only partially
/// documented.
///
/// If the hwloc documentation contains an exhaustive list of failure modes, we
/// trust it and return a pure Rust error type, panicking if another hwloc
/// error is observed.
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
    // I choose to implement From for RustError because that type has unbounded
    // complexity and thus benefits the most from it.
    Hwloc(RawHwlocError),
}

/// Requested string contains the NUL char
///
/// hwloc, like most C APIs, cannot handle strings with inner NULs, so you
/// should not pass a string containing such characters as a parameter to an
/// hwloc API.
///
/// This generic error type is only used when the only error that can occur is
/// that the input string is invalid. Otherwise, a more complex error type that
/// accounts for the possibility of NUL errors among others will be emitted.
#[derive(Copy, Clone, Debug, Default, Eq, Error, Hash, PartialEq)]
#[error("string cannot be used by hwloc, it contains the NUL char")]
pub struct NulError;

/// A method was passed an invalid parameter
///
/// This generic error type is only used when there is only a single way a
/// function parameter can be invalid, and the fact that it is invalid does
/// not depend on the value of another parameter. Otherwise, a more descriptive
/// dedicated error type will be used.
#[derive(Copy, Clone, Debug, Default, Eq, Error, Hash, PartialEq)]
#[error("parameter {0:?} is not valid for this operation")]
pub struct ParameterError<Parameter: Debug>(pub Parameter);
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
///
/// This generic error type is only used when the validity of flags does not
/// depend on the value of other function parameters. Otherwise, a more
/// descriptive dedicated error type will be used.
pub type FlagsError<Flags> = ParameterError<Flags>;

/// A [`Topology`] method was passed in a [`TopologyObject`] that does not
/// belong to said topology
///
/// Given that this is an obscure usage error that has tiny odds of happening in
/// the real world, it is not systematically reported as an error. Methods
/// whose semantics boil down to "return entity that matches this query if it
/// exists and `None` otherwise" may instead return `None` in this scenario.
#[derive(Copy, Clone, Debug, Default, Eq, Error, Hash, PartialEq)]
#[error("topology method was passed in a foreign topology object")]
pub struct ForeignObject;
