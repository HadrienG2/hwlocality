//! Generic error handling primitives
//!
//! While we do not shy away from using context-specific error types that
//! provide higher-quality error messages, for some common patterns we do emit
//! generic error types, which are implemented in this module.
//
// --- Implementation details ---
//
// At the implementation level, this is also the place where all the low-level
// handling of hwloc errors is implemented.

use crate::object::{TopologyObject, TopologyObjectID};
#[cfg(doc)]
use crate::topology::Topology;
use derive_more::From;
use errno::Errno;
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::{
    error::Error,
    ffi::{c_int, c_uint},
    fmt::Debug,
    ptr::NonNull,
};
use thiserror::Error;

/// Set errno to an initial value, eventually bring it back to normal
struct ErrnoGuard(Errno);
//
impl ErrnoGuard {
    /// Set errno to a new value, schedule a reset when this is dropped
    fn new(errno: Errno) -> Self {
        let old_errno = errno::errno();
        errno::set_errno(errno);
        Self(old_errno)
    }
}
//
impl Drop for ErrnoGuard {
    fn drop(&mut self) {
        errno::set_errno(self.0);
    }
}

/// Do something with errno checking
///
/// Call a user-provided callback, which tells if symptoms of a C-side error
/// were observed. If so, check for appearance of nonzero errno values and
/// report them.
///
/// When this function returns, errno is back to the state where it was before
/// the user callback was invoked.
fn check_errno<R: Copy + Ord>(
    callback: impl FnOnce() -> R,
    lowest_good_value: R,
) -> (R, Option<Errno>) {
    let _guard = ErrnoGuard::new(Errno(0));
    let result = callback();
    /// Outlined to reduce code bloat
    fn interpret_errno(should_check_errno: bool) -> Option<Errno> {
        should_check_errno
            .then(|| {
                let errno = errno::errno();
                (errno != Errno(0)).then_some(errno)
            })
            .flatten()
    }
    (result, interpret_errno(result < lowest_good_value))
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
#[error("{api} failed with errno {errno:?}")]
pub struct RawHwlocError {
    /// Hwloc entry point that failed
    pub api: &'static str,

    /// Observed errno value, if errno was set
    #[cfg_attr(windows, doc = "")]
    #[cfg_attr(windows, doc = "Note that even for entry points where hwloc is")]
    #[cfg_attr(windows, doc = "documented to set errno, this member may be")]
    #[cfg_attr(windows, doc = "`None` on Windows. This happens because ")]
    #[cfg_attr(windows, doc = "Windows has multiple implementations of its")]
    #[cfg_attr(windows, doc = "standard C library, called C RunTimes (CRTs),")]
    #[cfg_attr(windows, doc = "and getting your application to be link")]
    #[cfg_attr(windows, doc = "against the same CRT as your hwloc DLL is")]
    #[cfg_attr(windows, doc = "basically a matter of fragile guesswork...")]
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
    let (result, errno) = check_errno(call, 1 as *mut T);
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

/// Call an hwloc entry point that returns an `int` where -1 signals failure and
/// other negative values are not expected
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
    /// Outlined to reduce code bloat
    fn check_raw_result(
        raw_result: Result<c_int, RawNegIntError>,
    ) -> Result<c_uint, RawHwlocError> {
        match raw_result {
            Ok(positive) => {
                Ok(c_uint::try_from(positive).expect("Cannot happen due to 0 threshold above"))
            }
            Err(RawNegIntError {
                api,
                result: -1,
                errno,
            }) => Err(RawHwlocError { api, errno }),
            Err(other_err) => unreachable!("Unexpected hwloc output: {other_err}"),
        }
    }
    check_raw_result(call_hwloc_int_raw(api, call, 0))
}

/// Call an hwloc entry point that returns an `int` with standard boolean values
/// (1 if true, 0 if false)
pub(crate) fn call_hwloc_bool(
    api: &'static str,
    call: impl FnOnce() -> c_int,
) -> Result<bool, RawHwlocError> {
    /// Outlined to reduce code bloat
    fn check_raw_result(
        api: &'static str,
        raw_result: Result<c_uint, RawHwlocError>,
    ) -> Result<bool, RawHwlocError> {
        match raw_result {
            Ok(1) => Ok(true),
            Ok(0) => Ok(false),
            Ok(other) => unreachable!("Got unexpected boolean value {other} from {api}"),
            Err(e) => Err(e),
        }
    }
    check_raw_result(api, call_hwloc_int_normal(api, call))
}

/// Raw error emitted by hwloc functions that returns a negative int on failure
///
/// A few hwloc functions (most prominently bitmap queries and topology diffing)
/// return negative integer values other than -1 when erroring out. This error
/// type is an extension of [`RawHwlocError`] that allows you to catch and
/// process those negative return values.
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
#[error("{api} failed with result {result} and errno {errno:?}")]
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
///
/// Result values lower than `lowest_good_value` are treated as errors
pub(crate) fn call_hwloc_int_raw(
    api: &'static str,
    call: impl FnOnce() -> c_int,
    lowest_good_value: c_int,
) -> Result<c_int, RawNegIntError> {
    /// Outlined to reduce code bloat
    fn check_raw_result(
        api: &'static str,
        (result, errno): (c_int, Option<Errno>),
        lowest_good_value: c_int,
    ) -> Result<c_int, RawNegIntError> {
        (result >= lowest_good_value)
            .then_some(result)
            .ok_or(RawNegIntError { api, result, errno })
    }
    check_raw_result(api, check_errno(call, lowest_good_value), lowest_good_value)
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
#[derive(Copy, Clone, Debug, Eq, Error, Hash, PartialEq)]
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
//
impl<RustError: Error> HybridError<RustError> {
    /// Assume that all expected Rust-side error sources have been handled and
    /// panic otherwise, but still allow unexpected hwloc errors
    pub fn expect_only_hwloc(self, msg: &str) -> RawHwlocError {
        match self {
            Self::Hwloc(e) => e,
            Self::Rust(e) => panic!("{msg} (got unexpected Rust error {e}"),
        }
    }
}

/// A string meant for hwloc consumption contained the NUL char
///
/// hwloc, like most C APIs, cannot handle strings with inner NULs, so you
/// should not pass a string containing such characters as a parameter to an
/// hwloc API.
///
/// This generic error type is only used when the only error that can occur is
/// that the input string is invalid. Otherwise, a more complex error type that
/// accounts for the possibility of NUL errors among others will be emitted.
#[derive(Copy, Clone, Debug, Default, Eq, Error, Hash, Ord, PartialEq, PartialOrd)]
#[error("can't pass a string with NUL chars to hwloc")]
pub struct NulError;

/// A method was passed an invalid parameter
///
/// This generic error type is only used when there is only a single way a
/// function parameter can be invalid, and the fact that it is invalid does
/// not depend on the value of another parameter. Otherwise, a more descriptive
/// dedicated error type will be used.
#[derive(Copy, Clone, Debug, Default, Eq, Error, From, Hash, Ord, PartialEq, PartialOrd)]
#[error("parameter {0:?} isn't valid for this operation")]
pub struct ParameterError<Parameter: Debug>(pub Parameter);

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
//
// --- Implementation notes ---
//
// Not implementing Copy or exposing the inner data at this point because I want
// to keep options open for switching to another way to describe objects (Debug
// string, etc) in the future.
#[allow(missing_copy_implementations)]
#[derive(Clone, Debug, Eq, Error, Hash, PartialEq)]
#[error("object #{0} doesn't belong to this topology")]
pub struct ForeignObjectError(TopologyObjectID);
//
impl<'topology> From<&'topology TopologyObject> for ForeignObjectError {
    fn from(object: &'topology TopologyObject) -> Self {
        Self(object.global_persistent_index())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::assert_panics;
    use proptest::prelude::*;
    #[allow(unused)]
    use similar_asserts::assert_eq;
    use static_assertions::{assert_impl_all, assert_not_impl_any, assert_type_eq_all};
    use std::{
        fmt::{self, Binary, LowerExp, LowerHex, Octal, Pointer, UpperExp, UpperHex},
        hash::Hash,
        io::{self, Read},
        num::{NonZeroU32, NonZeroUsize},
        ops::Deref,
        panic::UnwindSafe,
        ptr,
    };

    // Check that public types in this module keep implementing all expected
    // traits, in the interest of detecting future semver-breaking changes
    assert_type_eq_all!(FlagsError<()>, ParameterError<()>);
    assert_impl_all!(ForeignObjectError:
        Clone, Error, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(ForeignObjectError:
        Binary, Copy, Default, Deref, Drop, IntoIterator, LowerExp, LowerHex,
        Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write,
        io::Write
    );
    assert_impl_all!(HybridError<NulError>:
        Copy, Error, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(HybridError<NulError>:
        Binary, Default, Deref, Drop, IntoIterator, LowerExp, LowerHex, Octal,
        PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write, io::Write
    );
    assert_impl_all!(NulError:
        Copy, Default, Error, Hash, Ord, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(NulError:
        Binary, Deref, Drop, IntoIterator, LowerExp, LowerHex, Octal, Pointer,
        Read, UpperExp, UpperHex, fmt::Write, io::Write
    );
    assert_impl_all!(ParameterError<()>:
        Copy, Default, Error, Hash, Ord, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(ParameterError<()>:
        Binary, Deref, Drop, IntoIterator, LowerExp, LowerHex, Octal, Pointer,
        Read, UpperExp, UpperHex, fmt::Write, io::Write
    );
    assert_impl_all!(RawHwlocError:
        Copy, Error, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(RawHwlocError:
        Binary, Default, Deref, Drop, IntoIterator, LowerExp, LowerHex, Octal,
        PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write, io::Write
    );

    proptest! {
        #[test]
        fn check_errno_normal(
            output: i128,
            lowest_good: i128,
            start_errno: i32,
            new_errno: NonZeroU32,
        ) {
            // Test boilerplate
            let start_errno = Errno(start_errno.wrapping_abs());
            let new_errno = Errno(i32::from_ne_bytes(new_errno.get().to_ne_bytes()).wrapping_abs());
            let _errno_guard = ErrnoGuard::new(start_errno);

            // Errno is only checked on failure
            let expected_errno = (output < lowest_good).then_some(new_errno);
            prop_assert_eq!(
                super::check_errno(
                    || {
                        errno::set_errno(new_errno);
                        output
                    },
                    lowest_good
                ),
                (output, expected_errno)
            );
            prop_assert_eq!(errno::errno(), start_errno);
        }

        #[test]
        fn check_errno_in_vain(output: i128, lowest_good: i128, start_errno: i32) {
            // Not setting errno on failure is handled properly
            let start_errno = Errno(start_errno.wrapping_abs());
            let _errno_guard = ErrnoGuard::new(start_errno);
            prop_assert_eq!(super::check_errno(|| output, lowest_good), (output, None));
            prop_assert_eq!(errno::errno(), start_errno);
        }

        #[test]
        fn ptr_success(nonnull: NonZeroUsize, start_errno: i32, new_errno: NonZeroU32) {
            // Test boilerplate
            let start_errno = Errno(start_errno.wrapping_abs());
            let new_errno = Errno(i32::from_ne_bytes(new_errno.get().to_ne_bytes()).wrapping_abs());
            let _errno_guard = ErrnoGuard::new(start_errno);
            let api = "foo";
            let nonnull_ptr = NonNull::new(nonnull.get() as *mut u8).unwrap();

            // Non-null output means success
            prop_assert_eq!(
                super::call_hwloc_ptr(api, || {
                    errno::set_errno(new_errno);
                    nonnull_ptr.as_ptr()
                }),
                Ok(nonnull_ptr)
            );
            prop_assert_eq!(errno::errno(), start_errno);
            prop_assert_eq!(
                super::call_hwloc_ptr_mut(api, || {
                    errno::set_errno(new_errno);
                    nonnull_ptr.as_ptr()
                }),
                Ok(nonnull_ptr)
            );
            prop_assert_eq!(errno::errno(), start_errno);
        }

        #[test]
        fn ptr_fail_with_errno(start_errno: i32, new_errno: NonZeroU32) {
            // Test boilerplate
            let start_errno = Errno(start_errno.wrapping_abs());
            let new_errno = Errno(i32::from_ne_bytes(new_errno.get().to_ne_bytes()).wrapping_abs());
            let _errno_guard = ErrnoGuard::new(start_errno);
            let api = "bar";

            // Null output means failure and will lead to an errno check
            let null_ptr = ptr::null_mut::<Vec<f32>>();
            prop_assert_eq!(
                super::call_hwloc_ptr(api, || {
                    errno::set_errno(new_errno);
                    null_ptr
                }),
                Err(RawHwlocError {
                    api,
                    errno: Some(new_errno)
                })
            );
            prop_assert_eq!(errno::errno(), start_errno);
            prop_assert_eq!(
                super::call_hwloc_ptr_mut(api, || {
                    errno::set_errno(new_errno);
                    null_ptr
                }),
                Err(RawHwlocError {
                    api,
                    errno: Some(new_errno)
                })
            );
            prop_assert_eq!(errno::errno(), start_errno);
        }

        #[test]
        fn ptr_fail_wo_errno(start_errno: i32) {
            // Test boilerplate
            let start_errno = Errno(start_errno.wrapping_abs());
            let _errno_guard = ErrnoGuard::new(start_errno);
            let api = "baz";
            let null_ptr = ptr::null_mut::<String>();

            // Not setting errno on failure is handled properly
            prop_assert_eq!(
                super::call_hwloc_ptr(api, || { null_ptr }),
                Err(RawHwlocError { api, errno: None })
            );
            prop_assert_eq!(errno::errno(), start_errno);
            prop_assert_eq!(
                super::call_hwloc_ptr_mut(api, || { null_ptr }),
                Err(RawHwlocError { api, errno: None })
            );
            prop_assert_eq!(errno::errno(), start_errno);
        }

        #[test]
        fn int_normal_general(output: i32, start_errno: i32, new_errno: NonZeroU32) {
            // Test boilerplate
            let start_errno = Errno(start_errno.wrapping_abs());
            let new_errno = Errno(i32::from_ne_bytes(new_errno.get().to_ne_bytes()).wrapping_abs());
            let _errno_guard = ErrnoGuard::new(start_errno);
            let api = "abc";

            // Prepare to call the function
            let call = || {
                let res = super::call_hwloc_int_normal(api, || {
                    errno::set_errno(new_errno);
                    output
                });
                prop_assert_eq!(errno::errno(), start_errno);
                Ok(res)
            };

            // Interpret results
            match output {
                bad if bad < -1 => assert_panics(call)?,
                -1 => prop_assert_eq!(
                    call()?,
                    Err(RawHwlocError {
                        api,
                        errno: Some(new_errno)
                    })
                ),
                positive => prop_assert_eq!(call()?, Ok(u32::try_from(positive).unwrap())),
            }
        }

        #[test]
        fn int_normal_err_with_errno(start_errno: i32, new_errno: NonZeroU32) {
            // Test boilerplate
            let start_errno = Errno(start_errno.wrapping_abs());
            let new_errno = Errno(i32::from_ne_bytes(new_errno.get().to_ne_bytes()).wrapping_abs());
            let _errno_guard = ErrnoGuard::new(start_errno);
            let api = "def";

            // Returning -1 means failure and will lead to an errno check
            prop_assert_eq!(
                super::call_hwloc_int_normal(api, || {
                    errno::set_errno(new_errno);
                    -1
                }),
                Err(RawHwlocError {
                    api,
                    errno: Some(new_errno)
                })
            );
            prop_assert_eq!(errno::errno(), start_errno);
        }

        #[test]
        fn int_normal_err_wo_errno(start_errno: i32) {
            // Test boilerplate
            let start_errno = Errno(start_errno.wrapping_abs());
            let _errno_guard = ErrnoGuard::new(start_errno);
            let api = "ghi";

            // Not setting errno on failure is handled properly
            prop_assert_eq!(
                super::call_hwloc_int_normal(api, || -1),
                Err(RawHwlocError { api, errno: None })
            );
            prop_assert_eq!(errno::errno(), start_errno);
        }

        #[test]
        fn int_raw_with_errno(
            output: i32,
            lowest_good_value: i32,
            start_errno: i32,
            new_errno: NonZeroU32,
        ) {
            // Test boilerplate
            let start_errno = Errno(start_errno.wrapping_abs());
            let new_errno = Errno(i32::from_ne_bytes(new_errno.get().to_ne_bytes()).wrapping_abs());
            let _errno_guard = ErrnoGuard::new(start_errno);
            let api = "jkl";

            // Run the function
            let result = super::call_hwloc_int_raw(
                api,
                || {
                    errno::set_errno(new_errno);
                    output
                },
                lowest_good_value,
            );
            prop_assert_eq!(errno::errno(), start_errno);

            // Interpret outcome
            if output >= lowest_good_value {
                prop_assert_eq!(result, Ok(output));
            } else {
                prop_assert_eq!(
                    result,
                    Err(RawNegIntError {
                        api,
                        result: output,
                        errno: Some(new_errno),
                    })
                );
            }
        }

        #[test]
        fn int_raw_wo_errno(output: i32, lowest_good_value: i32, start_errno: i32) {
            // Test boilerplate
            let start_errno = Errno(start_errno.wrapping_abs());
            let _errno_guard = ErrnoGuard::new(start_errno);
            let api = "opq";

            // Run the function
            let result = super::call_hwloc_int_raw(api, || output, lowest_good_value);
            prop_assert_eq!(errno::errno(), start_errno);

            // Interpret outcome
            if output >= lowest_good_value {
                prop_assert_eq!(result, Ok(output));
            } else {
                prop_assert_eq!(
                    result,
                    Err(RawNegIntError {
                        api,
                        result: output,
                        errno: None,
                    })
                );
            }
        }

        #[test]
        fn bool_general(output: i32, start_errno: i32, new_errno: NonZeroU32) {
            // Test boilerplate
            let start_errno = Errno(start_errno.wrapping_abs());
            let new_errno = Errno(i32::from_ne_bytes(new_errno.get().to_ne_bytes()).wrapping_abs());
            let _errno_guard = ErrnoGuard::new(start_errno);
            let api = "rst";

            // Prepare to call the function
            let call = || {
                let res = super::call_hwloc_bool(api, || {
                    errno::set_errno(new_errno);
                    output
                });
                prop_assert_eq!(errno::errno(), start_errno);
                Ok(res)
            };

            // Interpret outcome
            match output {
                -1 => prop_assert_eq!(
                    call()?,
                    Err(RawHwlocError {
                        api,
                        errno: Some(new_errno)
                    })
                ),
                0 => prop_assert_eq!(call()?, Ok(false)),
                1 => prop_assert_eq!(call()?, Ok(true)),
                _ => assert_panics(call)?,
            }
        }

        #[test]
        fn bool_err_with_errno(start_errno: i32, new_errno: NonZeroU32) {
            // Test boilerplate
            let start_errno = Errno(start_errno.wrapping_abs());
            let new_errno = Errno(i32::from_ne_bytes(new_errno.get().to_ne_bytes()).wrapping_abs());
            let _errno_guard = ErrnoGuard::new(start_errno);
            let api = "uvw";

            // Run the function
            prop_assert_eq!(
                super::call_hwloc_bool(api, || {
                    errno::set_errno(new_errno);
                    -1
                }),
                Err(RawHwlocError {
                    api,
                    errno: Some(new_errno)
                })
            );
            prop_assert_eq!(errno::errno(), start_errno);
        }

        #[test]
        fn bool_err_wo_errno(start_errno: i32) {
            // Test boilerplate
            let start_errno = Errno(start_errno.wrapping_abs());
            let _errno_guard = ErrnoGuard::new(start_errno);
            let api = "xyz";

            // Run the function
            prop_assert_eq!(
                super::call_hwloc_bool(api, || -1),
                Err(RawHwlocError { api, errno: None })
            );
            prop_assert_eq!(errno::errno(), start_errno);
        }

        #[test]
        fn bool_success(output: bool, start_errno: i32, new_errno: NonZeroU32) {
            // Test boilerplate
            let start_errno = Errno(start_errno.wrapping_abs());
            let new_errno = Errno(i32::from_ne_bytes(new_errno.get().to_ne_bytes()).wrapping_abs());
            let _errno_guard = ErrnoGuard::new(start_errno);
            let api = "cthulhu_phtagn";

            // Run the function
            prop_assert_eq!(
                super::call_hwloc_bool(api, || {
                    errno::set_errno(new_errno);
                    i32::from(output)
                }),
                Ok(output)
            );
            prop_assert_eq!(errno::errno(), start_errno);
        }

        #[test]
        fn parameter_error_from(x: i128) {
            prop_assert_eq!(ParameterError::from(x), ParameterError(x));
        }
    }
}
