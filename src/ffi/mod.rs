//! Useful tools for interacting with the hwloc C API
//!
//! This module contains a bunch of small utilities that proved convenient when
//! interacting with hwloc entry points, but do not clearly belong in any other
//! module.

pub(crate) mod int;
pub(crate) mod string;

use std::{
    ffi::{c_char, CStr},
    fmt, ptr,
};

// Re-export the PositiveInt type
pub use int::PositiveInt;

/// Translate a &-reference to an hwloc type into one to the matching wrapper
/// type
///
/// # Safety
///
/// `NewT` must be a `repr(transparent)` newtype of `T`
pub(crate) unsafe fn as_newtype<T, NewT>(raw: &T) -> &NewT {
    let ptr: *const T = raw;
    // SAFETY: - &*ptr is safe per se since ptr is just a reinterpreted &
    //         - Per safety precondition, T can be reinterpreted as NewT
    unsafe { &*ptr.cast::<NewT>() }
}

/// Translate an &mut-reference to an hwloc type into one to the matching
/// wrapper type
///
/// # Safety
///
/// `NewT` must be a `repr(transparent)` newtype of `T`
pub(crate) unsafe fn as_newtype_mut<T, NewT>(raw: &mut T) -> &mut NewT {
    let ptr: *mut T = raw;
    // SAFETY: - &mut *ptr is safe per se since ptr is just a reinterpreted &mut
    //         - Per safety precondition, T can be reinterpreted as NewT
    unsafe { &mut *ptr.cast::<NewT>() }
}

/// Dereference a C pointer with correct lifetime (*const -> & version)
///
/// # Safety
///
/// If non-null, p must be safe to dereference for the duration of the
/// reference-to-pointer's lifetime, and the target data must not be modified
/// as long as the reference exists.
pub(crate) unsafe fn deref_ptr<T>(p: &*const T) -> Option<&T> {
    if p.is_null() {
        return None;
    }
    // SAFETY: Per input precondition
    Some(unsafe { &**p })
}

/// Like [`deref_ptr()`], but performs a cast to a newtype along the way
///
/// # Safety
///
/// - If non-null, p must be safe to dereference for the duration of the
///   reference-to-pointer's lifetime, and the target data must not be modified
///   as long as the reference exists.
/// - `NewT` must be a `repr(transparent)` newtype of `T`
pub(crate) unsafe fn deref_ptr_newtype<T, NewT>(p: &*const T) -> Option<&NewT> {
    // SAFETY: Per input preconditions
    unsafe { deref_ptr(p).map(|r| as_newtype(r)) }
}

/// Dereference a C pointer with correct lifetime (*mut -> & version)
///
/// # Safety
///
/// If non-null, p must be safe to dereference for the duration of the
/// reference-to-pointer's lifetime, and the target data must not be modified
/// as long as the reference exists.
pub(crate) unsafe fn deref_ptr_mut<T>(p: &*mut T) -> Option<&T> {
    if p.is_null() {
        return None;
    }
    // SAFETY: Per input precondition
    Some(unsafe { &**p })
}

/// Like [`deref_ptr_mut()`], but performs a cast to a newtype along the way
///
/// # Safety
///
/// - If non-null, p must be safe to dereference for the duration of the
///   reference-to-pointer's lifetime, and the target data must not be modified
///   as long as the reference exists.
/// - `NewT` must be a `repr(transparent)` newtype of `T`
pub(crate) unsafe fn deref_ptr_mut_newtype<T, NewT>(p: &*mut T) -> Option<&NewT> {
    // SAFETY: Per input preconditions
    unsafe { deref_ptr_mut(p).map(|r| as_newtype(r)) }
}

/// Dereference a C pointer with correct lifetime (*mut -> &mut version)
///
/// # Safety
///
/// If non-null, p must be safe to dereference for the duration of the
/// reference-to-pointer's lifetime, and the target data must only be modified
/// via the output reference and not be read via any other channel as long as
/// the reference exists.
#[allow(unused)]
pub(crate) unsafe fn deref_mut_ptr<T>(p: &mut *mut T) -> Option<&mut T> {
    if p.is_null() {
        return None;
    }
    // SAFETY: Per input precondition
    Some(unsafe { &mut **p })
}

/// Like [`deref_mut_ptr()`], but performs a cast to a newtype along the way
///
/// # Safety
///
/// - If non-null, p must be safe to dereference for the duration of the
///   reference-to-pointer's lifetime, and the target data must only be modified
///   via the output reference and not be read via any other channel as long as
///   the reference exists.
/// - `NewT` must be a `repr(transparent)` newtype of `T`
#[allow(unused)]
pub(crate) unsafe fn deref_mut_ptr_newtype<T, NewT>(p: &mut *mut T) -> Option<&mut NewT> {
    // SAFETY: Per input preconditions
    unsafe { deref_mut_ptr(p).map(|r| as_newtype_mut(r)) }
}

/// Dereference a C-style string with correct lifetime
///
/// # Safety
///
/// If non-null, p must be safe to dereference for the duration of the
/// reference-to-pointer's lifetime, and the target data must not be modified
/// as long as the reference exists.
pub(crate) unsafe fn deref_str(p: &*mut c_char) -> Option<&CStr> {
    if p.is_null() {
        return None;
    }
    // SAFETY: Per input precondition
    Some(unsafe { CStr::from_ptr(*p) })
}

/// Get text output from an snprintf-like function
///
/// # Safety
///
/// `snprintf` must behave like the libc `snprintf()` function:
///
/// - If called with a null pointer and a zero length, it should return the
///   length of the output string (without trailing zero).
/// - If called with a pointer to a buffer and the length of that buffer, it
///   should write text to the buffer (with a trailing zero) and not affect it
///   in any other way.
pub(crate) unsafe fn call_snprintf(
    mut snprintf: impl FnMut(*mut c_char, usize) -> i32,
) -> Box<[c_char]> {
    let len_i32 = snprintf(ptr::null_mut(), 0);
    let len =
        usize::try_from(len_i32).expect("Got invalid string length from an snprintf-like API");
    let mut buf = vec![0i8; len + 1];
    assert_eq!(
        snprintf(buf.as_mut_ptr(), buf.len()),
        len_i32,
        "Got inconsistent string length from an snprintf-like API"
    );
    assert_eq!(
        buf.last().copied(),
        Some(0),
        "Got non-NUL char at end of snprintf-like API output"
    );
    buf.into()
}

/// Send the output of an snprintf-like function to a standard Rust formatter
///
/// # Safety
///
/// Same as [`call_snprintf()`].
pub(crate) fn write_snprintf(
    f: &mut fmt::Formatter<'_>,
    snprintf: impl FnMut(*mut c_char, usize) -> i32,
) -> fmt::Result {
    // SAFETY: Per input precondition
    let buf = unsafe { call_snprintf(snprintf) };
    // SAFETY: - The memory comes from a Box<[c_char]> ending with a
    //           NUL terminator.
    //         - The original buf is not modified or deallocated as long as the
    //           text CStr pointing to it is live.
    let text = unsafe { CStr::from_ptr(buf.as_ptr()) }.to_string_lossy();
    f.pad(&text)
}
