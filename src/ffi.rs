//! Raw access to the hwloc C API
//!
//! In addition to hwloc entry points, this module contains a bunch of small
//! utilities that proved convenient when interacting with said entry points,
//! but do not clearly belong in any other module.

use crate::errors::NulError;
use std::{
    ffi::{c_char, c_int, c_uint, c_void, CStr},
    fmt,
    ptr::{self, NonNull},
};

/// Assert that a c_int can be converted to a isize
///
/// As far as I can tell, this is only false on very weird platforms that aren't
/// supported by hwloc. However, counter-examples are welcome!
pub(crate) fn expect_isize(x: c_int) -> isize {
    x.try_into()
        .expect("Expected on any platform supported by hwloc")
}

/// Assert that a c_uint can be converted to a usize
///
/// As far as I can tell, this is only false on very weird platforms that aren't
/// supported by hwloc. However, counter-examples are welcome!
pub(crate) fn expect_usize(x: c_uint) -> usize {
    x.try_into()
        .expect("Expected on any platform supported by hwloc")
}

/// Translate a &-reference to an hwloc type into one to the matching wrapper
/// type
///
/// # Safety
///
/// `NewT` must be a `repr(transparent)` newtype of `T`
pub(crate) unsafe fn as_newtype<T, NewT>(raw: &T) -> &NewT {
    let ptr: *const T = raw;
    &*ptr.cast::<NewT>()
}

/// Translate an &mut-reference to an hwloc type into one to the matching
/// wrapper type
///
/// # Safety
///
/// `NewT` must be a `repr(transparent)` newtype of `T`
pub(crate) unsafe fn as_newtype_mut<T, NewT>(raw: &mut T) -> &mut NewT {
    let ptr: *mut T = raw;
    &mut *ptr.cast::<NewT>()
}

/// Dereference a C pointer with correct lifetime (*const -> & version)
pub(crate) unsafe fn deref_ptr<T>(p: &*const T) -> Option<&T> {
    if p.is_null() {
        return None;
    }
    Some(unsafe { &**p })
}

/// Like [`deref_ptr()`], but performs a cast to a newtype along the way
///
/// # Safety
///
/// - `NewT` must be a `repr(transparent)` newtype of `T`
pub(crate) unsafe fn deref_ptr_newtype<T, NewT>(p: &*const T) -> Option<&NewT> {
    deref_ptr(p).map(|r| as_newtype(r))
}

/// Dereference a C pointer with correct lifetime (*mut -> & version)
pub(crate) unsafe fn deref_ptr_mut<T>(p: &*mut T) -> Option<&T> {
    if p.is_null() {
        return None;
    }
    Some(unsafe { &**p })
}

/// Like [`deref_ptr_mut()`], but performs a cast to a newtype along the way
///
/// # Safety
///
/// - `NewT` must be a `repr(transparent)` newtype of `T`
pub(crate) unsafe fn deref_ptr_mut_newtype<T, NewT>(p: &*mut T) -> Option<&NewT> {
    deref_ptr_mut(p).map(|r| as_newtype(r))
}

/// Dereference a C pointer with correct lifetime (*mut -> &mut version)
#[allow(unused)]
pub(crate) unsafe fn deref_mut_ptr<T>(p: &mut *mut T) -> Option<&mut T> {
    if p.is_null() {
        return None;
    }
    Some(unsafe { &mut **p })
}

/// Like [`deref_mut_ptr()`], but performs a cast to a newtype along the way
///
/// # Safety
///
/// - `NewT` must be a `repr(transparent)` newtype of `T`
#[allow(unused)]
pub(crate) unsafe fn deref_mut_ptr_newtype<T, NewT>(p: &mut *mut T) -> Option<&mut NewT> {
    deref_mut_ptr(p).map(|r| as_newtype_mut(r))
}

/// Dereference a C-style string with correct lifetime
pub(crate) unsafe fn deref_str(p: &*mut c_char) -> Option<&CStr> {
    if p.is_null() {
        return None;
    }
    Some(unsafe { CStr::from_ptr(*p) })
}

/// Get text output from an snprintf-like function
pub(crate) fn call_snprintf(mut snprintf: impl FnMut(*mut c_char, usize) -> i32) -> Box<[c_char]> {
    let len_i32 = snprintf(ptr::null_mut(), 0);
    let len =
        usize::try_from(len_i32).expect("Got invalid string length from an snprintf-like API");
    let mut buf = vec![0i8; len + 1];
    assert_eq!(
        snprintf(buf.as_mut_ptr(), buf.len()),
        len_i32,
        "Got inconsistent string length from an snprintf-like API"
    );
    buf.into()
}

/// Send the output of an snprintf-like function to a standard Rust formatter
pub(crate) fn write_snprintf(
    f: &mut fmt::Formatter,
    snprintf: impl FnMut(*mut c_char, usize) -> i32,
) -> fmt::Result {
    let text = call_snprintf(snprintf);
    let text = unsafe { CStr::from_ptr(text.as_ptr()) }.to_string_lossy();
    f.pad(&text)
}

/// Less error-prone CString alternative
///
/// This fulfills the same goal as CString (go from Rust &str to C *char)
/// but with a less error-prone API and a libc-backed allocation whose ownership
/// can safely be transferred to C libraries that manage memory using
/// malloc/free like hwloc.
///
pub(crate) struct LibcString(NonNull<[c_char]>);
//
impl LibcString {
    /// Convert a Rust string to a C-compatible representation
    ///
    /// Returns `None` if the Rust string cannot be converted to a C
    /// representation because it contains null chars.
    pub fn new(s: impl AsRef<str>) -> Result<Self, NulError> {
        // Check input string for inner null chars
        let s = s.as_ref();
        if s.find('\0').is_some() {
            return Err(NulError);
        }

        // Allocate C string and wrap it in Self
        let len = s.len() + 1;
        let data = unsafe { libc::malloc(len) }.cast::<c_char>();
        let data = NonNull::new(data).expect("Failed to allocate string buffer");
        let buf = NonNull::from(unsafe { std::slice::from_raw_parts_mut(data.as_ptr(), len) });
        let result = Self(buf);

        // Fill the string and return it
        let bytes = unsafe { std::slice::from_raw_parts_mut(buf.as_ptr().cast::<u8>(), len) };
        let (last, elements) = bytes
            .split_last_mut()
            .expect("Cannot happen, len >= 1 by construction");
        elements.copy_from_slice(s.as_bytes());
        *last = b'\0';
        Ok(result)
    }

    /// Check the length of the string, including NUL terminator
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Make the string momentarily available to a C API that expects `const char*`
    ///
    /// Make sure the C API does not retain any pointer to the string after
    /// this LibcString is deallocated!
    pub fn borrow(&self) -> *const c_char {
        self.0.as_ptr().cast::<c_char>()
    }

    /// Transfer ownership of the string to a C API
    ///
    /// Unlike with regular CString, it is safe to pass this string to a C API
    /// that may later free it using `libc::free()`.
    pub fn into_raw(self) -> *mut c_char {
        let ptr = self.0.as_ptr().cast::<c_char>();
        std::mem::forget(self);
        ptr
    }
}
//
impl Drop for LibcString {
    fn drop(&mut self) {
        unsafe { libc::free(self.0.as_ptr().cast::<c_void>()) }
    }
}
//
unsafe impl Send for LibcString {}
unsafe impl Sync for LibcString {}
