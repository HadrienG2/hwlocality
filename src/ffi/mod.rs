//! Useful tools for interacting with the hwloc C API
//!
//! This module contains a bunch of small utilities that proved convenient when
//! interacting with hwloc entry points, but do not clearly belong in any other
//! module.

pub(crate) mod int;
pub(crate) mod string;
pub(crate) mod transparent;

use std::{
    ffi::{c_char, CStr},
    fmt, ptr,
};

// Re-export the PositiveInt type
pub use int::PositiveInt;

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
pub(crate) unsafe fn write_snprintf(
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        ffi::CString,
        fmt::{self, Debug},
    };

    #[test]
    fn deref_ptr_like() {
        // SAFETY: Safe to call on a null pointer
        assert_eq!(unsafe { deref_ptr(&ptr::null::<u16>()) }, None);
        // SAFETY: Safe to call on a null pointer
        assert_eq!(unsafe { deref_ptr_mut(&ptr::null_mut::<u16>()) }, None);
        // SAFETY: Safe to call on a null pointer
        assert_eq!(unsafe { deref_mut_ptr(&mut ptr::null_mut::<u16>()) }, None);

        let mut x = 42;
        {
            let p: *const u32 = &x;
            // SAFETY: Valid because the &x that p is from was valid
            let r = unsafe { deref_ptr(&p).unwrap() };
            assert!(ptr::eq(r, &x));
        }
        {
            let p_mut: *mut u32 = &mut x;
            // SAFETY: Valid because the &mut x that p is from was valid and the
            //         original &mut reference has gone out of scope
            let r = unsafe { deref_ptr_mut(&p_mut).unwrap() };
            assert!(ptr::eq(r, &x));
        }
        {
            let mut p_mut: *mut u32 = &mut x;
            // SAFETY: Valid because the &mut x that p is from was valid and the
            //         original &mut reference has gone out of scope
            let r = unsafe { deref_mut_ptr(&mut p_mut).unwrap() };
            assert!(ptr::eq(r, &x));
        }
    }

    #[test]
    fn deref_str() {
        assert_eq!(
            // SAFETY: Safe to call on a null pointer
            unsafe { super::deref_str(&ptr::null_mut::<c_char>()) },
            None
        );

        let s = CString::new("Hello world").unwrap();
        let p = s.as_ptr().cast_mut();
        // SAFETY: This is just a very convoluted way of borrowing s
        let s2 = unsafe { super::deref_str(&p).unwrap() };
        assert!(ptr::eq(s2.as_ptr(), p.cast_const()));
    }

    #[test]
    fn snprintf_wrappers() {
        const ORIGINAL: &str = "I'm sorry, Dave\0";

        // # Safety
        //
        // Must be called with correct snprintf inputs
        unsafe fn snprintf(buf: *mut c_char, len: usize) -> i32 {
            assert!(!(buf.is_null() && len != 0));
            let original_bytes = ORIGINAL.as_bytes();
            if !buf.is_null() {
                let truncated_len = len.min(original_bytes.len());
                // SAFETY: Acceptable per input assumption
                let buf = unsafe { std::slice::from_raw_parts_mut(buf.cast::<u8>(), len) };
                buf.copy_from_slice(&original_bytes[..truncated_len]);
            }
            i32::try_from(original_bytes.len() - 1).unwrap()
        }

        // SAFETY: snprintf closure is indeed an snprintf-like function
        assert!(unsafe { call_snprintf(|buf, len| snprintf(buf, len)) }
            .iter()
            .copied()
            .eq(ORIGINAL.bytes().map(|b| c_char::try_from(b).unwrap())));

        struct Harness;
        //
        impl Debug for Harness {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                // SAFETY: - write_snprintf can handle snprintf correctly
                //         - snprintf honors write_snprintf's assumptions
                unsafe { write_snprintf(f, |buf, len| snprintf(buf, len)) }
            }
        }
        //
        let x = format!("{Harness:?}");
        assert_eq!(x, &ORIGINAL[..ORIGINAL.len() - 1]);
    }
}
