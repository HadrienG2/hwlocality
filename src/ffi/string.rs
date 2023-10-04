//! A less error-prone [`CString`] alternative

use crate::errors::NulError;
use std::{
    ffi::{c_char, c_void},
    fmt::{self, Debug, Display},
    ptr::NonNull,
};

/// Less error-prone [`CString`] alternative
///
/// This fulfills the same goal as [`CString`] (go from Rust [`&str`] to C
/// `*char`) but with a less error-prone API and a libc-backed allocation whose
/// ownership can safely be transferred to C libraries that manage memory using
/// malloc/free like hwloc.
//
// --- Implementation details
//
// # Safety
//
// As a type invariant, the inner pointer is assumed to always point to a valid,
// non-aliased C string.
pub(crate) struct LibcString(NonNull<[c_char]>);
//
impl LibcString {
    /// Convert a Rust string to a C-compatible representation
    ///
    /// Returns `None` if the Rust string cannot be converted to a C
    /// representation because it contains null chars.
    pub(crate) fn new(s: impl AsRef<str>) -> Result<Self, NulError> {
        // Check input string for inner null chars
        let s = s.as_ref();
        if s.contains('\0') {
            return Err(NulError);
        }

        // Make sure the output C string would follow Rust's rules
        let len = s.len() + 1;
        assert!(
            len < isize::MAX as usize,
            "Cannot add a final NUL without breaking Rust's slice requirements"
        );

        // Allocate C string and wrap it in Self for auto-deallocation
        // SAFETY: malloc is safe to call for any nonzero length
        let buf = unsafe { libc::malloc(len) }.cast::<c_char>();
        let buf = NonNull::new(buf).expect("Failed to allocate string buffer");
        // Eventually using this slice pointer is safe because...
        // - buf is valid for reads and writes for len bytes
        // - Byte pointers are always aligned
        // - buf will be initialized and unaliased by the time this pointer is
        //   dereferenced
        // - len was checked to fit Rust's slice size requirements
        let buf = NonNull::slice_from_raw_parts(buf, len);
        let result = Self(buf);

        // Fill the string and return it
        let start = buf.as_ptr().cast::<u8>();
        // SAFETY: - By definition of a slice, the source range is correct
        //         - It is OK to write s.len() bytes as buf is of len s.len() + 1
        //         - Byte pointers are always aligned
        //         - Overlap between unrelated memory allocations is impossible
        unsafe { start.copy_from_nonoverlapping(s.as_ptr(), s.len()) };
        // SAFETY: Index s.len() is in bounds in a buffer of length s.len() + 1
        unsafe { start.add(s.len()).write(b'\0') };
        Ok(result)
    }

    /// Check the length of the string, including NUL terminator
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    /// Make the string momentarily available to a C API that expects `const char*`
    ///
    /// Make sure the C API does not retain any pointer to the string after
    /// this [`LibcString`] is deallocated!
    pub(crate) fn borrow(&self) -> *const c_char {
        self.0.as_ptr().cast::<c_char>()
    }

    /// Transfer ownership of the string to a C API
    ///
    /// Unlike with regular [`CString`], it is safe to pass this string to a C
    /// API that may later free it using `free()`.
    pub(crate) fn into_raw(self) -> *mut c_char {
        let ptr = self.0.as_ptr().cast::<c_char>();
        std::mem::forget(self);
        ptr
    }
}
//
impl AsRef<str> for LibcString {
    fn as_ref(&self) -> &str {
        // SAFETY: Per type invariant, this is a C string composed of an &str
        //         followed by a terminating NUL.
        unsafe {
            std::str::from_utf8_unchecked(std::slice::from_raw_parts(
                self.borrow().cast::<u8>(),
                self.len() - 1,
            ))
        }
    }
}
//
impl Debug for LibcString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s: &str = self.as_ref();
        f.pad(&format!("{s:?}"))
    }
}
//
impl Display for LibcString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s: &str = self.as_ref();
        f.pad(s)
    }
}
//
impl Drop for LibcString {
    fn drop(&mut self) {
        // SAFETY: self.0 comes from malloc and there is no way to deallocate it
        //         other than Drop so double free cannot happen
        unsafe { libc::free(self.0.as_ptr().cast::<c_void>()) }
    }
}
//
impl Eq for LibcString {}
//
impl PartialEq for LibcString {
    fn eq(&self, other: &Self) -> bool {
        self.as_ref() == other.as_ref()
    }
}
//
// SAFETY: LibcString exposes no internal mutability
unsafe impl Send for LibcString {}
//
// SAFETY: LibcString exposes no internal mutability
unsafe impl Sync for LibcString {}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck_macros::quickcheck;
    use std::ffi::CStr;

    macro_rules! check_new {
        ($result:expr, $input:expr) => {
            match ($input.contains('\0'), $result) {
                (false, Ok(result)) => result,
                (true, Err(NulError)) => return,
                (false, Err(NulError)) | (true, Ok(_)) => panic!("Should never happen"),
            }
        };
    }

    #[quickcheck]
    fn unary(s: String) {
        let c = check_new!(LibcString::new(&s), &s);

        assert_eq!(c.len(), s.len() + 1);
        // SAFETY: Safe as a type invariant of LibcString
        assert_eq!(unsafe { CStr::from_ptr(c.borrow()) }.to_str().unwrap(), s);
        assert_eq!(c.as_ref(), s);
        assert_eq!(c.to_string(), s);
        assert_eq!(format!("{c:?}"), format!("{s:?}"));

        let backup = c.0;
        let raw = c.into_raw();
        assert_eq!(raw, backup.cast::<c_char>().as_ptr());

        // SAFETY: Effectively replicates Drop. Correct because since into_raw()
        //         has been called, Drop will not be called.
        unsafe { libc::free(raw.cast::<c_void>()) };
    }

    #[quickcheck]
    fn binary(s1: String, s2: String) {
        let c1 = check_new!(LibcString::new(&s1), &s1);
        let c2 = check_new!(LibcString::new(&s2), &s2);
        assert_eq!(c1 == c2, s1 == s2);
    }
}
