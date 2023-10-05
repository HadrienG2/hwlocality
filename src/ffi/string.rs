//! A less error-prone [`CString`] alternative

use crate::errors::NulError;
#[allow(unused)]
#[cfg(test)]
use pretty_assertions::{assert_eq, assert_ne};
#[cfg(any(test, feature = "quickcheck"))]
use quickcheck::{Arbitrary, Gen};
#[cfg(any(test, feature = "quickcheck"))]
use rand::Rng;
use std::{
    ffi::{c_char, c_void},
    fmt::{self, Debug, Display},
    ptr::NonNull,
};

/// Less error-prone [`CString`] alternative
///
/// This fulfills a subset of the goals of [`CString`] (go from Rust [`&str`] to
/// C `*char`) but with...
///
/// - Contents that are guaranteed to be UTF-8
/// - A less error-prone borrowing API
/// - A libc-backed allocation whose ownership can safely be transferred to C
///   libraries that manage memory using malloc/free like hwloc, as long as this
///   program is linked to the same libc.
//
// --- Implementation details
//
// # Safety
//
// As a type invariant, the inner pointer is assumed to always point to a valid,
// non-aliased C string.
pub(crate) struct LibcString(NonNull<[c_char]>);

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

#[cfg(any(test, feature = "quickcheck"))]
impl Arbitrary for LibcString {
    fn arbitrary(g: &mut Gen) -> Self {
        let mut rng = rand::thread_rng();
        // Start from a valid UTF-8 string...
        let s = String::arbitrary(g)
            .chars()
            // ...but replace NUL with arbitrary other ASCII chars
            .map(|c| {
                if c == '\0' {
                    char::from(rng.gen_range(1..=127))
                } else {
                    c
                }
            })
            .collect::<String>();
        Self::new(s).expect("Ensured absence of NUL above")
    }

    #[cfg(not(tarpaulin_include))]
    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(
            self.as_ref()
                .to_owned()
                .shrink()
                .filter_map(|s| Self::new(s).ok()),
        )
    }
}

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

impl Clone for LibcString {
    fn clone(&self) -> Self {
        // Allocate C string and wrap it in Self for auto-deallocation
        let len = self.len();
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
        let output_start = buf.as_ptr().cast::<u8>();
        let input_start = self.as_ref().as_bytes().as_ptr();
        // SAFETY: - By definition of a slice, the source range is correct
        //         - It is OK to read len bytes as input has that many bytes
        //         - It is OK to write len bytes as output has that many bytes
        //         - Byte pointers are always aligned
        //         - Overlap between unrelated memory allocations is impossible
        unsafe { output_start.copy_from_nonoverlapping(input_start, len) };
        result
    }
}

impl Debug for LibcString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s: &str = self.as_ref();
        f.pad(&format!("{s:?}"))
    }
}

impl Display for LibcString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s: &str = self.as_ref();
        f.pad(s)
    }
}

impl Drop for LibcString {
    fn drop(&mut self) {
        // SAFETY: self.0 comes from malloc and there is no way to deallocate it
        //         other than Drop so double free cannot happen
        unsafe { libc::free(self.0.as_ptr().cast::<c_void>()) }
    }
}

impl Eq for LibcString {}

impl PartialEq for LibcString {
    fn eq(&self, other: &Self) -> bool {
        self.as_ref() == other.as_ref()
    }
}

// SAFETY: LibcString exposes no internal mutability
unsafe impl Send for LibcString {}

// SAFETY: LibcString exposes no internal mutability
unsafe impl Sync for LibcString {}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused)]
    use pretty_assertions::{assert_eq, assert_ne};
    use quickcheck_macros::quickcheck;
    use std::ffi::CStr;

    macro_rules! check_new {
        ($result:expr, $input:expr) => {
            match ($input.contains('\0'), $result) {
                (false, Ok(result)) => result,
                (true, Err(NulError)) => return,
                (false, Err(NulError)) | (true, Ok(_)) => {
                    panic!("LibcString::new should error out if and only if NUL is present")
                }
            }
        };
    }

    #[quickcheck]
    fn unary(s: String) {
        // Set up a C string
        let c = check_new!(LibcString::new(&s), &s);

        // Test basic properties
        assert_eq!(c.len(), s.len() + 1);
        // SAFETY: Safe as a type invariant of LibcString
        assert_eq!(unsafe { CStr::from_ptr(c.borrow()) }.to_str().unwrap(), s);
        assert_eq!(c.as_ref(), s);
        assert_eq!(c.to_string(), s);
        assert_eq!(format!("{c:?}"), format!("{s:?}"));

        // Test cloning
        let c2 = c.clone();
        assert_eq!(c2.len(), c.len());
        assert_ne!(c2.borrow(), c.borrow());
        assert_eq!(c2.as_ref(), c.as_ref());

        // Test raw char* extraction
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
