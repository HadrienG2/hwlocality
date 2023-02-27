//! Exporting topologies to XML

// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__xmlexport.html

use crate::{ffi, Topology};
use bitflags::bitflags;
use std::{
    borrow::Borrow,
    ffi::{c_char, c_int, c_ulong, CStr, OsStr},
    fmt::{self, Debug, Display},
    hash::Hash,
    ops::{Deref, Index},
    ptr::NonNull,
};

bitflags! {
    /// Flags to be given to [`Topology::export_xml()`]
    #[repr(C)]
    pub struct XMLExportFlags: c_ulong {
        /// Export XML that is loadable by hwloc v1.x
        ///
        /// The export may miss some details about the topology.
        const V1 = (1<<0);
    }
}

impl Default for XMLExportFlags {
    fn default() -> Self {
        Self::empty()
    }
}

/// XML string emitted by hwloc
///
/// This behaves like a `Box<str>` and will similarly automatically
/// liberate the allocated memory when it goes out of scope.
pub struct XML<'topology> {
    /// Underlying hwloc topology
    topology: &'topology Topology,

    /// Previously allocated XML string
    /// Checked to be a valid NUL-terminated UTF-8 string
    data: NonNull<[c_char]>,
}

impl<'topology> XML<'topology> {
    /// Wrap an hwloc XML string
    ///
    /// # Panics
    ///
    /// If the string is not valid UTF-8 (according to
    /// https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__xmlexport.html#ga333f79975b4eeb28a3d8fad3373583ce,
    /// hwloc should only generates ASCII at the time of writing)
    pub(crate) unsafe fn wrap(
        topology: &'topology Topology,
        base: *mut c_char,
        len: c_int,
    ) -> Option<Self> {
        // Handle null pointers and invalid lengths
        if base.is_null() || len < 1 {
            return None;
        }

        // Wrap the allocation
        let s = unsafe { CStr::from_ptr(base) };
        s.to_str()
            .expect("Unexpected non-UTF8 XML string from hwloc");
        debug_assert_eq!(
            s.to_bytes_with_nul().len(),
            usize::try_from(len).expect("Unexpected len from hwloc")
        );
        let data = s.to_bytes_with_nul() as *const [u8] as *const [c_char] as *mut [c_char];
        NonNull::new(data).map(|data| Self { topology, data })
    }

    /// Access the raw C string
    pub fn as_raw(&self) -> &CStr {
        // Safe because all necesary checks are done in `wrap()`
        unsafe {
            let data = self.data.as_ptr() as *const [u8];
            CStr::from_bytes_with_nul_unchecked(&*data)
        }
    }

    /// Shorthand for `<Self as AsRef<str>>::as_ref`
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

impl AsRef<[u8]> for XML<'_> {
    fn as_ref(&self) -> &[u8] {
        self.as_raw().to_bytes()
    }
}

impl AsRef<str> for XML<'_> {
    fn as_ref(&self) -> &str {
        // Safe because all necesary checks are done in `wrap()`
        unsafe { std::str::from_utf8_unchecked(self.as_raw().to_bytes()) }
    }
}

impl AsRef<OsStr> for XML<'_> {
    fn as_ref(&self) -> &OsStr {
        self.as_str().as_ref()
    }
}

impl Borrow<str> for XML<'_> {
    fn borrow(&self) -> &str {
        self.as_ref()
    }
}

impl Debug for XML<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <str as Debug>::fmt(self.as_str(), f)
    }
}

impl Deref for XML<'_> {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_ref()
    }
}

impl Display for XML<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <str as Display>::fmt(self.as_str(), f)
    }
}

impl Eq for XML<'_> {}

impl Hash for XML<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

impl<T> Index<T> for XML<'_>
where
    str: Index<T>,
{
    type Output = <str as Index<T>>::Output;

    fn index(&self, index: T) -> &Self::Output {
        self.as_str().index(index)
    }
}

impl Ord for XML<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl PartialEq for XML<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.as_str().eq(other.as_str())
    }
}

impl<T> PartialEq<T> for XML<'_>
where
    str: PartialEq<T>,
{
    fn eq(&self, other: &T) -> bool {
        self.as_str().eq(other)
    }
}

impl PartialOrd for XML<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Drop for XML<'_> {
    fn drop(&mut self) {
        let addr = self.data.as_ptr() as *mut c_char;
        unsafe { ffi::hwloc_free_xmlbuffer(self.topology.as_ptr(), addr) }
    }
}
