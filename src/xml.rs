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
    path::Path,
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

    /// Previously allocated XML string, checked to be a valid Rust str + NUL
    data: NonNull<[c_char]>,
}

impl<'topology> XML<'topology> {
    /// Wrap an hwloc XML string
    ///
    /// # Panics
    ///
    /// If the string is not valid UTF-8
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
        s.to_str().expect("hwloc emitted a non-UTF8 XML string");
        debug_assert_eq!(
            s.to_bytes_with_nul().len(),
            usize::try_from(len).expect("Unexpected len from hwloc")
        );
        let data = s.to_bytes_with_nul() as *const [u8] as *const [c_char] as *mut [c_char];
        NonNull::new(data).map(|data| Self { topology, data })
    }
}

impl AsRef<[u8]> for XML<'_> {
    fn as_ref(&self) -> &[u8] {
        let data = self.data.as_ptr() as *const u8;
        let len_wo_null = unsafe { self.data.as_ref().len() } - 1;
        unsafe { std::slice::from_raw_parts(data, len_wo_null) }
    }
}

impl AsRef<str> for XML<'_> {
    fn as_ref(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(self.as_ref()) }
    }
}

impl AsRef<OsStr> for XML<'_> {
    fn as_ref(&self) -> &OsStr {
        <Self as AsRef<str>>::as_ref(self).as_ref()
    }
}

impl AsRef<Path> for XML<'_> {
    fn as_ref(&self) -> &Path {
        <Self as AsRef<str>>::as_ref(self).as_ref()
    }
}

impl Borrow<str> for XML<'_> {
    fn borrow(&self) -> &str {
        self.as_ref()
    }
}

impl Debug for XML<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <str as Debug>::fmt(<Self as AsRef<str>>::as_ref(self), f)
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
        <str as Display>::fmt(<Self as AsRef<str>>::as_ref(self), f)
    }
}

impl Eq for XML<'_> {}

impl Hash for XML<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        <Self as AsRef<str>>::as_ref(self).hash(state)
    }
}

impl<T> Index<T> for XML<'_>
where
    str: Index<T>,
{
    type Output = <str as Index<T>>::Output;

    fn index(&self, index: T) -> &Self::Output {
        <Self as AsRef<str>>::as_ref(self).index(index)
    }
}

impl Ord for XML<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let s1 = <Self as AsRef<str>>::as_ref(self);
        let s2 = <Self as AsRef<str>>::as_ref(other);
        s1.cmp(s2)
    }
}

impl PartialEq for XML<'_> {
    fn eq(&self, other: &Self) -> bool {
        let s1 = <Self as AsRef<str>>::as_ref(self);
        let s2 = <Self as AsRef<str>>::as_ref(other);
        s1.eq(s2)
    }
}

impl<T> PartialEq<T> for XML<'_>
where
    str: PartialEq<T>,
{
    fn eq(&self, other: &T) -> bool {
        <Self as AsRef<str>>::as_ref(self).eq(other)
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
