//! Exporting topologies to XML

#[cfg(doc)]
use crate::{errors::NulError, topology::builder::TopologyBuilder};
use crate::{
    errors::{self, HybridError, RawHwlocError},
    ffi,
    path::{self, PathError},
    topology::Topology,
};
use bitflags::bitflags;
use std::{
    borrow::Borrow,
    ffi::{c_char, c_int, c_ulong, CStr, OsStr},
    fmt::{self, Debug, Display},
    hash::Hash,
    ops::{Deref, Index},
    path::Path,
    ptr::{self, NonNull},
};

/// # Exporting Topologies to XML
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__xmlexport.html
impl Topology {
    /// Export the topology into an XML file at filesystem location `path`
    ///
    /// If no path is given, the XML output is sent to standard output.
    ///
    /// This file may be loaded later using [`TopologyBuilder::from_xml_file()`].
    ///
    /// By default, the latest export format is used, which means older hwloc
    /// releases (e.g. v1.x) will not be able to import it. Exporting to v1.x
    /// specific XML format is possible using flag
    /// [`XMLExportFlags::V1`] but it may miss some details about the topology.
    /// Also, note that this option will be removed from the (upcoming at the
    /// time of writing) hwloc v3.0 release.
    ///
    /// If there is any chance that the exported file may ever be imported back
    /// by a process using hwloc 1.x, one should consider detecting it at
    /// runtime and using the corresponding export format.
    ///
    /// Only printable characters may be exported to XML string attributes. Any
    /// other character, especially any non-ASCII character, will be silently
    /// dropped.
    ///
    /// # Errors
    ///
    /// - [`NulError`] if `path` contains NUL chars.
    #[doc(alias = "hwloc_topology_export_xml")]
    pub fn export_xml_file(
        &self,
        path: Option<impl AsRef<Path>>,
        flags: XMLExportFlags,
    ) -> Result<(), HybridError<PathError>> {
        let path = if let Some(path) = path {
            path::make_hwloc_path(path.as_ref())?
        } else {
            path::make_hwloc_path(Path::new("-")).expect("Known to be valid")
        };
        errors::call_hwloc_int_normal("hwloc_topology_export_xml", || unsafe {
            ffi::hwloc_topology_export_xml(self.as_ptr(), path.borrow(), flags.bits())
        })
        .map_err(HybridError::Hwloc)?;
        Ok(())
    }

    /// Export the topology into an XML memory buffer
    ///
    /// This memory buffer may be loaded later using
    /// [`TopologyBuilder::from_xml()`].
    ///
    /// By default, the latest export format is used, which means older hwloc
    /// releases (e.g. v1.x) will not be able to import it. Exporting to v1.x
    /// specific XML format is possible using flag
    /// [`XMLExportFlags::V1`] but it may miss some details about the topology.
    /// Also, note that this option will be removed from the (upcoming at the
    /// time of writing) hwloc v3.0 release.
    ///
    /// If there is any chance that the exported file may ever be imported back
    /// by a process using hwloc 1.x, one should consider detecting it at
    /// runtime and using the corresponding export format.
    ///
    /// Only printable characters may be exported to XML string attributes. Any
    /// other character, especially any non-ASCII character, will be silently
    /// dropped.
    #[doc(alias = "hwloc_topology_export_xmlbuffer")]
    pub fn export_xml(&self, flags: XMLExportFlags) -> Result<XML, RawHwlocError> {
        let mut xmlbuffer = ptr::null_mut();
        let mut buflen = 0;
        errors::call_hwloc_int_normal("hwloc_topology_export_xmlbuffer", || unsafe {
            ffi::hwloc_topology_export_xmlbuffer(
                self.as_ptr(),
                &mut xmlbuffer,
                &mut buflen,
                flags.bits(),
            )
        })?;
        Ok(unsafe { XML::wrap(self, xmlbuffer, buflen) }
            .expect("Got null pointer from hwloc_topology_export_xmlbuffer"))
    }
}

bitflags! {
    /// Flags to be given to [`Topology::export_xml()`]
    #[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
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
    /// # Safety
    ///
    /// `base` must originate from `topology`.
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
        let data: *const [u8] = s.to_bytes_with_nul();
        let data = (data as *const [c_char]).cast_mut();
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
    #[doc(alias = "hwloc_free_xmlbuffer")]
    fn drop(&mut self) {
        let addr = self.data.as_ptr().cast::<c_char>();
        unsafe { ffi::hwloc_free_xmlbuffer(self.topology.as_ptr(), addr) }
    }
}
