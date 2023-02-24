//! Textual key-value information

use crate::ffi;
#[cfg(doc)]
use crate::support::DiscoverySupport;
use std::{
    ffi::{c_char, CStr},
    fmt,
    hash::Hash,
};

/// Key-value string attributes
#[repr(C)]
#[derive(Eq)]
#[doc(alias = "hwloc_info_s")]
pub struct TextualInfo {
    name: *mut c_char,
    value: *mut c_char,
}
//
impl TextualInfo {
    /// The name of the ObjectInfo
    pub fn name(&self) -> &CStr {
        unsafe { ffi::deref_str(&self.name) }.expect("Infos should have names")
    }

    /// The value of the ObjectInfo
    pub fn value(&self) -> &CStr {
        unsafe { ffi::deref_str(&self.value) }.expect("Infos should have values")
    }
}
//
impl fmt::Debug for TextualInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ObjectInfo")
            .field("name", &self.name())
            .field("value", &self.value())
            .finish()
    }
}
//
impl Hash for TextualInfo {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name().hash(state);
        self.value().hash(state);
    }
}
//
impl PartialEq for TextualInfo {
    fn eq(&self, other: &Self) -> bool {
        self.name() == other.name() && self.value() == other.value()
    }
}
//
unsafe impl Send for TextualInfo {}
unsafe impl Sync for TextualInfo {}
