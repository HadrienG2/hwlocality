//! Textual key-value information
//!
//! Several hwloc entities may be freely annotated with free-form textual
//! information in a key-value layout. This module provides an interface to
//! this information.

use crate::ffi::{self, LibcString};
use std::{
    ffi::{c_char, CStr},
    fmt,
    hash::Hash,
};

/// Textual key-value information
///
/// Used in multiple places of the hwloc API to provide extensible free-form
/// textual metadata.
//
// --- Implementation details ---
//
// # Safety
//
// As a type invariant, all inner pointers are assumed to be safe to dereference
// and devoid of mutable aliases if the TopologyObject is reachable at all.
//
// This is enforced through the following precautions:
//
// - No public API exposes an owned TextualInfo, only references to it bound by
//   the source topology's lifetime are exposed.
// - APIs for interacting with topologies and textual info honor Rust's
//   shared XOR mutable aliasing rules, with no internal mutability.
// - new() explicitly warns about associated aliasing/validity dangers.
//
// Provided that objects do not link to other objects outside of the topology
// they originate from, which is minimally sane expectation from hwloc, this
// should be enough.
#[doc(alias = "hwloc_info_s")]
#[repr(C)]
pub struct TextualInfo {
    /// Name indicating which information is being provided
    ///
    /// SAFETY: Do not modify
    name: *mut c_char,

    /// Information in textual form
    ///
    /// SAFETY: Do not modify
    value: *mut c_char,
}
//
impl TextualInfo {
    /// Build a TextualInfo struct
    ///
    /// # Safety
    ///
    /// The resulting `TextualInfo` struct may not be used after the end of the
    /// lifetime of underlying strings `name` and `value`.
    #[allow(unused)]
    pub(crate) fn new(name: &LibcString, value: &LibcString) -> Self {
        Self {
            name: name.borrow().cast_mut(),
            value: value.borrow().cast_mut(),
        }
    }

    /// Name indicating which information is being provided
    #[doc(alias = "hwloc_info_s::name")]
    pub fn name(&self) -> &CStr {
        // SAFETY: Pointer validity is a type invariant, Rust aliasing rules are
        //         enforced by deriving the reference from &self, which itself
        //         is derived from &Owner.
        unsafe { ffi::deref_str(&self.name) }.expect("Infos should have names")
    }

    /// Information in textual form
    #[doc(alias = "hwloc_info_s::value")]
    pub fn value(&self) -> &CStr {
        // SAFETY: Pointer validity is a type invariant, Rust aliasing rules are
        //         enforced by deriving the reference from &self, which itself
        //         is derived from &Topology.
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
impl Eq for TextualInfo {}
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
