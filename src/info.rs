//! Textual key-value information
//!
//! Several hwloc entities may be freely annotated with free-form textual
//! information in a key-value layout. This module provides an interface to
//! this information.

use crate::ffi::{self, string::LibcString, transparent::TransparentNewtype};
use hwlocality_sys::hwloc_info_s;
use std::{ffi::CStr, fmt, hash::Hash};

/// Textual key-value information
///
/// Used in multiple places of the hwloc API to provide extensible free-form
/// textual metadata.
//
// --- Implementation details ---
//
// # Safety
//
// As a type invariant, all inner pointers are assumed to be safe to
// dereference, and pointing to a valid C string devoid of mutable aliases, as
// long as the TextualInfo is reachable at all.
//
// This is enforced through the following precautions:
//
// - No public API exposes an owned TextualInfo, only references to it bound by
//   the parent topology's lifetime are exposed
// - APIs for interacting with topologies and textual info honor Rust's
//   shared XOR mutable aliasing rules, with no internal mutability
// - new() explicitly warns about associated aliasing/validity dangers
//
// Provided that objects do not link to strings allocated outside of the
// topology they originate from, which is a minimally sane expectation from
// hwloc, this should be enough.
#[allow(clippy::non_send_fields_in_send_ty)]
#[doc(alias = "hwloc_info_s")]
#[repr(transparent)]
pub struct TextualInfo(hwloc_info_s);
//
impl TextualInfo {
    /// Build a `hwloc_info_s` struct for hwloc consumption
    ///
    /// # Safety
    ///
    /// - Do not modify the target [`LibcString`]s as long as this is used
    /// - Do not use after the associated [`LibcString`]s have been dropped
    #[allow(unused)]
    pub(crate) unsafe fn borrow_raw(name: &LibcString, value: &LibcString) -> hwloc_info_s {
        hwloc_info_s {
            name: name.borrow().cast_mut(),
            value: value.borrow().cast_mut(),
        }
    }

    /// Name indicating which information is being provided
    #[doc(alias = "hwloc_info_s::name")]
    pub fn name(&self) -> &CStr {
        // SAFETY: - Pointer validity is assumed as a type invariant
        //         - Rust aliasing rules are enforced by deriving the reference
        //           from &self, which itself is derived from &Topology
        unsafe { ffi::deref_str(&self.0.name) }.expect("Infos should have names")
    }

    /// Information in textual form
    #[doc(alias = "hwloc_info_s::value")]
    pub fn value(&self) -> &CStr {
        // SAFETY: - Pointer validity is assumed as a type invariant
        //         - Rust aliasing rules are enforced by deriving the reference
        //           from &self, which itself is derived from &Topology
        unsafe { ffi::deref_str(&self.0.value) }.expect("Infos should have values")
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
// SAFETY: Does not have internal mutability
unsafe impl Send for TextualInfo {}
//
// SAFETY: Does not have internal mutability
unsafe impl Sync for TextualInfo {}
//
// SAFETY: TextualInfo is a repr(transparent) newtype of hwloc_info_s
unsafe impl TransparentNewtype for TextualInfo {
    type Inner = hwloc_info_s;
}
