//! Textual key-value information
//!
//! Several hwloc entities may be freely annotated with free-form textual
//! information in a key-value layout. This module provides an interface to
//! this information.

use crate::ffi::{self, string::LibcString, transparent::TransparentNewtype};
use hwlocality_sys::hwloc_info_s;
#[allow(unused)]
#[cfg(test)]
use pretty_assertions::{assert_eq, assert_ne};
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

impl fmt::Debug for TextualInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TextualInfo")
            .field("name", &self.name())
            .field("value", &self.value())
            .finish()
    }
}

impl Eq for TextualInfo {}

impl Hash for TextualInfo {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name().hash(state);
        self.value().hash(state);
    }
}

impl PartialEq for TextualInfo {
    fn eq(&self, other: &Self) -> bool {
        self.name() == other.name() && self.value() == other.value()
    }
}

// SAFETY: Does not have internal mutability
unsafe impl Send for TextualInfo {}

// SAFETY: Does not have internal mutability
unsafe impl Sync for TextualInfo {}

// SAFETY: TextualInfo is a repr(transparent) newtype of hwloc_info_s
unsafe impl TransparentNewtype for TextualInfo {
    type Inner = hwloc_info_s;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ffi::{string::LibcString, transparent::ToNewtype};
    #[allow(unused)]
    use pretty_assertions::{assert_eq, assert_ne};
    use quickcheck_macros::quickcheck;
    use static_assertions::assert_impl_all;
    use std::{
        collections::hash_map::RandomState,
        ffi::CString,
        fmt::Debug,
        hash::{BuildHasher, Hasher},
        panic::{RefUnwindSafe, UnwindSafe},
    };

    // Check that public types in this module keep implementing all expected
    // traits, in the interest of detecting future semver-breaking changes
    assert_impl_all!(TextualInfo:
        Debug, Eq, Hash, RefUnwindSafe, Send, Sized, Sync, Unpin, UnwindSafe
    );

    #[quickcheck]
    fn unary(name: LibcString, value: LibcString) {
        // Set up test entity
        // SAFETY: `name` and `value` won't be invalidated while this exists
        let raw_info = unsafe { TextualInfo::borrow_raw(&name, &value) };
        let info: &TextualInfo = (&raw_info).to_newtype();

        // Check raw data
        assert_eq!(info.0.name, name.borrow().cast_mut());
        assert_eq!(info.0.value, value.borrow().cast_mut());

        // Check high-level accessors
        let name_c = CString::new(name.as_ref()).unwrap();
        let value_c = CString::new(value.as_ref()).unwrap();
        assert_eq!(CString::from(info.name()), name_c);
        assert_eq!(CString::from(info.value()), value_c);
        assert_eq!(
            format!("{info:#?}"),
            format!(
                "TextualInfo {{\n    \
                    name: {name_c:?},\n    \
                    value: {value_c:?},\n\
                }}",
            )
        );

        // Check hashing
        let state = RandomState::new();
        let mut expected_hasher = state.build_hasher();
        name_c.hash(&mut expected_hasher);
        value_c.hash(&mut expected_hasher);
        let mut actual_hasher = state.build_hasher();
        info.hash(&mut actual_hasher);
        assert_eq!(actual_hasher.finish(), expected_hasher.finish());
    }

    #[quickcheck]
    fn binary(name1: LibcString, name2: LibcString, value1: LibcString, value2: LibcString) {
        // Set up test entity
        // SAFETY: `name` and `value` won't be invalidated while this exists
        let raw_info1 = unsafe { TextualInfo::borrow_raw(&name1, &value1) };
        let info1: &TextualInfo = (&raw_info1).to_newtype();
        // SAFETY: `name` and `value` won't be invalidated while this exists
        let raw_info2 = unsafe { TextualInfo::borrow_raw(&name2, &value2) };
        let info2: &TextualInfo = (&raw_info2).to_newtype();

        // Check equality
        assert_eq!(info1 == info2, name1 == name2 && value1 == value2);
    }
}
