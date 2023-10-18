//! File path handling
//!
//! Several hwloc methods ingest file paths. Conversion from Rust file paths to
//! C file paths can fail in several way, and this module is concerned with the
//! associated error detection and reporting.

use crate::{errors::NulError, ffi::string::LibcString};
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::path::Path;
use thiserror::Error;

/// Requested file path is not suitable for hwloc consumption
#[derive(Copy, Clone, Debug, Error, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum PathError {
    /// Path contains the NUL char, and is thus not compatible with C
    #[error("hwloc file paths can't contain NUL chars")]
    ContainsNul,

    /// Path contains non-Unicode data
    ///
    /// We need paths to be valid Unicode, even though most operating systems do
    /// not mandate it, because that is a prerequisite for portably converting
    /// paths to `char*` for C/hwloc consumption.
    #[error("hwloc file paths can't contain non-Unicode data")]
    NotUnicode,
}
//
impl From<NulError> for PathError {
    fn from(_: NulError) -> Self {
        Self::ContainsNul
    }
}

/// Convert a file path into something that hwloc can ingest, or die trying
///
/// # Errors
///
/// - [`ContainsNul`] if `path` contains NUL chars.
/// - [`NotUnicode`] if `path` contains non-Unicode data
pub(crate) fn make_hwloc_path(path: impl AsRef<Path>) -> Result<LibcString, PathError> {
    /// Polymorphized version of this function (avoids generics code bloat)
    fn polymorphized(path: &Path) -> Result<LibcString, PathError> {
        Ok(LibcString::new(
            path.to_str().ok_or(PathError::NotUnicode)?,
        )?)
    }
    polymorphized(path.as_ref())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::{path::PathParams, prelude::*};
    #[allow(unused)]
    use similar_asserts::assert_eq;
    use static_assertions::{assert_impl_all, assert_not_impl_any};
    use std::{
        error::Error,
        fmt::{self, Binary, LowerExp, LowerHex, Octal, Pointer, UpperExp, UpperHex},
        hash::Hash,
        io::{self, Read},
        ops::Deref,
        panic::UnwindSafe,
        path::PathBuf,
    };

    // Check that public types in this module keep implementing all expected
    // traits, in the interest of detecting future semver-breaking changes
    assert_impl_all!(PathError:
        Copy, Error, From<NulError>, Hash, Ord, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(PathError:
        Binary, Default, Deref, Drop, IntoIterator, LowerExp, LowerHex, Octal,
        Pointer, Read, UpperExp, UpperHex, fmt::Write, io::Write
    );

    /// Path generator that's actually exhaustive, unlike proptest's default
    fn any_path() -> impl Strategy<Value = PathBuf> {
        PathBuf::arbitrary_with(PathParams::default().with_component_regex(".*"))
    }

    proptest! {
        #[allow(clippy::option_if_let_else)]
        #[test]
        fn make_hwloc_path(path in any_path()) {
            let res = super::make_hwloc_path(&path);
            if let Some(s) = path.to_str() {
                if s.contains('\0') {
                    prop_assert_eq!(res, Err(PathError::ContainsNul));
                } else {
                    prop_assert_eq!(res.as_ref().map(AsRef::as_ref), Ok(s));
                }
            } else {
                prop_assert_eq!(res, Err(PathError::NotUnicode))
            }
        }
    }
}
