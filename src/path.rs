//! File path handling
//!
//! Several hwloc methods ingest file paths. Conversion from Rust file paths to
//! C file paths can fail in several way, and this module is concerned with the
//! associated error detection and reporting.

use crate::{errors::NulError, ffi::string::LibcString};
#[allow(unused)]
#[cfg(test)]
use pretty_assertions::{assert_eq, assert_ne};
use std::path::Path;
use thiserror::Error;

/// Requested file path is not valid
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum PathError {
    /// Path contains the NUL char, and is thus not compatible with C
    #[error("path contains the NUL char")]
    ContainsNul,

    /// Path contains non-Unicode data
    ///
    /// We need paths to be valid Unicode, even though most operating systems do
    /// not mandate it, because that is a prerequisite for portably converting
    /// paths to `char*` for C/hwloc consumption.
    #[error("path contains non-Unicode data")]
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
    #[allow(unused)]
    use pretty_assertions::{assert_eq, assert_ne};
    use quickcheck_macros::quickcheck;
    use static_assertions::assert_impl_all;
    use std::{
        error::Error,
        fmt::Debug,
        hash::Hash,
        panic::{RefUnwindSafe, UnwindSafe},
        path::PathBuf,
    };

    // Check that public types in this module keep implementing all expected
    // traits, in the interest of detecting future semver-breaking changes
    assert_impl_all!(PathError:
        Clone, Copy, Debug, Error, Eq, From<NulError>, Hash, RefUnwindSafe,
        Send, Sized, Sync, Unpin, UnwindSafe
    );

    #[allow(clippy::option_if_let_else)]
    #[quickcheck]
    fn make_hwloc_path(path: PathBuf) {
        let res = super::make_hwloc_path(&path);
        match path.to_str() {
            Some(s) => {
                if s.contains('\0') {
                    assert_eq!(res, Err(PathError::ContainsNul));
                } else {
                    assert_eq!(res.as_ref().map(AsRef::as_ref), Ok(s));
                }
            }
            None => assert_eq!(res, Err(PathError::NotUnicode)),
        }
    }
}
