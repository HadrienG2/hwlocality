//! File path handling

use crate::{errors::NulError, ffi::LibcString};
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
pub(crate) fn make_hwloc_path(path: impl AsRef<Path>) -> Result<LibcString, PathError> {
    Ok(LibcString::new(
        path.as_ref().to_str().ok_or(PathError::NotUnicode)?,
    )?)
}
