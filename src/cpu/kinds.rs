//! Kinds of CPU cores

// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpukinds.html

use crate::errors::RawIntError;
use thiserror::Error;

/// Efficiency of a CPU kind
///
/// A higher efficiency value means greater intrinsic performance (and possibly
/// less performance/power efficiency).
///
/// Efficiency ranges from 0 to the number of CPU kinds minus one.
pub type CpuEfficiency = usize;

/// Error while enumerating CPU kinds
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum CpuKindEnumerationError {
    /// No information about CPU kinds was found
    #[error("no information about CPU kinds was found")]
    Unknown,

    /// An unspecified hwloc error occured
    #[error(transparent)]
    HwlocError(#[from] RawIntError),
}

/// Error while querying a CPU kind from a CPU set
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum CpuKindFromSetError {
    /// CPU set is only partially included in some kind
    ///
    /// i.e. some CPUs in the set belong to a kind, others to other kind(s)
    #[error("CPU set is only partially included in some kind")]
    PartiallyIncluded,

    /// CPU set is not included in any kind, even partially
    ///
    /// i.e. CPU kind info isn't known or CPU set does not cover real CPUs
    #[error("CPU set is not included in any kind, even partially")]
    NotIncluded,

    /// An unspecified hwloc error occured
    #[error(transparent)]
    HwlocError(#[from] RawIntError),
}
