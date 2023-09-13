//! CPU-specific functionality
//!
//! Most of this module's functionality is exposed via methods of the
//! [`Topology`] struct. The module itself only hosts type definitions that are
//! related to this functionality.

pub mod binding;
pub mod cache;
pub mod cpuset;
#[cfg(feature = "hwloc-2_4_0")]
pub mod kind;

#[cfg(doc)]
use crate::topology::Topology;
