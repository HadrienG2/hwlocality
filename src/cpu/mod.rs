//! CPU-specific functionality

pub mod binding;
pub mod cache;
pub mod cpuset;
#[cfg(feature = "hwloc-2_4_0")]
pub mod kind;
