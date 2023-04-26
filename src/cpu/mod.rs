//! CPU management

pub mod binding;
pub mod caches;
pub mod cpusets;
#[cfg(feature = "hwloc-2_4_0")]
pub mod kinds;
