//! Memory-specific functionality
//!
//! Most of this module's functionality is exposed via methods of the
//! [`Topology`] struct. The module itself only hosts type definitions that are
//! related to this functionality.

#[cfg(feature = "hwloc-2_3_0")]
pub mod attribute;
pub mod binding;
pub mod nodeset;
