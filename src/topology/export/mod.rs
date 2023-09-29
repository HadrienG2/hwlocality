//! Exporting topologies to textual data
//!
//! An hwloc [`Topology`] can be saved to various textual formats. The resulting
//! text files can then be re-imported later on, without going through the full
//! hardware probing process again.
//!
//! Two formats are currently supported:
//!
//! - Synthetic topologies are a very simple textual representation that may only
//!   model certain topologies (they must be symmetric among other things, i.e.
//!   all CPU cores should be equal), and only some aspects of them (e.g. no I/O
//!   devices), but does so extremely concisely.
//! - XML export can, in principle, handle every single topology that hwloc can
//!   probe, but does so at the cost of extra complexity.

pub mod synthetic;
pub mod xml;

#[cfg(doc)]
use super::Topology;
