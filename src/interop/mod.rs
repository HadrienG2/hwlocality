//! Interoperability with other APIs
//!
//! Fundamentally, hwloc is an abstraction layer over OS APIs and a few direct
//! hardware interfaces. Sometimes, hwloc-based software also wants to interact
//! with OS APIs in a different way, and in that case having access to
//! translations of hwloc concepts into the vocabulary of other APIs is useful.
//! This is what the module you're looking at is about.

#[cfg(any(doc, target_os = "linux"))]
pub mod linux;
#[cfg(any(doc, all(feature = "hwloc-2_5_0", target_os = "windows")))]
pub mod windows;
