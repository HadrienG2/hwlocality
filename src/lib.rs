#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg, doc_cfg_hide))]
#![cfg_attr(docsrs, doc(cfg_hide(doc)))]

pub mod bitmap;
pub mod cpu;
pub mod errors;
pub(crate) mod ffi;
pub mod info;
#[cfg(any(doc, target_os = "linux"))]
mod linux;
pub mod memory;
pub mod object;
pub mod path;
pub mod topology;
#[cfg(any(doc, all(feature = "hwloc-2_5_0", target_os = "windows")))]
mod windows;

use hwlocality_sys::{hwloc_pid_t, hwloc_thread_t};

/// Thread identifier (OS-specific)
///
/// This is `HANDLE` on Windows and `libc::pthread_t` on all other platforms.
pub type ThreadId = hwloc_thread_t;

/// Process identifier (OS-specific)
///
/// This is `u32` on Windows and `libc::pid_t` on all other platforms.
pub type ProcessId = hwloc_pid_t;

/// Indicate at runtime which hwloc API version was used at build time
///
/// This number is updated to `(X<<16)+(Y<<8)+Z` when a new release X.Y.Z
/// actually modifies the API.
#[doc(alias = "hwloc_get_api_version")]
pub fn get_api_version() -> usize {
    ffi::expect_usize(unsafe { ffi::hwloc_get_api_version() })
}

// Disable the alias in test builds to make sure the implementation does not
// rely on it. It's better for use statements to point to the right place.
#[cfg(not(test))]
#[cfg_attr(docsrs, doc(cfg(all())))]
pub use topology::Topology;

/// This module is an implementation detail of [`Sealed`]
mod sealed {
    /// This trait can only be implemented by types inside this crate
    pub trait Sealed {}
}

/// Import of [`Sealed`] that only this crate can use
pub(crate) use sealed::Sealed;
