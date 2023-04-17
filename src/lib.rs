#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg, doc_cfg_hide))]
#![cfg_attr(docsrs, doc(cfg_hide(doc)))]

pub mod bitmaps;
pub mod cpu;
pub mod errors;
pub(crate) mod ffi;
pub mod info;
#[cfg(any(doc, target_os = "linux"))]
mod linux;
pub mod memory;
pub mod objects;
pub mod path;
pub mod topology;
#[cfg(any(doc, all(feature = "hwloc-2_5_0", target_os = "windows")))]
mod windows;

/// Thread identifier (OS-specific)
#[cfg(target_os = "windows")]
#[cfg_attr(docsrs, doc(cfg(doc)))]
pub type ThreadId = windows_sys::Win32::Foundation::HANDLE;

/// Process identifier (OS-specific)
#[cfg(target_os = "windows")]
#[cfg_attr(docsrs, doc(cfg(doc)))]
pub type ProcessId = u32;

/// Thread identifier (OS-specific)
#[cfg(not(target_os = "windows"))]
#[cfg_attr(docsrs, doc(cfg(doc)))]
pub type ThreadId = libc::pthread_t;

/// Process identifier (OS-specific)
#[cfg(not(target_os = "windows"))]
#[cfg_attr(docsrs, doc(cfg(doc)))]
pub type ProcessId = libc::pid_t;

/// Indicate at runtime which hwloc API version was used at build time.
/// This number is updated to (X<<16)+(Y<<8)+Z when a new release X.Y.Z
/// actually modifies the API.
///
/// Users may check for available features at build time using this number
#[doc(alias = "hwloc_get_api_version")]
pub fn get_api_version() -> u32 {
    unsafe { ffi::hwloc_get_api_version() }
}

// Disable the alias in test builds to make sure the implementation does not
// rely on it. It's better for use statements to point to the right place.
#[cfg(not(test))]
#[cfg_attr(docsrs, doc(cfg(doc)))]
pub use topology::Topology;
