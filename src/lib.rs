#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]

pub mod bitmaps;
pub mod cpu;
pub mod errors;
pub(crate) mod ffi;
pub mod info;
#[cfg(target_os = "linux")]
pub mod linux;
pub mod memory;
pub mod objects;
pub mod path;
pub mod topology;
#[cfg(all(feature = "hwloc-2_5_0", target_os = "windows"))]
pub mod windows;

#[cfg(target_os = "windows")]
/// Thread identifier
pub type ThreadId = windows_sys::Win32::Foundation::HANDLE;
#[cfg(target_os = "windows")]
/// Process identifier
pub type ProcessId = u32;
#[cfg(not(target_os = "windows"))]
/// Thread identifier
pub type ThreadId = libc::pthread_t;
#[cfg(not(target_os = "windows"))]
/// Process identifier
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
// rely on it, it's better for use statements to point to the right place.
#[cfg(not(test))]
pub use topology::Topology;
