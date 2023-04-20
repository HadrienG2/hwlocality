//! Linux-specific helpers

// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__linux.html

#[cfg(doc)]
use crate::cpu::binding::CpuBindingFlags;
use crate::{
    cpu::sets::CpuSet,
    errors::{self, HybridError, RawHwlocError},
    ffi,
    path::{self, PathError},
    topology::Topology,
};
use std::path::Path;

// This file is rustdoc-visible so we must provide a substitute for
// linux-specific libc entities when people run rustdoc on Windows.
#[cfg(target_os = "linux")]
use libc::pid_t;
#[cfg(all(doc, not(target_os = "linux")))]
#[allow(non_camel_case_types)]
struct pid_t;

/// # Linux-specific helpers
///
/// This includes helpers for manipulating Linux kernel cpumap files, and hwloc
/// equivalents of the Linux `sched_setaffinity` and `sched_getaffinity` system
/// calls.
impl Topology {
    /// Bind a thread `tid` on cpus given in `set`
    ///
    /// The behavior is exactly the same as the Linux `sched_setaffinity` system
    /// call, but uses a hwloc cpuset.
    ///
    /// This is equivalent to calling [`bind_process_cpu()`] with the [`THREAD`]
    /// binding flag.
    ///
    /// [`bind_process_cpu()`]: Topology::bind_process_cpu()
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[doc(alias = "hwloc_linux_set_tid_cpubind")]
    pub fn bind_tid_cpu(&self, tid: pid_t, set: &CpuSet) -> Result<(), RawHwlocError> {
        errors::call_hwloc_int_normal("hwloc_linux_set_tid_cpubind", || unsafe {
            ffi::hwloc_linux_set_tid_cpubind(self.as_ptr(), tid, set.as_ptr())
        })
        .map(|_| ())
    }

    /// Current binding of thread `tid`.
    ///
    /// Returns the [`CpuSet`] of PUs which the thread was last bound to.
    ///
    /// The behavior is exactly the same as the Linux `sched_getaffinity` system
    /// call, but uses a hwloc cpuset.
    ///
    /// This is equivalent to calling [`process_cpu_binding()`] with the
    /// [`THREAD`] binding flag.
    ///
    /// [`process_cpu_binding()`]: Topology::process_cpu_binding()
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[doc(alias = "hwloc_linux_get_tid_cpubind")]
    pub fn tid_cpu_binding(&self, tid: pid_t) -> Result<CpuSet, RawHwlocError> {
        let mut set = CpuSet::new();
        errors::call_hwloc_int_normal("hwloc_linux_get_tid_cpubind", || unsafe {
            ffi::hwloc_linux_get_tid_cpubind(self.as_ptr(), tid, set.as_mut_ptr())
        })
        .map(|_| set)
    }

    /// Last physical CPU where thread `tid` ran.
    ///
    /// Indicates the PU which the thread last ran on, as a singleton [`CpuSet`].
    ///
    /// This is equivalent to calling [`last_process_cpu_location()`] with the
    /// [`THREAD`] binding flag.
    ///
    /// [`last_process_cpu_location()`]: Topology::last_process_cpu_location()
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[doc(alias = "hwloc_linux_get_tid_last_cpu_location")]
    pub fn tid_last_cpu_location(&self, tid: pid_t) -> Result<CpuSet, RawHwlocError> {
        let mut set = CpuSet::new();
        errors::call_hwloc_int_normal("hwloc_linux_get_tid_last_cpu_location", || unsafe {
            ffi::hwloc_linux_get_tid_last_cpu_location(self.as_ptr(), tid, set.as_mut_ptr())
        })
        .map(|_| set)
    }

    /// Convert a linux kernel cpumask file path into a hwloc bitmap set.
    ///
    /// Might be used when reading CPU sets from sysfs attributes such as
    /// topology and caches for processors, or local_cpus for devices.
    ///
    /// Note that this function ignores the [HWLOC_FSROOT environment
    /// variable](https://hwloc.readthedocs.io/en/v2.9/envvar.html).
    #[doc(alias = "hwloc_linux_read_path_as_cpumask")]
    pub fn read_path_as_cpumask(
        &self,
        path: impl AsRef<Path>,
    ) -> Result<CpuSet, HybridError<PathError>> {
        let path = path::make_hwloc_path(path)?;
        let mut set = CpuSet::new();
        errors::call_hwloc_int_normal("hwloc_linux_read_path_as_cpumask", || unsafe {
            ffi::hwloc_linux_read_path_as_cpumask(path.borrow(), set.as_mut_ptr())
        })
        .map_err(HybridError::Hwloc)?;
        Ok(set)
    }
}
