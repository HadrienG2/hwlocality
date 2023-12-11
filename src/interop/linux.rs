//! Linux-specific helpers

#[cfg(doc)]
use crate::cpu::binding::CpuBindingFlags;
use crate::{
    cpu::cpuset::CpuSet,
    errors::{self, HybridError, RawHwlocError},
    path::{self, PathError},
    topology::Topology,
};
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::{ops::Deref, path::Path};

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
//
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__linux.html
impl Topology {
    /// Bind a thread `tid` on cpus given in `set`
    ///
    /// `set` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`.
    ///
    /// The behavior is exactly the same as the Linux `sched_setaffinity` system
    /// call, but uses a hwloc [`CpuSet`].
    ///
    /// This is equivalent to calling [`bind_process_cpu()`] with the [`THREAD`]
    /// binding flag.
    ///
    /// [`bind_process_cpu()`]: Topology::bind_process_cpu()
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_linux_set_tid_cpubind")]
    pub fn bind_tid_cpu(
        &self,
        tid: pid_t,
        set: impl Deref<Target = CpuSet>,
    ) -> Result<(), RawHwlocError> {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized(self_: &Topology, tid: pid_t, set: &CpuSet) -> Result<(), RawHwlocError> {
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - Bitmap is trusted to contain a valid ptr (type invariant)
            //         - hwloc ops are trusted not to modify *const parameters
            //         - TID cannot be validated (think TOCTOU), but hwloc should be
            //           able to handle an invalid TID
            errors::call_hwloc_int_normal("hwloc_linux_set_tid_cpubind", || unsafe {
                hwlocality_sys::hwloc_linux_set_tid_cpubind(self_.as_ptr(), tid, set.as_ptr())
            })
            .map(std::mem::drop)
        }
        polymorphized(self, tid, &set)
    }

    /// Current binding of thread `tid`.
    ///
    /// Returns the [`CpuSet`] of PUs which the thread was last bound to.
    ///
    /// The behavior is exactly the same as the Linux `sched_getaffinity` system
    /// call, but uses a hwloc [`CpuSet`].
    ///
    /// This is equivalent to calling [`process_cpu_binding()`] with the
    /// [`THREAD`] binding flag.
    ///
    /// [`process_cpu_binding()`]: Topology::process_cpu_binding()
    /// [`THREAD`]: CpuBindingFlags::THREAD
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_linux_get_tid_cpubind")]
    pub fn tid_cpu_binding(&self, tid: pid_t) -> Result<CpuSet, RawHwlocError> {
        let mut set = CpuSet::new();
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - Bitmap is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted not to modify *const parameters
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - TID cannot be validated (think TOCTOU), but hwloc should be
        //           able to handle an invalid TID
        errors::call_hwloc_int_normal("hwloc_linux_get_tid_cpubind", || unsafe {
            hwlocality_sys::hwloc_linux_get_tid_cpubind(self.as_ptr(), tid, set.as_mut_ptr())
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
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_linux_get_tid_last_cpu_location")]
    pub fn tid_last_cpu_location(&self, tid: pid_t) -> Result<CpuSet, RawHwlocError> {
        let mut set = CpuSet::new();
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - Bitmap is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted not to modify *const parameters
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - TID cannot be validated (think TOCTOU), but hwloc should be
        //           able to handle an invalid TID
        errors::call_hwloc_int_normal("hwloc_linux_get_tid_last_cpu_location", || unsafe {
            hwlocality_sys::hwloc_linux_get_tid_last_cpu_location(
                self.as_ptr(),
                tid,
                set.as_mut_ptr(),
            )
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
    ///
    /// # Errors
    ///
    /// - [`ContainsNul`] if `path` contains NUL chars.
    /// - [`NotUnicode`] if `path` contains non-Unicode data
    ///
    /// # Example
    ///
    #[cfg_attr(target_os = "linux", doc = "```rust")]
    #[cfg_attr(not(target_os = "linux"), doc = "```rust,ignore")]
    /// # use hwlocality::{topology::Topology, object::types::ObjectType};
    /// #
    /// # let topology = Topology::test_instance();
    /// #
    /// use eyre::eyre;
    ///
    /// // Read cpuset of first core via Linux sysfs
    /// let core_set = topology
    ///     .read_path_as_cpumask("/sys/devices/system/cpu/cpu0/topology/core_cpus")?;
    ///
    /// // Check that the hwloc version is consistent
    /// assert_eq!(
    ///     core_set,
    ///     topology
    ///         .objects_with_type(ObjectType::Core)
    ///         .next()
    ///         .ok_or_else(|| eyre!("Linux systesm should have CPU cores"))?
    ///         .cpuset()
    ///         .ok_or_else(|| eyre!("CPU cores should have cpusets"))?
    /// );
    /// #
    /// # Ok::<(), eyre::Report>(())
    /// ```
    ///
    /// [`ContainsNul`]: PathError::ContainsNul
    /// [`NotUnicode`]: PathError::NotUnicode
    #[doc(alias = "hwloc_linux_read_path_as_cpumask")]
    pub fn read_path_as_cpumask(
        &self,
        path: impl AsRef<Path>,
    ) -> Result<CpuSet, HybridError<PathError>> {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized(path: &Path) -> Result<CpuSet, HybridError<PathError>> {
            let path = path::make_hwloc_path(path)?;
            let mut set = CpuSet::new();
            // SAFETY: - Path is trusted to contain a valid C string (type invariant)
            //         - Bitmap is trusted to contain a valid ptr (type invariant)
            //         - hwloc ops are trusted not to modify *const parameters
            //         - hwloc ops are trusted to keep *mut parameters in a
            //           valid state unless stated otherwise
            errors::call_hwloc_int_normal("hwloc_linux_read_path_as_cpumask", || unsafe {
                hwlocality_sys::hwloc_linux_read_path_as_cpumask(path.borrow(), set.as_mut_ptr())
            })
            .map_err(HybridError::Hwloc)?;
            Ok(set)
        }
        polymorphized(path.as_ref())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::object::types::ObjectType;
    #[allow(unused)]
    use similar_asserts::assert_eq;

    #[test]
    fn read_path_as_cpumask() {
        let topology = Topology::test_instance();

        // Read cpuset of first core via Linux sysfs
        let core_set = topology
            .read_path_as_cpumask("/sys/devices/system/cpu/cpu0/topology/core_cpus")
            .unwrap();

        // Compare with hwloc result
        assert_eq!(
            core_set,
            topology
                .objects_with_type(ObjectType::Core)
                .next()
                .unwrap()
                .cpuset()
                .unwrap()
        );
    }
}
