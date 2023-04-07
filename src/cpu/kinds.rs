//! Kinds of CPU cores

// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpukinds.html

#[cfg(doc)]
use crate::support::DiscoverySupport;
use crate::{
    bitmaps::CpuSet,
    errors::{self, RawIntError},
    ffi,
    info::TextualInfo,
    Topology,
};
use libc::{ENOENT, EXDEV};
use std::{
    ffi::{c_int, c_uint},
    iter::FusedIterator,
    num::NonZeroUsize,
    ptr,
};
use thiserror::Error;

/// # Kinds of CPU cores
///
/// Platforms with heterogeneous CPUs may have some cores with different
/// features or frequencies. This API exposes identical PUs in sets called CPU
/// kinds. Each PU of the topology may only be in a single kind.
///
/// The number of kinds may be obtained with [`num_cpu_kinds()`]. If the
/// platform is homogeneous, there may be a single kind with all PUs. If the
/// platform or operating system does not expose any information about CPU
/// cores, there may be no kind at all.
///
/// Information about CPU kinds can also be enumerated using [`cpu_kinds()`].
/// For each CPU kind, an abstracted efficiency value is provided, along with
/// [info attributes](https://hwloc.readthedocs.io/en/v2.9/topoattrs.html#topoattrs_cpukinds)
/// such as "CoreType" or "FrequencyMaxMHz".
///
/// A higher efficiency value means greater intrinsic performance (and possibly
/// less performance/power efficiency). Kinds with lower efficiency values are
/// ranked first: the first CPU kind yielded by [`cpu_kinds()`] describes CPUs
/// with lower performance but higher energy-efficiency. Later CPU kinds would
/// rather describe power-hungry high-performance cores.
///
/// When available, efficiency values are gathered from the operating system. If
/// so, the [`DiscoverySupport::cpukind_efficiency()`] feature support flag
/// will be set. This is currently available on Windows 10, Mac OS X
/// (Darwin), and on some Linux platforms where core "capacity" is exposed in
/// sysfs.
///
/// If the operating system does not expose core efficiencies natively, hwloc
/// tries to compute efficiencies by comparing CPU kinds using frequencies
/// (on ARM), or core types and frequencies (on other architectures). The
/// environment variable `HWLOC_CPUKINDS_RANKING` may be used to change this
/// heuristics, see [Environment
/// Variables](https://hwloc.readthedocs.io/en/v2.9/envvar.html).
///
/// If hwloc fails to rank any kind, for instance because the operating system
/// does not expose efficiencies and core frequencies, all kinds will have an
/// unknown efficiency (None), and they are not ordered in any specific way.
///
/// The kind that describes a given CPU set (if any, and not partially) may also
/// be obtained with [`cpu_kind_from_set()`].
///
/// [`cpu_kind_from_set()`]: Topology::cpu_kind_from_set()
/// [`cpu_kinds()`]: Topology::cpu_kinds()
/// [`num_cpu_kinds()`]: Topology::num_cpu_kinds()
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpukinds.html
impl Topology {
    /// Number of different kinds of CPU cores in the topology
    ///
    /// # Errors
    ///
    /// - [`Unknown`] if no information about CPU kinds was found
    ///
    /// [`Unknown`]: CpuKindEnumerationError::Unknown
    #[doc(alias = "hwloc_cpukinds_get_nr")]
    pub fn num_cpu_kinds(&self) -> Result<NonZeroUsize, CpuKindEnumerationError> {
        let count = errors::call_hwloc_int("hwloc_cpukinds_get_nr", || unsafe {
            ffi::hwloc_cpukinds_get_nr(self.as_ptr(), 0)
        })?;
        NonZeroUsize::new(usize::try_from(count).expect("Unexpectedly high number of CPU kinds"))
            .ok_or(CpuKindEnumerationError::Unknown)
    }

    /// Enumerate CPU kinds, from least efficient efficient to most efficient
    ///
    /// For each CPU kind, provide the [`CpuSet`] of PUs belonging to that kind,
    /// how efficient this CPU kind is (if CPU kind efficiencies are known) and
    /// other things we know about it in textual form.
    ///
    /// # Errors
    ///
    /// - [`Unknown`] if no information about CPU kinds was found
    ///
    /// [`Unknown`]: CpuKindEnumerationError::Unknown
    #[doc(alias = "hwloc_cpukinds_get_info")]
    pub fn cpu_kinds(
        &self,
    ) -> Result<
        impl Iterator<Item = Result<(CpuSet, Option<CpuEfficiency>, &[TextualInfo]), RawIntError>>
            + Clone
            + DoubleEndedIterator
            + ExactSizeIterator
            + FusedIterator,
        CpuKindEnumerationError,
    > {
        // Iterate over all CPU kinds
        let num_cpu_kinds = usize::from(self.num_cpu_kinds()?);
        Ok((0..num_cpu_kinds).map(move |kind_index| self.cpu_kind(kind_index)))
    }

    /// Tell what we know about a CPU kind
    fn cpu_kind(
        &self,
        kind_index: usize,
    ) -> Result<(CpuSet, Option<CpuEfficiency>, &[TextualInfo]), RawIntError> {
        // Let hwloc tell us everything it knows about this CPU kind
        let kind_index = kind_index as c_uint;
        let mut cpuset = CpuSet::new();
        let mut efficiency = c_int::MAX;
        let mut nr_infos = 0 as c_uint;
        let mut infos = ptr::null_mut();
        errors::call_hwloc_int("hwloc_cpukinds_get_info", || unsafe {
            ffi::hwloc_cpukinds_get_info(
                self.as_ptr(),
                kind_index,
                cpuset.as_mut_ptr(),
                &mut efficiency,
                &mut nr_infos,
                &mut infos,
                0,
            )
        })?;

        // Post-process hwloc results, then emit them
        let efficiency = match efficiency {
            -1 => None,
            positive => Some(usize::try_from(positive).expect("Unexpected CpuEfficiency value")),
        };
        assert!(
            !infos.is_null(),
            "Got null infos pointer from hwloc_cpukinds_get_info"
        );
        let infos = unsafe {
            std::slice::from_raw_parts(
                infos,
                usize::try_from(nr_infos).expect("Unexpected info attribute count"),
            )
        };
        Ok((cpuset, efficiency, infos))
    }

    /// Query information about the CPU kind that contains CPUs listed in `set`
    ///
    /// # Errors
    ///
    /// - [`PartiallyIncluded`] if `set` is only partially included in some kind
    ///   (i.e. some CPUs in the set belong to a kind, others to other kind(s))
    /// - [`NotIncluded`] if `set` is not included in any kind, even partially
    ///   (i.e. CPU kind info isn't known or CPU set does not cover real CPUs)
    ///
    /// [`NotIncluded`]: CpuKindFromSetError::NotIncluded
    /// [`PartiallyIncluded`]: CpuKindFromSetError::PartiallyIncluded
    #[doc(alias = "hwloc_cpukinds_get_by_cpuset")]
    pub fn cpu_kind_from_set(
        &self,
        set: &CpuSet,
    ) -> Result<(CpuSet, Option<CpuEfficiency>, &[TextualInfo]), CpuKindFromSetError> {
        let result = errors::call_hwloc_int("hwloc_cpukinds_get_by_cpuset", || unsafe {
            ffi::hwloc_cpukinds_get_by_cpuset(self.as_ptr(), set.as_ptr(), 0)
        });
        let kind_index = match result {
            Err(
                raw_error @ RawIntError::Errno {
                    api: _,
                    errno: Some(errno),
                },
            ) => match errno.0 {
                EXDEV => return Err(CpuKindFromSetError::PartiallyIncluded),
                ENOENT => return Err(CpuKindFromSetError::NotIncluded),
                _ => return Err(CpuKindFromSetError::from(raw_error)),
            },
            other => usize::try_from(other?).expect("Unexpectedly high CPU kind index"),
        };
        let output = self.cpu_kind(kind_index)?;
        Ok(output)
    }
}

/// Efficiency of a CPU kind
///
/// A higher efficiency value means greater intrinsic performance (and possibly
/// less performance/power efficiency).
///
/// Efficiency ranges from 0 to the number of CPU kinds minus one.
pub type CpuEfficiency = usize;

/// Error while enumerating CPU kinds
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum CpuKindEnumerationError {
    /// No information about CPU kinds was found
    #[error("no information about CPU kinds was found")]
    Unknown,

    /// An unspecified hwloc error occured
    #[error(transparent)]
    HwlocError(#[from] RawIntError),
}

/// Error while querying a CPU kind from a CPU set
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum CpuKindFromSetError {
    /// CPU set is only partially included in some kind
    ///
    /// i.e. some CPUs in the set belong to a kind, others to other kind(s)
    #[error("CPU set is only partially included in some kind")]
    PartiallyIncluded,

    /// CPU set is not included in any kind, even partially
    ///
    /// i.e. CPU kind info isn't known or CPU set does not cover real CPUs
    #[error("CPU set is not included in any kind, even partially")]
    NotIncluded,

    /// An unspecified hwloc error occured
    #[error(transparent)]
    HwlocError(#[from] RawIntError),
}
