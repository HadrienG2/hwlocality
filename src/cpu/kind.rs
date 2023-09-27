//! Kinds of CPU cores
//!
//! This module lets you handle platforms with heterogeneous CPU cores, such as
//! [ARM big.LITTLE](https://fr.wikipedia.org/wiki/Big.LITTLE) and [Intel Adler
//! Lake](https://fr.wikipedia.org/wiki/Alder_Lake).
//!
//! Using it, you can query how many different kinds of CPUs are present on the
//! platform, which kind maps into which OS-exposed logical CPUs, and how these
//! CPU kinds differ from each other (power efficiency, clock speed, etc).
//!
//! Most of this module's functionality is exposed via [methods of the Topology
//! struct](../../topology/struct.Topology.html#kinds-of-cpu-cores). The module
//! itself only hosts type definitions that are related to this functionality.

#[cfg(doc)]
use crate::topology::support::DiscoverySupport;
use crate::{
    cpu::cpuset::CpuSet,
    errors::{self, HybridError, RawHwlocError},
    ffi::{self, LibcString},
    info::TextualInfo,
    topology::{editor::TopologyEditor, Topology},
};
use libc::{EINVAL, ENOENT, EXDEV};
use std::{
    borrow::Borrow,
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
/// sysfs. Efficiency values will range from 0 to the number of CPU kinds minus
/// one.
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
/// unknown efficiency (`None`), and they are not ordered in any specific way.
///
/// The kind that describes a given CPU set (if any, and not partially) may also
/// be queried with [`cpu_kind_from_set()`].
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
    /// - [`CpuKindsUnknown`] if no information about CPU kinds was found
    #[doc(alias = "hwloc_cpukinds_get_nr")]
    pub fn num_cpu_kinds(&self) -> Result<NonZeroUsize, CpuKindsUnknown> {
        let count = errors::call_hwloc_int_normal("hwloc_cpukinds_get_nr", || unsafe {
            hwlocality_sys::hwloc_cpukinds_get_nr(self.as_ptr(), 0)
        })
        .expect("All known failure cases are prevented by API design");
        NonZeroUsize::new(ffi::expect_usize(count)).ok_or(CpuKindsUnknown)
    }

    /// Enumerate CPU kinds, from least efficient efficient to most efficient
    ///
    /// For each CPU kind, provide the [`CpuSet`] of PUs belonging to that kind,
    /// how efficient this CPU kind is (if CPU kind efficiencies are known) and
    /// [other things we know about
    /// it](https://hwloc.readthedocs.io/en/v2.9/topoattrs.html#topoattrs_cpukinds).
    ///
    /// # Errors
    ///
    /// - [`CpuKindsUnknown`] if no information about CPU kinds was found
    #[doc(alias = "hwloc_cpukinds_get_info")]
    pub fn cpu_kinds(
        &self,
    ) -> Result<
        impl DoubleEndedIterator<Item = (CpuSet, Option<CpuEfficiency>, &[TextualInfo])>
            + Clone
            + ExactSizeIterator
            + FusedIterator,
        CpuKindsUnknown,
    > {
        // Iterate over all CPU kinds
        let num_cpu_kinds = usize::from(self.num_cpu_kinds()?);
        Ok((0..num_cpu_kinds).map(move |kind_index| self.cpu_kind(kind_index)))
    }

    /// Tell what we know about a CPU kind
    ///
    /// This internal method should only be called on CPU kind indices which are
    /// known to be valid by the high-level APIs.
    fn cpu_kind(&self, kind_index: usize) -> (CpuSet, Option<CpuEfficiency>, &[TextualInfo]) {
        // Let hwloc tell us everything it knows about this CPU kind
        let kind_index =
            c_uint::try_from(kind_index).expect("Should not happen if API contract is honored");
        let mut cpuset = CpuSet::new();
        let mut efficiency = c_int::MAX;
        let mut nr_infos: c_uint = 0;
        let mut infos = ptr::null_mut();
        errors::call_hwloc_int_normal("hwloc_cpukinds_get_info", || unsafe {
            hwlocality_sys::hwloc_cpukinds_get_info(
                self.as_ptr(),
                kind_index,
                cpuset.as_mut_ptr(),
                &mut efficiency,
                &mut nr_infos,
                &mut infos,
                0,
            )
        })
        .expect("All documented failure cases are prevented by API design");

        // Post-process hwloc results, then emit them
        let efficiency = match efficiency {
            -1 => None,
            other => {
                let positive = c_uint::try_from(other).expect("Unexpected CpuEfficiency value");
                Some(ffi::expect_usize(positive))
            }
        };
        assert!(
            !infos.is_null(),
            "Got null infos pointer from hwloc_cpukinds_get_info"
        );
        let infos = unsafe { std::slice::from_raw_parts(infos, ffi::expect_usize(nr_infos)) };
        (cpuset, efficiency, infos)
    }

    /// Query information about the CPU kind that contains CPUs listed in `set`
    ///
    /// # Errors
    ///
    /// - [`PartiallyIncluded`] if `set` is only partially included in some kind
    ///   (i.e. some CPUs in the set belong to a kind, others to other kind(s))
    /// - [`NotIncluded`] if `set` is not included in any kind, even partially
    ///   (i.e. CPU kind info isn't known or CPU set does not cover real CPUs)
    /// - [`InvalidSet`] if the CPU set is considered invalid for another reason
    ///
    /// [`InvalidSet`]: CpuKindFromSetError::InvalidSet
    /// [`NotIncluded`]: CpuKindFromSetError::NotIncluded
    /// [`PartiallyIncluded`]: CpuKindFromSetError::PartiallyIncluded
    #[doc(alias = "hwloc_cpukinds_get_by_cpuset")]
    pub fn cpu_kind_from_set(
        &self,
        set: impl Borrow<CpuSet>,
    ) -> Result<(CpuSet, Option<CpuEfficiency>, &[TextualInfo]), CpuKindFromSetError> {
        let result = errors::call_hwloc_int_normal("hwloc_cpukinds_get_by_cpuset", || unsafe {
            hwlocality_sys::hwloc_cpukinds_get_by_cpuset(self.as_ptr(), set.borrow().as_ptr(), 0)
        });
        let kind_index = match result {
            Ok(idx) => ffi::expect_usize(idx),
            Err(
                raw_error @ RawHwlocError {
                    api: _,
                    errno: Some(errno),
                },
            ) => match errno.0 {
                EXDEV => return Err(CpuKindFromSetError::PartiallyIncluded),
                ENOENT => return Err(CpuKindFromSetError::NotIncluded),
                EINVAL => return Err(CpuKindFromSetError::InvalidSet),
                _ => unreachable!("Unexpected hwloc error: {raw_error}"),
            },
            Err(raw_error) => unreachable!("Unexpected hwloc error: {raw_error}"),
        };
        Ok(self.cpu_kind(kind_index))
    }
}

/// # Kinds of CPU cores
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpukinds.html
impl<'topology> TopologyEditor<'topology> {
    /// Register a kind of CPU in the topology.
    ///
    /// Mark the PUs listed in `cpuset` as being of the same kind with respect
    /// to the given attributes.
    ///
    /// `forced_efficiency` should be `None` if unknown. Otherwise it is an
    /// abstracted efficiency value to enforce the ranking of all kinds if all
    /// of them have valid (and different) efficiencies.
    ///
    /// Note that the efficiency reported later by [`Topology::cpu_kinds()`] may
    /// differ because hwloc will scale efficiency values down to between 0 and
    /// the number of kinds minus 1.
    ///
    /// If `cpuset` overlaps with some existing kinds, those might get modified
    /// or split. For instance if existing kind A contains PUs 0 and 1, and one
    /// registers another kind for PU 1 and 2, there will be 3 resulting kinds:
    /// existing kind A is restricted to only PU 0; new kind B contains only PU
    /// 1 and combines information from A and from the newly-registered kind;
    /// new kind C contains only PU 2 and only gets information from the
    /// newly-registered kind.
    ///
    /// # Errors
    ///
    /// - [`InfoContainsNul`] if a provided info's key or value contains NUL chars
    /// - [`TooManyInfos`] if the number of specified (key, value) info tuples
    ///   exceeds hwloc's `c_uint::MAX` limit.
    ///
    /// [`InfoContainsNul`]: CpuKindRegisterError::InfoContainsNul
    /// [`TooManyInfos`]: CpuKindRegisterError::TooManyInfos
    #[doc(alias = "hwloc_cpukinds_register")]
    pub fn register_cpu_kind<'infos>(
        &mut self,
        cpuset: impl Borrow<CpuSet>,
        forced_efficiency: Option<CpuEfficiency>,
        infos: impl IntoIterator<Item = (&'infos str, &'infos str)>,
    ) -> Result<(), HybridError<CpuKindRegisterError>> {
        let forced_efficiency = forced_efficiency
            .map(|eff| c_int::try_from(eff).unwrap_or(c_int::MAX))
            .unwrap_or(-1);

        let input_infos = infos.into_iter();
        let mut infos = Vec::new();
        let mut infos_ptrs = Vec::new();
        if let Some(infos_len) = input_infos.size_hint().1 {
            infos.reserve(infos_len);
            infos_ptrs.reserve(infos_len);
        }
        for (name, value) in input_infos {
            let new_string =
                |s: &str| LibcString::new(s).map_err(|_| CpuKindRegisterError::InfoContainsNul);
            let (name, value) = (new_string(name)?, new_string(value)?);
            infos_ptrs.push(TextualInfo::new(&name, &value));
            infos.push((name, value));
        }
        let num_infos =
            c_uint::try_from(infos_ptrs.len()).map_err(|_| CpuKindRegisterError::TooManyInfos)?;

        errors::call_hwloc_int_normal("hwloc_cpukinds_register", || unsafe {
            hwlocality_sys::hwloc_cpukinds_register(
                self.topology_mut_ptr(),
                cpuset.borrow().as_ptr(),
                forced_efficiency,
                num_infos,
                infos_ptrs.as_ptr(),
                0,
            )
        })
        .map(std::mem::drop)
        .map_err(HybridError::Hwloc)
    }
}

/// Efficiency of a CPU kind
///
/// A higher efficiency value means greater intrinsic performance (and possibly
/// less performance/power efficiency).
///
/// Efficiency ranges from 0 to the number of CPU kinds minus one.
pub type CpuEfficiency = usize;

/// No information about CPU kinds was found
#[derive(Copy, Clone, Debug, Default, Error, Eq, Hash, PartialEq)]
#[error("no information about CPU kinds was found")]
pub struct CpuKindsUnknown;

/// Error while querying a CPU kind from a CPU set
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum CpuKindFromSetError {
    /// CPU set is only partially included in some kind
    ///
    /// i.e. some CPUs in the set belong to one kind, other CPUs belong to one
    /// or more other kinds.
    #[error("CPU set is only partially included in some kind")]
    PartiallyIncluded,

    /// CPU set is not included in any kind, even partially
    ///
    /// i.e. CPU kind info isn't known or this CPU set does not cover real CPUs.
    #[error("CPU set is not included in any kind, even partially")]
    NotIncluded,

    /// CPU set is considered invalid by hwloc for another reason
    #[error("CPU set is invalid")]
    InvalidSet,
}

/// Error while registering a new CPU kind
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum CpuKindRegisterError {
    /// One of the CPU kind's textual info strings contains the NUL char
    #[error("one of the CPU kind's textual info strings contains the NUL char")]
    InfoContainsNul,

    /// There are too many CPU kind textual info (key, value) pairs for hwloc
    #[error("there are too many CPU kind textual info (key, value) pairs for hwloc")]
    TooManyInfos,
}
