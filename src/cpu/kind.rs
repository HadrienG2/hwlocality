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
    errors::{self},
    ffi::{int, string::LibcString, transparent::AsNewtype},
    info::TextualInfo,
    topology::{editor::TopologyEditor, Topology},
};
use derive_more::Display;
use hwlocality_sys::hwloc_info_s;
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::{
    ffi::{c_int, c_uint},
    iter::FusedIterator,
    num::NonZeroUsize,
    ops::Deref,
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
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpukinds.html
impl Topology {
    /// Number of different kinds of CPU cores in the topology
    ///
    /// # Errors
    ///
    /// - [`NoData`] if no information about CPU kinds was found
    #[doc(alias = "hwloc_cpukinds_get_nr")]
    pub fn num_cpu_kinds(&self) -> Result<NonZeroUsize, NoData> {
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted not to modify *const parameters
        //         - Per documentation, flags should be zero
        let count = errors::call_hwloc_positive_or_minus1("hwloc_cpukinds_get_nr", || unsafe {
            hwlocality_sys::hwloc_cpukinds_get_nr(self.as_ptr(), 0)
        })
        .expect("All known failure cases are prevented by API design");
        NonZeroUsize::new(int::expect_usize(count)).ok_or(NoData)
    }

    /// Enumerate CPU kinds, sorted by decreasing power-efficiency
    ///
    /// The first listed CPU kind is most power-efficient, but has the weakest
    /// peak performance. Subsequent CPU kinds will process computations faster,
    /// but at the expense of consuming more power.
    ///
    /// For each CPU kind, we provide the [`CpuSet`] of PUs belonging to that
    /// kind, how efficient this CPU kind is (if CPU kind efficiencies are
    /// known) and [other things we know about
    /// it](https://hwloc.readthedocs.io/en/v2.9/topoattrs.html#topoattrs_cpukinds).
    ///
    /// # Errors
    ///
    /// - [`NoData`] if no information about CPU kinds was found
    #[doc(alias = "hwloc_cpukinds_get_info")]
    pub fn cpu_kinds(
        &self,
    ) -> Result<
        impl DoubleEndedIterator<Item = CpuKind<'_>> + Clone + ExactSizeIterator + FusedIterator,
        NoData,
    > {
        // Iterate over all CPU kinds
        let num_cpu_kinds = usize::from(self.num_cpu_kinds()?);
        // SAFETY: This only calls cpu_kind() with valid kind_index values
        Ok((0..num_cpu_kinds).map(move |kind_index| unsafe { self.cpu_kind(kind_index) }))
    }

    /// Tell what we know about a CPU kind
    ///
    /// # Safety
    ///
    /// This internal method should only be called on CPU kind indices which are
    /// known to be valid by the high-level APIs.
    unsafe fn cpu_kind(&self, kind_index: usize) -> CpuKind<'_> {
        // Let hwloc tell us everything it knows about this CPU kind
        let kind_index =
            c_uint::try_from(kind_index).expect("Should not happen if API contract is honored");
        let mut cpuset = CpuSet::new();
        let mut efficiency = c_int::MIN;
        let mut nr_infos: c_uint = 0;
        let mut infos = ptr::null_mut();
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - Bitmap is trusted to contain a valid ptr (type invariant)
        //         - hwloc ops are trusted not to modify *const parameters
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - Per documentation, efficiency, nr_infos and infos are
        //           pure out parameters that hwloc does not read
        //         - Per documentation, flags should be zero
        errors::call_hwloc_zero_or_minus1("hwloc_cpukinds_get_info", || unsafe {
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
                Some(int::expect_usize(positive))
            }
        };
        let infos = if infos.is_null() {
            assert_eq!(
                nr_infos, 0,
                "hwloc pretended to yield {nr_infos} infos but provided a null infos pointer"
            );
            &[]
        } else {
            #[allow(clippy::missing_docs_in_private_items)]
            type Element = TextualInfo;
            let infos_len = int::expect_usize(nr_infos);
            int::assert_slice_len::<Element>(infos_len);
            // SAFETY: - Per hwloc API contract, infos and nr_infos should be
            //           valid and point to valid state if the function returned
            //           successfully
            //         - We trust hwloc not to modify infos' target in a manner
            //           that violates Rust aliasing rules, as long as we honor
            //           these rules ourselves
            //         - Total size should not wrap for any valid allocation
            //         - infos_len was checked to fit Rust slice limits above
            //         - AsNewtype is trusted to be implemented correctly
            unsafe { std::slice::from_raw_parts::<Element>(infos.as_newtype(), infos_len) }
        };
        CpuKind {
            cpuset,
            efficiency,
            infos,
        }
    }

    /// Query information about the CPU kind that contains CPUs listed in `set`
    ///
    /// `set` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`.
    ///
    /// # Errors
    ///
    /// - [`PartiallyIncluded`] if `set` is only partially included in some kind
    ///   (i.e. some CPUs in the set belong to a kind, others to other kind(s))
    /// - [`NotIncluded`] if `set` is not included in any kind, even partially
    ///   (i.e. CPU kind info isn't known or CPU set does not cover real CPUs)
    ///
    /// [`NotIncluded`]: FromSetProblem::NotIncluded
    /// [`PartiallyIncluded`]: FromSetProblem::PartiallyIncluded
    #[doc(alias = "hwloc_cpukinds_get_by_cpuset")]
    pub fn cpu_kind_from_set(
        &self,
        set: impl Deref<Target = CpuSet>,
    ) -> Result<CpuKind<'_>, FromSetError> {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized<'self_>(
            self_: &'self_ Topology,
            set: &CpuSet,
        ) -> Result<CpuKind<'self_>, FromSetError> {
            // This reimplements hwloc_cpukinds_get_by_cpuset because it's very
            // little code and doing it ourselves allows us to work around the
            // pitfalls of relying on errno availability on Windows
            let error = |problem| Err(FromSetError(set.clone(), problem));
            match self_.cpu_kinds() {
                Ok(kinds) => {
                    // Find relevant CPU kind, checking if unsuccessful matches
                    // are at least partial matches
                    let mut intersects = false;
                    for kind in kinds {
                        if kind.cpuset.includes(set) {
                            return Ok(kind);
                        } else if kind.cpuset.intersects(set) {
                            intersects = true;
                        }
                    }

                    // Report lack of matches accordingly
                    if intersects {
                        error(FromSetProblem::PartiallyIncluded)
                    } else {
                        error(FromSetProblem::NotIncluded)
                    }
                }
                Err(NoData) => error(FromSetProblem::NotIncluded),
            }
        }
        polymorphized(self, &set)
    }
}

/// Kind of CPU core
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CpuKind<'topology> {
    /// CPUs that use this kind of core
    pub cpuset: CpuSet,

    /// CPU efficiency metric, if known
    ///
    /// A lower metric value means that the CPU is expected to consume less
    /// power, at the cost of possibly being less performant.
    pub efficiency: Option<CpuEfficiency>,

    /// Textual information
    pub infos: &'topology [TextualInfo],
}

/// # Kinds of CPU cores
//
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpukinds.html
impl TopologyEditor<'_> {
    /// Register a kind of CPU in the topology.
    ///
    /// Mark the PUs listed in `cpuset` as being of the same kind with respect
    /// to the given attributes.
    ///
    /// `cpuset` can be a `&'_ CpuSet` or a `BitmapRef<'_, CpuSet>`, but it must
    /// not be empty, and should only contain CPUs from the topology cpuset.
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
    /// - [`ExcessiveEfficiency`] if `forced_efficiency` exceeds hwloc's
    ///   [`c_int::MAX`] limit.
    /// - [`InfoContainsNul`] if a provided info's key or value contains NUL chars
    /// - [`NoCPUs`] if `cpuset` is empty.
    /// - [`TooManyInfos`] if the number of specified (key, value) info tuples
    ///   exceeds hwloc's [`c_uint::MAX`] limit.
    /// - [`UnknownCPUs`] if some CPUs from `cpuset` do not belong to this
    ///   topology.
    ///
    /// [`ExcessiveEfficiency`]: RegisterError::ExcessiveEfficiency
    /// [`InfoContainsNul`]: RegisterError::InfoContainsNul
    /// [`NoCPUs`]: RegisterError::NoCPUs
    /// [`TooManyInfos`]: RegisterError::TooManyInfos
    /// [`UnknownCPUs`]: RegisterError::UnknownCPUs
    #[allow(clippy::collection_is_never_read)]
    #[doc(alias = "hwloc_cpukinds_register")]
    pub fn register_cpu_kind<'infos>(
        &mut self,
        cpuset: impl Deref<Target = CpuSet>,
        forced_efficiency: Option<CpuEfficiency>,
        infos: impl IntoIterator<Item = (&'infos str, &'infos str)>,
    ) -> Result<(), RegisterError> {
        /// Polymorphized version of this function (avoids generics code bloat)
        ///
        /// # Safety
        ///
        /// The inner pointers of `raw_infos` must target valid NUL-terminated C
        /// strings?
        unsafe fn polymorphized(
            self_: &mut TopologyEditor<'_>,
            cpuset: &CpuSet,
            forced_efficiency: Option<CpuEfficiency>,
            raw_infos: Vec<hwloc_info_s>,
        ) -> Result<(), RegisterError> {
            // Check if the requested cpuset is empty
            if cpuset.is_empty() {
                return Err(RegisterError::NoCPUs);
            }

            // Check if the requested cpuset is part of the topology
            let complete_cpuset = self_.topology().complete_cpuset();
            if !complete_cpuset.includes(cpuset) {
                return Err(RegisterError::UnknownCPUs(cpuset - complete_cpuset));
            }

            // Translate forced_efficiency into hwloc's preferred format
            let forced_efficiency = if let Some(eff) = forced_efficiency {
                c_int::try_from(eff).map_err(|_| RegisterError::ExcessiveEfficiency(eff))?
            } else {
                -1
            };

            // Translate number of infos into hwloc's preferred format
            let infos_ptr = raw_infos.as_ptr();
            let num_infos =
                c_uint::try_from(raw_infos.len()).map_err(|_| RegisterError::TooManyInfos)?;

            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - Bitmap is trusted to contain a valid ptr (type invariant)
            //         - hwloc ops are trusted not to modify *const parameters
            //         - hwloc ops are trusted to keep *mut parameters in a
            //           valid state unless stated otherwise
            //         - Above logic enforces that forced_efficiency be >= -1,
            //           as hwloc demands
            //         - num_infos and infos_ptr originate from the same slice,
            //           so they should be valid and in sync
            //         - The source raw_infos struct has valid contents per
            //           function precondition
            //         - Per documentation, flags should be zero
            errors::call_hwloc_zero_or_minus1("hwloc_cpukinds_register", || unsafe {
                hwlocality_sys::hwloc_cpukinds_register(
                    self_.topology_mut_ptr(),
                    cpuset.as_ptr(),
                    forced_efficiency,
                    num_infos,
                    infos_ptr,
                    0,
                )
            })
            .expect("All known failure cases are prevented by API design");
            Ok(())
        }

        // Translate infos into hwloc's preferred format
        let input_infos = infos.into_iter();
        let mut infos = Vec::new();
        let mut raw_infos = Vec::new();
        if let Some(infos_len) = input_infos.size_hint().1 {
            infos.reserve(infos_len);
            raw_infos.reserve(infos_len);
        }
        for (name, value) in input_infos {
            let new_string =
                |s: &str| LibcString::new(s).map_err(|_| RegisterError::InfoContainsNul);
            let (name, value) = (new_string(name)?, new_string(value)?);
            // SAFETY: The source name and value LibcStrings are unmodified and
            //         retained by infos Vec until we're done using raw_infos
            raw_infos.push(unsafe { TextualInfo::borrow_raw(&name, &value) });
            infos.push((name, value));
        }

        // SAFETY: raw_infos contains valid infos (infos is still in scope,
        //         target strings have been checked for C suitability and
        //         converted to NUL-terminated format by LibcString)
        unsafe { polymorphized(self, &cpuset, forced_efficiency, raw_infos) }
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
///
/// The reason this is an error rather than a `None` option is that we know
/// there has to be at least one CPU kind in the system. hwloc just failed to
/// enumerate CPU kinds for some unknown reason.
#[derive(Copy, Clone, Debug, Default, Error, Eq, Hash, PartialEq)]
#[error("no information about CPU kinds was found")]
pub struct NoData;

/// Error while querying a CPU kind from a CPU set
#[derive(Clone, Debug, Error, Eq, Hash, PartialEq)]
#[error("CPU set {0} {1}")]
pub struct FromSetError(pub CpuSet, pub FromSetProblem);

/// Problem that was encountered while querying a CPU kind from a CPU set
//
// --- Implementation notes ---
//
// Not implementing Copy to leave room for future growth in case hwloc error
// semantics get clarified in a way that could use non-copy members someday.
#[allow(missing_copy_implementations)]
#[derive(Clone, Debug, Display, Eq, Hash, PartialEq)]
pub enum FromSetProblem {
    /// CPU set is only partially included in some kind
    ///
    /// i.e. some CPUs in the set belong to one kind, other CPUs belong to one
    /// or more other kinds.
    #[display("is only partially included in some CPU kind")]
    PartiallyIncluded,

    /// CPU set is not included in any kind, even partially
    ///
    /// i.e. CPU kind info isn't known or this CPU set does not cover real CPUs.
    #[display("isn't part of any known CPU kind")]
    NotIncluded,
}

/// Error while registering a new CPU kind
#[derive(Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum RegisterError {
    /// `forced_efficiency` value is above what hwloc can handle on this platform
    #[error("CPU kind forced_efficiency value {0} is too high for hwloc")]
    ExcessiveEfficiency(CpuEfficiency),

    /// One of the CPU kind's textual info strings contains the NUL char
    #[error("CPU kind textual info can't contain the NUL char")]
    InfoContainsNul,

    /// There are too many CPU kind textual info (key, value) pairs for hwloc
    #[error("hwloc can't handle that much CPU kind textual info")]
    TooManyInfos,

    /// A CPU kind cannot contain no CPU
    #[error("cannot register a CPU kind with an empty cpuset")]
    NoCPUs,

    /// Some specified CPUs are not part of the topology
    #[error("CPUs {0} are not part of the topology")]
    UnknownCPUs(CpuSet),
}
//
impl From<CpuEfficiency> for RegisterError {
    fn from(value: CpuEfficiency) -> Self {
        Self::ExcessiveEfficiency(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        cpu::cpuset::CpuSet,
        strategies::{any_string, topology_related_set},
    };
    use proptest::{collection::SizeRange, prelude::*};
    #[allow(unused)]
    #[cfg(test)]
    use similar_asserts::assert_eq;
    use std::{collections::HashSet, sync::OnceLock};

    fn cpu_kinds() -> Result<&'static [CpuKind<'static>], NoData> {
        static CPU_KINDS: OnceLock<Result<Vec<CpuKind<'static>>, NoData>> = OnceLock::new();
        match CPU_KINDS.get_or_init(|| Topology::test_instance().cpu_kinds().map(Vec::from_iter)) {
            Ok(v) => Ok(v.as_slice()),
            Err(NoData) => Err(NoData),
        }
    }

    #[test]
    fn check_cpu_kinds() {
        let topology = Topology::test_instance();

        if let Ok(kinds) = cpu_kinds() {
            let expected_num_kinds = topology
                .num_cpu_kinds()
                .expect("If there are kinds, num_cpu_kinds should return Ok");

            let mut seen_kinds = 0;
            let mut seen_cpus = CpuSet::new();
            // Last value of kind.efficiency if any, else None
            let mut last_efficiency: Option<Option<CpuEfficiency>> = None;

            for kind in kinds {
                assert!(!kind.cpuset.is_empty());
                assert!(!kind.cpuset.intersects(&seen_cpus));
                seen_cpus |= &kind.cpuset;

                if let Some(last_efficiency) = last_efficiency {
                    assert_eq!(kind.efficiency.is_some(), last_efficiency.is_some());
                }
                if let Some(efficiency) = kind.efficiency {
                    assert!(efficiency >= last_efficiency.map_or(0, Option::unwrap));
                    assert!(efficiency < expected_num_kinds.get());
                }
                last_efficiency = Some(kind.efficiency);

                // Info keys should be unique
                let mut seen_info = HashSet::new();
                for info in kind.infos {
                    assert!(seen_info.insert(info.name()));
                }

                seen_kinds += 1;
            }

            assert_eq!(seen_kinds, expected_num_kinds.get());
            assert!(seen_cpus.includes(topology.cpuset()));
            assert!(topology.complete_cpuset().includes(&seen_cpus));
        } else {
            topology
                .num_cpu_kinds()
                .expect_err("If there are no kinds, num_cpu_kinds should return Err(NoData)");
        }
    }

    /// Generate a cpuset and the expected output of
    /// `Topology::cpu_kind_from_set()`
    fn cpuset_and_kind() -> impl Strategy<Value = (CpuSet, Result<CpuKind<'static>, FromSetError>)>
    {
        // Query CPU kinds, if they are not known then any topology-related set
        // should return a NotIncluded error no query.
        let Ok(kinds) = cpu_kinds() else {
            return topology_related_set(Topology::complete_cpuset)
                .prop_map(|set| {
                    (
                        set.clone(),
                        Err(FromSetError(set, FromSetProblem::NotIncluded)),
                    )
                })
                .boxed();
        };

        // If we do have CPU kinds, then we must cover a number of scenarios:
        //
        // - Normal usage: CPU set is a subset of one of the kind cpusets
        // - Invalid usage where multiple CPU kinds are covered
        // - Invalid usage where some CPUs belong to a kind and others don't
        // - Invalid usage where no CPU belongs to a kind
        prop_oneof![
            2 => {
                prop::sample::select(kinds).prop_flat_map(|main_kind| {
                    let main_cpus = main_kind.cpuset.iter_set().collect::<Vec<_>>();
                    let num_main_cpus = main_cpus.len();
                    prop::sample::subsequence(main_cpus, 1..=num_main_cpus).prop_map(move |cpus| {
                        (cpus.into_iter().collect::<CpuSet>(), Ok(main_kind.clone()))
                    })
                })
            },
            3 => {
                topology_related_set(Topology::complete_cpuset)
                .prop_map(move |set| {
                    enum MatchKind<'a> {
                        None,
                        Inclusion(&'a CpuKind<'static>),
                        Intersection,
                    }
                    let mut match_kind = MatchKind::None;
                    for kind in kinds {
                        if kind.cpuset.includes(&set) {
                            match_kind = MatchKind::Inclusion(kind);
                            break;
                        } else if kind.cpuset.intersects(&set) {
                            match_kind = MatchKind::Intersection;
                            break;
                        }
                    }
                    match match_kind {
                        MatchKind::None => (set.clone(), Err(FromSetError(set, FromSetProblem::NotIncluded))),
                        MatchKind::Inclusion(kind) => (set, Ok(kind.clone())),
                        MatchKind::Intersection => (set.clone(), Err(FromSetError(set, FromSetProblem::PartiallyIncluded))),
                    }
                })
            }
        ]
        .boxed()
    }

    proptest! {
        #[test]
        fn cpu_kind_from_set((set, expected_result) in cpuset_and_kind()) {
            prop_assert_eq!(Topology::test_instance().cpu_kind_from_set(&set), expected_result);
        }
    }

    /// `forced_efficiency` generator for `register_cpu_kind` tests
    fn forced_efficiency() -> impl Strategy<Value = Option<CpuEfficiency>> {
        let max_valid = c_int::MAX as usize;
        prop_oneof![
            1 => Just(None),
            3 => (0..=max_valid).prop_map(Some),
            1 => ((max_valid+1)..usize::MAX).prop_map(Some)
        ]
    }

    /// String generator for the `infos` param of `register_cpu_kind`
    fn infos() -> impl Strategy<Value = Vec<(String, String)>> {
        let keep_nul = prop_oneof![
            4 => Just(false),
            1 => Just(true)
        ];
        keep_nul.prop_flat_map(|keep_nul| {
            let string = move || {
                any_string().prop_map(move |s| {
                    if keep_nul {
                        s
                    } else {
                        s.chars().filter(|&c| c != '\0').collect()
                    }
                })
            };
            prop::collection::vec((string(), string()), SizeRange::default())
        })
    }

    proptest! {
        #[test]
        #[ignore = "Waiting for hwloc release with patch for https://github.com/open-mpi/hwloc/issues/683"]
        fn register_cpu_kind(
            cpuset in topology_related_set(Topology::complete_cpuset),
            forced_efficiency in forced_efficiency(),
            infos in infos(),
        ) {
            // Perform the change
            let mut topology = Topology::test_instance().clone();
            let initial_kinds = cpu_kinds();
            let result = topology.edit(|editor| {
                editor.register_cpu_kind(&cpuset, forced_efficiency, infos.iter().map(|(name, value)| (name.as_str(), value.as_str())))
            });

            // Predict and check error cases
            let excessive_efficiency = forced_efficiency.is_some_and(|eff| eff > c_int::MAX as usize);
            let info_contains_nul = infos.iter().any(|(name, value)| name.contains('\0') || value.contains('\0'));
            let no_cpus = cpuset.is_empty();
            let too_many_infos = infos.len() > c_uint::MAX as usize;
            let complete_cpuset = Topology::test_instance().complete_cpuset();
            let unknown_cpus = !complete_cpuset.includes(&cpuset);
            prop_assert_eq!(result.is_err(), excessive_efficiency || info_contains_nul || too_many_infos || unknown_cpus || no_cpus);
            if let Err(e) = result {
                match e {
                    RegisterError::ExcessiveEfficiency(eff) => {
                        prop_assert!(excessive_efficiency);
                        prop_assert_eq!(forced_efficiency.unwrap(), eff);
                        prop_assert_eq!(e, RegisterError::from(eff));
                    }
                    RegisterError::InfoContainsNul => prop_assert!(info_contains_nul),
                    RegisterError::NoCPUs => prop_assert!(no_cpus),
                    RegisterError::TooManyInfos => prop_assert!(too_many_infos),
                    RegisterError::UnknownCPUs(unknown) => {
                        prop_assert!(unknown_cpus);
                        prop_assert_eq!(unknown, cpuset - complete_cpuset);
                    }
                }
                return Ok(());
            }

            // Predict new CPU kinds
            let mut shrunk_kinds = Vec::new();
            let mut new_kinds = Vec::new();
            struct NewKind {
                cpuset: CpuSet,
                old_infos: &'static [TextualInfo],
            }
            let mut new_cpuset = cpuset.clone();
            if let Ok(initial_kinds) = initial_kinds {
                for kind in initial_kinds {
                    if kind.cpuset.intersects(&cpuset) {
                        if kind.cpuset != cpuset {
                            let mut shrunk_kind = kind.clone();
                            shrunk_kind.cpuset = &kind.cpuset - &cpuset;
                            shrunk_kinds.push(shrunk_kind);
                        }
                        new_kinds.push(NewKind {
                            cpuset: (&kind.cpuset) & (&cpuset),
                            old_infos: kind.infos,
                        });
                        new_cpuset -= &kind.cpuset;
                    } else {
                        shrunk_kinds.push(kind.clone());
                    }
                }
            }
            if !new_cpuset.is_empty() {
                new_kinds.push(NewKind {
                    cpuset: new_cpuset,
                    old_infos: &[],
                })
            }

            // Check if actual CPU kinds match prediction
            let mut shrunk_kinds = shrunk_kinds.into_iter().peekable();
            let mut new_kinds = new_kinds.into_iter().fuse();
            for kind in topology.cpu_kinds().unwrap() {
                if let Some(next_shrunk_kind) = shrunk_kinds.peek() {
                    if kind.cpuset == next_shrunk_kind.cpuset {
                        prop_assert_eq!(kind.infos, next_shrunk_kind.infos);
                        shrunk_kinds.next();
                        continue;
                    }
                }
                let expected_kind = new_kinds.next().unwrap();
                prop_assert_eq!(kind.cpuset, expected_kind.cpuset);
                for info in kind.infos {
                    if !expected_kind.old_infos.iter().any(|old| old.name() == info.name()) {
                        let info_name = info.name().to_str().unwrap();
                        let info_value = info.value().to_str().unwrap();
                        prop_assert_eq!(
                            &infos.iter().find(|(name, _value)| name == info_name).unwrap().1,
                            info_value
                        );
                    }
                }
            }
            prop_assert!(shrunk_kinds.next().is_none());
            prop_assert!(new_kinds.next().is_none());
        }
    }
}
