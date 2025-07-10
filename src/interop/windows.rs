//! Windows-specific helpers

use crate::{
    cpu::cpuset::CpuSet,
    errors::{self, RawHwlocError},
    ffi::int,
    topology::Topology,
};
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::{ffi::c_uint, iter::FusedIterator, num::NonZeroUsize};

/// # Windows-specific helpers
///
/// These functions query Windows processor groups. These groups partition the
/// operating system into virtual sets of up to 64 neighbor PUs. Threads and
/// processes may only be bound inside a single group. Although Windows
/// processor groups may be exposed in the hwloc hierarchy as hwloc Groups,
/// they are also often merged into existing hwloc objects such as NUMA nodes
/// or Packages. This API provides explicit information about Windows processor
/// groups so that applications know whether binding to a large set of PUs may
/// fail because it spans over multiple Windows processor groups.
//
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__windows.html
impl Topology {
    /// Number of Windows processor groups
    ///
    /// # Errors
    ///
    /// One reason why this function can fail is if the topology does not match
    /// the current system (e.g. loaded from another machine through XML).
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_windows_get_nr_processor_groups")]
    pub fn num_processor_groups(&self) -> Result<NonZeroUsize, RawHwlocError> {
        let count =
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - hwloc ops are trusted not to modify *const parameters
            //         - Per documentation, flags must be zero
            errors::call_hwloc_positive_or_minus1("hwloc_windows_get_nr_processor_groups", || unsafe {
                hwlocality_sys::hwloc_windows_get_nr_processor_groups(self.as_ptr(), 0)
            })?;
        let count = NonZeroUsize::new(int::expect_usize(count))
            .expect("Unexpected 0 processor group count");
        Ok(count)
    }

    /// Enumerate the cpusets of Windows processor groups
    ///
    /// # Errors
    ///
    /// One reason why this function can fail is if the topology does not match
    /// the current system (e.g. loaded from another machine through XML).
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_windows_get_processor_group_cpuset")]
    pub fn processor_groups(
        &self,
    ) -> Result<
        impl DoubleEndedIterator<Item = Result<CpuSet, RawHwlocError>>
            + Clone
            + ExactSizeIterator
            + FusedIterator
            + '_,
        RawHwlocError,
    > {
        Ok(
            (0..usize::from(self.num_processor_groups()?)).map(|pg_index| {
                let mut set = CpuSet::new();
                let pg_index = c_uint::try_from(pg_index)
                    .expect("Can't fail, pg_index upper bound comes from hwloc");
                errors::call_hwloc_zero_or_minus1(
                    "hwloc_windows_get_processor_group_cpuset",
                    // SAFETY: - Topology is trusted to contain a valid ptr
                    //           (type invariant)
                    //         - Bitmap is trusted to contain a valid ptr
                    //           (type invariant)
                    //         - hwloc ops are trusted not to modify *const
                    //           parameters
                    //         - hwloc ops are trusted to keep *mut parameters
                    //           in a valid state unless stated otherwise
                    //         - pg_index is in bounds by construction
                    //         - Per documentation, flags must be zero
                    || unsafe {
                        hwlocality_sys::hwloc_windows_get_processor_group_cpuset(
                            self.as_ptr(),
                            pg_index,
                            set.as_mut_ptr(),
                            0,
                        )
                    },
                )?;
                Ok(set)
            }),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused)]
    use similar_asserts::assert_eq;

    #[test]
    fn processor_groups() {
        let topology = Topology::test_instance();
        let expected_num_groups = topology.num_processor_groups().unwrap();
        let mut actual_num_groups = 0;
        let mut cpuset_union = CpuSet::new();
        for group_cpuset in topology.processor_groups().unwrap() {
            cpuset_union |= group_cpuset.unwrap();
            actual_num_groups += 1;
        }
        assert_eq!(expected_num_groups.get(), actual_num_groups);
        assert!(cpuset_union.includes(topology.cpuset()));
        assert!(topology.complete_cpuset().includes(&cpuset_union));
    }
}
