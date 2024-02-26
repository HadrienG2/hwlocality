//! Single-threaded test process for testing the CPU and memory binding
//! functions that are only valid on a single thread.

// WARNING: DO NOT CREATE ANY OTHER #[test] FUNCTION IN THIS INTEGRATION TEST!

use hwlocality::{
    bitmap::{Bitmap, BitmapIndex, BitmapRef, OwnedSpecializedBitmap, SpecializedBitmap},
    cpu::{
        binding::{CpuBindingError, CpuBindingFlags},
        cpuset::CpuSet,
    },
    errors::ParameterError,
    topology::{
        support::{CpuBindingSupport, FeatureSupport},
        Topology,
    },
};
use proptest::{prelude::*, test_runner::TestRunner};
use std::{collections::HashSet, ffi::c_uint, ops::Deref};

// WARNING: DO NOT CREATE ANY OTHER #[test] FUNCTION IN THIS INTEGRATION TEST!

#[test]
fn single_threaded_test() {
    // Set up test harness
    let topology = Topology::test_instance();
    let mut runner = TestRunner::default();

    // Test CPU binding setup for current process
    if topology.supports(
        FeatureSupport::cpu_binding,
        CpuBindingSupport::set_current_process,
    ) {
        runner
            .run(
                &(
                    topology_related_set(Topology::complete_cpuset),
                    any_cpubind_flags(),
                ),
                |(cpuset, flags)| {
                    test_bind_cpu(topology, &cpuset, flags)?;
                    let cpuset_ref = BitmapRef::from(&cpuset);
                    test_bind_cpu(topology, cpuset_ref, flags)?;
                    Ok(())
                },
            )
            .unwrap();
    }

    // TODO: Test CPU binding queries for current process

    // TODO: Add other ST tests here
}

// WARNING: DO NOT CREATE ANY OTHER #[test] FUNCTION IN THIS INTEGRATION TEST!

/// Check that `Topology::bind_cpu()` works as expected for certain inputs
fn test_bind_cpu(
    topology: &Topology,
    set: impl Deref<Target = CpuSet> + Copy,
    flags: CpuBindingFlags,
) -> Result<(), TestCaseError> {
    // Run the CPU binding function
    let set2 = set;
    let result = topology.bind_cpu(set, flags);
    let set = set2.deref();

    // Make sure set is valid
    if set.is_empty() || !topology.complete_cpuset().includes(set) {
        prop_assert_eq!(result, Err(CpuBindingError::BadCpuSet(set.clone())));
        return Ok(());
    }

    // Also treat cpusets outside the topology's main cpuset as invalid when
    // bind_cpu errors out: it is not guaranteed to work with these sets.
    if let Err(CpuBindingError::BadCpuSet(set2)) = &result {
        if !topology.cpuset().includes(set) {
            prop_assert_eq!(set2, set);
            return Ok(());
        }
    }

    // Make sure flags are valid
    let target_flags =
        CpuBindingFlags::ASSUME_SINGLE_THREAD | CpuBindingFlags::THREAD | CpuBindingFlags::PROCESS;
    if (flags & target_flags).iter().count() != 1 {
        prop_assert_eq!(
            result,
            Err(CpuBindingError::BadFlags(ParameterError(flags)))
        );
        return Ok(());
    }

    // That should be it on Linux (will probably want to expand for other OSes)
    prop_assert_eq!(result, Ok(()));

    // CPU binding should have changed as a result of calling this function, and
    // in strict mode we know what it should have changed into.
    if topology.supports(
        FeatureSupport::cpu_binding,
        CpuBindingSupport::get_current_process,
    ) && flags.contains(CpuBindingFlags::STRICT)
    {
        prop_assert_eq!(topology.cpu_binding(flags & target_flags), Ok(set.clone()));
    }
    Ok(())
}

// WARNING: DO NOT CREATE ANY OTHER #[test] FUNCTION IN THIS INTEGRATION TEST!

// === The following is copypasted from hwlocality's testing code ===
//
// This is a workaround for the fact that integration tests do not link against
// the cfg(test) version of the crate and cannot request that the crate be built
// with the proptest feature.

/// Specialization of `set_with_reference` that uses the topology-wide cpuset or
/// nodeset as a reference
fn topology_related_set<Set: OwnedSpecializedBitmap>(
    topology_set: impl FnOnce(&Topology) -> BitmapRef<'_, Set>,
) -> impl Strategy<Value = Set> {
    set_with_reference(topology_set(Topology::test_instance()).as_ref())
}

/// [`CpuSet`] and [`NodeSet`] generator that is biased towards covering all
/// set-theoretically interesting configurations with respect to a `reference`
/// set that is somehow special to the function being tested:
///
/// - Empty (nothing inside, nothing outside)
/// - Disjoint (nothing inside, some outside)
/// - Complement (nothing inside, everything outside)
/// - Subset (some inside, nothing outside)
/// - Intersects (some inside, some outside)
/// - Subset complement (some inside, everything outside)
/// - Equal (everything inside, nothing outside)
/// - Superset (everything inside, some outside)
/// - Everything (everything inside, everything outside)
fn set_with_reference<Set: SpecializedBitmap>(ref_set: &Set) -> impl Strategy<Value = Set::Owned> {
    // First, one of the reference set and its complement has to be finite
    let ref_set: &Bitmap = ref_set.as_ref();
    let finite_set = if ref_set.weight().is_some() {
        ref_set.clone()
    } else {
        !ref_set
    };
    assert!(
        finite_set.weight().is_some(),
        "since bitmaps can only be infinite in one direction, \
        the complement of an infinite bitmap must be finite"
    );

    // We can define a subset of the finite set that has a fair chance of
    // covering all finite set elements and none of them + other configurations
    let finite_elems = finite_set.iter_set().collect::<Vec<_>>();
    let num_finite_elems = finite_elems.len();
    let inside_elems = prop_oneof![
        3 => prop::sample::subsequence(finite_elems.clone(), 0..=num_finite_elems),
        1 => Just(Vec::new()),
        1 => Just(finite_elems)
    ]
    .prop_map(|seq| seq.into_iter().collect::<Bitmap>());

    // Next we can pick a random set within the complement of the finite set by
    // picking a random set and subtracting the finite set from it
    let outside_elems = prop_oneof![
        3 => Just(Bitmap::new()),
        2 => any_bitmap().prop_map(move |any_elems| any_elems - &finite_set),
    ];

    // By combining these two sets which each have good coverage of all three
    // (nothing inside, some inside, everything inside) configurations of their
    // reference set, we get good coverage of all desired set configurations
    (inside_elems, outside_elems)
        .prop_map(|(inside_elems, outside_elems)| Set::Owned::from(inside_elems | outside_elems))
}

/// Generate an arbitrary Bitmap
fn any_bitmap() -> impl Strategy<Value = Bitmap> {
    let finite_bitmap = prop_oneof![
        1 => Just(Bitmap::new()),
        4 => any::<HashSet<c_uint>>().prop_map(|overflowing_indices| {
            overflowing_indices
                .into_iter()
                .map(|idx| {
                    // Keep indices small-ish, setting a bitmap index is O(N)
                    BitmapIndex::try_from(idx as usize % 256).unwrap()
                })
                .collect::<Bitmap>()
        }),
    ];
    (finite_bitmap, prop::bool::ANY).prop_map(|(mut bitmap, invert)| {
        if invert {
            bitmap.invert();
        }
        bitmap
    })
}

/// Generate arbitrary CpuBindingFlags
fn any_cpubind_flags() -> impl Strategy<Value = CpuBindingFlags> {
    let all_flags = CpuBindingFlags::all().iter().collect::<Vec<_>>();
    let num_flags = all_flags.len();
    prop::sample::subsequence(all_flags, 0..=num_flags)
        .prop_map(|some_flags| some_flags.into_iter().collect::<CpuBindingFlags>())
}

// WARNING: DO NOT CREATE ANY OTHER #[test] FUNCTION IN THIS INTEGRATION TEST!
