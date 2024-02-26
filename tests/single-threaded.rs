//! Single-threaded test process for testing the CPU and memory binding
//! functions that are only valid on a single thread.

// WARNING: DO NOT CREATE ANY OTHER #[test] FUNCTION IN THIS INTEGRATION TEST!

use hwlocality::{
    bitmap::{Bitmap, BitmapIndex, BitmapRef, OwnedSpecializedBitmap, SpecializedBitmap},
    cpu::{
        binding::{CpuBindingError, CpuBindingFlags},
        cpuset::CpuSet,
    },
    errors::{HybridError, ParameterError, RawHwlocError},
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
    dbg!(topology.cpuset());
    dbg!(topology.complete_cpuset());

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

    // Handle invalid cpuset errors
    if let Err(HybridError::Rust(CpuBindingError::BadCpuSet(set2))) = &result {
        prop_assert_eq!(set2, set);

        // Empty sets and sets outside the topology's complete cpuset are never
        // valid. cpusets outside the topology's main cpuset are also very
        // likely to be invalid binding targets, hence failure is expected upon
        // encountering them.
        //
        // Non-Linux platforms may also have arbitrary restrictions on what
        // constitutes a valid CPU binding target. In the case of Windows, this
        // is known to happen due to this OS' "processor group" notion.
        if set.is_empty() || !topology.cpuset().includes(set) || !cfg!(target_os = "linux") {
            return Ok(());
        } else {
            return Err(TestCaseError::Fail("Unexpected CpuBindingError".into()));
        }
    }

    // Make sure flags are valid
    let target_flags =
        CpuBindingFlags::ASSUME_SINGLE_THREAD | CpuBindingFlags::THREAD | CpuBindingFlags::PROCESS;
    if (flags & target_flags).iter().count() != 1 {
        prop_assert_eq!(
            result,
            Err(HybridError::Rust(CpuBindingError::BadFlags(
                ParameterError(flags)
            )))
        );
        return Ok(());
    }

    // Skip unknown errors on Windows: we can't interpret them
    if cfg!(windows) {
        if let Err(HybridError::Hwloc(RawHwlocError { errno: None, .. })) = result {
            return Ok(());
        }
    }

    // That should cover all known sources of error
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
