//! Single-threaded test process for testing the CPU and memory binding
//! functions that are only valid on a single thread.

// WARNING: DO NOT CREATE ANY OTHER #[test] FUNCTION IN THIS INTEGRATION TEST!
//
// If you need more tests, create more integration tests (but beware that they
// won't be able to share code.

use errno::Errno;
use hwlocality::{
    bitmap::{Bitmap, BitmapIndex, BitmapRef, OwnedSpecializedBitmap, SpecializedBitmap},
    cpu::{
        binding::{CpuBindingError, CpuBindingFlags, CpuBoundObject},
        cpuset::CpuSet,
    },
    errors::{HybridError, ParameterError, RawHwlocError},
    topology::Topology,
};
use proptest::{prelude::*, test_runner::TestRunner};
use std::{collections::HashSet, ffi::c_uint, fmt::Debug, ops::Deref};

/// Check that some FnMut that takes `impl Deref<Target = XyzSet>` works with
/// both `&XyzSet` and `BitmapRef<'_, XyzSet>`.
macro_rules! test_deref_set {
    ($fn_mut_of_deref_set:expr, $topology:expr, $set:expr $(, $other_args:expr)*) => {{
        $fn_mut_of_deref_set($topology, &$set $(, $other_args)*)?;
        let set_ref = BitmapRef::from(&$set);
        $fn_mut_of_deref_set($topology, set_ref $(, $other_args)*)
    }};
}

// WARNING: DO NOT CREATE ANY OTHER #[test] FUNCTION IN THIS INTEGRATION TEST!

#[test]
fn single_threaded_test() {
    // Set up test harness
    tracing_subscriber::fmt::init();
    let topology = Topology::test_instance();
    let my_pid = std::process::id();
    let my_tid = hwlocality::current_thread_id();

    // Display some debug information about the host to ease interpretation
    dbg!(topology.feature_support());
    dbg!(topology.cpuset());
    dbg!(topology.complete_cpuset());

    // Test CPU binding operations for current process
    if let Some(cpubind_support) = topology.feature_support().cpu_binding() {
        // Setting CPU bindings
        TestRunner::default()
            .run(
                &(
                    topology_related_set(Topology::complete_cpuset),
                    any_cpubind_flags(),
                ),
                |(cpuset, flags)| {
                    let target_flags = flags & target_flags();
                    let curr_proc = cpubind_support.set_current_process();
                    let curr_thr = cpubind_support.set_current_thread();
                    let can_set_self = match target_flags {
                        CpuBindingFlags::PROCESS => curr_proc,
                        CpuBindingFlags::THREAD => curr_thr,
                        CpuBindingFlags::ASSUME_SINGLE_THREAD => curr_proc | curr_thr,
                        _ => true, // Doesn't matter, will fail flag validation
                    };
                    if can_set_self {
                        test_deref_set!(
                            test_bind_cpu,
                            topology,
                            cpuset,
                            flags,
                            CpuBoundObject::ThisProgram
                        )?;
                    }
                    if cpubind_support.set_process() {
                        test_deref_set!(
                            test_bind_cpu,
                            topology,
                            cpuset,
                            flags,
                            CpuBoundObject::ProcessOrThread(my_pid)
                        )?;
                    }
                    if cpubind_support.set_thread() {
                        test_deref_set!(
                            test_bind_cpu,
                            topology,
                            cpuset,
                            flags,
                            CpuBoundObject::Thread(my_tid)
                        )?;
                    }
                    Ok(())
                },
            )
            .unwrap();

        // Querying CPU bindings
        TestRunner::default()
            .run(&any_cpubind_flags(), |flags| {
                let target_flags = flags & target_flags();
                let can_get_self = |curr_proc, curr_thr| match target_flags {
                    CpuBindingFlags::PROCESS => curr_proc,
                    CpuBindingFlags::THREAD => curr_thr,
                    CpuBindingFlags::ASSUME_SINGLE_THREAD => curr_proc | curr_thr,
                    _ => true, // Doesn't matter, will fail flag validation
                };
                if can_get_self(
                    cpubind_support.get_current_process(),
                    cpubind_support.get_current_thread(),
                ) {
                    test_cpu_binding(topology, flags, CpuBoundObject::ThisProgram)?;
                }
                if cpubind_support.get_process() {
                    test_cpu_binding(topology, flags, CpuBoundObject::ProcessOrThread(my_pid))?;
                }
                if cpubind_support.set_thread() {
                    test_cpu_binding(topology, flags, CpuBoundObject::Thread(my_tid))?;
                }
                if can_get_self(
                    cpubind_support.get_current_process_last_cpu_location(),
                    cpubind_support.get_current_thread_last_cpu_location(),
                ) {
                    test_last_cpu_location(topology, flags, CpuBoundObject::ThisProgram)?;
                }
                if cpubind_support.get_process_last_cpu_location() {
                    test_last_cpu_location(
                        topology,
                        flags,
                        CpuBoundObject::ProcessOrThread(my_pid),
                    )?;
                }
                Ok(())
            })
            .unwrap();
    }

    // TODO: Add other single-threaded tests here
}

// WARNING: DO NOT CREATE ANY OTHER #[test] FUNCTION IN THIS INTEGRATION TEST!

/// Handle some windows error edge cases
macro_rules! handle_windows_edge_cases {
    ($result:expr, $target:expr) => {
        if cfg!(windows) {
            if let Err(HybridError::Hwloc(RawHwlocError { errno, .. })) = $result {
                match errno {
                    // Ignore unknown errors: we can't make sense of them and they
                    // originate from a fishy CRT setup to begin with.
                    None => return Ok(()),

                    // Ignore invalid handle errors that occur when manipulating
                    // bindings by PID as this hwloc feature is known to be brittle
                    // (see https://github.com/open-mpi/hwloc/issues/78 )
                    Some(Errno(6)) if matches!($target, CpuBoundObject::ProcessOrThread(_)) => {
                        return Ok(())
                    }

                    // Nothing else is known to be particularly faillible on Windows
                    _ => {}
                }
            }
        }
    };
}

/// Check that methods that set CPU bindings work as expected for some inputs
#[tracing::instrument(skip(topology))]
fn test_bind_cpu(
    topology: &Topology,
    set: impl Deref<Target = CpuSet> + Copy + Debug,
    flags: CpuBindingFlags,
    target: CpuBoundObject,
) -> Result<(), TestCaseError> {
    // Run the CPU binding function
    let set2 = set;
    let result = match target {
        CpuBoundObject::ThisProgram => topology.bind_cpu(set, flags),
        CpuBoundObject::ProcessOrThread(pid) => topology.bind_process_cpu(pid, set, flags),
        CpuBoundObject::Thread(pid) => topology.bind_thread_cpu(pid, set, flags),
    };
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

    // Make sure the target flags are valid
    if check_bad_target_flags(target, flags, result.as_ref().err())? {
        return Ok(());
    }

    // Handle some Windows edge cases
    handle_windows_edge_cases!(&result, target);

    // That should cover all known sources of error
    if let Err(e) = result {
        tracing::error!("Got unexpected CPU binding setup error: {e}");
        return Err(TestCaseError::fail(format!("{e}")));
    }

    // CPU binding should have changed as a result of calling this function, and
    // in strict mode we know what it should have changed into.
    if flags.contains(CpuBindingFlags::STRICT) {
        let target_flags = flags & target_flags();
        let expected_binding = Ok(set.clone());
        // Here I'm taking the shortcut of assuming that if we can set CPU
        // bindings for a certain target, we can also query them. Introduce more
        // rigorous feature support checks if we find an OS where this is wrong.
        let actual_binding = match target {
            CpuBoundObject::ThisProgram => topology.cpu_binding(target_flags),
            CpuBoundObject::ProcessOrThread(pid) => topology.process_cpu_binding(pid, target_flags),
            CpuBoundObject::Thread(tid) => topology.thread_cpu_binding(tid, target_flags),
        };
        prop_assert_eq!(expected_binding, actual_binding);
    }
    Ok(())
}

/// Check that methods that get CPU bindings work as expected for some inputs
#[tracing::instrument(skip(topology))]
fn test_cpu_binding(
    topology: &Topology,
    flags: CpuBindingFlags,
    target: CpuBoundObject,
) -> Result<(), TestCaseError> {
    // Query the thread or process' current CPU affinity
    let result = match target {
        CpuBoundObject::ThisProgram => topology.cpu_binding(flags),
        CpuBoundObject::ProcessOrThread(pid) => topology.process_cpu_binding(pid, flags),
        CpuBoundObject::Thread(tid) => topology.thread_cpu_binding(tid, flags),
    };

    // Make sure the `STRICT` flag is not specified when querying threads
    if flags.contains(CpuBindingFlags::STRICT)
        && (matches!(target, CpuBoundObject::Thread(_)) || flags.contains(CpuBindingFlags::THREAD))
    {
        prop_assert_eq!(
            result,
            Err(HybridError::Rust(CpuBindingError::BadFlags(flags.into())))
        );
        return Ok(());
    }

    // Common code path with CPU location check
    check_cpubind_query_result(result, topology, flags, target)
}

/// Check that methods that get CPU locations work as expected for some inputs
#[tracing::instrument(skip(topology))]
fn test_last_cpu_location(
    topology: &Topology,
    flags: CpuBindingFlags,
    target: CpuBoundObject,
) -> Result<(), TestCaseError> {
    // Query the thread or process' current CPU location
    let result = match target {
        CpuBoundObject::ThisProgram => topology.last_cpu_location(flags),
        CpuBoundObject::ProcessOrThread(pid) => topology.last_process_cpu_location(pid, flags),
        CpuBoundObject::Thread(_) => panic!("Not currently supported by hwloc"),
    };

    // Make sure the `STRICT` flag was not specified
    if flags.contains(CpuBindingFlags::STRICT) {
        prop_assert_eq!(
            result,
            Err(HybridError::Rust(CpuBindingError::BadFlags(flags.into())))
        );
        return Ok(());
    }

    // Common code path with CPU affinity check
    check_cpubind_query_result(result, topology, flags, target)
}

/// Check the result of a CPU binding or CPU location query
#[tracing::instrument(skip(topology))]
fn check_cpubind_query_result(
    result: Result<CpuSet, HybridError<CpuBindingError>>,
    topology: &Topology,
    flags: CpuBindingFlags,
    target: CpuBoundObject,
) -> Result<(), TestCaseError> {
    // Make sure the target flags are valid
    if check_bad_target_flags(target, flags, result.as_ref().err())? {
        return Ok(());
    }

    // Make sure the `NO_MEMORY_BINDING` flag was not specified
    if flags.contains(CpuBindingFlags::NO_MEMORY_BINDING) {
        prop_assert_eq!(
            result,
            Err(HybridError::Rust(CpuBindingError::BadFlags(flags.into())))
        );
        return Ok(());
    }

    // Handle some Windows edge cases
    handle_windows_edge_cases!(&result, target);

    // That should cover all known sources of error
    let cpuset = match result {
        Ok(cpuset) => cpuset,
        Err(e) => {
            tracing::error!("Got unexpected CPU binding query error: {e}");
            return Err(TestCaseError::fail(format!("{e}")));
        }
    };

    // The retrieved cpu binding should at least somewhat make sense
    prop_assert!(!cpuset.is_empty());
    prop_assert!(topology.complete_cpuset().includes(&cpuset));
    Ok(())
}

/// CPU binding flags which specify whether a thread or process is targeted
fn target_flags() -> CpuBindingFlags {
    CpuBindingFlags::ASSUME_SINGLE_THREAD | CpuBindingFlags::THREAD | CpuBindingFlags::PROCESS
}

/// Check that either the "target flags" of CPU binding operations are used
/// correctly correctly or errors are reported correctly.
///
/// Return true if an error was detected, so that the output of the underlying
/// CPU binding function is not examined further.
#[tracing::instrument]
fn check_bad_target_flags(
    target: CpuBoundObject,
    flags: CpuBindingFlags,
    error: Option<&HybridError<CpuBindingError>>,
) -> Result<bool, TestCaseError> {
    // We are only concerned with flags that specify the target
    let target_flags = flags & target_flags();

    // If flags validation fails, we should get this error
    let expected_err = Some(HybridError::Rust(CpuBindingError::BadFlags(
        ParameterError(flags),
    )));
    let expected_err = expected_err.as_ref();

    // Handle Linux edge case where THREAD can be used on processes
    let is_linux_special_case = target_flags.contains(CpuBindingFlags::THREAD)
        && matches!(target, CpuBoundObject::ProcessOrThread(_));
    if is_linux_special_case && cfg!(not(target_os = "linux")) {
        prop_assert_eq!(error, expected_err);
        return Ok(true);
    }

    // Check that the number of target flags is right
    if (flags & target_flags).iter().count()
        != ((target == CpuBoundObject::ThisProgram) || is_linux_special_case) as usize
    {
        prop_assert_eq!(error, expected_err);
        return Ok(true);
    }
    Ok(false)
}

// WARNING: DO NOT CREATE ANY OTHER #[test] FUNCTION IN THIS INTEGRATION TEST!

// === The following is copypasted from hwlocality's unit testing code ===
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
