//! Single-threaded test process for testing the CPU and memory binding
//! functions that are only valid on a single thread.

// WARNING: DO NOT CREATE ANY OTHER #[test] FUNCTION IN THIS INTEGRATION TEST!
//
// If you need more tests, create more integration tests (but beware that they
// won't be able to share code.

use errno::Errno;
use hwlocality::{
    bitmap::{Bitmap, BitmapIndex, BitmapKind, BitmapRef, SpecializedBitmap, SpecializedBitmapRef},
    cpu::{
        binding::{CpuBindingError, CpuBindingFlags, CpuBoundObject},
        cpuset::CpuSet,
    },
    errors::{HybridError, ParameterError, RawHwlocError},
    memory::binding::{
        Bytes, MemoryAllocationError, MemoryBindingError, MemoryBindingFlags, MemoryBindingPolicy,
    },
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

/// Check that some FnMut that takes `impl SpecializedBitmap` works with all of
/// `&CpuSet`, `&NodeSet`, `BitmapRef<'_, CpuSet>` and `BitmapRef<'_, NodeSet>`.
macro_rules! test_specialized_bitmap {
    ($fn_mut_of_deref_set:expr, $topology:expr, $cpuset:expr, $nodeset:expr $(, $other_args:expr)*) => {{
        test_deref_set!($fn_mut_of_deref_set, $topology, $cpuset $(, $other_args)*)?;
        test_deref_set!($fn_mut_of_deref_set, $topology, $nodeset $(, $other_args)*)
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

    // Test CPU binding operations for current process
    if let Some(cpubind_support) = topology.feature_support().cpu_binding() {
        // Display the host's CPU configuration
        dbg!(topology.cpuset());
        dbg!(topology.complete_cpuset());

        // Setting CPU bindings
        TestRunner::default()
            .run(
                &(
                    topology_related_set(Topology::complete_cpuset),
                    any_cpubind_flags(),
                ),
                |(cpuset, flags)| {
                    let target_flags = flags & target_cpubind_flags();
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
                let target_flags = flags & target_cpubind_flags();
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

    // Test memory binding operations for current process
    if let Some(membind_support) = topology.feature_support().memory_binding() {
        // Display the host's NUMA configuration
        dbg!(topology.nodeset());
        dbg!(topology.complete_nodeset());

        // Test unbound memory allocations
        //
        // The allocation size range is chosen such that it can cover 2-3 pages
        // on typical architectures (Arm's max page size is 16 MiB, x86's is
        // actually 1 GiB but you'll never get that from a typical OS and it
        // gets costly to test with such large allocations).
        let len_range = 0usize..(48 * 1024 * 1024);
        TestRunner::default()
            .run(&len_range, |len| test_allocate_memory(topology, len))
            .unwrap();

        // Test bound memory allocations in all supported configurations
        TestRunner::default()
            .run(
                &(
                    &len_range,
                    topology_related_set(Topology::complete_cpuset),
                    topology_related_set(Topology::complete_nodeset),
                    any_membind_policy(),
                    any_membind_flags(),
                ),
                |(len, cpuset, nodeset, policy, flags)| {
                    // Test direct allocation of bound memory
                    if membind_support.allocate_bound() {
                        test_specialized_bitmap!(
                            test_allocate_bound_memory,
                            topology,
                            cpuset,
                            nodeset,
                            len,
                            policy,
                            flags
                        )?;
                    }

                    // Test allocation of bound memory that may require
                    // rebinding the process
                    let target_flags = flags & target_membind_flags();
                    let curr_proc = membind_support.set_current_process();
                    let curr_thr = membind_support.set_current_thread();
                    let can_bind_self = match target_flags {
                        MemoryBindingFlags::PROCESS => curr_proc,
                        MemoryBindingFlags::THREAD => curr_thr,
                        MemoryBindingFlags::ASSUME_SINGLE_THREAD => curr_proc | curr_thr,
                        _ => true, // Doesn't matter, will fail flag validation
                    };
                    if membind_support.allocate_bound() || can_bind_self {
                        test_specialized_bitmap!(
                            test_binding_allocate_memory,
                            topology,
                            cpuset,
                            nodeset,
                            len,
                            policy,
                            flags
                        )?;
                    }
                    Ok(())
                },
            )
            .unwrap();

        // TODO: Add more memory binding tests here. They should mostly follow
        //       the example of CPU binding, but they are a bit more involved
    }
}

// WARNING: DO NOT CREATE ANY OTHER #[test] FUNCTION IN THIS INTEGRATION TEST!

// === Memory binding test logic ===

/// Test that hwloc's basic memory allocator works.
#[tracing::instrument(skip(topology))]
fn test_allocate_memory(topology: &Topology, len: usize) -> Result<(), TestCaseError> {
    let result = topology.allocate_memory(len);
    match result {
        Ok(bytes) => check_memory_allocation(bytes, len),
        Err(HybridError::Rust(MemoryAllocationError::AllocationFailed)) => Ok(()),
        Err(other) => {
            let other = format!("{other}");
            tracing::error!("Got unexpected memory allocation error: {other}");
            Err(TestCaseError::fail(other))
        }
    }
}

/// Test that hwloc's pure bound memory allocator works
#[tracing::instrument(skip(topology))]
fn test_allocate_bound_memory(
    topology: &Topology,
    set: impl SpecializedBitmapRef + Copy + Debug,
    len: usize,
    policy: MemoryBindingPolicy,
    flags: MemoryBindingFlags,
) -> Result<(), TestCaseError> {
    let result = topology.allocate_bound_memory(len, set, policy, flags);
    check_allocate_bound(result, false, topology, &*set, len, policy, flags)
}

/// Test that hwloc's bound memory allocator that may rebind the process/thread
/// if necessary works
#[tracing::instrument(skip(topology))]
fn test_binding_allocate_memory(
    topology: &Topology,
    set: impl SpecializedBitmapRef + Copy + Debug,
    len: usize,
    policy: MemoryBindingPolicy,
    flags: MemoryBindingFlags,
) -> Result<(), TestCaseError> {
    let result = topology.binding_allocate_memory(len, set, policy, flags);
    check_allocate_bound(result, true, topology, &*set, len, policy, flags)
}

/// Common code path for bound memory allocations
#[tracing::instrument(skip(result, topology))]
fn check_allocate_bound<Set: SpecializedBitmap>(
    result: Result<Bytes<'_>, HybridError<MemoryBindingError<Set>>>,
    can_bind_program: bool,
    topology: &Topology,
    set: &Set,
    len: usize,
    policy: MemoryBindingPolicy,
    flags: MemoryBindingFlags,
) -> Result<(), TestCaseError> {
    // Handle invalid cpuset/nodeset errors
    if let Err(HybridError::Rust(MemoryBindingError::BadSet(object, set2))) = &result {
        prop_assert_eq!(set2, set);

        // Reinterpret the set as an untyped bitmap and find the associated
        // reference set (cpuset/nodeset) of the topology
        let set = set.as_bitmap_ref();
        let topology_set = match Set::BITMAP_KIND {
            BitmapKind::CpuSet => Bitmap::from(topology.cpuset().clone_target()),
            BitmapKind::NodeSet => Bitmap::from(topology.nodeset().clone_target()),
        };

        // Empty sets and sets outside the topology's complete cpuset/nodeset
        // are never valid. cpusets/nodesets outside the topology's main
        // cpuset/nodeset are also very likely to be invalid binding targets,
        // hence failure is expected upon encountering them.
        //
        // Non-Linux platforms may have arbitrary restrictions on what
        // constitutes a good CPU/memory binding target. In the case of Windows,
        // this is known to happen due to this OS' "processor group" notion.
        if set.is_empty() || !topology_set.includes(set) || !cfg!(target_os = "linux") {
            return Ok(());
        } else {
            let error = format!("{}", MemoryBindingError::BadSet(*object, set2.clone()));
            tracing::error!("Got unexpected {error}");
            return Err(TestCaseError::Fail(error.into()));
        }
    }

    // Make sure a single target flag is set if the allocation method can rebind
    // the current process/thread, no flag otherwise.
    if let Ok(true) = check_bad_membind_target_flags(can_bind_program, flags, result.as_ref().err())
    {
        return Ok(());
    }

    // The MIGRATE flag should not be used with pure memory allocation functions
    if !can_bind_program && flags.contains(MemoryBindingFlags::MIGRATE) {
        prop_assert!(matches!(result,
            Err(HybridError::Rust(MemoryBindingError::BadFlags(ParameterError(err_flags)))) if err_flags == flags));
        return Ok(());
    }

    // Handle unsupported policy/operation errors
    if let Err(HybridError::Rust(MemoryBindingError::Unsupported)) = result.as_ref() {
        // Detect use of an unsupported policy
        let membind_support = topology.feature_support().memory_binding().unwrap();
        let policy_supported = match policy {
            MemoryBindingPolicy::Bind => membind_support.bind_policy(),
            MemoryBindingPolicy::FirstTouch => membind_support.first_touch_policy(),
            MemoryBindingPolicy::Interleave => membind_support.interleave_policy(),
            MemoryBindingPolicy::NextTouch => membind_support.next_touch_policy(),
        };
        if !policy_supported {
            return Ok(());
        }

        // Non-Linux OSes have weird limitations, always tolerate the
        // Unsupported error on these platforms
        if cfg!(not(target_os = "linux")) {
            return Ok(());
        }
    }

    // At this point, all known error paths should have been considered
    let bytes = match result {
        Ok(bytes) => bytes,
        Err(e) => {
            tracing::error!("Got unexpected memory binding setup error: {e}");
            return Err(TestCaseError::fail(format!("{e}")));
        }
    };

    // Check that the final memory allocation makes sense
    check_memory_allocation(bytes, len)
}

/// Check that one hwloc memory allocator works
#[tracing::instrument(skip(bytes))]
fn check_memory_allocation(mut bytes: Bytes<'_>, len: usize) -> Result<(), TestCaseError> {
    prop_assert_eq!(bytes.len(), len);
    // If we allocated any bytes, check that we can write without
    // segfaults as a minimal sanity check
    if len > 0 {
        let first_byte = bytes.first_mut().unwrap().as_mut_ptr();
        // SAFETY: Originates from a valid reference
        unsafe { first_byte.write_volatile(42) };
        let last_byte = bytes.last_mut().unwrap().as_mut_ptr();
        // SAFETY: Originates from a valid reference
        unsafe { last_byte.write_volatile(142) };
    }
    Ok(())
}

/// Check that either the "target flags" of CPU binding operations are used
/// correctly correctly or errors are reported correctly.
///
/// Return true if an error was detected, so that the output of the underlying
/// CPU binding function is not examined further.
#[tracing::instrument]
fn check_bad_membind_target_flags<Set: SpecializedBitmap>(
    can_bind_program: bool,
    flags: MemoryBindingFlags,
    error: Option<&HybridError<MemoryBindingError<Set>>>,
) -> Result<bool, TestCaseError> {
    // We are only concerned with flags that specify the target
    let target_flags = flags & target_membind_flags();

    // Check that the number of target flags is right
    if (flags & target_flags).iter().count() != (can_bind_program as usize) {
        let expected_err = HybridError::Rust(MemoryBindingError::BadFlags(ParameterError(flags)));
        prop_assert_eq!(error, Some(&expected_err));
        return Ok(true);
    }
    Ok(false)
}

/// CPU binding flags which specify whether a thread or process is targeted
fn target_membind_flags() -> MemoryBindingFlags {
    MemoryBindingFlags::ASSUME_SINGLE_THREAD
        | MemoryBindingFlags::THREAD
        | MemoryBindingFlags::PROCESS
}

// === CPU binding test logic ===

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
            let error = format!("{}", CpuBindingError::BadCpuSet(set2.clone()));
            tracing::error!("Got unexpected {error}");
            return Err(TestCaseError::Fail(error.into()));
        }
    }

    // Make sure the target flags are valid
    if check_bad_cpubind_target_flags(target, flags, result.as_ref().err())? {
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
        let target_flags = flags & target_cpubind_flags();
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
    if check_bad_cpubind_target_flags(target, flags, result.as_ref().err())? {
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

/// Check that either the "target flags" of CPU binding operations are used
/// correctly correctly or errors are reported correctly.
///
/// Return true if an error was detected, so that the output of the underlying
/// CPU binding function is not examined further.
#[tracing::instrument]
fn check_bad_cpubind_target_flags(
    target: CpuBoundObject,
    flags: CpuBindingFlags,
    error: Option<&HybridError<CpuBindingError>>,
) -> Result<bool, TestCaseError> {
    // We are only concerned with flags that specify the target
    let target_flags = flags & target_cpubind_flags();

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

/// CPU binding flags which specify whether a thread or process is targeted
fn target_cpubind_flags() -> CpuBindingFlags {
    CpuBindingFlags::ASSUME_SINGLE_THREAD | CpuBindingFlags::THREAD | CpuBindingFlags::PROCESS
}

// WARNING: DO NOT CREATE ANY OTHER #[test] FUNCTION IN THIS INTEGRATION TEST!

// === The following is copypasted from hwlocality's unit testing code ===
//
// This is a workaround for the fact that integration tests do not link against
// the cfg(test) version of the crate and cannot request that the crate be built
// with the proptest feature.

/// Specialization of `set_with_reference` that uses the topology-wide cpuset or
/// nodeset as a reference
fn topology_related_set<Set: SpecializedBitmap>(
    topology_set: impl FnOnce(&Topology) -> BitmapRef<'_, Set>,
) -> impl Strategy<Value = Set> {
    set_with_reference(topology_set(Topology::test_instance()))
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
fn set_with_reference<SetRef: SpecializedBitmapRef>(
    reference: SetRef,
) -> impl Strategy<Value = SetRef::Owned> {
    // First, one of the reference set and its complement has to be finite
    let reference = reference.as_bitmap_ref();
    let finite_set = if reference.weight().is_some() {
        reference.clone()
    } else {
        !reference
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
        .prop_map(|(inside_elems, outside_elems)| SetRef::Owned::from(inside_elems | outside_elems))
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
        .prop_map(|some_flags| some_flags.into_iter().collect())
}

/// Generate an arbitrary memory binding policy
fn any_membind_policy() -> impl Strategy<Value = MemoryBindingPolicy> {
    let policies = enum_iterator::all::<MemoryBindingPolicy>().collect::<Vec<_>>();
    prop::sample::select(policies)
}

/// Generate an arbitrary set of user-accessible memory binding flags
fn any_membind_flags() -> impl Strategy<Value = MemoryBindingFlags> {
    let all_flags = MemoryBindingFlags::all()
        .iter()
        .filter(|flag| *flag != MemoryBindingFlags::BY_NODE_SET)
        .collect::<Vec<_>>();
    let num_flags = all_flags.len();
    prop::sample::subsequence(all_flags, 0..=num_flags)
        .prop_map(|some_flags| some_flags.into_iter().collect())
}

// WARNING: DO NOT CREATE ANY OTHER #[test] FUNCTION IN THIS INTEGRATION TEST!
