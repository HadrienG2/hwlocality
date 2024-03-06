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
    memory::{
        binding::{
            Bytes, MemoryAllocationError, MemoryBindingError, MemoryBindingFlags,
            MemoryBindingPolicy,
        },
        nodeset::NodeSet,
    },
    topology::{
        support::{FeatureSupport, MemoryBindingSupport},
        Topology,
    },
    ProcessId,
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
        let curr_proc = cpubind_support.set_current_process();
        let curr_thr = cpubind_support.set_current_thread();
        let can_bind_self = |flags| match flags & target_cpubind_flags() {
            CpuBindingFlags::PROCESS => curr_proc,
            CpuBindingFlags::THREAD => curr_thr,
            CpuBindingFlags::ASSUME_SINGLE_THREAD => curr_proc | curr_thr,
            _ => true, // Doesn't matter, will fail flag validation
        };
        TestRunner::default()
            .run(
                &(
                    topology_related_set(Topology::complete_cpuset),
                    any_cpubind_flags(),
                ),
                |(cpuset, flags)| {
                    if can_bind_self(flags) {
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
                let can_query_self = |curr_proc, curr_thr| match target_flags {
                    CpuBindingFlags::PROCESS => curr_proc,
                    CpuBindingFlags::THREAD => curr_thr,
                    CpuBindingFlags::ASSUME_SINGLE_THREAD => curr_proc | curr_thr,
                    _ => true, // Doesn't matter, will fail flag validation
                };
                if can_query_self(
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
                if can_query_self(
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
        //
        // We also bias towards zero-sized allocations as that's a special case
        // that goes through a dedicated code path.
        let any_len = prop_oneof![
            1 => Just(0usize),
            2 => 1usize..(48 * 1024 * 1024)
        ];
        TestRunner::default()
            .run(&any_len, |len| test_allocate_memory(topology, len))
            .unwrap();

        // Test bound memory allocations in all supported configurations
        let can_bind_thisproc = membind_support.set_current_process();
        let can_bind_thisthread = membind_support.set_current_thread();
        let can_bind_self = |flags| match flags & target_membind_flags() {
            MemoryBindingFlags::PROCESS => can_bind_thisproc,
            MemoryBindingFlags::THREAD => can_bind_thisthread,
            MemoryBindingFlags::ASSUME_SINGLE_THREAD => can_bind_thisproc | can_bind_thisthread,
            _ => true, // Doesn't matter, will fail flag validation
        };
        TestRunner::default()
            .run(
                &(
                    &any_len,
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
                    if membind_support.allocate_bound() || can_bind_self(flags) {
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

        // Test process memory binding in all supported configurations
        TestRunner::default()
            .run(
                &(
                    topology_related_set(Topology::complete_cpuset),
                    topology_related_set(Topology::complete_nodeset),
                    any_membind_policy(),
                    any_membind_flags(),
                ),
                |(cpuset, nodeset, policy, flags)| {
                    if can_bind_self(flags) {
                        test_specialized_bitmap!(
                            test_bind_memory,
                            topology,
                            cpuset,
                            nodeset,
                            policy,
                            flags
                        )?;
                        test_unbind_memory(topology, flags)?;
                    }
                    if membind_support.set_process() {
                        test_specialized_bitmap!(
                            test_bind_process_memory,
                            topology,
                            cpuset,
                            nodeset,
                            my_pid,
                            policy,
                            flags
                        )?;
                        test_unbind_process_memory(topology, my_pid, flags)?;
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
        // Ignore unknown errors on Windows, we can't really interpret them
        #[cfg(windows)]
        Err(HybridError::Rust(MemoryAllocationError::Unknown)) => Ok(()),
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
    // Check for common memory binding errors
    let Some(bytes) =
        check_common_membind_errors(result, can_bind_program, topology, set, policy, flags)?
    else {
        return Ok(());
    };

    // If possible, check that the final memory allocation is indeed bound at
    // the right location. This requires...
    //
    // - Support for querying the memory binding of a memory area (duh)
    // - Strict binding mode (otherwise the actual location may be slightly
    //   different from what was requested)
    // - Nonzero allocation size (otherwise the location cannot be queried)
    // - Binding by NodeSet (as result of binding by CpuSet is hard to predict)
    if topology.supports(
        FeatureSupport::memory_binding,
        MemoryBindingSupport::get_area,
    ) && flags.contains(MemoryBindingFlags::STRICT)
        && len > 0
        && Set::BITMAP_KIND == BitmapKind::NodeSet
    {
        let result = topology.area_memory_binding::<_, Set>(&bytes[..], MemoryBindingFlags::STRICT);
        if result != Ok((set.clone(), Some(policy))) {
            tracing::error!("Got unexpected final allocation memory binding {result:?}");
            return Err(TestCaseError::fail(
                "Unexpected final allocation memory binding",
            ));
        }
    }

    // Check that the final memory allocation makes sense
    check_memory_allocation(bytes, len)
}

/// Check that one hwloc memory allocator works
#[tracing::instrument(skip(bytes))]
fn check_memory_allocation(mut bytes: Bytes<'_>, len: usize) -> Result<(), TestCaseError> {
    prop_assert_eq!(
        bytes.len(),
        len,
        "Final allocation has the wrong number of bytes"
    );
    // If we allocated any bytes, check that we can write without
    // segfaults as a minimal sanity check
    if len > 0 {
        let first_byte = bytes.first_mut().unwrap().as_mut_ptr();
        // SAFETY: Simple use of a valid reference
        unsafe { first_byte.write_volatile(42) };
        let last_byte = bytes.last_mut().unwrap().as_mut_ptr();
        // SAFETY: Simple use of a valid reference
        unsafe { last_byte.write_volatile(142) };
    }
    Ok(())
}

/// Test that hwloc's current process binding works
#[tracing::instrument(skip(topology))]
fn test_bind_memory(
    topology: &Topology,
    set: impl SpecializedBitmapRef + Copy + Debug,
    policy: MemoryBindingPolicy,
    flags: MemoryBindingFlags,
) -> Result<(), TestCaseError> {
    let result = topology.bind_memory(set, policy, flags);
    check_bind_memory(result, None, topology, &*set, policy, flags)
}

/// Test that hwloc's targeted process binding works
#[tracing::instrument(skip(topology))]
fn test_bind_process_memory(
    topology: &Topology,
    set: impl SpecializedBitmapRef + Copy + Debug,
    pid: ProcessId,
    policy: MemoryBindingPolicy,
    flags: MemoryBindingFlags,
) -> Result<(), TestCaseError> {
    let result = topology.bind_process_memory(pid, set, policy, flags);
    check_bind_memory(result, Some(pid), topology, &*set, policy, flags)
}

/// Common code path for process memory binding
#[tracing::instrument(skip(topology))]
fn check_bind_memory<Set: SpecializedBitmap>(
    result: Result<(), HybridError<MemoryBindingError<Set>>>,
    pid: Option<ProcessId>,
    topology: &Topology,
    set: &Set,
    policy: MemoryBindingPolicy,
    flags: MemoryBindingFlags,
) -> Result<(), TestCaseError> {
    // Check for common memory binding errors
    let Some(()) = check_common_membind_errors(result, true, topology, set, policy, flags)? else {
        return Ok(());
    };

    // If possible, check that the final process is indeed bound at the right
    // location. This requires...
    //
    // - Support for querying the memory binding of processes (duh)
    // - Strict binding mode (otherwise the actual location may be different)
    // - Binding by NodeSet (result of binding by CpuSet is hard to predict)
    if flags.contains(MemoryBindingFlags::STRICT) && Set::BITMAP_KIND == BitmapKind::NodeSet {
        let membind_support = topology.feature_support().memory_binding().unwrap();
        let final_binding = if let Some(pid) = pid {
            membind_support
                .get_process()
                .then(|| topology.process_memory_binding(pid, MemoryBindingFlags::STRICT))
        } else {
            (membind_support.get_current_process() || membind_support.get_current_thread()).then(
                || {
                    topology.memory_binding(
                        (flags & target_membind_flags()) | MemoryBindingFlags::STRICT,
                    )
                },
            )
        };
        if let Some(Ok(set_and_policy)) = &final_binding {
            if set_and_policy != &(set.clone(), Some(policy)) {
                tracing::error!("Got unexpected final process memory binding {final_binding:?}");
                return Err(TestCaseError::fail(
                    "Unexpected final process memory binding",
                ));
            }
        }
    }
    Ok(())
}

/// Check errors that can occur for all functions that bind memory
#[tracing::instrument(skip(topology, result))]
fn check_common_membind_errors<Set: SpecializedBitmap, Res: Debug>(
    result: Result<Res, HybridError<MemoryBindingError<Set>>>,
    can_bind_program: bool,
    topology: &Topology,
    set: &Set,
    policy: MemoryBindingPolicy,
    flags: MemoryBindingFlags,
) -> Result<Option<Res>, TestCaseError> {
    // Ignore unknown errors on Windows, we can't really make sense of them
    #[cfg(windows)]
    if let Err(HybridError::Rust(MemoryBindingError::Unknown)) = &result {
        return Ok(None);
    }

    // Handle invalid cpuset/nodeset errors
    if let Err(HybridError::Rust(MemoryBindingError::BadSet(object, set2))) = &result {
        prop_assert_eq!(
            set2,
            set,
            "Memory binding error set doesn't match input set"
        );

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
            return Ok(None);
        } else {
            let error = format!("{}", MemoryBindingError::BadSet(*object, set2.clone()));
            tracing::error!("Got unexpected {error}");
            return Err(TestCaseError::fail(error));
        }
    }

    // The MIGRATE flag should not be used with pure memory allocation functions
    let forbidden_flags = if can_bind_program {
        MemoryBindingFlags::empty()
    } else {
        MemoryBindingFlags::MIGRATE
    };

    // Make sure a single target flag is set if the allocation method can rebind
    // the current process/thread, no flag otherwise.
    if let Ok(true) = check_membind_flags(
        forbidden_flags,
        can_bind_program,
        flags,
        result.as_ref().err(),
    ) {
        return Ok(None);
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
            return Ok(None);
        }

        // Detect use of an unsupported flag
        if !membind_support.migrate_flag() && flags.contains(MemoryBindingFlags::MIGRATE) {
            return Ok(None);
        }
    }

    // At this point, all known Linux error paths should have been considered
    match result {
        Ok(bytes) => Ok(Some(bytes)),
        Err(e) => {
            if cfg!(target_os = "linux") {
                tracing::error!("Got unexpected memory binding setup error: {e}");
                Err(TestCaseError::fail(format!("{e}")))
            } else {
                // Non-Linux OSes have weird memory binding limitations, so we
                // always tolerate unexpected errors on these platforms
                Ok(None)
            }
        }
    }
}

/// Test that hwloc's current process un-binding works
#[tracing::instrument(skip(topology))]
fn test_unbind_memory(topology: &Topology, flags: MemoryBindingFlags) -> Result<(), TestCaseError> {
    let result = topology.unbind_memory(flags);
    check_unbind_memory(result, None, topology, flags)
}

/// Test that hwloc's targeted process un-binding works
#[tracing::instrument(skip(topology))]
fn test_unbind_process_memory(
    topology: &Topology,
    pid: ProcessId,
    flags: MemoryBindingFlags,
) -> Result<(), TestCaseError> {
    let result = topology.unbind_process_memory(pid, flags);
    check_unbind_memory(result, Some(pid), topology, flags)
}

/// Check errors that can occur for all functions that unbind memory
#[tracing::instrument(skip(topology, result))]
fn check_unbind_memory<Set: SpecializedBitmap>(
    result: Result<(), HybridError<MemoryBindingError<Set>>>,
    pid: Option<ProcessId>,
    topology: &Topology,
    flags: MemoryBindingFlags,
) -> Result<(), TestCaseError> {
    // Ignore unknown errors on Windows, we can't really make sense of them
    #[cfg(windows)]
    if let Err(HybridError::Rust(MemoryBindingError::Unknown)) = &result {
        return Ok(());
    }

    // Make sure a single target flag is set if the allocation method can rebind
    // the current process/thread, no flag otherwise.
    if let Ok(true) = check_membind_flags(
        MemoryBindingFlags::MIGRATE | MemoryBindingFlags::STRICT,
        pid.is_none(),
        flags,
        result.as_ref().err(),
    ) {
        return Ok(());
    }

    // At this point, all known Linux error paths should have been considered
    if let Err(e) = result {
        if cfg!(target_os = "linux") {
            tracing::error!("Got unexpected memory binding setup error: {e}");
            return Err(TestCaseError::fail(format!("{e}")));
        } else {
            // Non-Linux OSes have weird memory binding limitations, so we
            // always tolerate unexpected errors on these platforms
            return Ok(());
        }
    }

    // If possible, check that memory was indeed un-bound
    let membind_support = topology.feature_support().memory_binding().unwrap();
    let query_result = if let Some(pid) = pid {
        membind_support
            .get_process()
            .then(|| topology.process_memory_binding::<NodeSet>(pid, MemoryBindingFlags::STRICT))
    } else {
        (membind_support.get_current_process() || membind_support.get_current_thread()).then(|| {
            topology.memory_binding::<NodeSet>(
                (flags & target_membind_flags()) | MemoryBindingFlags::STRICT,
            )
        })
    };
    if let Some(Ok((nodeset, _policy))) = &query_result {
        if nodeset != &*topology.allowed_nodeset() {
            tracing::error!("Got unexpected unbound process binding: {query_result:?}");
            return Err(TestCaseError::fail("Unexpected unbound process binding"));
        }
    }
    Ok(())
}

/// Check that either the "target flags" of CPU binding operations are used
/// correctly correctly or errors are reported correctly.
///
/// Return true if an error was detected, so that the output of the underlying
/// CPU binding function is not examined further.
#[tracing::instrument]
fn check_membind_flags<Set: SpecializedBitmap>(
    forbidden_flags: MemoryBindingFlags,
    can_bind_thisprogram: bool,
    actual_flags: MemoryBindingFlags,
    error: Option<&HybridError<MemoryBindingError<Set>>>,
) -> Result<bool, TestCaseError> {
    // Make sure no forbidden flags are used
    let has_forbidden_flags = actual_flags.intersects(forbidden_flags);

    // Make sure target flags are used correctly
    let target_flags = actual_flags & target_membind_flags();
    let has_bad_target_flags = target_flags.iter().count() != (can_bind_thisprogram as usize);

    // Check that the number of target flags is right
    if has_forbidden_flags || has_bad_target_flags {
        let expected_error =
            HybridError::Rust(MemoryBindingError::BadFlags(ParameterError(actual_flags)));
        if error != Some(&expected_error) {
            tracing::error!("Expected bad target flags error, got {error:?}");
            return Err(TestCaseError::fail("Unexpected bad target flags outcome"));
        }
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
        prop_assert_eq!(set2, set, "CPU binding error set doesn't match input set");

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
            tracing::error!("Got unexpected bad CPU set error {error}");
            return Err(TestCaseError::fail(error));
        }
    }

    // Make sure the target flags are valid
    if check_cpubind_flags(
        CpuBindingFlags::empty(),
        target,
        flags,
        result.as_ref().err(),
    )? {
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
        let cpubind_support = topology.feature_support().cpu_binding().unwrap();
        let actual_binding = match target {
            // This is a bit of a logical shortcut, it assumes that if we can
            // set CPU binding for the current process/thread we can also query
            // it if we are able to query CPU bindings at all. Fix it if we ever
            // find a system where this is wrong.
            CpuBoundObject::ThisProgram => (cpubind_support.get_current_process()
                || cpubind_support.get_current_thread())
            .then(|| topology.cpu_binding(target_flags)),
            CpuBoundObject::ProcessOrThread(pid) => cpubind_support
                .get_process()
                .then(|| topology.process_cpu_binding(pid, target_flags)),
            CpuBoundObject::Thread(tid) => cpubind_support
                .get_thread()
                .then(|| topology.thread_cpu_binding(tid, target_flags)),
        };
        if let Some(actual_binding) = actual_binding {
            if actual_binding != Ok(set.clone()) {
                tracing::error!("Unexpected final process/thread CPU binding {actual_binding:?}");
                return Err(TestCaseError::fail(
                    "Unexpected final process/thread CPU binding",
                ));
            }
        }
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
    let forbidden_flags =
        if matches!(target, CpuBoundObject::Thread(_)) || flags.contains(CpuBindingFlags::THREAD) {
            CpuBindingFlags::STRICT
        } else {
            CpuBindingFlags::empty()
        };

    // Common code path with CPU location check
    check_cpubind_query_result(result, topology, flags, target, forbidden_flags)
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

    // Common code path with CPU affinity check
    check_cpubind_query_result(result, topology, flags, target, CpuBindingFlags::STRICT)
}

/// Check the result of a CPU binding or CPU location query
#[tracing::instrument(skip(topology))]
fn check_cpubind_query_result(
    result: Result<CpuSet, HybridError<CpuBindingError>>,
    topology: &Topology,
    flags: CpuBindingFlags,
    target: CpuBoundObject,
    forbidden_flags: CpuBindingFlags,
) -> Result<(), TestCaseError> {
    // Make sure the target flags are valid
    if check_cpubind_flags(forbidden_flags, target, flags, result.as_ref().err())? {
        return Ok(());
    }

    // Make sure the `NO_MEMORY_BINDING` flag was not specified
    if flags.contains(CpuBindingFlags::NO_MEMORY_BINDING) {
        let expected_error = HybridError::Rust(CpuBindingError::BadFlags(ParameterError(flags)));
        if result.as_ref().err() != Some(&expected_error) {
            tracing::error!("Expected bad target flags error, got {result:?}");
            return Err(TestCaseError::fail("Unexpected bad target flags outcome"));
        }
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
    prop_assert!(
        !cpuset.is_empty(),
        "Should never observe an empty CPU binding"
    );
    prop_assert!(
        topology.complete_cpuset().includes(&cpuset),
        "Should never observe a CPU binding that overflows the topology"
    );
    Ok(())
}

/// Check that either the "target flags" of CPU binding operations are used
/// correctly correctly or errors are reported correctly.
///
/// Return true if an error was detected, so that the output of the underlying
/// CPU binding function is not examined further.
#[tracing::instrument]
fn check_cpubind_flags(
    forbidden_flags: CpuBindingFlags,
    target: CpuBoundObject,
    actual_flags: CpuBindingFlags,
    error: Option<&HybridError<CpuBindingError>>,
) -> Result<bool, TestCaseError> {
    // If flags validation fails, we should get this error
    let expected_err = Some(HybridError::Rust(CpuBindingError::BadFlags(
        ParameterError(actual_flags),
    )));
    let expected_err = expected_err.as_ref();

    // Make sure no forbidden flags are present
    let mut bad_flags = actual_flags.intersects(forbidden_flags);

    // Otherwise, we are concerned with flags that specify the target
    let target_flags = actual_flags & target_cpubind_flags();

    // Only on Linux can THREAD can be used on processes
    let is_linux_special_case = target_flags.contains(CpuBindingFlags::THREAD)
        && matches!(target, CpuBoundObject::ProcessOrThread(_));
    bad_flags |= is_linux_special_case && cfg!(not(target_os = "linux"));

    // Number of target flags should be correct for this operation
    bad_flags |= (actual_flags & target_flags).iter().count()
        != (target == CpuBoundObject::ThisProgram || is_linux_special_case) as usize;
    if bad_flags {
        if error != expected_err {
            tracing::error!("Expected bad target flags error, got {error:?}");
            return Err(TestCaseError::fail("Unexpected bad target flags outcome"));
        }
        return Ok(true);
    }
    Ok(false)
}

/// CPU binding flags which specify whether a thread or process is targeted
fn target_cpubind_flags() -> CpuBindingFlags {
    CpuBindingFlags::ASSUME_SINGLE_THREAD | CpuBindingFlags::THREAD | CpuBindingFlags::PROCESS
}

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
