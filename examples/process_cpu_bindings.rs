use std::collections::{BTreeMap, BTreeSet};

use hwlocality::{
    cpu::{binding::CpuBindingFlags, cpuset::CpuSet},
    topology::{
        builder::BuildFlags,
        support::{CpuBindingSupport, FeatureSupport},
    },
    ProcessId, Topology,
};
use sysinfo::{ProcessRefreshKind, RefreshKind, System};

/// Example which displays process CPU bindings
fn main() -> eyre::Result<()> {
    // Create topology and check feature support
    let topology = Topology::builder()
        .with_flags(BuildFlags::INCLUDE_DISALLOWED)?
        .build()?;
    if !topology.supports(FeatureSupport::cpu_binding, CpuBindingSupport::get_process) {
        println!("This example needs support for querying process CPU bindings");
        return Ok(());
    }
    if !sysinfo::IS_SUPPORTED_SYSTEM {
        println!("This example needs support for querying the process list");
        return Ok(());
    }

    // FIXME: hwloc's get_proc_cpu_binding() mysteriously fails on Windows CI.
    //        May want to try again once this upstream issue is resolved:
    //        https://github.com/open-mpi/hwloc/issues/78
    if cfg!(target_os = "windows") {
        println!(
            "This example currently fails on Windows for unknown reasons, and has been disabled"
        );
        return Ok(());
    }

    // List processes and group them by CPU binding.
    // Use the empty CpuSet as an error sentinel, which is okay since a
    // process cannot be bound to no CPU (otherwise it couldn't make progress)
    let mut binding_to_pids = BTreeMap::<CpuSet, BTreeSet<ProcessId>>::new();
    let sys = System::new_with_specifics(
        RefreshKind::nothing().with_processes(ProcessRefreshKind::nothing()),
    );
    for pid in sys.processes().keys().copied() {
        let pid = usize::from(pid) as ProcessId;
        let binding = topology
            .process_cpu_binding(pid, CpuBindingFlags::empty())
            .unwrap_or(CpuSet::new());
        assert!(binding_to_pids.entry(binding).or_default().insert(pid));
    }

    // Display CPU binding names and PID lists, find the width of the largest display
    let mut widest_binding_name = 0;
    let mut widest_pid_list = 0;
    let displays = binding_to_pids
        .into_iter()
        .map(|(binding, pid_list)| {
            let binding_name = if binding.is_empty() {
                "Query failed".to_string()
            } else if binding == topology.complete_cpuset() {
                "All online CPUs".to_string()
            } else if binding == topology.allowed_cpuset() {
                "All allowed CPUs".to_string()
            } else if binding == topology.cpuset() {
                "All visible CPUs".to_string()
            } else {
                binding.to_string()
            };
            let pid_list = format!("{pid_list:?}");
            assert!(
                binding_name.is_ascii() && pid_list.is_ascii(),
                "Need to use unicode_width if this isn't true"
            );
            widest_binding_name = widest_binding_name.max(binding_name.len());
            widest_pid_list = widest_pid_list.max(pid_list.len());
            (binding_name, pid_list)
        })
        .collect::<Vec<_>>();

    // Display process PID bindings in a tabular fashion
    println!(
        "{0:binding_width$} │ PIDs",
        "CPU binding",
        binding_width = widest_binding_name
    );
    println!(
        "{0:─<binding_width$}─┼─{0:─<pids_width$}",
        "",
        binding_width = widest_binding_name,
        // Make header no larger than 80 columns to avoid terminal width overflow
        pids_width = widest_pid_list.min(80 - widest_binding_name - 3)
    );
    for (binding_name, pid_list) in displays {
        println!("{binding_name:widest_binding_name$} │ {pid_list}");
    }

    Ok(())
}
