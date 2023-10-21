use eyre::eyre;
use hwlocality::{
    cpu::binding::CpuBindingFlags,
    object::{types::ObjectType, TopologyObject},
    ProcessId, Topology,
};
use sysinfo::SystemExt;

/// Example which binds an arbitrary process (in this example this very same one)
/// to the last processing unit (core or hyperthread).
fn main() -> eyre::Result<()> {
    // Create topology and check feature support
    let topology = Topology::new()?;
    let Some(support) = topology.feature_support().cpu_binding() else {
        println!("This example requires CPU binding support");
        return Ok(());
    };
    if !(support.get_process() && support.set_process()) {
        println!("This example needs support for querying and setting process CPU bindings");
        return Ok(());
    }
    if !sysinfo::System::IS_SUPPORTED {
        println!("This example needs support for querying current PID");
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

    // Determine the active process' PID
    let pid = get_pid();
    println!("Binding Process with PID {pid:?}");

    // Grab last PU and extract its CpuSet
    let cpuset = last_pu(&topology)?
        .cpuset()
        .ok_or_else(|| eyre!("PU objects should have a CpuSet"))?;

    // Query the current cpu binding, and location if supported
    let print_binding_location = |situation: &str| -> eyre::Result<()> {
        println!(
            "Cpu Binding {situation}: {:?}",
            topology.process_cpu_binding(pid, CpuBindingFlags::empty())?
        );
        if support.get_process_last_cpu_location() {
            println!(
                "Cpu Location {situation}: {:?}",
                topology.last_process_cpu_location(pid, CpuBindingFlags::empty())?
            )
        }
        Ok(())
    };

    // Query binding and CPU location before binding
    print_binding_location("before binding")?;

    // Bind to one core.
    topology.bind_process_cpu(pid, cpuset, CpuBindingFlags::empty())?;

    // Query binding and CPU location after binding
    print_binding_location("after binding")?;

    Ok(())
}

/// Find the last PU
fn last_pu(topology: &Topology) -> eyre::Result<&TopologyObject> {
    topology
        .objects_with_type(ObjectType::PU)
        .next_back()
        .ok_or_else(|| eyre!("system should have at least one PU"))
}

/// Query the current process' PID
fn get_pid() -> ProcessId {
    usize::from(sysinfo::get_current_pid().expect("Failed to query PID")) as _
}
