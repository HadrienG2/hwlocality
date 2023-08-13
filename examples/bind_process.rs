use anyhow::Context;
use hwlocality::{
    cpu::binding::CpuBindingFlags,
    objects::{types::ObjectType, TopologyObject},
    ProcessId, Topology,
};

/// Example which binds an arbitrary process (in this example this very same one)
/// to the last processing unit (core or hyperthread).
fn main() -> anyhow::Result<()> {
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
    // FIXME: get_proc_cpu_binding fails on Windows CI for unknown reasons
    //        May want to try again once this upsteam issue is resolved:
    //        https://github.com/open-mpi/hwloc/issues/78
    if cfg!(target_os = "windows") {
        println!(
            "This example currently fails on Windows for unknown reasons, and has been disabled"
        );
        return Ok(());
    }

    // load the current pid through libc
    let pid = get_pid();

    println!("Binding Process with PID {pid:?}");

    // Grab last PU and extract its CpuSet
    let cpuset = last_pu(&topology)?
        .cpuset()
        .context("PU objects should have a CpuSet")?;

    // Query the current cpu binding, and location if supported
    let print_binding_location = |situation: &str| -> anyhow::Result<()> {
        println!(
            "Cpu Binding {situation}: {:?}",
            topology.process_cpu_binding(pid, CpuBindingFlags::PROCESS)?
        );
        if support.get_process_last_cpu_location() {
            println!(
                "Cpu Location {situation}: {:?}",
                topology.last_process_cpu_location(pid, CpuBindingFlags::PROCESS)?
            )
        }
        Ok(())
    };

    // Query binding and CPU location before binding
    print_binding_location("before binding")?;

    // Bind to one core.
    topology.bind_process_cpu(pid, &cpuset, CpuBindingFlags::PROCESS)?;

    // Query binding and CPU location after binding
    print_binding_location("after binding")?;

    Ok(())
}

/// Find the last PU
fn last_pu(topology: &Topology) -> anyhow::Result<&TopologyObject> {
    topology
        .objects_with_type(ObjectType::PU)
        .next_back()
        .context("System should have at least once PU")
}

#[cfg(target_os = "windows")]
fn get_pid() -> ProcessId {
    unsafe { windows_sys::Win32::System::Threading::GetCurrentProcessId() }
}

#[cfg(not(target_os = "windows"))]
fn get_pid() -> ProcessId {
    unsafe { libc::getpid() }
}
