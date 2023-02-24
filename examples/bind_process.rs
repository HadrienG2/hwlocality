use anyhow::{ensure, Context};
use hwloc2::{
    cpu::binding::CpuBindingFlags,
    objects::{types::ObjectType, TopologyObject},
    ProcessId, Topology,
};

/// Example which binds an arbitrary process (in this example this very same one)
/// to the last processing unit (core or hyperthread).
fn main() -> anyhow::Result<()> {
    // Create topology and check feature support
    let topology = Topology::new()?;
    let support = topology
        .feature_support()
        .cpu_binding()
        .context("This example requires CPU binding support")?;
    ensure!(
        support.get_process() && support.set_process(),
        "This example needs support for querying and setting process CPU bindings"
    );

    // load the current pid through libc
    let pid = get_pid();

    println!("Binding Process with PID {:?}", pid);

    // Grab last PU and extract its CpuSet
    let cpuset = last_pu(&topology)?
        .cpuset()
        .context("PU objects should have a CpuSet")?;

    println!(
        "Before Bind: {:?}",
        topology.process_cpu_binding(pid, CpuBindingFlags::PROCESS)?
    );

    // Print last CPU Location, if supported
    let print_last_location = || -> anyhow::Result<()> {
        if support.get_process_last_cpu_location() {
            println!(
                "Last Known CPU Location: {:?}",
                topology.last_process_cpu_location(pid, CpuBindingFlags::PROCESS)?
            )
        }
        Ok(())
    };

    // Print last CPU location before binding
    print_last_location()?;

    // Bind to one core.
    topology.bind_process_cpu(pid, cpuset, CpuBindingFlags::PROCESS)?;

    println!(
        "After Bind: {:?}",
        topology.process_cpu_binding(pid, CpuBindingFlags::PROCESS)?
    );

    // Print last CPU location after binding
    print_last_location()?;

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
