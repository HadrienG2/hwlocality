use hwloc2::{
    cpu::binding::CpuBindingFlags,
    objects::{types::ObjectType, TopologyObject},
    ProcessId, Topology,
};

/// Example which binds an arbitrary process (in this example this very same one) to
/// the last core.
fn main() {
    let mut topo = Topology::new().unwrap();

    // load the current pid through libc
    let pid = get_pid();

    println!("Binding Process with PID {:?}", pid);

    // Grab last core and exctract its CpuSet
    let mut cpuset = last_core(&mut topo).cpuset().unwrap().clone();

    // Get only one logical processor (in case the core is SMT/hyper-threaded).
    cpuset.singlify();

    println!(
        "Before Bind: {:?}",
        topo.process_cpu_binding(pid, CpuBindingFlags::PROCESS)
            .unwrap()
    );

    // Last CPU Location for this PID (not implemented on all systems)
    if let Ok(l) = topo.last_process_cpu_location(pid, CpuBindingFlags::PROCESS) {
        println!("Last Known CPU Location: {:?}", l);
    }

    // Bind to one core.
    topo.bind_process_cpu(pid, &cpuset, CpuBindingFlags::PROCESS)
        .unwrap();

    println!(
        "After Bind: {:?}",
        topo.process_cpu_binding(pid, CpuBindingFlags::PROCESS)
            .unwrap()
    );

    // Last CPU Location for this PID (not implemented on all systems)
    if let Ok(l) = topo.last_process_cpu_location(pid, CpuBindingFlags::PROCESS) {
        println!("Last Known CPU Location: {:?}", l);
    }
}

/// Find the last core
fn last_core(topo: &mut Topology) -> &TopologyObject {
    let core_depth = topo.depth_or_below_for_type(ObjectType::Core).unwrap();
    let all_cores = topo.objects_at_depth(core_depth);
    all_cores.last().unwrap()
}

#[cfg(target_os = "windows")]
fn get_pid() -> ProcessId {
    unsafe { windows_sys::Win32::System::Threading::GetCurrentProcessId() }
}

#[cfg(not(target_os = "windows"))]
fn get_pid() -> ProcessId {
    unsafe { libc::getpid() }
}
