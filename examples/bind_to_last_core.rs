use anyhow::{ensure, Context};
use hwloc2::{
    cpu::binding::CpuBindingFlags,
    objects::{types::ObjectType, TopologyObject},
    Topology,
};

/// Bind to only one thread of the last core of the machine.
///
/// First find out where cores are, or else smaller sets of CPUs if
/// the OS doesn't have the notion of a "core".
///
/// Example Output with 2 cores (no HT) on linux:
///
/// ```
/// Cpu Binding before explicit bind: 0-1
/// Cpu Location before explicit bind: 0
/// Correctly bound to last core
/// Cpu Binding after explicit bind: 1
/// Cpu Location after explicit bind: 1
/// ```
fn main() -> anyhow::Result<()> {
    // Create topology and check feature support
    let topology = Topology::new()?;
    let support = topology
        .feature_support()
        .cpu_binding()
        .context("This example requires CPU binding support")?;
    ensure!(
        support.get_current_process() && support.set_current_process(),
        "This example needs support for querying and setting current process CPU bindings"
    );

    let topology = Topology::new()?;

    // Grab last core and exctract its CpuSet
    let cpuset = last_core(&topology)?
        .cpuset()
        .context("Cores should have CPUsets")?;

    // Query the current cpu binding, and location if supported
    let print_binding_location = || -> anyhow::Result<()> {
        println!(
            "Cpu Binding before explicit bind: {:?}",
            topology.cpu_binding(CpuBindingFlags::PROCESS)?
        );
        if support.get_current_process_last_cpu_location() {
            println!(
                "Cpu Location before explicit bind: {:?}",
                topology.last_cpu_location(CpuBindingFlags::PROCESS)?
            )
        }
        Ok(())
    };

    // Check binding and location before binding
    print_binding_location()?;

    // Try to bind all threads of the current (possibly multithreaded) process.
    topology.bind_cpu(cpuset, CpuBindingFlags::PROCESS)?;
    println!("Correctly bound to last core");

    // Check binding and location before binding
    print_binding_location()?;

    Ok(())
}

/// Find the last core
fn last_core(topo: &Topology) -> anyhow::Result<&TopologyObject> {
    let core_depth = topo.depth_or_below_for_type(ObjectType::Core)?;
    let mut all_cores = topo.objects_at_depth(core_depth);
    all_cores
        .next_back()
        .context("At least one Core or PU should be present")
}
