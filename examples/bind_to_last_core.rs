use anyhow::Context;
use hwlocality::{
    cpu::binding::CpuBindingFlags,
    object::{types::ObjectType, TopologyObject},
    Topology,
};

/// Bind to the CPU last core of the machine.
///
/// First find out where cores are, or else smaller sets of logical CPUs if
/// the OS doesn't have the notion of a "core".
///
/// Example Output with 2 cores (no HT) on linux:
///
/// ```
/// Cpu Binding before explicit binding: 0-1
/// Cpu Location before explicit binding: 0
/// Correctly bound to last core
/// Cpu Binding after explicit binding: 1
/// Cpu Location after explicit binding: 1
/// ```
fn main() -> anyhow::Result<()> {
    // Create topology and check feature support
    let topology = Topology::new()?;
    let Some(support) = topology.feature_support().cpu_binding() else {
        println!("This example requires CPU binding support");
        return Ok(());
    };
    if !((support.get_current_process() || support.get_current_thread())
        && (support.set_current_process() || support.set_current_thread()))
    {
        println!(
            "This example needs support for querying and setting current process CPU bindings"
        );
        return Ok(());
    }

    // Find the last core on the system and extract its CpuSet
    let cpuset = last_core(&topology)?
        .cpuset()
        .context("Cores should have CPUsets")?;

    // Query the current cpu binding, and location if supported
    let print_binding_location = |situation: &str| -> anyhow::Result<()> {
        println!(
            "Cpu Binding {situation}: {:?}",
            topology.cpu_binding(CpuBindingFlags::ASSUME_SINGLE_THREAD)?
        );
        if support.get_current_process_last_cpu_location() {
            println!(
                "Cpu Location {situation}: {:?}",
                topology.last_cpu_location(CpuBindingFlags::ASSUME_SINGLE_THREAD)?
            )
        }
        Ok(())
    };

    // Check binding and location before binding
    print_binding_location("before explicit binding")?;

    // Try to bind all threads of the current (possibly multithreaded) process.
    topology.bind_cpu(cpuset, CpuBindingFlags::ASSUME_SINGLE_THREAD)?;
    println!("Correctly bound to last core");

    // Check binding and location before binding
    print_binding_location("after explicit binding")?;

    Ok(())
}

/// Find the last core on the system
fn last_core(topology: &Topology) -> anyhow::Result<&TopologyObject> {
    let core_depth = topology.depth_or_below_for_type(ObjectType::Core)?;
    let mut all_cores = topology.objects_at_depth(core_depth);
    all_cores
        .next_back()
        .context("At least one Core or PU should be present")
}
