use hwlocality::{
    topology::support::{CpuBindingSupport, FeatureSupport, MemoryBindingSupport},
    Topology,
};

/// Example on how to check for specific topology support of a feature.
fn main() -> anyhow::Result<()> {
    let topology = Topology::new()?;

    // Check if processes can be bound to cpusets
    println!("CPU binding support:");
    let cpu_binding_support = |check_feature: fn(&CpuBindingSupport) -> bool| {
        topology.supports(FeatureSupport::cpu_binding, check_feature)
    };
    println!(
        "- Current process: {}",
        cpu_binding_support(CpuBindingSupport::set_current_process)
    );
    println!(
        "- Any process: {}",
        cpu_binding_support(CpuBindingSupport::set_process)
    );

    // Check if threads can be bound to cpusets
    println!(
        "- Current thread: {}",
        cpu_binding_support(CpuBindingSupport::set_current_thread)
    );
    println!(
        "- Any thread: {}",
        cpu_binding_support(CpuBindingSupport::set_thread)
    );

    // Check if processes can be bound to NUMA nodes
    println!("\nMemory binding support:");
    let memory_binding_support = |check_feature: fn(&MemoryBindingSupport) -> bool| {
        topology.supports(FeatureSupport::memory_binding, check_feature)
    };
    println!(
        "- Current process: {}",
        memory_binding_support(MemoryBindingSupport::set_current_process)
    );
    println!(
        "- Any process: {}",
        memory_binding_support(MemoryBindingSupport::set_process)
    );

    // Check if threads can be bound to NUMA nodes
    println!(
        "- Current thread: {}",
        memory_binding_support(MemoryBindingSupport::set_current_thread)
    );

    // Check if memory allocations can be bound to NUMA nodes
    println!(
        "- New bound allocation: {}",
        memory_binding_support(MemoryBindingSupport::allocate_bound)
    );
    println!(
        "- Bind pre-existing allocation: {}",
        memory_binding_support(MemoryBindingSupport::set_area)
    );

    // Debug Print all the Support Flags
    println!("\nRaw support flags: {:#?}", topology.feature_support());

    Ok(())
}
