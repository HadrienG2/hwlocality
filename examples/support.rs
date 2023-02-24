use hwloc2::{
    support::{CpuBindingSupport, FeatureSupport, MemoryBindingSupport},
    Topology,
};

/// Example on how to check for specific topology support of a feature.
fn main() -> anyhow::Result<()> {
    let topology = Topology::new()?;

    // Check if Process Binding for CPUs is supported
    let cpu_binding_support = |check_feature: fn(&CpuBindingSupport) -> bool| {
        topology.supports(FeatureSupport::cpu_binding, check_feature)
    };
    println!(
        "CPU Binding (current process) supported: {}",
        cpu_binding_support(CpuBindingSupport::set_current_process)
    );
    println!(
        "CPU Binding (any process) supported: {}",
        cpu_binding_support(CpuBindingSupport::set_process)
    );

    // Check if Thread Binding for CPUs is supported
    println!(
        "CPU Binding (current thread) supported: {}",
        cpu_binding_support(CpuBindingSupport::set_current_thread)
    );
    println!(
        "CPU Binding (any thread) supported: {}",
        cpu_binding_support(CpuBindingSupport::set_thread)
    );

    // Check if Memory Binding is supported
    println!(
        "Memory Binding supported: {}",
        topology.supports(
            FeatureSupport::memory_binding,
            MemoryBindingSupport::set_current_process
        )
    );

    // Debug Print all the Support Flags
    println!("All Flags:\n{:#?}", topology.feature_support());

    Ok(())
}
