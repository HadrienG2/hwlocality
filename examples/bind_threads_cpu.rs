use anyhow::Context;
use hwlocality::{
    cpu::binding::CpuBindingFlags,
    objects::types::ObjectType,
    topology::support::{DiscoverySupport, FeatureSupport},
    ThreadId, Topology,
};

/// Example which spawns one thread per core and then assigns it to each.
///
/// Example Output with 2 cores (no HT) on linux:
///
/// ```
/// Found 2 cores.
/// Thread 0: Binding went from 0-1 to 0
/// Thread 1: Binding went from 0-1 to 1
/// ```
fn main() -> anyhow::Result<()> {
    // Create topology and check feature support
    let topology = Topology::new()?;
    if !topology.supports(FeatureSupport::discovery, DiscoverySupport::pu_count) {
        println!("This example needs accurate reporting of PU objects");
        return Ok(());
    }
    let Some(cpu_support) = topology.feature_support().cpu_binding() else {
        println!("This example requires CPU binding support");
        return Ok(());
    };
    if !(cpu_support.get_thread() && cpu_support.set_thread()) {
        println!("This example needs support for querying and setting thread CPU bindings");
        return Ok(());
    }

    // Grab the number of cores in a block so that the lock is removed once
    // the end of the block is reached.
    let core_depth = topology.depth_or_below_for_type(ObjectType::Core)?;
    let cores = topology.objects_at_depth(core_depth).collect::<Vec<_>>();
    println!("Found {} cores", cores.len());

    // Spawn one thread for each and pass the topology down into scope.
    std::thread::scope(|scope| {
        for (idx, core) in cores.into_iter().enumerate() {
            let topology = &topology;
            scope.spawn(move || -> anyhow::Result<()> {
                // Get the current thread id and lock the topology to use.
                let tid = get_thread_id();

                // Thread binding before explicit set.
                let before = topology.thread_cpu_binding(tid, CpuBindingFlags::THREAD)?;

                // load the cpuset for the given core index.
                let mut bind_to = core
                    .cpuset()
                    .context("CPU cores should have CpuSets")?
                    .clone();

                // Get only one logical processor (in case the core is SMT/hyper-threaded).
                bind_to.singlify();

                // Set the binding.
                topology.bind_thread_cpu(tid, &bind_to, CpuBindingFlags::THREAD)?;

                // Thread binding after explicit set.
                let after = topology.thread_cpu_binding(tid, CpuBindingFlags::THREAD)?;

                // Report what was done
                println!("Thread {idx}: Binding went from {before:?} to {after:?}");

                Ok(())
            });
        }
    });

    Ok(())
}

/// Helper method to get the thread id through libc or windows API
#[cfg(not(target_os = "windows"))]
fn get_thread_id() -> ThreadId {
    unsafe { libc::pthread_self() }
}
//
#[cfg(target_os = "windows")]
fn get_thread_id() -> ThreadId {
    unsafe { windows_sys::Win32::System::Threading::GetCurrentThread() }
}
