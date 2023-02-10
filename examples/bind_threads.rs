use hwloc2::{bitmap::CpuSet, cpu::CpuBindingFlags, objects::types::ObjectType, Topology};
use std::sync::{Arc, Mutex};
use std::thread;

/// Example which spawns one thread per core and then assigns it to each.
///
/// Example Output with 2 cores (no HT) on linux:
///
/// ```
/// Found 2 cores.
/// Thread 0: Before Some(0-1), After Some(0)
/// Thread 1: Before Some(0-1), After Some(1)
/// ```
fn main() {
    let topo = Arc::new(Mutex::new(Topology::new().unwrap()));

    // Grab the number of cores in a block so that the lock is removed once
    // the end of the block is reached.
    let num_cores = {
        let topo_rc = topo.clone();
        let topo_locked = topo_rc.lock().unwrap();
        (*topo_locked).objects_with_type(ObjectType::Core).len()
    };
    println!("Found {} cores.", num_cores);

    // Spawn one thread for each and pass the topology down into scope.
    let handles: Vec<_> = (0..num_cores)
        .map(|i| {
            let child_topo = topo.clone();
            thread::spawn(move || {
                // Get the current thread id and lock the topology to use.
                let tid = get_thread_id();
                let mut locked_topo = child_topo.lock().unwrap();

                // Thread binding before explicit set.
                let before = locked_topo
                    .thread_cpu_binding(tid, CpuBindingFlags::THREAD)
                    .unwrap();

                // load the cpuset for the given core index.
                let mut bind_to = cpuset_for_core(&*locked_topo, i).clone();

                // Get only one logical processor (in case the core is SMT/hyper-threaded).
                bind_to.singlify();

                // Set the binding.
                locked_topo
                    .bind_thread_cpu(tid, &bind_to, CpuBindingFlags::THREAD)
                    .unwrap();

                // Thread binding after explicit set.
                let after = locked_topo
                    .thread_cpu_binding(tid, CpuBindingFlags::THREAD)
                    .unwrap();
                println!("Thread {}: Before {:?}, After {:?}", i, before, after);
            })
        })
        .collect();

    // Wait for all threads to complete before ending the program.
    for h in handles {
        h.join().unwrap();
    }
}

/// Load the `CpuSet` for the given core index.
fn cpuset_for_core(topology: &Topology, idx: usize) -> &CpuSet {
    let cores = topology.objects_with_type(ObjectType::Core);
    match cores.get(idx) {
        Some(val) => val.cpuset().unwrap(),
        None => panic!("No Core found with id {}", idx),
    }
}

/// Helper method to get the thread id through libc, with current rust stable (1.5.0) its not
/// possible otherwise I think.
#[cfg(not(target_os = "windows"))]
fn get_thread_id() -> libc::pthread_t {
    unsafe { libc::pthread_self() }
}

#[cfg(target_os = "windows")]
fn get_thread_id() -> winapi::winnt::HANDLE {
    unsafe { kernel32::GetCurrentThread() }
}
