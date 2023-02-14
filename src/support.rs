//! Topology support

// - API: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__configuration.html#gab8c76173c4a8ce1a9a9366012b1388e6
// - Struct: https://hwloc.readthedocs.io/en/v2.9/structhwloc__topology__support.html

use crate::ffi;
use libc::c_uchar;
use std::fmt;

/// Set of flags describing actual support for this topology
#[repr(C)]
pub struct TopologySupport {
    discovery: *const DiscoverySupport,
    cpubind: *const CpuBindingSupport,
    membind: *const MemoryBindingSupport,
    misc: *const MiscSupport,
}

impl TopologySupport {
    /// Flags describing actual discovery support for this topology
    pub fn discovery(&self) -> Option<&DiscoverySupport> {
        unsafe { ffi::deref_ptr(&self.discovery) }
    }

    /// Flags describing actual CPU binding support for this topology
    pub fn cpu_binding(&self) -> Option<&CpuBindingSupport> {
        unsafe { ffi::deref_ptr(&self.cpubind) }
    }

    /// Flags describing actual memory binding support for this topology
    pub fn memory_binding(&self) -> Option<&MemoryBindingSupport> {
        unsafe { ffi::deref_ptr(&self.membind) }
    }

    /// Flags describing miscellaneous features
    pub fn misc(&self) -> Option<&MiscSupport> {
        unsafe { ffi::deref_ptr(&self.misc) }
    }
}

impl fmt::Debug for TopologySupport {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("TopologySupport")
            .field("discovery", &self.discovery())
            .field("cpubind", &self.cpu_binding())
            .field("membind", &self.memory_binding())
            .field("misc", &self.misc())
            .finish()
    }
}

/// Flags describing actual discovery support for this topology
#[repr(C)]
#[derive(Debug)]
pub struct DiscoverySupport {
    pu: c_uchar,
    numa: c_uchar,
    numa_memory: c_uchar,
    disallowed_pu: c_uchar,
    disallowed_numa: c_uchar,
    cpukind_efficiency: c_uchar,
}

impl DiscoverySupport {
    /// Detecting the number of PU objects is supported
    pub fn pu(&self) -> bool {
        support_flag(self.pu)
    }

    /// Detecting the number of NUMA nodes is supported
    pub fn numa_count(&self) -> bool {
        support_flag(self.numa)
    }

    /// Detecting the amount of memory in NUMA nodes is supported
    pub fn numa_memory(&self) -> bool {
        support_flag(self.numa_memory)
    }

    /// Detecting and identifying PU objects that are not available to the
    /// current process is supported
    pub fn disallowed_pu(&self) -> bool {
        support_flag(self.disallowed_pu)
    }

    /// Detecting and identifying NUMA nodes that are not available to the
    /// current process is supported
    pub fn disallowed_numa(&self) -> bool {
        support_flag(self.disallowed_numa)
    }

    /// Detecting the efficiency of CPU kinds is supported
    pub fn cpukind_efficiency(&self) -> bool {
        support_flag(self.cpukind_efficiency)
    }
}

/// Flags describing actual CPU binding support for this topology
///
/// A flag may be set even if the feature isn't supported in all cases
/// (e.g. binding to random sets of non-contiguous objects).
#[repr(C)]
#[derive(Debug)]
pub struct CpuBindingSupport {
    set_thisproc_cpubind: c_uchar,
    get_thisproc_cpubind: c_uchar,
    set_proc_cpubind: c_uchar,
    get_proc_cpubind: c_uchar,
    set_thisthread_cpubind: c_uchar,
    get_thisthread_cpubind: c_uchar,
    set_thread_cpubind: c_uchar,
    get_thread_cpubind: c_uchar,
    get_thisproc_last_cpu_location: c_uchar,
    get_proc_last_cpu_location: c_uchar,
    get_thisthread_last_cpu_location: c_uchar,
}

impl CpuBindingSupport {
    /// Binding the whole current process is supported.
    pub fn set_current_process(&self) -> bool {
        support_flag(self.set_thisproc_cpubind)
    }

    /// Getting the binding of the whole current process is supported.
    pub fn get_current_process(&self) -> bool {
        support_flag(self.get_thisproc_cpubind)
    }

    /// Binding a whole given process is supported.
    pub fn set_process(&self) -> bool {
        support_flag(self.set_proc_cpubind)
    }

    /// Getting the binding of a whole given process is supported.
    pub fn get_process(&self) -> bool {
        support_flag(self.get_proc_cpubind)
    }

    /// Binding the current thread only is supported.
    pub fn set_current_thread(&self) -> bool {
        support_flag(self.set_thisthread_cpubind)
    }

    /// Getting the binding of the current thread only is supported.
    pub fn get_current_thread(&self) -> bool {
        support_flag(self.get_thisthread_cpubind)
    }

    /// Binding a given thread only is supported.
    pub fn set_thread(&self) -> bool {
        support_flag(self.set_thread_cpubind)
    }

    /// Getting the binding of a given thread only is supported.
    pub fn get_thread(&self) -> bool {
        support_flag(self.get_thread_cpubind)
    }

    /// Getting the last processors where the whole current process ran is supported.
    pub fn get_current_process_last_cpu_location(&self) -> bool {
        support_flag(self.get_thisproc_last_cpu_location)
    }

    /// Getting the last processors where a whole process ran is supported.
    pub fn get_process_last_cpu_location(&self) -> bool {
        support_flag(self.get_proc_last_cpu_location)
    }

    /// Getting the last processors where the current thread ran is supported.
    pub fn get_current_thread_last_cpu_location(&self) -> bool {
        support_flag(self.get_thisthread_last_cpu_location)
    }
}

/// Flags describing actual memory binding support for this topology
///
/// A flag may be set even if the feature isn't supported in all cases
/// (e.g. binding to random sets of non-contiguous objects).
#[repr(C)]
#[derive(Debug)]
pub struct MemoryBindingSupport {
    set_thisproc_membind: c_uchar,
    get_thisproc_membind: c_uchar,
    set_proc_membind: c_uchar,
    get_proc_membind: c_uchar,
    set_thisthread_membind: c_uchar,
    get_thisthread_membind: c_uchar,
    set_area_membind: c_uchar,
    get_area_membind: c_uchar,
    alloc_membind: c_uchar,
    firsttouch_membind: c_uchar,
    bind_membind: c_uchar,
    interleave_membind: c_uchar,
    replicate_membind: c_uchar,
    nexttouch_membind: c_uchar,
    migrate_membind: c_uchar,
    get_area_memlocation: c_uchar,
}

impl MemoryBindingSupport {
    /// Binding the whole current process is supported.
    pub fn set_current_process(&self) -> bool {
        support_flag(self.set_thisproc_membind)
    }

    /// Getting the binding of the whole current process is supported.
    pub fn get_current_process(&self) -> bool {
        support_flag(self.get_thisproc_membind)
    }

    /// Binding a whole given process is supported.
    pub fn set_process(&self) -> bool {
        support_flag(self.set_proc_membind)
    }

    /// Getting the binding of a whole given process is supported.
    pub fn get_process(&self) -> bool {
        support_flag(self.get_proc_membind)
    }

    /// Binding the current thread only is supported.
    pub fn set_current_thread(&self) -> bool {
        support_flag(self.set_thisthread_membind)
    }

    /// Getting the binding of the current thread only is supported.
    pub fn get_current_thread(&self) -> bool {
        support_flag(self.get_thisthread_membind)
    }

    /// Binding a given memory area is supported.
    pub fn set_area(&self) -> bool {
        support_flag(self.set_area_membind)
    }

    /// Getting the binding of a given memory area is supported.
    pub fn get_area(&self) -> bool {
        support_flag(self.get_area_membind)
    }

    /// Allocating a bound memory area is supported.
    pub fn alloc(&self) -> bool {
        support_flag(self.alloc_membind)
    }

    /// First-touch policy is supported.
    pub fn first_touch(&self) -> bool {
        support_flag(self.firsttouch_membind)
    }

    /// Bind policy is supported.
    pub fn bind(&self) -> bool {
        support_flag(self.bind_membind)
    }

    /// Interleave policy is supported.
    pub fn interleave(&self) -> bool {
        support_flag(self.interleave_membind)
    }

    /// Replication policy is supported.
    pub fn replicate(&self) -> bool {
        support_flag(self.replicate_membind)
    }

    /// Next-touch migration policy is supported.
    pub fn next_touch(&self) -> bool {
        support_flag(self.nexttouch_membind)
    }

    /// Migration flags is supported.
    pub fn migrate(&self) -> bool {
        support_flag(self.migrate_membind)
    }

    /// Getting the last NUMA nodes where a memory area was allocated is supported
    pub fn get_area_memory_location(&self) -> bool {
        support_flag(self.get_area_memlocation)
    }
}

/// Flags describing miscellaneous features
#[repr(C)]
#[derive(Debug)]
pub struct MiscSupport {
    imported_support: c_uchar,
}

impl MiscSupport {
    /// Support was imported when importing another topology
    pub fn imported(&self) -> bool {
        support_flag(self.imported_support)
    }
}

/// Decode topology support flag
fn support_flag(flag: c_uchar) -> bool {
    assert!(
        flag == 0 || flag == 1,
        "Unexpected support flag value {flag}"
    );
    flag == 1
}

#[cfg(test)]
mod tests {
    use crate::Topology;

    #[test]
    #[cfg(target_os = "linux")]
    fn should_support_cpu_binding_on_linux() {
        let topo = Topology::new().unwrap();

        assert!(topo.support().cpu_binding().unwrap().set_current_process());
        assert!(topo.support().cpu_binding().unwrap().set_current_thread());
    }

    #[test]
    #[cfg(target_os = "freebsd")]
    fn should_support_cpu_binding_on_freebsd() {
        let topo = Topology::new().unwrap();

        assert!(topo.support().cpu_binding().unwrap().set_current_process());
        assert!(topo.support().cpu_binding().unwrap().set_current_thread());
    }

    #[test]
    #[cfg(target_os = "macos")]
    fn should_not_support_cpu_binding_on_macos() {
        let topo = Topology::new().unwrap();

        assert_eq!(
            false,
            topo.support().cpu_binding().unwrap().set_current_process()
        );
        assert_eq!(
            false,
            topo.support().cpu_binding().unwrap().set_current_thread()
        );
    }
}
