//! hwloc feature support

// - API: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__configuration.html#gab8c76173c4a8ce1a9a9366012b1388e6
// - Struct: https://hwloc.readthedocs.io/en/v2.9/structhwloc__topology__support.html

use crate::ffi;
use std::{ffi::c_uchar, fmt, hash::Hash, ptr};

/// Set of flags describing actual hwloc feature support for this topology
#[repr(C)]
pub struct FeatureSupport {
    discovery: *const DiscoverySupport,
    cpubind: *const CpuBindingSupport,
    membind: *const MemoryBindingSupport,
    #[cfg(feature = "hwloc-2_3_0")]
    misc: *const MiscSupport,
}
//
impl FeatureSupport {
    /// Support for discovering information about the topology
    pub fn discovery(&self) -> Option<&DiscoverySupport> {
        unsafe { ffi::deref_ptr(&self.discovery) }
    }

    /// Support for getting and setting thread/process CPU bindings
    pub fn cpu_binding(&self) -> Option<&CpuBindingSupport> {
        unsafe { ffi::deref_ptr(&self.cpubind) }
    }

    /// Support for getting and setting thread/process NUMA node bindings
    pub fn memory_binding(&self) -> Option<&MemoryBindingSupport> {
        unsafe { ffi::deref_ptr(&self.membind) }
    }

    /// Miscellaneous support information
    #[cfg(feature = "hwloc-2_3_0")]
    pub fn misc(&self) -> Option<&MiscSupport> {
        unsafe { ffi::deref_ptr(&self.misc) }
    }
}
//
impl Default for FeatureSupport {
    fn default() -> Self {
        Self {
            discovery: ptr::null(),
            cpubind: ptr::null(),
            membind: ptr::null(),
            #[cfg(feature = "hwloc-2_3_0")]
            misc: ptr::null(),
        }
    }
}
//
impl fmt::Debug for FeatureSupport {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut debug = f.debug_struct("FeatureSupport");
        debug
            .field("discovery", &self.discovery())
            .field("cpubind", &self.cpu_binding())
            .field("membind", &self.memory_binding());
        #[cfg(feature = "hwloc-2_3_0")]
        debug.field("misc", &self.misc());
        debug.finish()
    }
}
//
impl Hash for FeatureSupport {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.discovery().hash(state);
        self.cpu_binding().hash(state);
        self.memory_binding().hash(state);
        #[cfg(feature = "hwloc-2_3_0")]
        self.misc().hash(state);
    }
}
//
impl PartialEq for FeatureSupport {
    #[allow(unused_mut)]
    fn eq(&self, other: &Self) -> bool {
        let mut eq = self.discovery() == other.discovery()
            && self.cpu_binding() == other.cpu_binding()
            && self.memory_binding() == other.memory_binding();
        #[cfg(feature = "hwloc-2_3_0")]
        {
            eq &= self.misc() == other.misc();
        }
        eq
    }
}
//
impl Eq for FeatureSupport {}

/// Support for discovering information about the topology
#[repr(C)]
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct DiscoverySupport {
    pu: c_uchar,
    numa: c_uchar,
    numa_memory: c_uchar,
    #[cfg(feature = "hwloc-2_1_0")]
    disallowed_pu: c_uchar,
    #[cfg(feature = "hwloc-2_1_0")]
    disallowed_numa: c_uchar,
    #[cfg(feature = "hwloc-2_4_0")]
    cpukind_efficiency: c_uchar,
}

impl DiscoverySupport {
    /// Detecting the number of PU objects is supported
    pub fn pu_count(&self) -> bool {
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
    #[cfg(feature = "hwloc-2_1_0")]
    pub fn disallowed_pu(&self) -> bool {
        support_flag(self.disallowed_pu)
    }

    /// Detecting and identifying NUMA nodes that are not available to the
    /// current process is supported
    #[cfg(feature = "hwloc-2_1_0")]
    pub fn disallowed_numa(&self) -> bool {
        support_flag(self.disallowed_numa)
    }

    /// Detecting the efficiency of CPU kinds is supported
    #[cfg(feature = "hwloc-2_4_0")]
    pub fn cpukind_efficiency(&self) -> bool {
        support_flag(self.cpukind_efficiency)
    }
}

/// Support for getting and setting thread/process CPU bindings
///
/// A flag may be set even if the feature isn't supported in all cases
/// (e.g. binding to random sets of non-contiguous objects).
#[repr(C)]
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
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

/// Support for getting and setting thread/process NUMA node bindings
///
/// A flag may be set even if the feature isn't supported in all cases
/// (e.g. binding to random sets of non-contiguous objects).
#[repr(C)]
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
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

    /// Getting the last NUMA nodes where a memory area was allocated is supported
    pub fn get_area_memory_location(&self) -> bool {
        support_flag(self.get_area_memlocation)
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

    /// Next-touch migration policy is supported.
    pub fn next_touch(&self) -> bool {
        support_flag(self.nexttouch_membind)
    }

    /// Replication policy is supported.
    pub fn replicate(&self) -> bool {
        support_flag(self.replicate_membind)
    }

    /// Migration flags is supported.
    pub fn migrate(&self) -> bool {
        support_flag(self.migrate_membind)
    }
}

/// Miscellaneous support information
#[cfg(feature = "hwloc-2_3_0")]
#[repr(C)]
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct MiscSupport {
    imported_support: c_uchar,
}

#[cfg(feature = "hwloc-2_3_0")]
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
    use super::*;
    use crate::topology::Topology;

    fn cpu_binding_supported(kind: fn(&CpuBindingSupport) -> bool) -> bool {
        Topology::test_instance().supports(FeatureSupport::cpu_binding, kind)
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn should_support_cpu_binding_on_linux() {
        assert!(cpu_binding_supported(
            CpuBindingSupport::set_current_process
        ));
        assert!(cpu_binding_supported(CpuBindingSupport::set_current_thread));
    }

    #[test]
    #[cfg(target_os = "freebsd")]
    fn should_support_cpu_binding_on_freebsd() {
        assert!(cpu_binding_supported(
            CpuBindingSupport::set_current_process
        ));
        assert!(cpu_binding_supported(CpuBindingSupport::set_current_thread));
    }

    #[test]
    #[cfg(target_os = "macos")]
    fn should_not_support_cpu_binding_on_macos() {
        assert!(!cpu_binding_supported(
            CpuBindingSupport::set_current_process
        ));
        assert!(!cpu_binding_supported(
            CpuBindingSupport::set_current_thread
        ));
    }
}
