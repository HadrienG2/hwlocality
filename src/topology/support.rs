//! hwloc feature support
// TODO: Long-form description

// - API: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__configuration.html#gab8c76173c4a8ce1a9a9366012b1388e6
// - Struct: https://hwloc.readthedocs.io/en/v2.9/structhwloc__topology__support.html

#[cfg(doc)]
use super::builder::BuildFlags;
use crate::ffi;
#[cfg(feature = "hwloc-2_3_0")]
use hwlocality_sys::hwloc_topology_misc_support;
use hwlocality_sys::{
    hwloc_topology_cpubind_support, hwloc_topology_discovery_support,
    hwloc_topology_membind_support, hwloc_topology_support,
};
use std::{ffi::c_uchar, fmt, hash::Hash};

/// Set of flags describing actual hwloc feature support for this topology
//
// --- Implementation details ---
//
// # Safety
//
// As a type invariant, all inner pointers are assumed to be safe to dereference
// and devoid of mutable aliases if non-null, as long as the host
// FeatureSupport is reachable at all.
//
// This is enforced through the following precautions:
//
// - No API exposes an owned FeatureSupport, only references to it bound by
//   the source topology's lifetime are exposed
// - The initial feature support that is set up by hwloc at topology
//   construction time is trusted to be correct
// - There is no API for modifying a loaded topology's feature support
#[derive(Default)]
#[doc(alias = "hwloc_topology_support")]
#[repr(transparent)]
pub struct FeatureSupport(hwloc_topology_support);
//
impl FeatureSupport {
    /// Support for discovering information about the topology
    #[doc(alias = "hwloc_topology_support::discovery")]
    pub fn discovery(&self) -> Option<&DiscoverySupport> {
        // SAFETY: - Pointer validity is a type invariant
        //         - Rust aliasing rules are enforced by deriving the reference
        //           from &self, which itself is derived from &Topology
        //         - DiscoverySupport is a repr(transparent) newtype of
        //           hwloc_topology_discovery_support
        unsafe { ffi::deref_ptr_newtype(&self.0.discovery) }
    }

    /// Support for getting and setting thread/process CPU bindings
    #[doc(alias = "hwloc_topology_support::cpubind")]
    pub fn cpu_binding(&self) -> Option<&CpuBindingSupport> {
        // SAFETY: - Pointer validity is a type invariant
        //         - Rust aliasing rules are enforced by deriving the reference
        //           from &self, which itself is derived from &Topology
        //         - CpuBindingSupport is a repr(transparent) newtype of
        //           hwloc_topology_cpubind_support
        unsafe { ffi::deref_ptr_newtype(&self.0.cpubind) }
    }

    /// Support for getting and setting thread/process NUMA node bindings
    #[doc(alias = "hwloc_topology_support::membind")]
    pub fn memory_binding(&self) -> Option<&MemoryBindingSupport> {
        // SAFETY: - Pointer validity is a type invariant
        //         - Rust aliasing rules are enforced by deriving the reference
        //           from &self, which itself is derived from &Topology
        //         - MemoryBinding is indeed a newtype of
        //           hwloc_topology_membind_support
        unsafe { ffi::deref_ptr_newtype(&self.0.membind) }
    }

    /// Miscellaneous support information
    #[cfg(feature = "hwloc-2_3_0")]
    #[doc(alias = "hwloc_topology_support::misc")]
    pub fn misc(&self) -> Option<&MiscSupport> {
        // SAFETY: - Pointer validity is a type invariant
        //         - Rust aliasing rules are enforced by deriving the reference
        //           from &self, which itself is derived from &Topology
        //         - MiscSupport is a repr(transparent) newtype of
        //           hwloc_topology_misc_support
        unsafe { ffi::deref_ptr_newtype(&self.0.misc) }
    }
}
//
impl fmt::Debug for FeatureSupport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
//
unsafe impl Send for FeatureSupport {}
unsafe impl Sync for FeatureSupport {}

/// Support for discovering information about the topology
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_topology_discovery_support")]
#[repr(transparent)]
pub struct DiscoverySupport(hwloc_topology_discovery_support);
//
impl DiscoverySupport {
    /// Detecting the number of PU objects is supported
    #[doc(alias = "hwloc_topology_discovery_support::pu")]
    pub fn pu_count(&self) -> bool {
        support_flag(self.0.pu)
    }

    /// Detecting the number of NUMA nodes is supported
    #[doc(alias = "hwloc_topology_discovery_support::numa")]
    pub fn numa_count(&self) -> bool {
        support_flag(self.0.numa)
    }

    /// Detecting the amount of memory in NUMA nodes is supported
    #[doc(alias = "hwloc_topology_discovery_support::numa_memory")]
    pub fn numa_memory(&self) -> bool {
        support_flag(self.0.numa_memory)
    }

    /// Detecting and identifying PU objects that are not available to the
    /// current process is supported
    #[cfg(feature = "hwloc-2_1_0")]
    #[doc(alias = "hwloc_topology_discovery_support::disallowed_pu")]
    pub fn disallowed_pu(&self) -> bool {
        support_flag(self.0.disallowed_pu)
    }

    /// Detecting and identifying NUMA nodes that are not available to the
    /// current process is supported
    #[cfg(feature = "hwloc-2_1_0")]
    #[doc(alias = "hwloc_topology_discovery_support::disallowed_numa")]
    pub fn disallowed_numa(&self) -> bool {
        support_flag(self.0.disallowed_numa)
    }

    /// Detecting the efficiency of CPU kinds is supported
    ///
    /// See also [Kinds of CPU cores](../struct.Topology.html#kinds-of-cpu-cores).
    #[cfg(feature = "hwloc-2_4_0")]
    #[doc(alias = "hwloc_topology_discovery_support::cpukind_efficiency")]
    pub fn cpukind_efficiency(&self) -> bool {
        support_flag(self.0.cpukind_efficiency)
    }
}

/// Support for getting and setting thread/process CPU bindings
///
/// A flag may be set even if the feature isn't supported in all cases
/// (e.g. binding to random sets of non-contiguous objects).
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_topology_cpubind_support")]
#[repr(transparent)]
pub struct CpuBindingSupport(hwloc_topology_cpubind_support);
//
impl CpuBindingSupport {
    /// Binding the whole current process is supported
    #[doc(alias = "hwloc_topology_cpubind_support::set_thisproc_cpubind")]
    pub fn set_current_process(&self) -> bool {
        support_flag(self.0.set_thisproc_cpubind)
    }

    /// Getting the binding of the whole current process is supported
    #[doc(alias = "hwloc_topology_cpubind_support::get_thisproc_cpubind")]
    pub fn get_current_process(&self) -> bool {
        support_flag(self.0.get_thisproc_cpubind)
    }

    /// Binding a whole given process is supported
    #[doc(alias = "hwloc_topology_cpubind_support::set_proc_cpubind")]
    pub fn set_process(&self) -> bool {
        support_flag(self.0.set_proc_cpubind)
    }

    /// Getting the binding of a whole given process is supported
    #[doc(alias = "hwloc_topology_cpubind_support::get_proc_cpubind")]
    pub fn get_process(&self) -> bool {
        support_flag(self.0.get_proc_cpubind)
    }

    /// Binding the current thread only is supported
    #[doc(alias = "hwloc_topology_cpubind_support::set_thisthread_cpubind")]
    pub fn set_current_thread(&self) -> bool {
        support_flag(self.0.set_thisthread_cpubind)
    }

    /// Getting the binding of the current thread only is supported
    #[doc(alias = "hwloc_topology_cpubind_support::get_thisthread_cpubind")]
    pub fn get_current_thread(&self) -> bool {
        support_flag(self.0.get_thisthread_cpubind)
    }

    /// Binding a given thread only is supported
    #[doc(alias = "hwloc_topology_cpubind_support::set_thread_cpubind")]
    pub fn set_thread(&self) -> bool {
        support_flag(self.0.set_thread_cpubind)
    }

    /// Getting the binding of a given thread only is supported
    #[doc(alias = "hwloc_topology_cpubind_support::get_thread_cpubind")]
    pub fn get_thread(&self) -> bool {
        support_flag(self.0.get_thread_cpubind)
    }

    /// Getting the last processors where the whole current process ran is supported
    #[doc(alias = "hwloc_topology_cpubind_support::get_thisproc_last_cpu_location")]
    pub fn get_current_process_last_cpu_location(&self) -> bool {
        support_flag(self.0.get_thisproc_last_cpu_location)
    }

    /// Getting the last processors where a whole process ran is supported
    #[doc(alias = "hwloc_topology_cpubind_support::get_proc_last_cpu_location")]
    pub fn get_process_last_cpu_location(&self) -> bool {
        support_flag(self.0.get_proc_last_cpu_location)
    }

    /// Getting the last processors where the current thread ran is supported
    #[doc(alias = "hwloc_topology_cpubind_support::get_thisthread_last_cpu_location")]
    pub fn get_current_thread_last_cpu_location(&self) -> bool {
        support_flag(self.0.get_thisthread_last_cpu_location)
    }
}

/// Support for getting and setting thread/process NUMA node bindings
///
/// A flag may be set even if the feature isn't supported in all cases
/// (e.g. binding to random sets of non-contiguous objects).
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_topology_membind_support")]
#[repr(transparent)]
pub struct MemoryBindingSupport(hwloc_topology_membind_support);
//
impl MemoryBindingSupport {
    /// Binding the whole current process is supported
    #[doc(alias = "hwloc_topology_membind_support::set_thisproc_membind")]
    pub fn set_current_process(&self) -> bool {
        support_flag(self.0.set_thisproc_membind)
    }

    /// Getting the binding of the whole current process is supported
    #[doc(alias = "hwloc_topology_membind_support::get_thisproc_membind")]
    pub fn get_current_process(&self) -> bool {
        support_flag(self.0.get_thisproc_membind)
    }

    /// Binding a whole given process is supported
    #[doc(alias = "hwloc_topology_membind_support::set_proc_membind")]
    pub fn set_process(&self) -> bool {
        support_flag(self.0.set_proc_membind)
    }

    /// Getting the binding of a whole given process is supported
    #[doc(alias = "hwloc_topology_membind_support::get_proc_membind")]
    pub fn get_process(&self) -> bool {
        support_flag(self.0.get_proc_membind)
    }

    /// Binding the current thread only is supported
    #[doc(alias = "hwloc_topology_membind_support::set_thisthread_membind")]
    pub fn set_current_thread(&self) -> bool {
        support_flag(self.0.set_thisthread_membind)
    }

    /// Getting the binding of the current thread only is supported
    #[doc(alias = "hwloc_topology_membind_support::get_thisthread_membind")]
    pub fn get_current_thread(&self) -> bool {
        support_flag(self.0.get_thisthread_membind)
    }

    /// Binding a given memory area is supported
    #[doc(alias = "hwloc_topology_membind_support::set_area_membind")]
    pub fn set_area(&self) -> bool {
        support_flag(self.0.set_area_membind)
    }

    /// Getting the binding of a given memory area is supported
    #[doc(alias = "hwloc_topology_membind_support::get_area_membind")]
    pub fn get_area(&self) -> bool {
        support_flag(self.0.get_area_membind)
    }

    /// Getting the last NUMA nodes where a memory area was allocated is supported
    #[doc(alias = "hwloc_topology_membind_support::get_area_memlocation")]
    pub fn get_area_memory_location(&self) -> bool {
        support_flag(self.0.get_area_memlocation)
    }

    /// Allocating a bound memory area is supported
    #[doc(alias = "hwloc_topology_membind_support::alloc_membind")]
    pub fn alloc(&self) -> bool {
        support_flag(self.0.alloc_membind)
    }

    /// First-touch policy is supported
    #[doc(alias = "hwloc_topology_membind_support::firsttouch_membind")]
    pub fn first_touch_policy(&self) -> bool {
        support_flag(self.0.firsttouch_membind)
    }

    /// Bind policy is supported
    #[doc(alias = "hwloc_topology_membind_support::bind_membind")]
    pub fn bind_policy(&self) -> bool {
        support_flag(self.0.bind_membind)
    }

    /// Interleave policy is supported
    #[doc(alias = "hwloc_topology_membind_support::interleave_membind")]
    pub fn interleave_policy(&self) -> bool {
        support_flag(self.0.interleave_membind)
    }

    /// Next-touch migration policy is supported
    #[doc(alias = "hwloc_topology_membind_support::nexttouch_membind")]
    pub fn next_touch_policy(&self) -> bool {
        support_flag(self.0.nexttouch_membind)
    }

    /// Migration flag is supported
    #[doc(alias = "hwloc_topology_membind_support::migrate_membind")]
    pub fn migrate_flag(&self) -> bool {
        support_flag(self.0.migrate_membind)
    }
}

/// Miscellaneous support information
#[cfg(feature = "hwloc-2_3_0")]
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_topology_misc_support")]
#[repr(transparent)]
pub struct MiscSupport(hwloc_topology_misc_support);
//
#[cfg(feature = "hwloc-2_3_0")]
impl MiscSupport {
    /// Support was imported when importing another topology
    ///
    /// See also [`BuildFlags::IMPORT_SUPPORT`].
    #[doc(alias = "hwloc_topology_misc_support::imported_support")]
    pub fn imported(&self) -> bool {
        support_flag(self.0.imported_support)
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

    #[allow(unused)]
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
