//! hwloc feature support
//!
//! Generally speaking, a given hardware/OS platform will not support every
//! hwloc feature. This module exposes the feature support flags,
//! which you can query using the [`Topology::feature_support()`] method and its
//! [`Topology::supports()`] shortcut.

// - API: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__configuration.html#gab8c76173c4a8ce1a9a9366012b1388e6
// - Struct: https://hwloc.readthedocs.io/en/v2.9/structhwloc__topology__support.html

#[cfg(doc)]
use super::{builder::BuildFlags, Topology};
use crate::ffi::{
    self,
    transparent::{AsNewtype, TransparentNewtype},
};
#[cfg(feature = "hwloc-2_3_0")]
use hwlocality_sys::hwloc_topology_misc_support;
use hwlocality_sys::{
    hwloc_topology_cpubind_support, hwloc_topology_discovery_support,
    hwloc_topology_membind_support, hwloc_topology_support,
};
#[allow(unused)]
#[cfg(test)]
use pretty_assertions::{assert_eq, assert_ne};
use std::{ffi::c_uchar, fmt, hash::Hash};

/// Set of flags describing actual hwloc feature support for this topology
///
/// You cannot create an owned object of this type, it belongs to the topology.
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
#[allow(clippy::non_send_fields_in_send_ty, missing_copy_implementations)]
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
        unsafe { ffi::deref_ptr(&self.0.discovery).map(AsNewtype::as_newtype) }
    }

    /// Support for getting and setting thread/process CPU bindings
    #[doc(alias = "hwloc_topology_support::cpubind")]
    pub fn cpu_binding(&self) -> Option<&CpuBindingSupport> {
        // SAFETY: - Pointer validity is a type invariant
        //         - Rust aliasing rules are enforced by deriving the reference
        //           from &self, which itself is derived from &Topology
        unsafe { ffi::deref_ptr(&self.0.cpubind).map(AsNewtype::as_newtype) }
    }

    /// Support for getting and setting thread/process NUMA node bindings
    #[doc(alias = "hwloc_topology_support::membind")]
    pub fn memory_binding(&self) -> Option<&MemoryBindingSupport> {
        // SAFETY: - Pointer validity is a type invariant
        //         - Rust aliasing rules are enforced by deriving the reference
        //           from &self, which itself is derived from &Topology
        unsafe { ffi::deref_ptr(&self.0.membind).map(AsNewtype::as_newtype) }
    }

    /// Miscellaneous support information
    #[cfg(feature = "hwloc-2_3_0")]
    #[doc(alias = "hwloc_topology_support::misc")]
    pub fn misc(&self) -> Option<&MiscSupport> {
        // SAFETY: - Pointer validity is a type invariant
        //         - Rust aliasing rules are enforced by deriving the reference
        //           from &self, which itself is derived from &Topology
        unsafe { ffi::deref_ptr(&self.0.misc).map(AsNewtype::to_newtype) }
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
// SAFETY: No internal mutability
unsafe impl Send for FeatureSupport {}
//
// SAFETY: No internal mutability
unsafe impl Sync for FeatureSupport {}
//
// SAFETY: FeatureSupport is a repr(transparent) newtype of hwloc_topology_support
unsafe impl TransparentNewtype for FeatureSupport {
    type Inner = hwloc_topology_support;
}

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
//
// SAFETY: DiscoverySupport is a repr(transparent) newtype of hwloc_topology_discovery_support
unsafe impl TransparentNewtype for DiscoverySupport {
    type Inner = hwloc_topology_discovery_support;
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
//
// SAFETY: CpuBindingSupport is a repr(transparent) newtype of hwloc_topology_cpubind_support
unsafe impl TransparentNewtype for CpuBindingSupport {
    type Inner = hwloc_topology_cpubind_support;
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
    pub fn allocate_bound(&self) -> bool {
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
//
// SAFETY: MemoryBindingSupport is a repr(transparent) newtype of hwloc_topology_membind_support
unsafe impl TransparentNewtype for MemoryBindingSupport {
    type Inner = hwloc_topology_membind_support;
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
//
#[cfg(feature = "hwloc-2_3_0")]
// SAFETY: MiscSupport is a repr(transparent) newtype of hwloc_topology_misc_support
unsafe impl TransparentNewtype for MiscSupport {
    type Inner = hwloc_topology_misc_support;
}

/// Decode topology support flag
fn support_flag(flag: c_uchar) -> bool {
    assert!(
        flag == 0 || flag == 1,
        "Unexpected support flag value {flag}"
    );
    flag == 1
}

#[allow(clippy::cognitive_complexity, clippy::too_many_lines)]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::topology::Topology;
    #[allow(unused)]
    use pretty_assertions::{assert_eq, assert_ne};
    use static_assertions::{assert_impl_all, assert_not_impl_any};
    use std::{
        collections::hash_map::DefaultHasher,
        fmt::{
            self, Binary, Debug, Display, LowerExp, LowerHex, Octal, Pointer, UpperExp, UpperHex,
        },
        hash::{Hash, Hasher},
        io::{self, Read},
        ops::Deref,
        panic::UnwindSafe,
        ptr,
    };

    // Check that public types in this module keep implementing all expected
    // traits, in the interest of detecting future semver-breaking changes
    assert_impl_all!(FeatureSupport:
        Debug, Default, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(FeatureSupport:
        Binary, Clone, Deref, Display, Drop, IntoIterator, LowerExp, LowerHex,
        Octal, PartialOrd, Pointer, Read, ToOwned, UpperExp, UpperHex,
        fmt::Write, io::Write
    );
    assert_impl_all!(CpuBindingSupport:
        Copy, Default, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(CpuBindingSupport:
        Binary, Deref, Drop, IntoIterator, LowerExp, LowerHex, Octal,
        PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write, io::Write
    );
    assert_impl_all!(DiscoverySupport:
        Copy, Default, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(DiscoverySupport:
        Binary, Deref, Drop, IntoIterator, LowerExp, LowerHex, Octal,
        PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write, io::Write
    );
    assert_impl_all!(MemoryBindingSupport:
        Copy, Default, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(MemoryBindingSupport:
        Binary, Deref, Drop, IntoIterator, LowerExp, LowerHex, Octal,
        PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write, io::Write
    );
    #[cfg(feature = "hwloc-2_3_0")]
    assert_impl_all!(MiscSupport:
        Copy, Default, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    #[cfg(feature = "hwloc-2_3_0")]
    assert_not_impl_any!(MiscSupport:
        Binary, Deref, Drop, IntoIterator, LowerExp, LowerHex, Octal,
        PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write, io::Write
    );

    fn expect_support(
        discovery: hwloc_topology_discovery_support,
        cpubind: hwloc_topology_cpubind_support,
        membind: hwloc_topology_membind_support,
    ) {
        let support = Topology::test_instance().feature_support();
        let flag = |flag: c_uchar| flag != 0;

        let discovery_support = support.discovery().unwrap();
        assert_eq!(discovery_support.pu_count(), flag(discovery.pu));
        assert_eq!(discovery_support.numa_count(), flag(discovery.numa));
        assert_eq!(discovery_support.numa_memory(), flag(discovery.numa_memory));
        #[cfg(feature = "hwloc-2_1_0")]
        {
            assert_eq!(
                discovery_support.disallowed_pu(),
                flag(discovery.disallowed_pu)
            );
            assert_eq!(
                discovery_support.disallowed_numa(),
                flag(discovery.disallowed_numa)
            );
        }
        // NOTE: Support for cpukind_efficiency has varied over time, so can't
        //       test its value for a given OS

        let cpubind_support = support.cpu_binding().unwrap();
        assert_eq!(
            cpubind_support.set_current_process(),
            flag(cpubind.set_thisproc_cpubind)
        );
        assert_eq!(
            cpubind_support.get_current_process(),
            flag(cpubind.get_thisproc_cpubind)
        );
        assert_eq!(
            cpubind_support.set_process(),
            flag(cpubind.set_proc_cpubind)
        );
        assert_eq!(
            cpubind_support.get_process(),
            flag(cpubind.get_proc_cpubind)
        );
        assert_eq!(
            cpubind_support.set_current_thread(),
            flag(cpubind.set_thisthread_cpubind)
        );
        assert_eq!(
            cpubind_support.get_current_thread(),
            flag(cpubind.get_thisthread_cpubind)
        );
        assert_eq!(
            cpubind_support.set_thread(),
            flag(cpubind.set_thread_cpubind)
        );
        assert_eq!(
            cpubind_support.get_thread(),
            flag(cpubind.get_thread_cpubind)
        );
        assert_eq!(
            cpubind_support.get_current_process_last_cpu_location(),
            flag(cpubind.get_thisproc_last_cpu_location)
        );
        assert_eq!(
            cpubind_support.get_process_last_cpu_location(),
            flag(cpubind.get_proc_last_cpu_location)
        );
        assert_eq!(
            cpubind_support.get_current_thread_last_cpu_location(),
            flag(cpubind.get_thisthread_last_cpu_location)
        );

        let membind_support = support.memory_binding().unwrap();
        assert_eq!(
            membind_support.set_current_process(),
            flag(membind.set_thisproc_membind)
        );
        assert_eq!(
            membind_support.get_current_process(),
            flag(membind.get_thisproc_membind)
        );
        assert_eq!(
            membind_support.set_process(),
            flag(membind.set_proc_membind)
        );
        assert_eq!(
            membind_support.get_process(),
            flag(membind.get_proc_membind)
        );
        assert_eq!(
            membind_support.set_current_thread(),
            flag(membind.set_thisthread_membind)
        );
        assert_eq!(
            membind_support.get_current_thread(),
            flag(membind.get_thisthread_membind)
        );
        assert_eq!(membind_support.set_area(), flag(membind.set_area_membind));
        assert_eq!(membind_support.get_area(), flag(membind.get_area_membind));
        assert_eq!(
            membind_support.get_area_memory_location(),
            flag(membind.get_area_memlocation)
        );
        assert_eq!(
            membind_support.allocate_bound(),
            flag(membind.alloc_membind)
        );
        assert_eq!(
            membind_support.first_touch_policy(),
            flag(membind.firsttouch_membind)
        );
        assert_eq!(membind_support.bind_policy(), flag(membind.bind_membind));
        assert_eq!(
            membind_support.interleave_policy(),
            flag(membind.interleave_membind)
        );
        assert_eq!(
            membind_support.next_touch_policy(),
            flag(membind.nexttouch_membind)
        );
        assert_eq!(
            membind_support.migrate_flag(),
            flag(membind.migrate_membind)
        );

        #[cfg(feature = "hwloc-2_3_0")]
        assert!(!support.misc().unwrap().imported());
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn linux() {
        expect_support(
            hwloc_topology_discovery_support {
                pu: 1,
                numa: 1,
                numa_memory: 1,
                #[cfg(feature = "hwloc-2_1_0")]
                disallowed_pu: 1,
                #[cfg(feature = "hwloc-2_1_0")]
                disallowed_numa: 1,
                #[cfg(feature = "hwloc-2_4_0")]
                cpukind_efficiency: 1,
            },
            hwloc_topology_cpubind_support {
                set_thisproc_cpubind: 1,
                get_thisproc_cpubind: 1,
                set_proc_cpubind: 1,
                get_proc_cpubind: 1,
                set_thisthread_cpubind: 1,
                get_thisthread_cpubind: 1,
                set_thread_cpubind: 1,
                get_thread_cpubind: 1,
                get_thisproc_last_cpu_location: 1,
                get_proc_last_cpu_location: 1,
                get_thisthread_last_cpu_location: 1,
            },
            hwloc_topology_membind_support {
                set_thisproc_membind: 0,
                get_thisproc_membind: 0,
                set_proc_membind: 0,
                get_proc_membind: 0,
                set_thisthread_membind: 1,
                get_thisthread_membind: 1,
                set_area_membind: 1,
                get_area_membind: 1,
                alloc_membind: 1,
                firsttouch_membind: 1,
                bind_membind: 1,
                interleave_membind: 1,
                nexttouch_membind: 0,
                migrate_membind: 1,
                get_area_memlocation: 1,
            },
        );
    }

    #[test]
    #[cfg(target_os = "macos")]
    fn macos() {
        expect_support(
            hwloc_topology_discovery_support {
                pu: 1,
                numa: 1,
                numa_memory: 0,
                #[cfg(feature = "hwloc-2_1_0")]
                disallowed_pu: 0,
                #[cfg(feature = "hwloc-2_1_0")]
                disallowed_numa: 0,
                #[cfg(feature = "hwloc-2_4_0")]
                cpukind_efficiency: 1,
            },
            hwloc_topology_cpubind_support {
                set_thisproc_cpubind: 0,
                get_thisproc_cpubind: 0,
                set_proc_cpubind: 0,
                get_proc_cpubind: 0,
                set_thisthread_cpubind: 0,
                get_thisthread_cpubind: 0,
                set_thread_cpubind: 0,
                get_thread_cpubind: 0,
                get_thisproc_last_cpu_location: 0,
                get_proc_last_cpu_location: 0,
                get_thisthread_last_cpu_location: 0,
            },
            hwloc_topology_membind_support {
                set_thisproc_membind: 0,
                get_thisproc_membind: 0,
                set_proc_membind: 0,
                get_proc_membind: 0,
                set_thisthread_membind: 0,
                get_thisthread_membind: 0,
                set_area_membind: 0,
                get_area_membind: 0,
                alloc_membind: 0,
                firsttouch_membind: 0,
                bind_membind: 0,
                interleave_membind: 0,
                nexttouch_membind: 0,
                migrate_membind: 0,
                get_area_memlocation: 0,
            },
        );
    }

    #[test]
    #[cfg(target_os = "windows")]
    fn windows() {
        expect_support(
            hwloc_topology_discovery_support {
                pu: 1,
                numa: 1,
                numa_memory: 1,
                #[cfg(feature = "hwloc-2_1_0")]
                disallowed_pu: 0,
                #[cfg(feature = "hwloc-2_1_0")]
                disallowed_numa: 0,
                #[cfg(feature = "hwloc-2_4_0")]
                cpukind_efficiency: 1,
            },
            hwloc_topology_cpubind_support {
                set_thisproc_cpubind: 1,
                get_thisproc_cpubind: 1,
                set_proc_cpubind: 1,
                get_proc_cpubind: 1,
                set_thisthread_cpubind: 1,
                get_thisthread_cpubind: 1,
                set_thread_cpubind: 1,
                get_thread_cpubind: 1,
                get_thisproc_last_cpu_location: 0,
                get_proc_last_cpu_location: 0,
                get_thisthread_last_cpu_location: 1,
            },
            hwloc_topology_membind_support {
                set_thisproc_membind: 1,
                get_thisproc_membind: 1,
                set_proc_membind: 1,
                get_proc_membind: 1,
                set_thisthread_membind: 1,
                get_thisthread_membind: 1,
                set_area_membind: 0,
                get_area_membind: 0,
                alloc_membind: 1,
                firsttouch_membind: 0,
                bind_membind: 1,
                interleave_membind: 0,
                nexttouch_membind: 0,
                migrate_membind: 0,
                get_area_memlocation: 1,
            },
        );
    }

    #[test]
    fn feature_support() {
        let default_support = Topology::test_instance().feature_support();
        let null_support = &FeatureSupport(hwloc_topology_support {
            discovery: ptr::null(),
            cpubind: ptr::null(),
            membind: ptr::null(),
            #[cfg(feature = "hwloc-2_3_0")]
            misc: ptr::null(),
        });
        let null_discovery = &FeatureSupport(hwloc_topology_support {
            discovery: ptr::null(),
            ..default_support.0
        });
        let null_cpubind = &FeatureSupport(hwloc_topology_support {
            cpubind: ptr::null(),
            ..default_support.0
        });
        let null_membind = &FeatureSupport(hwloc_topology_support {
            membind: ptr::null(),
            ..default_support.0
        });
        #[cfg(feature = "hwloc-2_3_0")]
        let null_misc = &FeatureSupport(hwloc_topology_support {
            misc: ptr::null(),
            ..default_support.0
        });

        fn check_debug(support: &FeatureSupport) {
            #[cfg(feature = "hwloc-2_3_0")]
            let misc_debug = format!(", misc: {:?}", support.misc());
            #[cfg(not(feature = "hwloc-2_3_0"))]
            let misc_debug = String::new();
            assert_eq!(
                format!("{support:?}"),
                format!(
                    "FeatureSupport {{ discovery: {:?}, cpubind: {:?}, membind: {:?}{} }}",
                    support.discovery(),
                    support.cpu_binding(),
                    support.memory_binding(),
                    misc_debug,
                )
            );
        }
        check_debug(default_support);
        check_debug(null_support);
        check_debug(null_discovery);
        check_debug(null_cpubind);
        check_debug(null_membind);
        #[cfg(feature = "hwloc-2_3_0")]
        check_debug(null_misc);

        fn hash<T: Hash>(t: &T) -> u64 {
            let mut s = DefaultHasher::new();
            t.hash(&mut s);
            s.finish()
        }
        fn compare(support1: &FeatureSupport, support2: &FeatureSupport, equal: bool) {
            if equal {
                assert_eq!(support1, support2);
                assert_eq!(hash(support1), hash(support2));
            } else {
                assert_ne!(support1, support2);
                assert_ne!(hash(support1), hash(support2));
            }
        }
        compare(default_support, default_support, true);
        compare(null_support, null_support, true);
        compare(default_support, null_support, false);
        compare(default_support, null_discovery, false);
        compare(default_support, null_cpubind, false);
        compare(default_support, null_membind, false);
        #[cfg(feature = "hwloc-2_3_0")]
        compare(default_support, null_misc, false);
    }
}
