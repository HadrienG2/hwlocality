//! Rust Bindings for the Hwloc library
//!
//! This library is a rust binding to the hwloc C library, which provides a portable abstraction
//! of the hierarchical topology of modern architectures, including NUMA memory nodes, sockets,
//! shared caches, cores and simultaneous multithreading.
//!
//! # Usage
//!
//! First, add the following to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! hwloc = "0.3.0"
//! ```
//!
//! Next, add this to your crate root:
//!
//! ```no_run
//! extern crate hwloc;
//! ```
//!
//! Here is a quick example which walks the `Topology` and prints it out:
//!
//! ```no_run
//! extern crate hwloc;
//!
//! use hwloc::Topology;
//!
//! fn main() {
//! 	let topo = Topology::new().unwrap();
//!
//! 	for i in 0..topo.depth() {
//! 		println!("*** Objects at level {}", i);
//!
//! 		for (idx, object) in topo.objects_at_depth(i).iter().enumerate() {
//! 			println!("{}: {}", idx, object);
//! 		}
//! 	}
//! }
//! ```
//!
//! You can also [look at](https://github.com/daschl/hwloc-rs/tree/master/examples)
//! more examples, if you want to run them check out the next section below.
//!
//! # Running Examples
//! The library ships with examples, and to run them you need to clone the repository
//! and then run them through `cargo run --example=`.
//!
//! ```bash
//! $ git clone https://github.com/daschl/hwloc-rs.git
//! $ cd hwloc-rs
//! ```
//!
//! To run an example (which will download the dependencies and build it) you can
//! use `cargo run -example=`:
//!
//! ```bash
//! $ cargo run --example=walk_tree
//!    Compiling libc v0.2.3
//!    ...
//!    Compiling hwloc v0.2.0 (file:///vagrant/hwloc-rs)
//!      Running `target/debug/examples/walk_tree`
//! *** Printing overall tree
//! Machine (490MB): #0
//!  Socket (): #0
//!   L2d (6144KB): #4294967295
//!    L1d (32KB): #4294967295
//!     Core (): #0
//!      PU (): #0
//!   L1d (32KB): #4294967295
//!     Core (): #1
//!      PU (): #1
//! ```
//!
//! # License
//! This project uses the MIT license, please see the
//! [LICENSE](https://github.com/daschl/hwloc-rs/blob/master/LICENSE) file for more
//! information.

#![allow(dead_code)]
#[macro_use]
extern crate bitflags;
extern crate errno;
extern crate libc;
extern crate num;
#[cfg(target_os = "windows")]
extern crate winapi;

mod ffi;
mod topology_object;
mod bitmap;
mod support;

pub use ffi::{ObjectType, TypeDepthError, TopologyFlag, CpuBindFlags, MemBindPolicy};
pub use bitmap::{Bitmap, CpuSet, NodeSet};
pub use support::{TopologySupport, TopologyDiscoverySupport, TopologyCpuBindSupport,
                  TopologyMemBindSupport};
pub use topology_object::{TopologyObject, TopologyObjectMemory};

use num::{ToPrimitive, FromPrimitive};
use errno::errno;

pub struct Topology {
    topo: *mut ffi::HwlocTopology,
    support: *const TopologySupport,
}

#[allow(non_camel_case_types)]
#[cfg(target_os = "windows")]
pub type pthread_t = winapi::winnt::HANDLE;
#[allow(non_camel_case_types)]
#[cfg(target_os = "windows")]
pub type pid_t = winapi::minwindef::DWORD;
#[allow(non_camel_case_types)]
#[cfg(not(target_os = "windows"))]
pub type pthread_t = libc::pthread_t;
#[allow(non_camel_case_types)]
#[cfg(not(target_os = "windows"))]
pub type pid_t = libc::pid_t;

unsafe impl Send for Topology {}
unsafe impl Sync for Topology {}

impl Topology {
    /// Creates a new Topology.
    ///
    /// If no further customization is needed on init, this method
    /// represents the main entry point. A topology is returned
    /// which contains the logical representation of the physical
    /// hardware.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc::Topology;
    ///
    /// let topology = Topology::new();
    /// ```
    ///
    /// Note that the topology implements the Drop trait, so when
    /// it goes out of scope no further cleanup is necessary.
    pub fn new() -> Option<Topology> {
        let mut topo: *mut ffi::HwlocTopology = std::ptr::null_mut();

        unsafe {
            if ffi::hwloc_topology_init(&mut topo) == -1 {
                return None
            }
            if ffi::hwloc_topology_load(topo) == -1 {
                ffi::hwloc_topology_destroy(topo);
                return None
            }
        }

        let support = unsafe { ffi::hwloc_topology_get_support(topo) };

        Some(Topology {
            topo: topo,
            support: support,
        })
    }

    /// Creates a new Topology with custom flags.
    ///
    /// This method works like `new`, but allows to provide a vector
    /// of flags which customize the topology discovery process.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc::{Topology, TopologyFlag};
    ///
    /// let topology = Topology::with_flags(vec![TopologyFlag::IsThisSystem]);
    /// ```
    ///
    /// Note that the topology implements the Drop trait, so when
    /// it goes out of scope no further cleanup is necessary.
    pub fn with_flags(flags: Vec<TopologyFlag>) -> Option<Topology> {
        let mut topo: *mut ffi::HwlocTopology = std::ptr::null_mut();

        let final_flag = flags
            .iter()
            .map(|f| f.to_u64().unwrap())
            .fold(0, |out, current| out | current);

        unsafe {
            if ffi::hwloc_topology_init(&mut topo) == -1 {
                return None
            }
            ffi::hwloc_topology_set_flags(topo, final_flag);
            if ffi::hwloc_topology_load(topo) == -1 {
                ffi::hwloc_topology_destroy(topo);
                return None
            }
        }

        let support = unsafe { ffi::hwloc_topology_get_support(topo) };

        Some(Topology {
            topo: topo,
            support: support,
        })
    }

    pub fn support(&self) -> &TopologySupport {
        unsafe { &*self.support }
    }

    /// Returns the flags currently set for this topology.
    ///
    /// Note that the flags are only used during initialization, so this
    /// method can just be used for debugging purposes.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc::{Topology,TopologyFlag};
    ///
    /// let default_topology = Topology::new().unwrap();
    /// assert_eq!(0, default_topology.flags().len());
    ///
    /// let topology_with_flags = Topology::with_flags(vec![TopologyFlag::IsThisSystem]).unwrap();
    /// assert_eq!(vec![TopologyFlag::IsThisSystem], topology_with_flags.flags());
    /// ```
    pub fn flags(&self) -> Vec<TopologyFlag> {
        let stored_flags = unsafe { ffi::hwloc_topology_get_flags(self.topo) };

        (0..64)
            .map(|x| (1 << x) & stored_flags)
            .filter(|&x| x > 0)
            .map(|x| TopologyFlag::from_u64(x).unwrap())
            .collect::<Vec<TopologyFlag>>()
    }

    /// Returns the full depth of the topology.
    ///
    /// In practice, the full depth of the topology equals the depth of the `ObjectType::PU`
    /// plus one.
    ///
    /// The full topology depth is useful to know if one needs to manually traverse the
    /// complete topology.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc::Topology;
    ///
    /// let topology = Topology::new().unwrap();
    /// assert!(topology.depth() > 0);
    /// ```
    pub fn depth(&self) -> u32 {
        unsafe { ffi::hwloc_topology_get_depth(self.topo) as u32 }
    }

    /// Returns the depth for the given `ObjectType`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc::{Topology,ObjectType};
    ///
    /// let topology = Topology::new().unwrap();
    ///
    /// let machine_depth = topology.depth_for_type(&ObjectType::Machine).unwrap();
    /// let pu_depth = topology.depth_for_type(&ObjectType::PU).unwrap();
    /// assert!(machine_depth < pu_depth);
    /// ```
    ///
    /// # Failures
    ///
    /// If hwloc can't find the depth for the given `ObjectType`, this method will
    /// return an error from the `TypeDepthError` enum. See this one for more info
    /// on each specific error.
    ///
    /// Note that for `ObjectType::Bridge`, `ObjectType::PCIDevice` and `ObjectType::OSDevice`,
    /// always an error will be returned which signals their virtual depth.
    pub fn depth_for_type(&self, object_type: &ObjectType) -> Result<u32, TypeDepthError> {
        let result = unsafe { ffi::hwloc_get_type_depth(self.topo, object_type.clone()) };

        match result {
            result if result >= 0 => Ok(result as u32),
            -1 => Err(TypeDepthError::TypeDepthUnknown),
            -2 => Err(TypeDepthError::TypeDepthMultiple),
            -3 => Err(TypeDepthError::TypeDepthBridge),
            -4 => Err(TypeDepthError::TypeDepthPCIDevice),
            -5 => Err(TypeDepthError::TypeDepthOSDevice),
            _ => Err(TypeDepthError::Unkown),
        }
    }

    pub fn depth_or_below_for_type(&self, object_type: &ObjectType) -> Result<u32, TypeDepthError> {
        match self.depth_for_type(object_type) {
            Ok(d) => Ok(d),
            Err(TypeDepthError::TypeDepthUnknown) => {
                let pu_depth = self.depth_for_type(&ObjectType::PU).unwrap();
                for i in (0..pu_depth).rev() {
                    if self.type_at_depth(i) < *object_type {
                        return Ok(i + 1);
                    }
                }
                Err(TypeDepthError::TypeDepthUnknown)
            }
            Err(e) => Err(e),
        }
    }

    pub fn depth_or_above_for_type(&self, object_type: &ObjectType) -> Result<u32, TypeDepthError> {
        match self.depth_for_type(object_type) {
            Ok(d) => Ok(d),
            Err(TypeDepthError::TypeDepthUnknown) => {
                let pu_depth = self.depth_for_type(&ObjectType::PU).unwrap();
                for i in 0..pu_depth {
                    if self.type_at_depth(i) > *object_type {
                        return Ok(i - 1);
                    }
                }
                Err(TypeDepthError::TypeDepthUnknown)
            }
            Err(e) => Err(e),
        }
    }

    // pub fn depth_or_below_for_type(&self, object_type: ObjectType)

    /// Returns the corresponding `ObjectType` for the given depth.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc::{Topology,ObjectType};
    ///
    /// let topology = Topology::new().unwrap();
    ///
    /// // Load depth for PU to assert against
    /// let pu_depth = topology.depth_for_type(&ObjectType::PU).unwrap();
    /// // Retrieve the type for the given depth
    /// assert_eq!(ObjectType::PU, topology.type_at_depth(pu_depth));
    /// ```
    ///
    /// # Panics
    ///
    /// This method will panic if the given depth is larger than the full depth
    /// minus one. It can't be negative since its an unsigned integer, but be
    /// careful with the depth provided in general.
    pub fn type_at_depth(&self, depth: u32) -> ObjectType {
        if depth > self.depth() - 1 {
            panic!("The provided depth {} is out of bounds.", depth);
        }

        unsafe { ffi::hwloc_get_depth_type(self.topo, depth as i32) }
    }

    /// Returns the number of objects at the given depth.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc::Topology;
    ///
    /// let topology = Topology::new().unwrap();
    ///
    /// let topo_depth = topology.depth();
    /// assert!(topology.size_at_depth(topo_depth - 1) > 0);
    /// ```
    ///
    /// # Panics
    ///
    /// This method will panic if the given depth is larger than the full depth
    /// minus one. It can't be negative since its an unsigned integer, but be
    /// careful with the depth provided in general.
    pub fn size_at_depth(&self, depth: u32) -> u32 {
        if depth > self.depth() - 1 {
            panic!("The provided depth {} is out of bounds.", depth);
        }

        unsafe { ffi::hwloc_get_nbobjs_by_depth(self.topo, depth) }
    }

    /// Returns the `TopologyObject` at the root of the topology.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc::{Topology,TopologyObject};
    ///
    /// let topology = Topology::new().unwrap();
    ///
    /// assert_eq!(topology.type_at_root(), topology.object_at_root().object_type());
    /// ```
    pub fn object_at_root(&self) -> &TopologyObject {
        self.objects_at_depth(0).first().unwrap()
    }

    /// Returns the `ObjectType` at the root of the topology.
    ///
    /// This method is a convenient shorthand for `type_at_depth(0)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc::{Topology,ObjectType};
    ///
    /// let topology = Topology::new().unwrap();
    ///
    /// let root_type = topology.type_at_root();
    /// let depth_type = topology.type_at_depth(0);
    /// assert_eq!(root_type, depth_type);
    /// ```
    pub fn type_at_root(&self) -> ObjectType {
        self.type_at_depth(0)
    }

    /// Returns all `TopologyObjects` with the given `ObjectType`.
    pub fn objects_with_type(&self,
                             object_type: &ObjectType)
                             -> Result<Vec<&TopologyObject>, TypeDepthError> {
        match self.depth_for_type(object_type) {
            Ok(depth) => Ok(self.objects_at_depth(depth)),
            Err(TypeDepthError::TypeDepthOSDevice) => {
                Ok(self.objects_at_depth(TypeDepthError::TypeDepthOSDevice as u32))
            }
            Err(TypeDepthError::TypeDepthPCIDevice) => {
                Ok(self.objects_at_depth(TypeDepthError::TypeDepthPCIDevice as u32))
            }
            Err(TypeDepthError::TypeDepthBridge) => {
                Ok(self.objects_at_depth(TypeDepthError::TypeDepthBridge as u32))
            }
            Err(e) => Err(e),
        }
    }

    /// Returns all `TopologyObject`s at the given depth.
    pub fn objects_at_depth(&self, depth: u32) -> Vec<&TopologyObject> {
        let size = self.size_at_depth(depth);
        (0..size)
            .map(|idx| unsafe { &*ffi::hwloc_get_obj_by_depth(self.topo, depth, idx) })
            .collect::<Vec<&TopologyObject>>()
    }

    /// Binds the current process or thread on CPUs given in the `CpuSet`.
    pub fn set_cpubind(&mut self, set: CpuSet, flags: CpuBindFlags) -> Result<(), CpuBindError> {
        let result = unsafe { ffi::hwloc_set_cpubind(self.topo, set.as_ptr(), flags.bits()) };

        match result {
            r if r < 0 => {
                let e = errno();
                Err(CpuBindError::Generic(e.0 as i32, format!("{}", e)))
            }
            _ => Ok(()),
        }
    }

    /// Get current process or thread binding.
    pub fn get_cpubind(&self, flags: CpuBindFlags) -> Option<CpuSet> {
        let raw_set = unsafe { ffi::hwloc_bitmap_alloc() };
        let res = unsafe { ffi::hwloc_get_cpubind(self.topo, raw_set, flags.bits()) };
        if res >= 0 {
            Some(CpuSet::from_raw(raw_set, true))
        } else {
            None
        }
    }

    /// Binds a process (identified by its `pid`) on CPUs identified by the given `CpuSet`.
    pub fn set_cpubind_for_process(&mut self,
                                   pid: pid_t,
                                   set: CpuSet,
                                   flags: CpuBindFlags)
                                   -> Result<(), CpuBindError> {
        let result =
            unsafe { ffi::hwloc_set_proc_cpubind(self.topo, pid, set.as_ptr(), flags.bits()) };

        match result {
            r if r < 0 => {
                let e = errno();
                Err(CpuBindError::Generic(e.0 as i32, format!("{}", e)))
            }
            _ => Ok(()),
        }
    }

    /// Get the current physical binding of a process, identified by its `pid`.
    pub fn get_cpubind_for_process(&self, pid: pid_t, flags: CpuBindFlags) -> Option<CpuSet> {
        let raw_set = unsafe { ffi::hwloc_bitmap_alloc() };
        let res = unsafe { ffi::hwloc_get_proc_cpubind(self.topo, pid, raw_set, flags.bits()) };
        if res >= 0 {
            Some(CpuSet::from_raw(raw_set, true))
        } else {
            None
        }
    }

    /// Bind a thread (by its `tid`) on CPUs given in through the `CpuSet`.
    pub fn set_cpubind_for_thread(&mut self,
                                  tid: pthread_t,
                                  set: CpuSet,
                                  flags: CpuBindFlags)
                                  -> Result<(), CpuBindError> {
        let result =
            unsafe { ffi::hwloc_set_thread_cpubind(self.topo, tid, set.as_ptr(), flags.bits()) };

        match result {
            r if r < 0 => {
                let e = errno();
                Err(CpuBindError::Generic(e.0 as i32, format!("{}", e)))
            }
            _ => Ok(()),
        }
    }

    /// Get the current physical binding of thread `tid`.
    pub fn get_cpubind_for_thread(&self, tid: pthread_t, flags: CpuBindFlags) -> Option<CpuSet> {
        let raw_set = unsafe { ffi::hwloc_bitmap_alloc() };
        let res = unsafe { ffi::hwloc_get_thread_cpubind(self.topo, tid, raw_set, flags.bits()) };
        if res >= 0 {
            Some(CpuSet::from_raw(raw_set, true))
        } else {
            None
        }
    }

    /// Get the last physical CPU where the current process or thread ran.
    ///
    /// The operating system may move some tasks from one processor
    /// to another at any time according to their binding,
    /// so this function may return something that is already
    /// outdated.
    ///
    /// Flags can include either `CPUBIND_PROCESS` or `CPUBIND_THREAD` to
    /// specify whether the query should be for the whole process (union of all CPUs
    /// on which all threads are running), or only the current thread. If the
    /// process is single-threaded, flags can be set to zero to let hwloc use
    /// whichever method is available on the underlying OS.
    pub fn get_cpu_location(&self, flags: CpuBindFlags) -> Option<CpuSet> {
        let raw_set = unsafe { ffi::hwloc_bitmap_alloc() };
        let res = unsafe { ffi::hwloc_get_last_cpu_location(self.topo, raw_set, flags.bits()) };
        if res >= 0 {
            Some(CpuSet::from_raw(raw_set, true))
        } else {
            None
        }
    }

    /// Get the last physical CPU where a process ran.
    ///
    /// The operating system may move some tasks from one processor to another at any
    /// time according to their binding, so this function may return something that is
    /// already outdated.
    pub fn get_cpu_location_for_process(&self, pid: pid_t, flags: CpuBindFlags) -> Option<CpuSet> {
        let raw_set = unsafe { ffi::hwloc_bitmap_alloc() };
        let res =
            unsafe { ffi::hwloc_get_proc_last_cpu_location(self.topo, pid, raw_set, flags.bits()) };
        if res >= 0 {
            Some(CpuSet::from_raw(raw_set, true))
        } else {
            None
        }
    }
}

impl Drop for Topology {
    fn drop(&mut self) {
        unsafe { ffi::hwloc_topology_destroy(self.topo) }
    }
}

#[derive(Debug)]
pub enum CpuBindError {
    Generic(i32, String),
}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn should_set_and_get_flags() {
        let topo = Topology::with_flags(vec![TopologyFlag::IncludeDisallowed, TopologyFlag::ThisSystemAllowedResources]).unwrap();
        assert_eq!(vec![TopologyFlag::IncludeDisallowed, TopologyFlag::ThisSystemAllowedResources],
                   topo.flags());
    }

    #[test]
    fn should_get_topology_depth() {
        let topo = Topology::new().unwrap();
        assert!(topo.depth() > 0);
    }

    #[test]
    fn should_match_types_and_their_depth() {
        let topo = Topology::new().unwrap();

        let pu_depth = topo.depth_for_type(&ObjectType::PU).ok().unwrap();
        assert!(pu_depth > 0);
        assert_eq!(ObjectType::PU, topo.type_at_depth(pu_depth));
    }

    #[test]
    fn should_get_nbobjs_by_depth() {
        let topo = Topology::new().unwrap();
        assert!(topo.size_at_depth(1) > 0);
    }

    #[test]
    fn should_get_root_object() {
        let topo = Topology::new().unwrap();

        let root_obj = topo.object_at_root();
        assert_eq!(ObjectType::Machine, root_obj.object_type());
        assert!(root_obj.total_memory() > 0);
        assert_eq!(0, root_obj.depth());
        assert_eq!(0, root_obj.logical_index());
        println!("{}", root_obj);
        assert!(root_obj.first_child().is_some());
        assert!(root_obj.last_child().is_some());
    }

    #[test]
    #[cfg(target_os="linux")]
    fn should_support_cpu_binding_on_linux() {
        let topo = Topology::new().unwrap();

        assert!(topo.support().cpu().set_current_process());
        assert!(topo.support().cpu().set_current_thread());
    }

    #[test]
    #[cfg(target_os="freebsd")]
    fn should_support_cpu_binding_on_freebsd() {
        let topo = Topology::new().unwrap();

        assert!(topo.support().cpu().set_current_process());
        assert!(topo.support().cpu().set_current_thread());
    }

    #[test]
    #[cfg(target_os="macos")]
    fn should_not_support_cpu_binding_on_macos() {
        let topo = Topology::new().unwrap();

        assert_eq!(false, topo.support().cpu().set_current_process());
        assert_eq!(false, topo.support().cpu().set_current_thread());
    }

    #[test]
    fn should_produce_cpubind_bitflags() {
        assert_eq!("1", format!("{:b}", CpuBindFlags::CPUBIND_PROCESS.bits()));
        assert_eq!("10", format!("{:b}", CpuBindFlags::CPUBIND_THREAD.bits()));
        assert_eq!("100", format!("{:b}", CpuBindFlags::CPUBIND_STRICT.bits()));
        assert_eq!("101",
                   format!("{:b}", (CpuBindFlags::CPUBIND_STRICT | CpuBindFlags::CPUBIND_PROCESS).bits()));
    }

}
