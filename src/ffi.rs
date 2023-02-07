use crate::{
    bitmap::IntHwlocBitmap,
    support::TopologySupport,
    topology_object::{TopologyObject, TopologyObjectAttributes},
};
use libc::{c_char, c_int, c_uchar, c_uint, c_ulong, c_void, pid_t, pthread_t, size_t};
use num::{FromPrimitive, ToPrimitive};
use std::cmp::{Ordering, PartialOrd};

bitflags! {
    /// Process/Thread binding flags.
    ///
    /// These bit flags can be used to refine the binding policy.
    ///
    /// The default (Process) is to bind the current process, assumed to be
    /// single-threaded, in a non-strict way.  This is the most portable
    /// way to bind as all operating systems usually provide it.
    ///
    /// **Note:** Not all systems support all kinds of binding.
    ///
    /// The following flags (constants) are available:
    ///
    /// - **CPUBIND_PROCESS:** Bind all threads of the current (possibly) multithreaded process.
    /// - **CPUBIND_THREAD:** Bind current thread of current process.
    /// - **CPUBIND_STRICT:** Request for strict binding from the OS.
    /// - **CPUBIND_NO_MEMBIND:** Avoid any effect on memory binding.
    #[repr(C)]
    pub struct CpuBindFlags: i32 {
        /// Bind all threads of the current (possibly) multithreaded process.
        const CPUBIND_PROCESS = (1<<0);
        /// Bind current thread of current process.
        const CPUBIND_THREAD  = (1<<1);
        /// Request for strict binding from the OS.
        const CPUBIND_STRICT = (1<<2);
        /// Avoid any effect on memory binding.
        const CPUBIND_NO_MEMBIND = (1<<3);
    }
}

bitflags! {
    #[repr(C)]
    pub struct MemBindPolicy: i32 {
        /// Reset the memory allocation policy to the system default. Depending on the operating
        /// system, this may correspond to MEMBIND_FIRSTTOUCH (Linux), or MEMBIND_BIND (AIX,
        /// HP-UX, OSF, Solaris, Windows).
        const MEMBIND_DEFAULT = 0;
        /// Allocate memory but do not immediately bind it to a specific locality. Instead,
        /// each page in the allocation is bound only when it is first touched. Pages are
        /// individually bound to the local NUMA node of the first thread that touches it. If
        /// there is not enough memory on the node, allocation may be done in the specified
        /// cpuset before allocating on other nodes.
        const MEMBIND_FIRSTTOUCH = 1;
        /// Allocate memory on the specified nodes.
        const MEMBIND_BIND = 2;
        /// Allocate memory on the given nodes in an interleaved / round-robin manner.
        /// The precise layout of the memory across multiple NUMA nodes is OS/system specific.
        /// Interleaving can be useful when threads distributed across the specified NUMA nodes
        /// will all be accessing the whole memory range concurrently, since the interleave will
        /// then balance the memory references.
        const MEMBIND_INTERLEAVE = 3;
        /// For each page bound with this policy, by next time it is touched (and next time
        /// only), it is moved from its current location to the local NUMA node of the thread
        /// where the memory reference occurred (if it needs to be moved at all).
        const MEMBIND_NEXTTOUCH = 4;
        /// Returned by get_membind() functions when multiple threads or parts of a memory
        /// area have differing memory binding policies.
        const MEMBIND_MIXED = -1;
    }
}

pub enum HwlocTopology {}

/// Represents the type of a topology object.
///
/// Note that (partial) ordering for object types is implemented as a call
/// into the `hwloc` library which defines ordering as follows:
///
/// - A == B if `ObjectType::A` and `ObjectType::B` are the same.
/// - A < B if `ObjectType::A` includes objects of type `ObjectType::B`.
/// - A > B if objects of `ObjectType::A` are included in type `ObjectType::B`.
///
/// It can also help to think of it as comparing the relative depths of each type, so
/// a `ObjectType::System` will be smaller than a `ObjectType::PU` since the system
/// contains processing units.
#[repr(u32)]
#[derive(Debug, Clone)]
pub enum ObjectType {
    /// The typical root object type. A set of processors and memory with cache
    /// coherency.
    Machine,
    /// Physical package, what goes into a socket. In the physical meaning,
    /// i.e. that you can add or remove physically.
    Package,
    /// A computation unit (may be shared by several logical processors).
    Core,
    /// Processing Unit, or (Logical) Processor.
    ///
    /// An execution unit (may share a core with some other logical
    /// processors, e.g. in the case of an SMT core). Objects of this kind
    /// are always reported and can thus be used as fallback when others are
    /// not.
    PU,
    /// Data cache
    ///
    /// Level 1 Data (or Unified) Cache.
    L1Cache,
    /// Data cache
    ///
    /// Level 2 Data (or Unified) Cache.
    L2Cache,
    /// Data cache
    ///
    /// Level 3 Data (or Unified) Cache.
    L3Cache,
    /// Data cache
    ///
    /// Level 4 Data (or Unified) Cache.
    L4Cache,
    /// Data cache
    ///
    /// Level 5 Data (or Unified) Cache.
    L5Cache,
    /// Instruction cache
    ///
    /// Level 1 Instruction cache (filtered out by default)
    L1iCache,
    /// Instruction cache
    ///
    /// Level 2 Instruction cache (filtered out by default)
    L2iCache,
    /// Instruction cache
    ///
    /// Level 3 Instruction cache (filtered out by default)
    L3iCache,
    /// Group objects.
    ///
    /// Objects which do not fit in the above but are detected by hwloc and
    /// are useful to take into account for affinity. For instance, some
    /// operating systems expose their arbitrary processors aggregation this
    /// way. And hwloc may insert such objects to group NUMA nodes according
    /// to their distances.
    ///
    /// These objects are ignored when they do not bring any structure.
    Group,
    /// A set of processors around memory which the processors can directly
    /// access.
    NUMANode,
    /// Any bridge that connects the host or an I/O bus, to another I/O bus.
    ///
    /// Bridge objects have neither CPU sets nor node sets.
    /// They are not added to the topology unless I/O discovery
    /// is enabled through the custom flags.
    Bridge,
    /// PCI device.
    ///
    /// These objects have neither CPU sets nor node sets.
    /// They are not added to the topology unless I/O discovery
    /// is enabled through the custom flags.
    PCIDevice,
    /// Operating system device.
    ///
    /// These objects have neither CPU sets nor node sets. They are not
    /// added to the topology unless I/O discovery is enabled
    /// through the custom flags.
    OSDevice,
    /// Miscellaneous objects.
    ///
    /// Objects without particular meaning, that can e.g. be
    /// added by the application for its own use, or by hwloc
    /// for miscellaneous objects such as MemoryModule (DIMMs).
    Misc,
    /// Memory-side cache
    ///
    /// Memory-side cache (filtered out by default).
    ///
    /// A cache in front of a specific NUMA node.
    ///
    /// Memory objects are not listed in the main children list, but rather in the dedicated Memory
    /// children list.
    ///
    /// Memory-side cache have a special depth ::HWLOC_TYPE_DEPTH_MEMCACHE instead of a normal
    /// depth just like other objects in the main tree.
    Memcache,
    /// Die within a physical package.
    ///
    /// A subpart of the physical package, that contains multiple cores.
    Die,
    /// An internal sentinel value.
    TypeMax,
}

impl PartialOrd for ObjectType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let compared = unsafe { hwloc_compare_types(self.clone(), other.clone()) };
        match compared {
            c if c < 0 => Some(Ordering::Less),
            c if c == 0 => Some(Ordering::Equal),
            c if c > 0 => Some(Ordering::Greater),
            _ => None,
        }
    }
}

impl PartialEq for ObjectType {
    fn eq(&self, other: &Self) -> bool {
        match self.partial_cmp(other) {
            Some(Ordering::Equal) => true,
            _ => false,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum TypeDepthError {
    /// No object of given type exists in the topology.
    TypeDepthUnknown = -1,
    /// Objects of given type exist at different depth in the topology.
    TypeDepthMultiple = -2,
    /// Virtual depth for NUMA node object level.
    TypeDepthNumaNode = -3,
    /// Virtual depth for bridge object level.
    TypeDepthBridge = -4,
    /// Virtual depth for PCI device object level.
    TypeDepthPCIDevice = -5,
    /// Virtual depth for software device object level.
    TypeDepthOSDevice = -6,
    /// Virtual depth for misc. entry object level.
    TypeDepthMisc = -7,
    /// HWLOC returned a depth error which is not known to the rust binding.
    Unkown = -99,
}

const TOPOLOGY_FLAG_INCLUDE_DISALLOWED: i64 = 1;
const TOPOLOGY_FLAG_IS_THISSYSTEM: i64 = 2;
const TOPOLOGY_FLAG_THISSYSTEM_ALLOWED_RESOURCES: i64 = 4;

#[derive(Debug, PartialEq)]
pub enum TopologyFlag {
    IncludeDisallowed = TOPOLOGY_FLAG_INCLUDE_DISALLOWED as isize,
    IsThisSystem = TOPOLOGY_FLAG_IS_THISSYSTEM as isize,
    ThisSystemAllowedResources = TOPOLOGY_FLAG_THISSYSTEM_ALLOWED_RESOURCES as isize,
}

impl ToPrimitive for TopologyFlag {
    fn to_i64(&self) -> Option<i64> {
        match *self {
            TopologyFlag::IncludeDisallowed => Some(TopologyFlag::IncludeDisallowed as i64),
            TopologyFlag::IsThisSystem => Some(TopologyFlag::IsThisSystem as i64),
            TopologyFlag::ThisSystemAllowedResources => {
                Some(TopologyFlag::ThisSystemAllowedResources as i64)
            }
        }
    }

    fn to_u64(&self) -> Option<u64> {
        self.to_i64().and_then(|x| x.to_u64())
    }
}

impl FromPrimitive for TopologyFlag {
    fn from_i64(n: i64) -> Option<Self> {
        match n {
            TOPOLOGY_FLAG_INCLUDE_DISALLOWED => Some(TopologyFlag::IncludeDisallowed),
            TOPOLOGY_FLAG_IS_THISSYSTEM => Some(TopologyFlag::IsThisSystem),
            TOPOLOGY_FLAG_THISSYSTEM_ALLOWED_RESOURCES => {
                Some(TopologyFlag::ThisSystemAllowedResources)
            }
            _ => None,
        }
    }

    fn from_u64(n: u64) -> Option<Self> {
        FromPrimitive::from_i64(n as i64)
    }
}

#[repr(C)]
pub enum TypeFilter {
    /// Keep all objects of this type
    KeepAll = 0,
    /// Ignore all objects of this type
    KeepNone = 1,
    /// Only ignore objects if their entire level does not bring any structure
    KeepStructure = 2,
    /// Only keep ilkely-important objects of the given type
    KeepImportant = 3,
}

macro_rules! extern_c_block {
    ($link_name:literal) => {
        #[link(name = $link_name)]
        extern "C" {

            // Indicate at runtime which hwloc API version was used at build time.
            pub fn hwloc_get_api_version() -> c_uint;

            // === Topology Creation and Destruction ===

            pub fn hwloc_topology_init(topology: *mut *mut HwlocTopology) -> c_int;
            pub fn hwloc_topology_load(topology: *mut HwlocTopology) -> c_int;
            pub fn hwloc_topology_destroy(topology: *mut HwlocTopology);

            // === Topology Utilities
            pub fn hwloc_topology_dup(
                newtop: *mut *mut HwlocTopology,
                oldtop: *mut HwlocTopology,
            ) -> c_int;
            pub fn hwloc_topology_abi_check(topology: *mut HwlocTopology) -> c_int;
            pub fn hwloc_topology_check(topology: *mut HwlocTopology) -> c_int;

            // === Topology Detection Configuration and Query ===
            pub fn hwloc_topology_set_pid(topology: *mut HwlocTopology, pid: pid_t) -> c_int;
            pub fn hwloc_topology_set_synthetic(
                topology: *mut HwlocTopology,
                description: *const c_char,
            ) -> c_int;
            pub fn hwloc_topology_set_xml(
                topology: *mut HwlocTopology,
                xmlpath: *const c_char,
            ) -> c_int;
            pub fn hwloc_topology_set_xmlbuffer(
                topology: *mut HwlocTopology,
                buffer: *const c_char,
                size: c_int,
            ) -> c_int;
            pub fn hwloc_topology_set_components(
                topology: *mut HwlocTopology,
                flags: c_ulong,
                name: *const c_char,
            ) -> c_int;

            pub fn hwloc_topology_set_flags(topology: *mut HwlocTopology, flags: c_ulong) -> c_int;
            pub fn hwloc_topology_get_flags(topology: *mut HwlocTopology) -> c_ulong;
            pub fn hwloc_topology_is_thissystem(topology: *mut HwlocTopology) -> c_int;

            pub fn hwloc_topology_get_support(
                topology: *mut HwlocTopology,
            ) -> *const TopologySupport;

            pub fn hwloc_topology_set_type_filter(
                topology: *mut HwlocTopology,
                otype: ObjectType,
                filter: c_uchar,
            ) -> c_int;
            pub fn hwloc_topology_get_type_filter(
                topology: *mut HwlocTopology,
                otype: ObjectType,
                filter: *mut c_uchar,
            ) -> c_int;
            pub fn hwloc_topology_set_all_types_filter(
                topology: *mut HwlocTopology,
                filter: c_uchar,
            ) -> c_int;
            pub fn hwloc_topology_set_cache_types_filter(
                topology: *mut HwlocTopology,
                otype: ObjectType,
                filter: c_uchar,
            ) -> c_int;
            pub fn hwloc_topology_set_icache_types_filter(
                topology: *mut HwlocTopology,
                otype: ObjectType,
                filter: c_uchar,
            ) -> c_int;
            pub fn hwloc_topology_set_io_types_filter(
                topology: *mut HwlocTopology,
                otype: ObjectType,
                filter: c_uchar,
            ) -> c_int;

            pub fn hwloc_topology_set_userdata(topology: *mut HwlocTopology, data: *const c_void);
            pub fn hwloc_topology_get_userdata(topology: *mut HwlocTopology) -> *mut c_void;

            pub fn hwloc_topology_restrict(
                topology: *mut HwlocTopology,
                set: *const IntHwlocBitmap,
                flags: c_ulong,
            ) -> c_int;
            pub fn hwloc_topology_allow(
                topology: *mut HwlocTopology,
                set: *const IntHwlocBitmap,
                flags: c_ulong,
            ) -> c_int;

            pub fn hwloc_topology_insert_misc_object(
                topology: *mut HwlocTopology,
                parent: *mut TopologyObject,
                name: *const c_char,
            ) -> *mut TopologyObject;
            pub fn hwloc_topology_alloc_group_object(
                topology: *mut HwlocTopology,
            ) -> *mut TopologyObject;
            pub fn hwloc_topology_insert_group_object(
                topology: *mut HwlocTopology,
                group: *mut TopologyObject,
            ) -> *mut TopologyObject;

            pub fn hwloc_obj_add_other_obj_sets(
                dst: *mut TopologyObject,
                src: *mut TopologyObject,
            ) -> c_int;

            // === Object levels, depths and types ===

            pub fn hwloc_topology_get_depth(topology: *mut HwlocTopology) -> c_int;
            pub fn hwloc_get_type_depth(
                topology: *mut HwlocTopology,
                object_type: ObjectType,
            ) -> c_int;
            pub fn hwloc_get_memory_parents_depth(topology: *mut HwlocTopology) -> c_int;
            pub fn hwloc_get_depth_type(topology: *mut HwlocTopology, depth: c_int) -> ObjectType;
            pub fn hwloc_get_nbobjs_by_depth(topology: *mut HwlocTopology, depth: c_uint)
                -> c_uint;

            pub fn hwloc_get_obj_by_depth(
                topology: *mut HwlocTopology,
                depth: c_uint,
                idx: c_uint,
            ) -> *mut TopologyObject;

            // === CPU Binding ===
            pub fn hwloc_set_cpubind(
                topology: *mut HwlocTopology,
                set: *const IntHwlocBitmap,
                flags: c_int,
            ) -> c_int;
            pub fn hwloc_get_cpubind(
                topology: *mut HwlocTopology,
                set: *mut IntHwlocBitmap,
                flags: c_int,
            ) -> c_int;
            pub fn hwloc_set_proc_cpubind(
                topology: *mut HwlocTopology,
                pid: pid_t,
                set: *const IntHwlocBitmap,
                flags: c_int,
            ) -> c_int;
            pub fn hwloc_get_proc_cpubind(
                topology: *mut HwlocTopology,
                pid: pid_t,
                set: *mut IntHwlocBitmap,
                flags: c_int,
            ) -> c_int;
            pub fn hwloc_set_thread_cpubind(
                topology: *mut HwlocTopology,
                thread: pthread_t,
                set: *const IntHwlocBitmap,
                flags: c_int,
            ) -> c_int;
            pub fn hwloc_get_thread_cpubind(
                topology: *mut HwlocTopology,
                pid: pthread_t,
                set: *mut IntHwlocBitmap,
                flags: c_int,
            ) -> c_int;
            pub fn hwloc_get_last_cpu_location(
                topology: *mut HwlocTopology,
                set: *mut IntHwlocBitmap,
                flags: c_int,
            ) -> c_int;
            pub fn hwloc_get_proc_last_cpu_location(
                topology: *mut HwlocTopology,
                pid: pid_t,
                set: *mut IntHwlocBitmap,
                flags: c_int,
            ) -> c_int;

            // === Memory Binding ===
            pub fn hwloc_set_membind(
                topology: *mut HwlocTopology,
                set: *const IntHwlocBitmap,
                policy: MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub fn hwloc_get_membind(
                topology: *mut HwlocTopology,
                set: *mut IntHwlocBitmap,
                policy: *mut MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub fn hwloc_set_proc_membind(
                topology: *mut HwlocTopology,
                pid: pid_t,
                set: *const IntHwlocBitmap,
                policy: MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub fn hwloc_get_proc_membind(
                topology: *mut HwlocTopology,
                pid: pid_t,
                set: *mut IntHwlocBitmap,
                policy: *mut MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub fn hwloc_set_area_membind(
                topology: *mut HwlocTopology,
                addr: *const c_void,
                len: size_t,
                set: *const IntHwlocBitmap,
                policy: MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub fn hwloc_get_area_membind(
                topology: *mut HwlocTopology,
                addr: *const c_void,
                len: size_t,
                set: *mut IntHwlocBitmap,
                policy: *mut MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub fn hwloc_get_area_memlocation(
                topology: *mut HwlocTopology,
                addr: *const c_void,
                len: size_t,
                set: *mut IntHwlocBitmap,
                flags: c_int,
            ) -> c_int;
            pub fn hwloc_alloc(topology: *mut HwlocTopology, len: size_t) -> *mut c_void;
            pub fn hwloc_alloc_membind(
                topology: *mut HwlocTopology,
                len: size_t,
                set: *const IntHwlocBitmap,
                policy: MemBindPolicy,
                flags: c_int,
            ) -> *mut c_void;
            pub fn hwloc_free(
                topology: *mut HwlocTopology,
                addr: *mut c_void,
                len: size_t,
            ) -> c_int;

            // === Bitmap Methods ===
            pub fn hwloc_bitmap_alloc() -> *mut IntHwlocBitmap;
            pub fn hwloc_bitmap_alloc_full() -> *mut IntHwlocBitmap;
            pub fn hwloc_bitmap_free(bitmap: *mut IntHwlocBitmap);
            pub fn hwloc_bitmap_list_asprintf(
                strp: *mut *mut c_char,
                bitmap: *const IntHwlocBitmap,
            ) -> c_int;
            pub fn hwloc_bitmap_set(bitmap: *mut IntHwlocBitmap, id: c_uint);
            pub fn hwloc_bitmap_set_range(bitmap: *mut IntHwlocBitmap, begin: c_uint, end: c_int);
            pub fn hwloc_bitmap_clr(bitmap: *mut IntHwlocBitmap, id: c_uint);
            pub fn hwloc_bitmap_clr_range(bitmap: *mut IntHwlocBitmap, begin: c_uint, end: c_int);
            pub fn hwloc_bitmap_weight(bitmap: *const IntHwlocBitmap) -> c_int;
            pub fn hwloc_bitmap_zero(bitmap: *mut IntHwlocBitmap);
            pub fn hwloc_bitmap_iszero(bitmap: *const IntHwlocBitmap) -> c_int;
            pub fn hwloc_bitmap_isset(bitmap: *const IntHwlocBitmap, id: c_uint) -> c_int;
            pub fn hwloc_bitmap_singlify(bitmap: *mut IntHwlocBitmap);
            pub fn hwloc_bitmap_not(result: *mut IntHwlocBitmap, bitmap: *const IntHwlocBitmap);
            pub fn hwloc_bitmap_or(
                result: *mut IntHwlocBitmap,
                bitmap1: *const IntHwlocBitmap,
                bitmap2: *const IntHwlocBitmap,
            );
            pub fn hwloc_bitmap_and(
                result: *mut IntHwlocBitmap,
                bitmap1: *const IntHwlocBitmap,
                bitmap2: *const IntHwlocBitmap,
            );
            pub fn hwloc_bitmap_xor(
                result: *mut IntHwlocBitmap,
                bitmap1: *const IntHwlocBitmap,
                bitmap2: *const IntHwlocBitmap,
            );
            pub fn hwloc_bitmap_first(bitmap: *const IntHwlocBitmap) -> c_int;
            pub fn hwloc_bitmap_last(bitmap: *const IntHwlocBitmap) -> c_int;
            pub fn hwloc_bitmap_dup(src: *const IntHwlocBitmap) -> *mut IntHwlocBitmap;
            pub fn hwloc_bitmap_compare(
                left: *const IntHwlocBitmap,
                right: *const IntHwlocBitmap,
            ) -> c_int;
            pub fn hwloc_bitmap_isequal(
                left: *const IntHwlocBitmap,
                right: *const IntHwlocBitmap,
            ) -> c_int;
            pub fn hwloc_bitmap_isfull(bitmap: *const IntHwlocBitmap) -> c_int;
            pub fn hwloc_bitmap_next(bitmap: *const IntHwlocBitmap, prev: c_int) -> c_int;

            pub fn hwloc_obj_type_string(object_type: ObjectType) -> *const c_char;
            pub fn hwloc_obj_type_snprintf(
                into: *mut c_char,
                size: size_t,
                object: *const TopologyObject,
                verbose: c_int,
            ) -> c_int;
            pub fn hwloc_obj_attr_snprintf(
                into: *mut c_char,
                size: size_t,
                object: *const TopologyObject,
                separator: *const c_char,
                verbose: c_int,
            ) -> c_int;
            pub fn hwloc_type_sscanf(
                strng: *const c_char,
                obj_type: *mut ObjectType,
                attrs: *mut TopologyObjectAttributes,
                attrs_size: size_t,
            ) -> c_int;
            pub fn hwloc_type_sscanf_as_depth(
                strng: *const c_char,
                obj_type: *mut ObjectType,
                topology: *mut HwlocTopology,
                depthp: *mut c_int,
            ) -> c_int;

            pub fn hwloc_obj_add_info(
                obj: *mut TopologyObject,
                name: *const c_char,
                value: *const c_char,
            ) -> c_int;

            pub fn hwloc_compare_types(type1: ObjectType, type2: ObjectType) -> c_int;
        }
    };
}

#[cfg(target_os = "windows")]
extern_c_block!("libhwloc");

#[cfg(not(target_os = "windows"))]
extern_c_block!("hwloc");

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn should_convert_flag_to_primitive() {
        assert_eq!(1, TopologyFlag::IncludeDisallowed as u64);
        assert_eq!(4, TopologyFlag::ThisSystemAllowedResources as u64);
    }

    #[test]
    fn should_compare_object_types() {
        assert!(ObjectType::Machine == ObjectType::Machine);
        assert!(ObjectType::PU == ObjectType::PU);

        assert!(ObjectType::Machine < ObjectType::PU);
        assert!(ObjectType::PU > ObjectType::L1Cache);
    }
}
