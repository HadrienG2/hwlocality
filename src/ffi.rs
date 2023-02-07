use crate::{
    bitmap::RawBitmap,
    support::TopologySupport,
    topology_object::{types::RawObjectType, TopologyObject, TopologyObjectAttributes},
};
use bitflags::bitflags;
use libc::{c_char, c_int, c_uchar, c_uint, c_ulong, c_void, pid_t, pthread_t, size_t};
use num::{FromPrimitive, ToPrimitive};

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
            pub(crate) fn hwloc_get_api_version() -> c_uint;

            // === Bitmap API ( https://www.open-mpi.org/projects/hwloc/doc/v2.9.0/a00181.php ) ===

            #[must_use]
            pub(crate) fn hwloc_bitmap_alloc() -> *mut RawBitmap;
            #[must_use]
            pub(crate) fn hwloc_bitmap_alloc_full() -> *mut RawBitmap;
            pub(crate) fn hwloc_bitmap_free(bitmap: *mut RawBitmap);
            #[must_use]
            pub(crate) fn hwloc_bitmap_dup(src: *const RawBitmap) -> *mut RawBitmap;
            #[must_use]
            pub(crate) fn hwloc_bitmap_copy(dst: *mut RawBitmap, src: *const RawBitmap) -> c_int;

            #[must_use]
            pub(crate) fn hwloc_bitmap_list_asprintf(
                strp: *mut *mut c_char,
                bitmap: *const RawBitmap,
            ) -> c_int;

            pub(crate) fn hwloc_bitmap_zero(bitmap: *mut RawBitmap);
            pub(crate) fn hwloc_bitmap_fill(bitmap: *mut RawBitmap);
            #[must_use]
            pub(crate) fn hwloc_bitmap_set(bitmap: *mut RawBitmap, id: c_uint) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_set_range(
                bitmap: *mut RawBitmap,
                begin: c_uint,
                end: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_clr(bitmap: *mut RawBitmap, id: c_uint) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_clr_range(
                bitmap: *mut RawBitmap,
                begin: c_uint,
                end: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_bitmap_singlify(bitmap: *mut RawBitmap);

            #[must_use]
            pub(crate) fn hwloc_bitmap_isset(bitmap: *const RawBitmap, id: c_uint) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_iszero(bitmap: *const RawBitmap) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_isfull(bitmap: *const RawBitmap) -> c_int;

            #[must_use]
            pub(crate) fn hwloc_bitmap_first(bitmap: *const RawBitmap) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_next(bitmap: *const RawBitmap, prev: c_int) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_last(bitmap: *const RawBitmap) -> c_int;

            #[must_use]
            pub(crate) fn hwloc_bitmap_weight(bitmap: *const RawBitmap) -> c_int;

            #[must_use]
            pub(crate) fn hwloc_bitmap_or(
                result: *mut RawBitmap,
                bitmap1: *const RawBitmap,
                bitmap2: *const RawBitmap,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_and(
                result: *mut RawBitmap,
                bitmap1: *const RawBitmap,
                bitmap2: *const RawBitmap,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_xor(
                result: *mut RawBitmap,
                bitmap1: *const RawBitmap,
                bitmap2: *const RawBitmap,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_not(
                result: *mut RawBitmap,
                bitmap: *const RawBitmap,
            ) -> c_int;

            pub(crate) fn hwloc_bitmap_isequal(
                left: *const RawBitmap,
                right: *const RawBitmap,
            ) -> c_int;
            pub(crate) fn hwloc_bitmap_compare(
                left: *const RawBitmap,
                right: *const RawBitmap,
            ) -> c_int;

            // === Ordering between ObjectTypes ===

            #[must_use]
            pub(crate) fn hwloc_compare_types(type1: RawObjectType, type2: RawObjectType) -> c_int;

            // === Kinds of ObjectTypes ===

            #[must_use]
            pub(crate) fn hwloc_obj_type_is_normal(ty: RawObjectType) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_obj_type_is_io(ty: RawObjectType) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_obj_type_is_memory(ty: RawObjectType) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_obj_type_is_cache(ty: RawObjectType) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_obj_type_is_dcache(ty: RawObjectType) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_obj_type_is_icache(ty: RawObjectType) -> c_int;

            // === FIXME: The following FFIs have not yet been checked for correctness ===

            // === Topology Creation and Destruction ===

            pub(crate) fn hwloc_topology_init(topology: *mut *mut HwlocTopology) -> c_int;
            pub(crate) fn hwloc_topology_load(topology: *mut HwlocTopology) -> c_int;
            pub(crate) fn hwloc_topology_destroy(topology: *mut HwlocTopology);

            // === Topology Utilities
            pub(crate) fn hwloc_topology_dup(
                newtop: *mut *mut HwlocTopology,
                oldtop: *mut HwlocTopology,
            ) -> c_int;
            pub(crate) fn hwloc_topology_abi_check(topology: *mut HwlocTopology) -> c_int;
            pub(crate) fn hwloc_topology_check(topology: *mut HwlocTopology) -> c_int;

            // === Topology Detection Configuration and Query ===
            pub(crate) fn hwloc_topology_set_pid(topology: *mut HwlocTopology, pid: pid_t)
                -> c_int;
            pub(crate) fn hwloc_topology_set_synthetic(
                topology: *mut HwlocTopology,
                description: *const c_char,
            ) -> c_int;
            pub(crate) fn hwloc_topology_set_xml(
                topology: *mut HwlocTopology,
                xmlpath: *const c_char,
            ) -> c_int;
            pub(crate) fn hwloc_topology_set_xmlbuffer(
                topology: *mut HwlocTopology,
                buffer: *const c_char,
                size: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_topology_set_components(
                topology: *mut HwlocTopology,
                flags: c_ulong,
                name: *const c_char,
            ) -> c_int;

            pub(crate) fn hwloc_topology_set_flags(
                topology: *mut HwlocTopology,
                flags: c_ulong,
            ) -> c_int;
            pub(crate) fn hwloc_topology_get_flags(topology: *mut HwlocTopology) -> c_ulong;
            pub(crate) fn hwloc_topology_is_thissystem(topology: *mut HwlocTopology) -> c_int;

            pub(crate) fn hwloc_topology_get_support(
                topology: *mut HwlocTopology,
            ) -> *const TopologySupport;

            pub(crate) fn hwloc_topology_set_type_filter(
                topology: *mut HwlocTopology,
                otype: RawObjectType,
                filter: c_uchar,
            ) -> c_int;
            pub(crate) fn hwloc_topology_get_type_filter(
                topology: *mut HwlocTopology,
                otype: RawObjectType,
                filter: *mut c_uchar,
            ) -> c_int;
            pub(crate) fn hwloc_topology_set_all_types_filter(
                topology: *mut HwlocTopology,
                filter: c_uchar,
            ) -> c_int;
            pub(crate) fn hwloc_topology_set_cache_types_filter(
                topology: *mut HwlocTopology,
                otype: RawObjectType,
                filter: c_uchar,
            ) -> c_int;
            pub(crate) fn hwloc_topology_set_icache_types_filter(
                topology: *mut HwlocTopology,
                otype: RawObjectType,
                filter: c_uchar,
            ) -> c_int;
            pub(crate) fn hwloc_topology_set_io_types_filter(
                topology: *mut HwlocTopology,
                otype: RawObjectType,
                filter: c_uchar,
            ) -> c_int;

            pub(crate) fn hwloc_topology_set_userdata(
                topology: *mut HwlocTopology,
                data: *const c_void,
            );
            pub(crate) fn hwloc_topology_get_userdata(topology: *mut HwlocTopology) -> *mut c_void;

            pub(crate) fn hwloc_topology_restrict(
                topology: *mut HwlocTopology,
                set: *const RawBitmap,
                flags: c_ulong,
            ) -> c_int;
            pub(crate) fn hwloc_topology_allow(
                topology: *mut HwlocTopology,
                set: *const RawBitmap,
                flags: c_ulong,
            ) -> c_int;

            pub(crate) fn hwloc_topology_insert_misc_object(
                topology: *mut HwlocTopology,
                parent: *mut TopologyObject,
                name: *const c_char,
            ) -> *mut TopologyObject;
            pub(crate) fn hwloc_topology_alloc_group_object(
                topology: *mut HwlocTopology,
            ) -> *mut TopologyObject;
            pub(crate) fn hwloc_topology_insert_group_object(
                topology: *mut HwlocTopology,
                group: *mut TopologyObject,
            ) -> *mut TopologyObject;

            pub(crate) fn hwloc_obj_add_other_obj_sets(
                dst: *mut TopologyObject,
                src: *mut TopologyObject,
            ) -> c_int;

            // === Object levels, depths and types ===

            pub(crate) fn hwloc_topology_get_depth(topology: *mut HwlocTopology) -> c_int;
            pub(crate) fn hwloc_get_type_depth(
                topology: *mut HwlocTopology,
                object_type: RawObjectType,
            ) -> c_int;
            pub(crate) fn hwloc_get_memory_parents_depth(topology: *mut HwlocTopology) -> c_int;
            pub(crate) fn hwloc_get_depth_type(
                topology: *mut HwlocTopology,
                depth: c_int,
            ) -> RawObjectType;
            pub(crate) fn hwloc_get_nbobjs_by_depth(
                topology: *mut HwlocTopology,
                depth: c_uint,
            ) -> c_uint;

            pub(crate) fn hwloc_get_obj_by_depth(
                topology: *mut HwlocTopology,
                depth: c_uint,
                idx: c_uint,
            ) -> *mut TopologyObject;

            // === CPU Binding ===
            pub(crate) fn hwloc_set_cpubind(
                topology: *mut HwlocTopology,
                set: *const RawBitmap,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_cpubind(
                topology: *mut HwlocTopology,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_set_proc_cpubind(
                topology: *mut HwlocTopology,
                pid: pid_t,
                set: *const RawBitmap,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_proc_cpubind(
                topology: *mut HwlocTopology,
                pid: pid_t,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_set_thread_cpubind(
                topology: *mut HwlocTopology,
                thread: pthread_t,
                set: *const RawBitmap,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_thread_cpubind(
                topology: *mut HwlocTopology,
                pid: pthread_t,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_last_cpu_location(
                topology: *mut HwlocTopology,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_proc_last_cpu_location(
                topology: *mut HwlocTopology,
                pid: pid_t,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;

            // === Memory Binding ===
            pub(crate) fn hwloc_set_membind(
                topology: *mut HwlocTopology,
                set: *const RawBitmap,
                policy: MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_membind(
                topology: *mut HwlocTopology,
                set: *mut RawBitmap,
                policy: *mut MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_set_proc_membind(
                topology: *mut HwlocTopology,
                pid: pid_t,
                set: *const RawBitmap,
                policy: MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_proc_membind(
                topology: *mut HwlocTopology,
                pid: pid_t,
                set: *mut RawBitmap,
                policy: *mut MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_set_area_membind(
                topology: *mut HwlocTopology,
                addr: *const c_void,
                len: size_t,
                set: *const RawBitmap,
                policy: MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_area_membind(
                topology: *mut HwlocTopology,
                addr: *const c_void,
                len: size_t,
                set: *mut RawBitmap,
                policy: *mut MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_area_memlocation(
                topology: *mut HwlocTopology,
                addr: *const c_void,
                len: size_t,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_alloc(topology: *mut HwlocTopology, len: size_t) -> *mut c_void;
            pub(crate) fn hwloc_alloc_membind(
                topology: *mut HwlocTopology,
                len: size_t,
                set: *const RawBitmap,
                policy: MemBindPolicy,
                flags: c_int,
            ) -> *mut c_void;
            pub(crate) fn hwloc_free(
                topology: *mut HwlocTopology,
                addr: *mut c_void,
                len: size_t,
            ) -> c_int;

            // === TopologyObject text I/O ===

            pub(crate) fn hwloc_obj_type_string(object_type: RawObjectType) -> *const c_char;
            pub(crate) fn hwloc_obj_type_snprintf(
                into: *mut c_char,
                size: size_t,
                object: *const TopologyObject,
                verbose: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_obj_attr_snprintf(
                into: *mut c_char,
                size: size_t,
                object: *const TopologyObject,
                separator: *const c_char,
                verbose: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_type_sscanf(
                strng: *const c_char,
                obj_type: *mut RawObjectType,
                attrs: *mut TopologyObjectAttributes,
                attrs_size: size_t,
            ) -> c_int;
            pub(crate) fn hwloc_type_sscanf_as_depth(
                strng: *const c_char,
                obj_type: *mut RawObjectType,
                topology: *mut HwlocTopology,
                depthp: *mut c_int,
            ) -> c_int;

            // === Adding custom metadata to TopologyObject ===

            pub(crate) fn hwloc_obj_add_info(
                obj: *mut TopologyObject,
                name: *const c_char,
                value: *const c_char,
            ) -> c_int;
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
}
