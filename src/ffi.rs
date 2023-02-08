use crate::{
    bitmap::RawBitmap,
    object::{attributes::RawObjectAttributes, types::RawObjectType, TopologyObject},
    support::TopologySupport,
    MemBindPolicy, RawTopology,
};
use libc::{c_char, c_int, c_uchar, c_uint, c_ulong, c_void, pid_t, pthread_t, size_t};
use std::ffi::CStr;

/// Dereference a C-style string with correct lifetime
pub(crate) fn deref_string(p: &*mut c_char) -> Option<&str> {
    if p.is_null() {
        return None;
    }
    unsafe { CStr::from_ptr(*p) }.to_str().ok()
}

macro_rules! extern_c_block {
    ($link_name:literal) => {
        #[link(name = $link_name)]
        extern "C" {
            // === API versioning: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__api__version.html ===

            // Indicate at runtime which hwloc API version was used at build time.
            pub(crate) fn hwloc_get_api_version() -> c_uint;

            // === Object types: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__object__types.html ===

            #[must_use]
            pub(crate) fn hwloc_compare_types(type1: RawObjectType, type2: RawObjectType) -> c_int;

            // === Bitmap API: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__bitmap.html ===

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

            // === Kinds of ObjectTypes: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__types.html ===

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

            pub(crate) fn hwloc_topology_init(topology: *mut *mut RawTopology) -> c_int;
            pub(crate) fn hwloc_topology_load(topology: *mut RawTopology) -> c_int;
            pub(crate) fn hwloc_topology_destroy(topology: *mut RawTopology);

            // === Topology Utilities
            pub(crate) fn hwloc_topology_dup(
                newtop: *mut *mut RawTopology,
                oldtop: *mut RawTopology,
            ) -> c_int;
            pub(crate) fn hwloc_topology_abi_check(topology: *mut RawTopology) -> c_int;
            pub(crate) fn hwloc_topology_check(topology: *mut RawTopology) -> c_int;

            // === Topology Detection Configuration and Query ===
            pub(crate) fn hwloc_topology_set_pid(topology: *mut RawTopology, pid: pid_t) -> c_int;
            pub(crate) fn hwloc_topology_set_synthetic(
                topology: *mut RawTopology,
                description: *const c_char,
            ) -> c_int;
            pub(crate) fn hwloc_topology_set_xml(
                topology: *mut RawTopology,
                xmlpath: *const c_char,
            ) -> c_int;
            pub(crate) fn hwloc_topology_set_xmlbuffer(
                topology: *mut RawTopology,
                buffer: *const c_char,
                size: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_topology_set_components(
                topology: *mut RawTopology,
                flags: c_ulong,
                name: *const c_char,
            ) -> c_int;

            pub(crate) fn hwloc_topology_set_flags(
                topology: *mut RawTopology,
                flags: c_ulong,
            ) -> c_int;
            pub(crate) fn hwloc_topology_get_flags(topology: *mut RawTopology) -> c_ulong;
            pub(crate) fn hwloc_topology_is_thissystem(topology: *mut RawTopology) -> c_int;

            pub(crate) fn hwloc_topology_get_support(
                topology: *mut RawTopology,
            ) -> *const TopologySupport;

            pub(crate) fn hwloc_topology_set_type_filter(
                topology: *mut RawTopology,
                otype: RawObjectType,
                filter: c_uchar,
            ) -> c_int;
            pub(crate) fn hwloc_topology_get_type_filter(
                topology: *mut RawTopology,
                otype: RawObjectType,
                filter: *mut c_uchar,
            ) -> c_int;
            pub(crate) fn hwloc_topology_set_all_types_filter(
                topology: *mut RawTopology,
                filter: c_uchar,
            ) -> c_int;
            pub(crate) fn hwloc_topology_set_cache_types_filter(
                topology: *mut RawTopology,
                otype: RawObjectType,
                filter: c_uchar,
            ) -> c_int;
            pub(crate) fn hwloc_topology_set_icache_types_filter(
                topology: *mut RawTopology,
                otype: RawObjectType,
                filter: c_uchar,
            ) -> c_int;
            pub(crate) fn hwloc_topology_set_io_types_filter(
                topology: *mut RawTopology,
                otype: RawObjectType,
                filter: c_uchar,
            ) -> c_int;

            pub(crate) fn hwloc_topology_set_userdata(
                topology: *mut RawTopology,
                data: *const c_void,
            );
            pub(crate) fn hwloc_topology_get_userdata(topology: *mut RawTopology) -> *mut c_void;

            pub(crate) fn hwloc_topology_restrict(
                topology: *mut RawTopology,
                set: *const RawBitmap,
                flags: c_ulong,
            ) -> c_int;
            pub(crate) fn hwloc_topology_allow(
                topology: *mut RawTopology,
                set: *const RawBitmap,
                flags: c_ulong,
            ) -> c_int;

            pub(crate) fn hwloc_topology_insert_misc_object(
                topology: *mut RawTopology,
                parent: *mut TopologyObject,
                name: *const c_char,
            ) -> *mut TopologyObject;
            pub(crate) fn hwloc_topology_alloc_group_object(
                topology: *mut RawTopology,
            ) -> *mut TopologyObject;
            pub(crate) fn hwloc_topology_insert_group_object(
                topology: *mut RawTopology,
                group: *mut TopologyObject,
            ) -> *mut TopologyObject;

            pub(crate) fn hwloc_obj_add_other_obj_sets(
                dst: *mut TopologyObject,
                src: *mut TopologyObject,
            ) -> c_int;

            // === Object levels, depths and types ===

            pub(crate) fn hwloc_topology_get_depth(topology: *mut RawTopology) -> c_int;
            pub(crate) fn hwloc_get_type_depth(
                topology: *mut RawTopology,
                object_type: RawObjectType,
            ) -> c_int;
            pub(crate) fn hwloc_get_memory_parents_depth(topology: *mut RawTopology) -> c_int;
            pub(crate) fn hwloc_get_depth_type(
                topology: *mut RawTopology,
                depth: c_int,
            ) -> RawObjectType;
            pub(crate) fn hwloc_get_nbobjs_by_depth(
                topology: *mut RawTopology,
                depth: c_uint,
            ) -> c_uint;

            pub(crate) fn hwloc_get_obj_by_depth(
                topology: *mut RawTopology,
                depth: c_uint,
                idx: c_uint,
            ) -> *mut TopologyObject;

            // === CPU Binding ===
            pub(crate) fn hwloc_set_cpubind(
                topology: *mut RawTopology,
                set: *const RawBitmap,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_cpubind(
                topology: *mut RawTopology,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_set_proc_cpubind(
                topology: *mut RawTopology,
                pid: pid_t,
                set: *const RawBitmap,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_proc_cpubind(
                topology: *mut RawTopology,
                pid: pid_t,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_set_thread_cpubind(
                topology: *mut RawTopology,
                thread: pthread_t,
                set: *const RawBitmap,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_thread_cpubind(
                topology: *mut RawTopology,
                pid: pthread_t,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_last_cpu_location(
                topology: *mut RawTopology,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_proc_last_cpu_location(
                topology: *mut RawTopology,
                pid: pid_t,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;

            // === Memory Binding ===
            pub(crate) fn hwloc_set_membind(
                topology: *mut RawTopology,
                set: *const RawBitmap,
                policy: MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_membind(
                topology: *mut RawTopology,
                set: *mut RawBitmap,
                policy: *mut MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_set_proc_membind(
                topology: *mut RawTopology,
                pid: pid_t,
                set: *const RawBitmap,
                policy: MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_proc_membind(
                topology: *mut RawTopology,
                pid: pid_t,
                set: *mut RawBitmap,
                policy: *mut MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_set_area_membind(
                topology: *mut RawTopology,
                addr: *const c_void,
                len: size_t,
                set: *const RawBitmap,
                policy: MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_area_membind(
                topology: *mut RawTopology,
                addr: *const c_void,
                len: size_t,
                set: *mut RawBitmap,
                policy: *mut MemBindPolicy,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_get_area_memlocation(
                topology: *mut RawTopology,
                addr: *const c_void,
                len: size_t,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_alloc(topology: *mut RawTopology, len: size_t) -> *mut c_void;
            pub(crate) fn hwloc_alloc_membind(
                topology: *mut RawTopology,
                len: size_t,
                set: *const RawBitmap,
                policy: MemBindPolicy,
                flags: c_int,
            ) -> *mut c_void;
            pub(crate) fn hwloc_free(
                topology: *mut RawTopology,
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
                attrs: *mut RawObjectAttributes,
                attrs_size: size_t,
            ) -> c_int;
            pub(crate) fn hwloc_type_sscanf_as_depth(
                strng: *const c_char,
                obj_type: *mut RawObjectType,
                topology: *mut RawTopology,
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
