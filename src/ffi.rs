use crate::{
    bitmap::RawBitmap,
    builder::{BuildFlags, ComponentsFlags, RawTypeFilter},
    depth::RawDepth,
    editor::RestrictFlags,
    memory::{MemoryBindingFlags, RawMemoryBindingPolicy},
    objects::{types::RawObjectType, TopologyObject},
    support::TopologySupport,
    ProcessId, RawTopology, ThreadId,
};
use libc::{c_char, c_int, c_uint, c_ulong, c_void, size_t};
use std::{ffi::CStr, fmt, ptr};

/// Dereference a C pointer with correct lifetime (*const -> & version)
pub(crate) unsafe fn deref_ptr<T>(p: &*const T) -> Option<&T> {
    if p.is_null() {
        return None;
    }
    Some(unsafe { &**p })
}

/// Dereference a C pointer with correct lifetime (*mut -> & version)
pub(crate) unsafe fn deref_ptr_mut<T>(p: &*mut T) -> Option<&T> {
    if p.is_null() {
        return None;
    }
    Some(unsafe { &**p })
}

/// Dereference a C pointer with correct lifetime (*mut -> &mut version)
pub(crate) unsafe fn deref_mut_ptr<T>(p: &mut *mut T) -> Option<&mut T> {
    if p.is_null() {
        return None;
    }
    Some(unsafe { &mut **p })
}

/// Dereference a C-style string with correct lifetime
pub(crate) unsafe fn deref_string(p: &*mut c_char) -> Option<&str> {
    if p.is_null() {
        return None;
    }
    unsafe { CStr::from_ptr(*p) }.to_str().ok()
}

/// Get text output from an snprintf-like function
pub(crate) fn call_snprintf(mut snprintf: impl FnMut(*mut c_char, size_t) -> i32) -> Box<[c_char]> {
    let len_i32 = snprintf(ptr::null_mut(), 0);
    let len =
        usize::try_from(len_i32).expect("Got invalid string length from an snprintf-like API");
    let mut buf = vec![0i8; len + 1];
    assert_eq!(
        snprintf(buf.as_mut_ptr(), buf.len()),
        len_i32,
        "Got inconsistent string length from an snprintf-like API"
    );
    buf.into()
}

/// Send the output of an snprintf-like function to a standard Rust formatter
pub(crate) fn write_snprintf(
    f: &mut fmt::Formatter,
    snprintf: impl FnMut(*mut c_char, size_t) -> i32,
) -> fmt::Result {
    let chars = call_snprintf(snprintf);
    write!(
        f,
        "{}",
        unsafe { CStr::from_ptr(chars.as_ptr()) }
            .to_str()
            .expect("Got invalid string from an snprintf-like API")
    )
}

macro_rules! extern_c_block {
    ($link_name:literal) => {
        #[link(name = $link_name)]
        extern "C" {
            // === API versioning: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__api__version.html

            #[must_use]
            pub(crate) fn hwloc_get_api_version() -> c_uint;

            // === Object types: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__object__types.html

            #[must_use]
            pub(crate) fn hwloc_compare_types(type1: RawObjectType, type2: RawObjectType) -> c_int;

            // === Topology creation and destruction: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__creation.html

            #[must_use]
            pub(crate) fn hwloc_topology_init(topology: *mut *mut RawTopology) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_load(topology: *mut RawTopology) -> c_int;
            pub(crate) fn hwloc_topology_destroy(topology: *mut RawTopology);
            #[must_use]
            pub(crate) fn hwloc_topology_dup(
                newtop: *mut *mut RawTopology,
                oldtop: *const RawTopology,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_abi_check(topology: *const RawTopology) -> c_int;

            // === Object levels, depths and types: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__levels.html

            #[must_use]
            pub(crate) fn hwloc_topology_get_depth(topology: *const RawTopology) -> RawDepth;
            #[must_use]
            pub(crate) fn hwloc_get_type_depth(
                topology: *const RawTopology,
                object_type: RawObjectType,
            ) -> RawDepth;
            #[must_use]
            pub(crate) fn hwloc_get_memory_parents_depth(topology: *const RawTopology) -> RawDepth;
            #[must_use]
            pub(crate) fn hwloc_get_depth_type(
                topology: *const RawTopology,
                depth: RawDepth,
            ) -> RawObjectType;
            #[must_use]
            pub(crate) fn hwloc_get_nbobjs_by_depth(
                topology: *const RawTopology,
                depth: RawDepth,
            ) -> c_uint;
            #[must_use]
            pub(crate) fn hwloc_get_obj_by_depth(
                topology: *const RawTopology,
                depth: RawDepth,
                idx: c_uint,
            ) -> *mut TopologyObject;

            // === Converting between object types, attributes and strings: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__object__strings.html

            #[must_use]
            pub(crate) fn hwloc_obj_type_snprintf(
                into: *mut c_char,
                size: size_t,
                object: *const TopologyObject,
                verbose: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_obj_attr_snprintf(
                into: *mut c_char,
                size: size_t,
                object: *const TopologyObject,
                separator: *const c_char,
                verbose: c_int,
            ) -> c_int;
            // NOTE: Not exposing type printf/scanf for now

            // === Consulting and adding Key-Value info attributes: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__info__attr.html

            #[must_use]
            pub(crate) fn hwloc_obj_add_info(
                obj: *mut TopologyObject,
                name: *const c_char,
                value: *const c_char,
            ) -> c_int;

            // === CPU binding: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpubinding.html

            #[must_use]
            pub(crate) fn hwloc_set_cpubind(
                topology: *const RawTopology,
                set: *const RawBitmap,
                flags: c_uint,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_cpubind(
                topology: *const RawTopology,
                set: *mut RawBitmap,
                flags: c_uint,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_set_proc_cpubind(
                topology: *const RawTopology,
                pid: ProcessId,
                set: *const RawBitmap,
                flags: c_uint,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_proc_cpubind(
                topology: *const RawTopology,
                pid: ProcessId,
                set: *mut RawBitmap,
                flags: c_uint,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_set_thread_cpubind(
                topology: *const RawTopology,
                thread: ThreadId,
                set: *const RawBitmap,
                flags: c_uint,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_thread_cpubind(
                topology: *const RawTopology,
                pid: ThreadId,
                set: *mut RawBitmap,
                flags: c_uint,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_last_cpu_location(
                topology: *const RawTopology,
                set: *mut RawBitmap,
                flags: c_uint,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_proc_last_cpu_location(
                topology: *const RawTopology,
                pid: ProcessId,
                set: *mut RawBitmap,
                flags: c_uint,
            ) -> c_int;

            // === Memory binding: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__membinding.html

            #[must_use]
            pub(crate) fn hwloc_set_membind(
                topology: *const RawTopology,
                set: *const RawBitmap,
                policy: RawMemoryBindingPolicy,
                flags: MemoryBindingFlags,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_membind(
                topology: *const RawTopology,
                set: *mut RawBitmap,
                policy: *mut RawMemoryBindingPolicy,
                flags: MemoryBindingFlags,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_set_proc_membind(
                topology: *const RawTopology,
                pid: ProcessId,
                set: *const RawBitmap,
                policy: RawMemoryBindingPolicy,
                flags: MemoryBindingFlags,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_proc_membind(
                topology: *const RawTopology,
                pid: ProcessId,
                set: *mut RawBitmap,
                policy: *mut RawMemoryBindingPolicy,
                flags: MemoryBindingFlags,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_set_area_membind(
                topology: *const RawTopology,
                addr: *const c_void,
                len: size_t,
                set: *const RawBitmap,
                policy: RawMemoryBindingPolicy,
                flags: MemoryBindingFlags,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_area_membind(
                topology: *const RawTopology,
                addr: *const c_void,
                len: size_t,
                set: *mut RawBitmap,
                policy: *mut RawMemoryBindingPolicy,
                flags: MemoryBindingFlags,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_area_memlocation(
                topology: *const RawTopology,
                addr: *const c_void,
                len: size_t,
                set: *mut RawBitmap,
                flags: MemoryBindingFlags,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_alloc(topology: *const RawTopology, len: size_t) -> *mut c_void;
            #[must_use]
            pub(crate) fn hwloc_alloc_membind(
                topology: *const RawTopology,
                len: size_t,
                set: *const RawBitmap,
                policy: RawMemoryBindingPolicy,
                flags: MemoryBindingFlags,
            ) -> *mut c_void;
            #[must_use]
            pub(crate) fn hwloc_free(
                topology: *const RawTopology,
                addr: *mut c_void,
                len: size_t,
            ) -> c_int;

            // === Changing the source of topology discovery: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__setsource.html

            #[must_use]
            pub(crate) fn hwloc_topology_set_pid(
                topology: *mut RawTopology,
                pid: ProcessId,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_set_synthetic(
                topology: *mut RawTopology,
                description: *const c_char,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_set_xml(
                topology: *mut RawTopology,
                xmlpath: *const c_char,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_set_xmlbuffer(
                topology: *mut RawTopology,
                buffer: *const c_char,
                size: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_set_components(
                topology: *mut RawTopology,
                flags: ComponentsFlags,
                name: *const c_char,
            ) -> c_int;

            // === Topology detection configuration and query: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__configuration.html

            #[must_use]
            pub(crate) fn hwloc_topology_set_flags(
                topology: *mut RawTopology,
                flags: BuildFlags,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_get_flags(topology: *const RawTopology) -> c_ulong;
            #[must_use]
            pub(crate) fn hwloc_topology_is_thissystem(topology: *const RawTopology) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_get_support(
                topology: *const RawTopology,
            ) -> *const TopologySupport;
            #[must_use]
            pub(crate) fn hwloc_topology_set_type_filter(
                topology: *mut RawTopology,
                ty: RawObjectType,
                filter: RawTypeFilter,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_get_type_filter(
                topology: *const RawTopology,
                ty: RawObjectType,
                filter: *mut RawTypeFilter,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_set_all_types_filter(
                topology: *mut RawTopology,
                filter: RawTypeFilter,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_set_cache_types_filter(
                topology: *mut RawTopology,
                filter: RawTypeFilter,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_set_icache_types_filter(
                topology: *mut RawTopology,
                filter: RawTypeFilter,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_set_io_types_filter(
                topology: *mut RawTopology,
                filter: RawTypeFilter,
            ) -> c_int;
            // NOTE: set_userdata and get_userdata are NOT exposed because they
            //       are hard to make work with copying, persistence and thread
            //       safety and are not so useful as to justify the effort.

            // === Modifying a loaded Topology: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__tinker.html

            #[must_use]
            pub(crate) fn hwloc_topology_restrict(
                topology: *mut RawTopology,
                set: *const RawBitmap,
                flags: RestrictFlags,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_allow(
                topology: *mut RawTopology,
                cpuset: *const RawBitmap,
                nodeset: *const RawBitmap,
                flags: c_ulong,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_insert_misc_object(
                topology: *mut RawTopology,
                parent: *mut TopologyObject,
                name: *const c_char,
            ) -> *mut TopologyObject;
            #[must_use]
            pub(crate) fn hwloc_topology_alloc_group_object(
                topology: *mut RawTopology,
            ) -> *mut TopologyObject;
            #[must_use]
            pub(crate) fn hwloc_topology_insert_group_object(
                topology: *mut RawTopology,
                group: *mut TopologyObject,
            ) -> *mut TopologyObject;
            #[must_use]
            pub(crate) fn hwloc_obj_add_other_obj_sets(
                dst: *mut TopologyObject,
                src: *const TopologyObject,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_refresh(topology: *mut RawTopology) -> c_int;

            // === Finding objects inside a CPUset: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__find__inside.html

            // TODO

            // === Kinds of ObjectTypes: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__types.html

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

            // === Finding objects, miscellaneous helpers: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__find__misc.html

            // TODO

            // === CPU and node sets of entire topologies: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__topology__sets.html

            // TODO

            // === Bitmap API: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__bitmap.html

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
            pub(crate) fn hwloc_bitmap_list_snprintf(
                buf: *mut c_char,
                len: size_t,
                bitmap: *const RawBitmap,
            ) -> c_int;
            // NOTE: Not exposing other printfs and scanfs for now

            pub(crate) fn hwloc_bitmap_zero(bitmap: *mut RawBitmap);
            pub(crate) fn hwloc_bitmap_fill(bitmap: *mut RawBitmap);
            #[must_use]
            pub(crate) fn hwloc_bitmap_only(bitmap: *mut RawBitmap, id: c_uint) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_allbut(bitmap: *mut RawBitmap, id: c_uint) -> c_int;
            // NOTE: Not exposing ulong-based APIs for now, so no from_ulong, from_ith_ulong, from_ulongs
            #[must_use]
            pub(crate) fn hwloc_bitmap_set(bitmap: *mut RawBitmap, id: c_uint) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_set_range(
                bitmap: *mut RawBitmap,
                begin: c_uint,
                end: c_int,
            ) -> c_int;
            // NOTE: Not exposing ulong-based APIs for now, so no set_ith_ulong
            #[must_use]
            pub(crate) fn hwloc_bitmap_clr(bitmap: *mut RawBitmap, id: c_uint) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_clr_range(
                bitmap: *mut RawBitmap,
                begin: c_uint,
                end: c_int,
            ) -> c_int;
            pub(crate) fn hwloc_bitmap_singlify(bitmap: *mut RawBitmap);
            // NOTE: Not exposing ulong-based APIs for now, so no to_ulong, to_ith_ulong, to_ulongs and nr_ulongs

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
            pub(crate) fn hwloc_bitmap_first_unset(bitmap: *const RawBitmap) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_next_unset(bitmap: *const RawBitmap, prev: c_int) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_last_unset(bitmap: *const RawBitmap) -> c_int;

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
            pub(crate) fn hwloc_bitmap_andnot(
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

            #[must_use]
            pub(crate) fn hwloc_bitmap_intersects(
                left: *const RawBitmap,
                right: *const RawBitmap,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_isincluded(
                left: *const RawBitmap,
                right: *const RawBitmap,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_bitmap_isequal(
                left: *const RawBitmap,
                right: *const RawBitmap,
            ) -> c_int;
            // NOTE: Not providing compare_first since it trivially follows from
            //       first_set and seems obscure.
            #[must_use]
            pub(crate) fn hwloc_bitmap_compare(
                left: *const RawBitmap,
                right: *const RawBitmap,
            ) -> c_int;

            // === TODO: Other APIs

            // TODO: Cover more later: distances, interop, CPU kinds, etc...
            //       Beware that primitives that modify the topology should be
            //       exposed in the TopologyEditor, not Topology, because per
            //       hwloc documentation hwloc_topology_refresh() must be called
            //       before multithreaded access is thread-safe again.
        }
    };
}

#[cfg(target_os = "windows")]
extern_c_block!("libhwloc");

#[cfg(not(target_os = "windows"))]
extern_c_block!("hwloc");
