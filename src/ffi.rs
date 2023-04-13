use crate::{
    bitmaps::RawBitmap,
    errors::NulError,
    info::TextualInfo,
    memory::{
        attributes::{MemoryAttributeID, RawLocation},
        binding::RawMemoryBindingPolicy,
    },
    objects::{
        depth::RawDepth,
        distances::{DistancesAddHandle, RawDistances, RawDistancesTransform},
        types::RawObjectType,
        TopologyObject,
    },
    topology::{builder::RawTypeFilter, support::FeatureSupport, RawTopology},
    ProcessId, ThreadId,
};
#[cfg(target_os = "linux")]
use libc::pid_t;
use std::{
    ffi::{c_char, c_int, c_uint, c_ulong, c_void, CStr},
    fmt,
    marker::{PhantomData, PhantomPinned},
    ptr::{self, NonNull},
};

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
pub(crate) unsafe fn deref_str(p: &*mut c_char) -> Option<&CStr> {
    if p.is_null() {
        return None;
    }
    Some(unsafe { CStr::from_ptr(*p) })
}

/// Get text output from an snprintf-like function
pub(crate) fn call_snprintf(mut snprintf: impl FnMut(*mut c_char, usize) -> i32) -> Box<[c_char]> {
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
    snprintf: impl FnMut(*mut c_char, usize) -> i32,
) -> fmt::Result {
    let chars = call_snprintf(snprintf);
    write!(
        f,
        "{}",
        unsafe { CStr::from_ptr(chars.as_ptr()) }.to_string_lossy()
    )
}

/// Less error-prone CString alternative
///
/// This fulfills the same goal as CString (go from Rust &str to C *char)
/// but with a less error-prone API and a libc-backed allocation whose ownership
/// can safely be transferred to C libraries that manage memory using
/// malloc/free like hwloc.
///
pub(crate) struct LibcString(NonNull<[c_char]>);
//
impl LibcString {
    /// Convert a Rust string to a C-compatible representation
    ///
    /// Returns `None` if the Rust string cannot be converted to a C
    /// representation because it contains null chars.
    pub fn new(s: impl AsRef<str>) -> Result<Self, NulError> {
        // Check input string for inner null chars
        let s = s.as_ref();
        if s.find('\0').is_some() {
            return Err(NulError);
        }

        // Allocate C string and wrap it in Self
        let len = s.len() + 1;
        let data = unsafe { libc::malloc(len) } as *mut c_char;
        let data = NonNull::new(data).expect("Failed to allocate string buffer");
        let buf = NonNull::from(unsafe { std::slice::from_raw_parts_mut(data.as_ptr(), len) });
        let result = Self(buf);

        // Fill the string and return it
        let bytes = unsafe { std::slice::from_raw_parts_mut(buf.as_ptr() as *mut u8, len) };
        let (last, elements) = bytes
            .split_last_mut()
            .expect("Cannot happen, len >= 1 by construction");
        elements.copy_from_slice(s.as_bytes());
        *last = b'\0';
        Ok(result)
    }

    /// Check the length of the string, including NUL terminator
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Make the string momentarily available to a C API that expects `const char*`
    ///
    /// Make sure the C API does not retain any pointer to the string after
    /// this LibcString is deallocated!
    pub fn borrow(&self) -> *const c_char {
        self.0.as_ptr() as *const c_char
    }

    /// Transfer ownership of the string to a C API
    ///
    /// Unlike with regular CString, it is safe to pass this string to a C API
    /// that may later free it using `libc::free()`.
    pub fn into_raw(self) -> *mut c_char {
        let ptr = self.0.as_ptr() as *mut c_char;
        std::mem::forget(self);
        ptr
    }
}
//
impl Drop for LibcString {
    fn drop(&mut self) {
        unsafe { libc::free(self.0.as_ptr() as *mut c_void) }
    }
}

/// Rust model of a C incomplete type (struct declaration without a definition)
/// From https://doc.rust-lang.org/nomicon/ffi.html#representing-opaque-structs
#[repr(C)]
pub(crate) struct IncompleteType {
    _data: [u8; 0],
    _marker: PhantomData<(*mut u8, PhantomPinned)>,
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
                size: usize,
                object: *const TopologyObject,
                verbose: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_obj_attr_snprintf(
                into: *mut c_char,
                size: usize,
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
                flags: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_cpubind(
                topology: *const RawTopology,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_set_proc_cpubind(
                topology: *const RawTopology,
                pid: ProcessId,
                set: *const RawBitmap,
                flags: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_proc_cpubind(
                topology: *const RawTopology,
                pid: ProcessId,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_set_thread_cpubind(
                topology: *const RawTopology,
                thread: ThreadId,
                set: *const RawBitmap,
                flags: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_thread_cpubind(
                topology: *const RawTopology,
                pid: ThreadId,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_last_cpu_location(
                topology: *const RawTopology,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_proc_last_cpu_location(
                topology: *const RawTopology,
                pid: ProcessId,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;

            // === Memory binding: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__membinding.html

            #[must_use]
            pub(crate) fn hwloc_set_membind(
                topology: *const RawTopology,
                set: *const RawBitmap,
                policy: RawMemoryBindingPolicy,
                flags: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_membind(
                topology: *const RawTopology,
                set: *mut RawBitmap,
                policy: *mut RawMemoryBindingPolicy,
                flags: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_set_proc_membind(
                topology: *const RawTopology,
                pid: ProcessId,
                set: *const RawBitmap,
                policy: RawMemoryBindingPolicy,
                flags: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_proc_membind(
                topology: *const RawTopology,
                pid: ProcessId,
                set: *mut RawBitmap,
                policy: *mut RawMemoryBindingPolicy,
                flags: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_set_area_membind(
                topology: *const RawTopology,
                addr: *const c_void,
                len: usize,
                set: *const RawBitmap,
                policy: RawMemoryBindingPolicy,
                flags: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_area_membind(
                topology: *const RawTopology,
                addr: *const c_void,
                len: usize,
                set: *mut RawBitmap,
                policy: *mut RawMemoryBindingPolicy,
                flags: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_area_memlocation(
                topology: *const RawTopology,
                addr: *const c_void,
                len: usize,
                set: *mut RawBitmap,
                flags: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_alloc(topology: *const RawTopology, len: usize) -> *mut c_void;
            #[must_use]
            pub(crate) fn hwloc_alloc_membind(
                topology: *const RawTopology,
                len: usize,
                set: *const RawBitmap,
                policy: RawMemoryBindingPolicy,
                flags: c_int,
            ) -> *mut c_void;
            #[must_use]
            pub(crate) fn hwloc_free(
                topology: *const RawTopology,
                addr: *mut c_void,
                len: usize,
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
                flags: c_ulong,
                name: *const c_char,
            ) -> c_int;

            // === Topology detection configuration and query: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__configuration.html

            #[must_use]
            pub(crate) fn hwloc_topology_set_flags(
                topology: *mut RawTopology,
                flags: c_ulong,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_get_flags(topology: *const RawTopology) -> c_ulong;
            #[must_use]
            pub(crate) fn hwloc_topology_is_thissystem(topology: *const RawTopology) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_get_support(
                topology: *const RawTopology,
            ) -> *const FeatureSupport;
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
                flags: c_ulong,
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

            #[must_use]
            pub(crate) fn hwloc_bitmap_singlify_per_core(
                topology: *const RawTopology,
                cpuset: *mut RawBitmap,
                which: c_uint,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_obj_with_same_locality(
                topology: *const RawTopology,
                src: *const TopologyObject,
                ty: RawObjectType,
                subtype: *const c_char,
                nameprefix: *const c_char,
                flags: c_ulong,
            ) -> *const TopologyObject;

            // === CPU and node sets of entire topologies: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__topology__sets.html

            #[must_use]
            pub(crate) fn hwloc_topology_get_complete_cpuset(
                topology: *const RawTopology,
            ) -> *const RawBitmap;
            #[must_use]
            pub(crate) fn hwloc_topology_get_topology_cpuset(
                topology: *const RawTopology,
            ) -> *const RawBitmap;
            #[must_use]
            pub(crate) fn hwloc_topology_get_allowed_cpuset(
                topology: *const RawTopology,
            ) -> *const RawBitmap;
            #[must_use]
            pub(crate) fn hwloc_topology_get_complete_nodeset(
                topology: *const RawTopology,
            ) -> *const RawBitmap;
            #[must_use]
            pub(crate) fn hwloc_topology_get_topology_nodeset(
                topology: *const RawTopology,
            ) -> *const RawBitmap;
            #[must_use]
            pub(crate) fn hwloc_topology_get_allowed_nodeset(
                topology: *const RawTopology,
            ) -> *const RawBitmap;

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
                len: usize,
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
            pub(crate) fn hwloc_bitmap_singlify(bitmap: *mut RawBitmap) -> c_int;
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

            // === Exporting Topologies to XML: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__xmlexport.html

            #[must_use]
            pub(crate) fn hwloc_topology_export_xml(
                topology: *const RawTopology,
                xmlpath: *const c_char,
                flags: c_ulong,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_topology_export_xmlbuffer(
                topology: *const RawTopology,
                xmlbuffer: *mut *mut c_char,
                buflen: *mut c_int,
                flags: c_ulong,
            ) -> c_int;
            pub(crate) fn hwloc_free_xmlbuffer(
                topology: *const RawTopology,
                xmlbuffer: *mut c_char,
            );
            // NOTE: Not exposing userdata at the moment, so no need to bind
            //       associated API functions yet.

            // === Exporting Topologies to Synthetic: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__syntheticexport.html

            #[must_use]
            pub(crate) fn hwloc_topology_export_synthetic(
                topology: *const RawTopology,
                buffer: *mut c_char,
                buflen: usize,
                flags: c_ulong,
            ) -> c_int;

            // === Retrieve distances between objects: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__get.html

            #[must_use]
            pub(crate) fn hwloc_distances_get(
                topology: *const RawTopology,
                nr: *mut c_uint,
                distances: *mut *mut RawDistances,
                kind: c_ulong,
                flags: c_ulong,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_distances_get_by_depth(
                topology: *const RawTopology,
                depth: c_int,
                nr: *mut c_uint,
                distances: *mut *mut RawDistances,
                kind: c_ulong,
                flags: c_ulong,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_distances_get_by_type(
                topology: *const RawTopology,
                ty: RawObjectType,
                nr: *mut c_uint,
                distances: *mut *mut RawDistances,
                kind: c_ulong,
                flags: c_ulong,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_distances_get_by_name(
                topology: *const RawTopology,
                name: *const c_char,
                nr: *mut c_uint,
                distances: *mut *mut RawDistances,
                flags: c_ulong,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_distances_get_name(
                topology: *const RawTopology,
                distances: *const RawDistances,
            ) -> *const c_char;
            pub(crate) fn hwloc_distances_release(
                topology: *const RawTopology,
                distances: *const RawDistances,
            );
            #[must_use]
            pub(crate) fn hwloc_distances_transform(
                topology: *const RawTopology,
                distances: *mut RawDistances,
                transform: RawDistancesTransform,
                transform_attr: *mut c_void,
                flags: c_ulong,
            ) -> c_int;

            // === Add distances between objects: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__add.html

            #[must_use]
            pub(crate) fn hwloc_distances_add_create(
                topology: *mut RawTopology,
                name: *const c_char,
                kind: c_ulong,
                flags: c_ulong,
            ) -> DistancesAddHandle;
            #[must_use]
            pub(crate) fn hwloc_distances_add_values(
                topology: *mut RawTopology,
                handle: DistancesAddHandle,
                nbobjs: c_uint,
                objs: *const *const TopologyObject,
                values: *const u64,
                flags: c_ulong,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_distances_add_commit(
                topology: *mut RawTopology,
                handle: DistancesAddHandle,
                flags: c_ulong,
            ) -> c_int;

            // === Remove distances between objects: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__remove.html

            #[must_use]
            pub(crate) fn hwloc_distances_remove(topology: *mut RawTopology) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_distances_remove_by_depth(
                topology: *mut RawTopology,
                depth: c_int,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_distances_release_remove(
                topology: *mut RawTopology,
                distances: *mut RawDistances,
            ) -> c_int;

            // === Comparing memory node attributes for finding where to allocate on: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs.html

            #[must_use]
            pub(crate) fn hwloc_memattr_get_by_name(
                topology: *const RawTopology,
                name: *const c_char,
                id: *mut MemoryAttributeID,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_get_local_numanode_objs(
                topology: *const RawTopology,
                location: *const RawLocation,
                nr: *mut c_uint,
                nodes: *mut *const TopologyObject,
                flags: c_ulong,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_memattr_get_value(
                topology: *const RawTopology,
                attribute: MemoryAttributeID,
                target_node: *const TopologyObject,
                initiator: *const RawLocation,
                flags: c_ulong,
                value: *mut u64,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_memattr_get_best_target(
                topology: *const RawTopology,
                attribute: MemoryAttributeID,
                initiator: *const RawLocation,
                flags: c_ulong,
                best_target: *mut *const TopologyObject,
                value: *mut u64,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_memattr_get_best_initiator(
                topology: *const RawTopology,
                attribute: MemoryAttributeID,
                target: *const TopologyObject,
                flags: c_ulong,
                best_initiator: *mut RawLocation,
                value: *mut u64,
            ) -> c_int;

            // === Managing memory attributes: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs__manage.html

            #[must_use]
            pub(crate) fn hwloc_memattr_get_name(
                topology: *const RawTopology,
                attribute: MemoryAttributeID,
                name: *mut *const c_char,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_memattr_get_flags(
                topology: *const RawTopology,
                attribute: MemoryAttributeID,
                flags: *mut c_ulong,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_memattr_register(
                topology: *const RawTopology,
                name: *const c_char,
                flags: c_ulong,
                id: *mut MemoryAttributeID,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_memattr_set_value(
                topology: *const RawTopology,
                attribute: MemoryAttributeID,
                target_node: *const TopologyObject,
                initiator: *const RawLocation,
                flags: c_ulong,
                value: u64,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_memattr_get_targets(
                topology: *const RawTopology,
                attribute: MemoryAttributeID,
                initiator: *const RawLocation,
                flags: c_ulong,
                nr: *mut c_uint,
                targets: *mut *const TopologyObject,
                values: *mut u64,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_memattr_get_initiators(
                topology: *const RawTopology,
                attribute: MemoryAttributeID,
                target_node: *const TopologyObject,
                flags: c_ulong,
                nr: *mut c_uint,
                initiators: *mut RawLocation,
                values: *mut u64,
            ) -> c_int;

            // === Kinds of CPU cores: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpukinds.html

            #[must_use]
            pub(crate) fn hwloc_cpukinds_get_nr(
                topology: *const RawTopology,
                flags: c_ulong,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_cpukinds_get_by_cpuset(
                topology: *const RawTopology,
                cpuset: *const RawBitmap,
                flags: c_ulong,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_cpukinds_get_info(
                topology: *const RawTopology,
                kind_index: c_uint,
                cpuset: *mut RawBitmap,
                efficiency: *mut c_int,
                nr_infos: *mut c_uint,
                infos: *mut *mut TextualInfo,
                flags: c_ulong,
            ) -> c_int;
            #[must_use]
            pub(crate) fn hwloc_cpukinds_register(
                topology: *mut RawTopology,
                cpuset: *const RawBitmap,
                forced_efficiency: c_int,
                nr_infos: c_uint,
                infos: *const TextualInfo,
                flags: c_ulong,
            ) -> c_int;

            // === Linux-specific helpers: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__linux.html

            #[cfg(target_os = "linux")]
            #[must_use]
            pub(crate) fn hwloc_linux_set_tid_cpubind(
                topology: *const RawTopology,
                tid: pid_t,
                set: *const RawBitmap,
            ) -> c_int;
            #[cfg(target_os = "linux")]
            #[must_use]
            pub(crate) fn hwloc_linux_get_tid_cpubind(
                topology: *const RawTopology,
                tid: pid_t,
                set: *mut RawBitmap,
            ) -> c_int;
            #[cfg(target_os = "linux")]
            #[must_use]
            pub(crate) fn hwloc_linux_get_tid_last_cpu_location(
                topology: *const RawTopology,
                tid: pid_t,
                set: *mut RawBitmap,
            ) -> c_int;
            #[cfg(target_os = "linux")]
            #[must_use]
            pub(crate) fn hwloc_linux_read_path_as_cpumask(
                path: *const c_char,
                set: *const RawBitmap,
            ) -> c_int;

            // NOTE: libnuma interop is waiting for higher quality libnuma bindings

            // === Windows-specific helpers: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__windows.html

            #[cfg(target_os = "windows")]
            #[must_use]
            pub(crate) fn hwloc_windows_get_nr_processor_groups(
                topology: *const RawTopology,
                flags: c_ulong,
            ) -> c_int;
            #[cfg(target_os = "windows")]
            #[must_use]
            pub(crate) fn hwloc_windows_get_processor_group_cpuset(
                topology: *const RawTopology,
                pg_index: c_uint,
                cpuset: *mut RawBitmap,
                flags: c_ulong,
            ) -> c_int;

            // NOTE: glibc interop is waiting for higher quality cpuset support
            //       in the libc crate: right now, it is not possible to safely
            //       crate a `cpu_set_t`, but functions that manipulate them
            //       expect `&mut cpu_set_t`...

            // === TODO: Other APIs

            // TODO: Cover more later: interop, differences, sharing, etc...
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
