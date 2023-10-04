#![allow(non_camel_case_types, unknown_lints)]
#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg, doc_cfg_hide))]
#![cfg_attr(docsrs, doc(cfg_hide(doc)))]
// Last allow-by-default lint review performed as of Rust 1.72
#![deny(
    clippy::as_ptr_cast_mut,
    clippy::as_underscore,
    clippy::assertions_on_result_states,
    clippy::bool_to_int_with_if,
    clippy::borrow_as_ptr,
    clippy::branches_sharing_code,
    clippy::cargo_common_metadata,
    clippy::case_sensitive_file_extension_comparisons,
    clippy::cast_lossless,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_precision_loss,
    clippy::cast_ptr_alignment,
    clippy::cast_sign_loss,
    clippy::checked_conversions,
    clippy::clear_with_drain,
    clippy::clone_on_ref_ptr,
    clippy::cloned_instead_of_copied,
    clippy::cognitive_complexity,
    clippy::collection_is_never_read,
    clippy::create_dir,
    clippy::debug_assert_with_mut_call,
    clippy::decimal_literal_representation,
    clippy::derive_partial_eq_without_eq,
    clippy::doc_link_with_quotes,
    clippy::doc_markdown,
    clippy::empty_drop,
    clippy::empty_enum,
    clippy::empty_line_after_doc_comments,
    clippy::empty_line_after_outer_attr,
    clippy::empty_structs_with_brackets,
    clippy::enum_glob_use,
    clippy::equatable_if_let,
    clippy::exit,
    clippy::expl_impl_clone_on_copy,
    clippy::explicit_deref_methods,
    clippy::explicit_into_iter_loop,
    clippy::explicit_iter_loop,
    clippy::fallible_impl_from,
    clippy::filter_map_next,
    clippy::flat_map_option,
    clippy::float_cmp,
    clippy::float_cmp_const,
    clippy::fn_to_numeric_cast_any,
    clippy::format_push_string,
    clippy::from_iter_instead_of_collect,
    clippy::get_unwrap,
    clippy::if_not_else,
    clippy::if_then_some_else_none,
    clippy::implicit_clone,
    clippy::implicit_hasher,
    clippy::imprecise_flops,
    clippy::index_refutable_slice,
    clippy::inline_always,
    clippy::invalid_upcast_comparisons,
    clippy::iter_not_returning_iterator,
    clippy::iter_on_empty_collections,
    clippy::iter_on_single_items,
    clippy::iter_with_drain,
    clippy::large_digit_groups,
    clippy::large_stack_arrays,
    clippy::large_types_passed_by_value,
    clippy::linkedlist,
    clippy::macro_use_imports,
    clippy::manual_assert,
    clippy::manual_clamp,
    clippy::manual_instant_elapsed,
    clippy::manual_let_else,
    clippy::manual_ok_or,
    clippy::manual_string_new,
    clippy::many_single_char_names,
    clippy::map_unwrap_or,
    clippy::match_bool,
    clippy::match_same_arms,
    clippy::match_wildcard_for_single_variants,
    clippy::mismatching_type_param_order,
    clippy::missing_assert_message,
    clippy::missing_docs_in_private_items,
    clippy::missing_errors_doc,
    clippy::missing_fields_in_debug,
    clippy::mixed_read_write_in_expression,
    clippy::mut_mut,
    clippy::mutex_atomic,
    clippy::mutex_integer,
    clippy::naive_bytecount,
    clippy::needless_collect,
    clippy::needless_continue,
    clippy::needless_for_each,
    clippy::negative_feature_names,
    clippy::no_mangle_with_rust_abi,
    clippy::non_send_fields_in_send_ty,
    clippy::nonstandard_macro_braces,
    clippy::option_if_let_else,
    clippy::option_option,
    clippy::or_fun_call,
    clippy::partial_pub_fields,
    clippy::path_buf_push_overwrite,
    clippy::print_stderr,
    clippy::print_stdout,
    clippy::ptr_as_ptr,
    clippy::ptr_cast_constness,
    clippy::pub_without_shorthand,
    clippy::range_minus_one,
    clippy::range_plus_one,
    clippy::rc_buffer,
    clippy::rc_mutex,
    clippy::redundant_clone,
    clippy::redundant_closure_for_method_calls,
    clippy::redundant_feature_names,
    clippy::ref_option_ref,
    clippy::ref_patterns,
    clippy::rest_pat_in_fully_bound_structs,
    clippy::same_functions_in_if_condition,
    clippy::self_named_module_files,
    clippy::semicolon_inside_block,
    clippy::semicolon_outside_block,
    clippy::significant_drop_in_scrutinee,
    clippy::similar_names,
    clippy::single_match_else,
    clippy::str_to_string,
    clippy::string_add,
    clippy::string_lit_as_bytes,
    clippy::string_to_string,
    clippy::suboptimal_flops,
    clippy::suspicious_operation_groupings,
    clippy::tests_outside_test_module,
    clippy::todo,
    clippy::too_many_lines,
    clippy::trailing_empty_array,
    clippy::transmute_ptr_to_ptr,
    clippy::trivial_regex,
    clippy::trivially_copy_pass_by_ref,
    clippy::try_err,
    clippy::type_repetition_in_bounds,
    clippy::undocumented_unsafe_blocks,
    clippy::unicode_not_nfc,
    clippy::unimplemented,
    clippy::uninlined_format_args,
    clippy::unnecessary_box_returns,
    clippy::unnecessary_join,
    clippy::unnecessary_safety_comment,
    clippy::unnecessary_safety_doc,
    clippy::unnecessary_self_imports,
    clippy::unnecessary_struct_initialization,
    clippy::unnecessary_wraps,
    clippy::unneeded_field_pattern,
    clippy::unnested_or_patterns,
    clippy::unreadable_literal,
    clippy::unsafe_derive_deserialize,
    clippy::unused_async,
    clippy::unused_peekable,
    clippy::unused_rounding,
    clippy::unwrap_used,
    clippy::use_debug,
    clippy::use_self,
    clippy::used_underscore_binding,
    clippy::useless_let_if_seq,
    clippy::verbose_bit_mask,
    clippy::verbose_file_reads,
    clippy::wildcard_dependencies,
    clippy::wildcard_enum_match_arm,
    clippy::wildcard_imports,
    clippy::zero_sized_map_values,
    invalid_reference_casting,
    macro_use_extern_crate,
    missing_abi,
    missing_copy_implementations,
    missing_debug_implementations,
    // FIXME: Bring back missing_docs,
    non_ascii_idents,
    pointer_structural_match,
    rust_2018_compatibility,
    rust_2021_compatibility,
    rustdoc::bare_urls,
    rustdoc::broken_intra_doc_links,
    rustdoc::invalid_codeblock_attributes,
    rustdoc::invalid_html_tags,
    rustdoc::invalid_rust_codeblocks,
    rustdoc::missing_crate_level_docs,
    rustdoc::private_intra_doc_links,
    rustdoc::unescaped_backticks,
    trivial_casts,
    trivial_numeric_casts,
    unreachable_pub,
    unsafe_op_in_unsafe_fn,
    variant_size_differences
)]
#![warn(
    clippy::dbg_macro,
    future_incompatible,
    keyword_idents,
    let_underscore,
    meta_variable_misuse,
    noop_method_call,
    rust_2018_idioms,
    unused
)]
#![doc = include_str!("../README.md")]

#[cfg(target_os = "linux")]
use libc::pid_t;
use std::{
    ffi::{c_char, c_float, c_int, c_uchar, c_uint, c_ulong, c_ushort, c_void},
    fmt::Debug,
    marker::{PhantomData, PhantomPinned},
    ptr,
};

// === Things which are not part of the main hwloc documentation

/// pid_t placeholder for rustdoc
#[cfg(all(doc, not(target_os = "linux")))]
pub type pid_t = c_int;

/// Rust model of a C incomplete type (struct declaration without a definition)
///
/// From <https://doc.rust-lang.org/nomicon/ffi.html#representing-opaque-structs>
///
/// This type purposely implements no traits, not even Debug, because you should
/// never, ever deal with it directly, only with raw pointers to it that you
/// blindly pass to the hwloc API.
#[repr(C)]
struct IncompleteType {
    /// Stolen from
    /// <https://doc.rust-lang.org/nomicon/ffi.html#representing-opaque-structs>
    ///
    /// No idea why the original author thought the `_marker` field is not
    /// sufficient, but the authors of this book tend to be more well-versed
    /// into compiler black magic than I do, so let's keep it that way...
    _data: [u8; 0],

    /// Ensures `Send`, `Sync` and `Unpin` are not implemented
    _marker: PhantomData<(*mut u8, PhantomPinned)>,
}

/// Thread identifier (OS-specific)
///
/// This is `HANDLE` on Windows and `libc::pthread_t` on all other platforms.
#[cfg(target_os = "windows")]
#[cfg_attr(docsrs, doc(cfg(all())))]
pub type hwloc_thread_t = windows_sys::Win32::Foundation::HANDLE;

/// Process identifier (OS-specific)
///
/// This is `u32` on Windows and `libc::pid_t` on all other platforms.
#[cfg(target_os = "windows")]
#[cfg_attr(docsrs, doc(cfg(all())))]
pub type hwloc_pid_t = u32;

/// Thread identifier (OS-specific)
///
/// This is `HANDLE` on Windows and `libc::pthread_t` on all other platforms.
#[cfg(not(target_os = "windows"))]
#[cfg_attr(docsrs, doc(cfg(all())))]
pub type hwloc_thread_t = libc::pthread_t;

/// Process identifier (OS-specific)
///
/// This is `u32` on Windows and `libc::pid_t` on all other platforms.
#[cfg(not(target_os = "windows"))]
#[cfg_attr(docsrs, doc(cfg(all())))]
pub type hwloc_pid_t = libc::pid_t;

// === Object Sets: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__object__sets.html

/// A non-modifiable [`hwloc_cpuset_t`]
pub type hwloc_const_cpuset_t = hwloc_const_bitmap_t;

/// A non-modifiable [`hwloc_nodeset_t`]
pub type hwloc_const_nodeset_t = hwloc_const_bitmap_t;

/// A CPU set is a bitmap whose bits are set according to CPU physical OS indexes
///
/// It may be consulted and modified with the bitmap API as any [`hwloc_bitmap_t`].
pub type hwloc_cpuset_t = hwloc_bitmap_t;

/// A node set is a bitmap whose bits are set according to NUMA memory node
/// physical OS indexes
///
/// It may be consulted and modified with the bitmap API as any
/// [`hwloc_bitmap_t`].
///
/// When binding memory on a system without any NUMA node, the single main
/// memory bank is considered as NUMA node `#0`.
///
/// See also [Converting between CPU sets and node
/// sets](https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__nodeset__convert.html).
pub type hwloc_nodeset_t = hwloc_bitmap_t;

// === Object Types: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__object__types.html

/// Value returned by [`hwloc_compare_types()`] when types can not be compared
pub const HWLOC_TYPE_UNORDERED: c_int = c_int::MAX;

/// Type of one side (upstream or downstream) of an I/O bridge
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
#[doc(alias = "hwloc_obj_bridge_type_e")]
pub type hwloc_obj_bridge_type_t = c_uint;

/// Host-side of a bridge, only possible upstream
pub const HWLOC_OBJ_BRIDGE_HOST: hwloc_obj_bridge_type_t = 0;

/// PCI-side of a bridge
pub const HWLOC_OBJ_BRIDGE_PCI: hwloc_obj_bridge_type_t = 1;

/// Cache type
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
#[doc(alias = "hwloc_obj_cache_type_e")]
pub type hwloc_obj_cache_type_t = c_uint;

/// Unified cache
pub const HWLOC_OBJ_CACHE_UNIFIED: hwloc_obj_cache_type_t = 0;

/// Data cache
pub const HWLOC_OBJ_CACHE_DATA: hwloc_obj_cache_type_t = 1;

/// Instruction cache (filtered out by default)
pub const HWLOC_OBJ_CACHE_INSTRUCTION: hwloc_obj_cache_type_t = 2;

/// Type of a OS device
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
#[doc(alias = "hwloc_obj_osdev_type_e")]
pub type hwloc_obj_osdev_type_t = c_uint;

/// Operating system storage device (e.g. block)
///
/// For instance "sda" or "dax2.0" on Linux.
#[doc(alias = "HWLOC_OBJ_OSDEV_BLOCK")]
pub const HWLOC_OBJ_OSDEV_STORAGE: hwloc_obj_osdev_type_t = 0;

/// Operating system GPU device
///
/// For instance ":0.0" for a GL display, "card0" for a Linux DRM device.
pub const HWLOC_OBJ_OSDEV_GPU: hwloc_obj_osdev_type_t = 1;

/// Operating system network device
///
/// For instance the "eth0" interface on Linux.
pub const HWLOC_OBJ_OSDEV_NETWORK: hwloc_obj_osdev_type_t = 2;

#[allow(clippy::doc_markdown)]
/// Operating system openfabrics device
///
/// For instance the "mlx4_0" InfiniBand HCA, "hfi1_0" Omni-Path interface,
/// or "bxi0" Atos/Bull BXI HCA on Linux.
pub const HWLOC_OBJ_OSDEV_OPENFABRICS: hwloc_obj_osdev_type_t = 3;

#[allow(clippy::doc_markdown)]
/// Operating system dma engine device
///
/// For instance the "dma0chan0" DMA channel on Linux.
pub const HWLOC_OBJ_OSDEV_DMA: hwloc_obj_osdev_type_t = 4;

#[allow(clippy::doc_markdown)]
/// Operating system co-processor device
///
/// For instance "opencl0d0" for a OpenCL device, "cuda0" for a CUDA device.
pub const HWLOC_OBJ_OSDEV_COPROC: hwloc_obj_osdev_type_t = 5;

#[allow(clippy::doc_markdown)]
/// Operating system memory device
///
/// For instance DAX file for non-volatile or high-bandwidth memory, like
/// "dax2.0" on Linux.
#[cfg(feature = "hwloc-3_0_0")]
pub const HWLOC_OBJ_OSDEV_MEMORY: hwloc_obj_osdev_type_t = 6;

/// Type of topology object
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
#[doc(alias = "hwloc_obj_type_e")]
pub type hwloc_obj_type_t = c_uint;

/// The root object, a set of processors and memory with cache coherency
///
/// This type is always used for the root object of a topology, and never
/// used anywhere else. Hence it never has a parent.
pub const HWLOC_OBJ_MACHINE: hwloc_obj_type_t = 0;

/// Physical package, what goes into a physical motherboard socket
///
/// Usually contains multiple cores, and possibly some dies.
pub const HWLOC_OBJ_PACKAGE: hwloc_obj_type_t = 1;

/// A computation unit (may be shared by several PUs aka logical processors)
pub const HWLOC_OBJ_CORE: hwloc_obj_type_t = 2;

/// Processing Unit, or (Logical) Processor
///
/// An execution unit (may share a core with some other logical
/// processors, e.g. in the case of an SMT core).
///
/// This is the leaf of the CPU resource hierarchy, it can only have Misc
/// children.
///
/// It is always reported even when other objects are not detected. However,
/// an incorrect number of PUs may be reported if
/// [`hwloc_topology_discovery_support::pu`] is not set.
pub const HWLOC_OBJ_PU: hwloc_obj_type_t = 3;

/// Level 1 Data (or Unified) Cache
pub const HWLOC_OBJ_L1CACHE: hwloc_obj_type_t = 4;

/// Level 2 Data (or Unified) Cache
pub const HWLOC_OBJ_L2CACHE: hwloc_obj_type_t = 5;

/// Level 3 Data (or Unified) Cache
pub const HWLOC_OBJ_L3CACHE: hwloc_obj_type_t = 6;

/// Level 4 Data (or Unified) Cache
pub const HWLOC_OBJ_L4CACHE: hwloc_obj_type_t = 7;

/// Level 5 Data (or Unified) Cache
// NOTE: If hwloc adds more cache levels, update the hwlocality::cache module accordingly
pub const HWLOC_OBJ_L5CACHE: hwloc_obj_type_t = 8;

/// Level 1 Instruction cache (filtered out by default)
pub const HWLOC_OBJ_L1ICACHE: hwloc_obj_type_t = 9;

/// Level 2 Instruction cache (filtered out by default)
pub const HWLOC_OBJ_L2ICACHE: hwloc_obj_type_t = 10;

/// Level 3 Instruction cache (filtered out by default)
pub const HWLOC_OBJ_L3ICACHE: hwloc_obj_type_t = 11;

/// Group object
///
/// Objects which do not fit in the above but are detected by hwloc and
/// are useful to take into account for affinity. For instance, some
/// operating systems expose their arbitrary processors aggregation this
/// way. And hwloc may insert such objects to group NUMA nodes according
/// to their distances. See also [What are these Group objects in my
/// topology?](https://hwloc.readthedocs.io/en/v2.9/faq.html#faq_groups).
///
/// These objects are ignored when they do not bring any structure (see
/// [`HWLOC_TYPE_FILTER_KEEP_STRUCTURE`])
pub const HWLOC_OBJ_GROUP: hwloc_obj_type_t = 12;

/// NUMA node
///
/// An object that contains memory that is directly and byte-accessible to
/// the host processors. It is usually close to some cores
/// (the corresponding objects are descendants of the NUMA node object in
/// the hwloc tree).
///
/// This is the smallest object representing Memory resources, it cannot
/// have any child except Misc objects. However it may have Memory-side
/// cache parents.
///
/// There is always at least one such object in the topology even if the machine
/// is not NUMA. However, an incorrect number of NUMA nodes may be reported if
/// [`hwloc_topology_discovery_support::numa`] is not set.
///
/// Memory objects are not listed in the main children list, but rather in the
/// dedicated Memory children list. They also have a special depth
/// [`HWLOC_TYPE_DEPTH_NUMANODE`] instead of a normal depth just like other
/// objects in the main tree.
pub const HWLOC_OBJ_NUMANODE: hwloc_obj_type_t = 13;

/// Bridge (filtered out by default)
///
/// Any bridge that connects the host or an I/O bus, to another I/O bus.
///
/// Bridges are not added to the topology unless their filtering is changed
/// (see [`hwloc_topology_set_type_filter()`] and
/// [`hwloc_topology_set_io_types_filter()`]).
///
/// I/O objects are not listed in the main children list, but rather in the
/// dedicated Memory children list. They have NULL CPU and node sets. They
/// also have a special depth [`HWLOC_TYPE_DEPTH_BRIDGE`] instead of a normal
/// depth just like other objects in the main tree.
pub const HWLOC_OBJ_BRIDGE: hwloc_obj_type_t = 14;

/// PCI device (filtered out by default)
///
/// PCI devices are not added to the topology unless their filtering is
/// changed (see [`hwloc_topology_set_type_filter()`] and
/// [`hwloc_topology_set_io_types_filter()`]).
///
/// I/O objects are not listed in the main children list, but rather in the
/// dedicated I/O children list. They have NULL CPU and node sets. They also
/// have a special depth [`HWLOC_TYPE_DEPTH_PCI_DEVICE`] instead of a normal
/// depth just like other objects in the main tree.
pub const HWLOC_OBJ_PCI_DEVICE: hwloc_obj_type_t = 15;

/// Operating system device (filtered out by default)
///
/// OS devices are not added to the topology unless their filtering is
/// changed (see [`hwloc_topology_set_type_filter()`] and
/// [`hwloc_topology_set_io_types_filter()`]).
///
/// I/O objects are not listed in the main children list, but rather in the
/// dedicated I/O children list. They have NULL CPU and node sets. They also
/// have a special depth [`HWLOC_TYPE_DEPTH_OS_DEVICE`] instead of a normal
/// depth just like other objects in the main tree.
pub const HWLOC_OBJ_OS_DEVICE: hwloc_obj_type_t = 16;

/// Miscellaneous object (filtered out by default)
///
/// Objects without particular meaning, that can e.g. be added by the
/// application for its own use, or by hwloc for miscellaneous objects such
/// as memory modules (DIMMs).
///
/// They are not added to the topology unless their filtering is
/// changed (see [`hwloc_topology_set_type_filter()`]).
///
/// Misc objects have no CPU and node sets, and may only have other Misc objects
/// as children. They are not part of the main children list, but rather reside
/// in the dedicated Misc children list. They have NULL CPU and node sets.
/// They also have a special depth [`HWLOC_TYPE_DEPTH_MISC`] instead of a normal
/// depth just like other objects in the main tree.
pub const HWLOC_OBJ_MISC: hwloc_obj_type_t = 17;

/// Memory-side cache (filtered out by default)
///
/// A cache in front of a specific NUMA node. This object always has at
/// least one NUMA node as a memory child.
///
/// Memory objects are not listed in the main children list, but rather in
/// the dedicated Memory children list. They also have a special depth
/// [`HWLOC_TYPE_DEPTH_MEMCACHE`] instead of a normal depth just like other
/// objects in the main tree.
#[cfg(feature = "hwloc-2_1_0")]
pub const HWLOC_OBJ_MEMCACHE: hwloc_obj_type_t = 18;

/// Die within a physical package
///
/// A subpart of the physical package, that contains multiple cores.
#[cfg(feature = "hwloc-2_1_0")]
pub const HWLOC_OBJ_DIE: hwloc_obj_type_t = 19;

// === Object Structure and Attributes: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__objects.html

/// Hardware topology object
#[derive(Debug)]
#[repr(C)]
pub struct hwloc_obj {
    /// Type of object
    #[doc(alias = "hwloc_obj::type")]
    pub ty: hwloc_obj_type_t,

    /// Subtype string to better describe the type field
    ///
    /// See <https://hwloc.readthedocs.io/en/v2.9/attributes.html#attributes_normal>
    /// for a list of subtype strings that hwloc can emit.
    pub subtype: *mut c_char,

    /// The OS-provided physical index number
    ///
    /// It is not guaranteed unique across the entire machine,
    /// except for PUs and NUMA nodes.
    ///
    /// Set to [`HWLOC_UNKNOWN_INDEX`] if unknown or irrelevant for this object.
    pub os_index: c_uint,

    /// Object-specific name, if any
    ///
    /// Mostly used for identifying OS devices and Misc objects where a name
    /// string is more useful than numerical indices.
    pub name: *mut c_char,

    /// Total memory (in bytes) in NUMA nodes below this object
    ///
    /// May not be accurate if
    /// [`hwloc_topology_discovery_support::numa_memory`] is not set.
    pub total_memory: u64,

    /// Object type-specific attributes, if any
    pub attr: *mut hwloc_obj_attr_u,

    /// Vertical index in the hierarchy
    ///
    /// For normal objects, this is the depth of the horizontal level that
    /// contains this object and its cousins of the same type. If the topology
    /// is symmetric, this is equal to the parent depth plus one, and also equal
    /// to the number of parent/child links from the root object to here.
    ///
    /// For special objects (NUMA nodes, I/O and Misc) that are not in the main
    /// tree, this is a special value that is unique to their type.
    pub depth: hwloc_get_type_depth_e,

    /// Horizontal index in the whole list of similar objects, hence guaranteed
    /// unique across the entire machine
    ///
    /// Could be a "cousin_rank" since it's the rank within the "cousin" list.
    ///
    /// Note that this index may change when restricting the topology
    /// or when inserting a group.
    pub logical_index: c_uint,

    /// Next object of same type and depth
    pub next_cousin: hwloc_obj_t,

    /// Previous object of same type and depth
    pub prev_cousin: hwloc_obj_t,

    /// Parent object
    ///
    /// Only NULL for the root [`HWLOC_OBJ_MACHINE`] object.
    pub parent: hwloc_obj_t,

    /// Index in the parent's relevant child list for this object type
    pub sibling_rank: c_uint,

    /// Next object below the same parent, in the same child list
    pub next_sibling: hwloc_obj_t,

    /// Previous object below the same parent, in the same child list
    pub prev_sibling: hwloc_obj_t,

    /// Number of normal children (excluding Memory, Misc and I/O)
    pub arity: c_uint,

    /// Normal children of this object
    pub children: *mut hwloc_obj_t,

    /// First normal child of this object
    pub first_child: hwloc_obj_t,

    /// Last normal child of this object
    pub last_child: hwloc_obj_t,

    /// Truth that this object is symmetric, which means all normal children and
    /// their children have identical subtrees
    ///
    /// Memory, I/O and Misc children are ignored.
    ///
    /// If this is true of the root object, then the topology may be exported
    /// as a synthetic string.
    pub symmetric_subtree: c_int,

    /// Number of memory children
    pub memory_arity: c_uint,

    /// First memory child of this object
    ///
    /// NUMA nodes and Memory-side caches are listed here instead of in the
    /// normal [`children`] list. See also [`hwloc_obj_type_is_memory()`].
    ///
    /// A memory hierarchy starts from a normal CPU-side object (e.g.
    /// [`HWLOC_OBJ_PACKAGE`]) and ends with NUMA nodes as leaves. There might
    /// exist some memory-side caches between them in the middle of the memory
    /// subtree.
    ///
    /// [`children`]: Self::children
    pub memory_first_child: hwloc_obj_t,

    /// Number of I/O children
    pub io_arity: c_uint,

    /// First I/O child of this object
    ///
    /// Bridges, PCI and OS devices are listed here instead of in the normal
    /// [`children`] list. See also [`hwloc_obj_type_is_io()`].
    ///
    /// [`children`]: Self::children
    pub io_first_child: hwloc_obj_t,

    /// Number of Misc children
    pub misc_arity: c_uint,

    /// First Misc child of this object
    ///
    /// Misc objects are listed here instead of in the normal [`children`] list.
    ///
    /// [`children`]: Self::children
    pub misc_first_child: hwloc_obj_t,

    /// CPUs covered by this object
    ///
    /// This is the set of CPUs for which there are PU objects in the
    /// topology under this object, i.e. which are known to be physically
    /// contained in this object and known how (the children path between this
    /// object and the PU objects).
    ///
    /// If the [`HWLOC_TOPOLOGY_FLAG_INCLUDE_DISALLOWED`] topology building
    /// configuration flag is set, some of these CPUs may be online but not
    /// allowed for binding, see [`hwloc_topology_get_allowed_cpuset()`].
    ///
    /// All objects have CPU and node sets except Misc and I/O objects, so if
    /// you know this object to be a normal or Memory object, you can safely
    /// assume this pointer to be non-NULL.
    pub cpuset: hwloc_cpuset_t,

    /// The complete CPU set of this object
    ///
    /// To the CPUs listed by [`cpuset`], this adds CPUs for which topology
    /// information is unknown or incomplete, some offline CPUs, and CPUs that
    /// are ignored when the [`HWLOC_TOPOLOGY_FLAG_INCLUDE_DISALLOWED`] topology
    /// building configuration flag is not set.
    ///
    /// Thus no corresponding PU object may be found in the topology, because
    /// the precise position is undefined. It is however known that it would be
    /// somewhere under this object.
    ///
    /// [`cpuset`]: Self::cpuset
    pub complete_cpuset: hwloc_cpuset_t,

    /// NUMA nodes covered by this object or containing this object.
    ///
    /// This is the set of NUMA nodes for which there are NUMA node objects in
    /// the topology under or above this object, i.e. which are known to be
    /// physically contained in this object or containing it and known how
    /// (the children path between this object and the NUMA node objects). In
    /// the end, these nodes are those that are close to the current object.
    ///
    #[cfg_attr(
        feature = "hwloc-2_3_0",
        doc = "With hwloc 2.3+, [`hwloc_get_local_numanode_objs()`] may be used to"
    )]
    #[cfg_attr(feature = "hwloc-2_3_0", doc = "list those NUMA nodes more precisely.")]
    ///
    /// If the [`HWLOC_TOPOLOGY_FLAG_INCLUDE_DISALLOWED`] topology building
    /// configuration flag is set, some of these nodes may not be allowed for
    /// allocation, see [`hwloc_topology_get_allowed_nodeset()`].
    ///
    /// If there are no NUMA nodes in the machine, all the memory is close to
    /// this object, so the nodeset is full.
    ///
    /// All objects have CPU and node sets except Misc and I/O objects, so if
    /// you know this object to be a normal or Memory object, you can safely
    /// assume this pointer to be non-NULL.
    pub nodeset: hwloc_nodeset_t,

    /// The complete NUMA node set of this object
    ///
    /// To the nodes listed by [`nodeset`], this adds nodes for which topology
    /// information is unknown or incomplete, some offline nodes, and nodes
    /// that are ignored when the
    /// [`HWLOC_TOPOLOGY_FLAG_INCLUDE_DISALLOWED`] topology building
    /// configuration flag is not set.
    ///
    /// Thus no corresponding NUMANode object may be found in the topology,
    /// because the precise position is undefined. It is however known that it
    /// would be somewhere under this object.
    ///
    /// If there are no NUMA nodes in the machine, all the memory is close to
    /// this object, so complete_nodeset is full.
    ///
    /// [`nodeset`]: Self::nodeset
    pub complete_nodeset: hwloc_nodeset_t,

    /// Complete list of (key, value) textual info pairs
    ///
    /// hwloc defines [a number of standard object info attribute names with
    /// associated semantics](https://hwloc.readthedocs.io/en/v2.9/attributes.html#attributes_info).
    ///
    /// Beware that hwloc allows multiple informations with the same key to
    /// exist, although no sane programs should leverage this possibility.
    pub infos: *mut hwloc_info_s,

    /// Number of (key, value) pairs in [`infos`]
    ///
    /// [`infos`]: Self::infos
    pub infos_count: c_uint,

    /// Application-given private data pointer, initialized to NULL, use it as
    /// you wish
    //
    // TODO: Add once support is ready: "See
    // [`hwloc_topology_set_userdata_export_callback()`] if you wish to export
    // this field to XML."
    pub userdata: *mut c_void,

    /// Global persistent index
    ///
    /// Generated by hwloc, unique across the topology (contrary to
    /// [`os_index`]) and persistent across topology changes (contrary to
    /// [`logical_index`]).
    ///
    /// All this means you can safely use this index as a cheap key representing
    /// the object in a Set or a Map, as long as that Set or Map only refers to
    /// [`hwloc_obj`]s originating from a single [`hwloc_topology`].
    ///
    /// [`logical_index`]: Self::logical_index
    /// [`os_index`]: Self::os_index
    pub gp_index: u64,
}

/// Value of [`hwloc_obj::os_index`] when unknown or irrelevant for this object
pub const HWLOC_UNKNOWN_INDEX: c_uint = c_uint::MAX;

/// Convenience typedef, a pointer to a struct [`hwloc_obj`]
pub type hwloc_obj_t = *mut hwloc_obj;

/// [`hwloc_obj_type_t`]-specific attributes
#[derive(Copy, Clone)]
#[repr(C)]
pub union hwloc_obj_attr_u {
    /// [`HWLOC_OBJ_NUMANODE`]-specific attributes
    pub numa: hwloc_numanode_attr_s,

    /// Cache-specific attributes
    pub cache: hwloc_cache_attr_s,

    /// [`HWLOC_OBJ_GROUP`]-specific attributes
    pub group: hwloc_group_attr_s,

    /// [`HWLOC_OBJ_PCI_DEVICE`]-specific attributes
    pub pcidev: hwloc_pcidev_attr_s,

    /// [`HWLOC_OBJ_BRIDGE`]-specific attributes
    pub bridge: hwloc_bridge_attr_s,

    /// [`HWLOC_OBJ_OS_DEVICE`]-specific attributes
    pub osdev: hwloc_osdev_attr_s,
}
//
impl Debug for hwloc_obj_attr_u {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("hwloc_obj_attr_u").finish_non_exhaustive()
    }
}

/// [`HWLOC_OBJ_NUMANODE`]-specific attributes
#[derive(Copy, Clone, Debug)]
#[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s")]
#[repr(C)]
pub struct hwloc_numanode_attr_s {
    /// Local memory in bytes
    ///
    /// May not be accurate if
    /// [`hwloc_topology_discovery_support::numa_memory`] is not set.
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::local_memory")]
    pub local_memory: u64,

    /// Number of memory page types
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::page_types_len")]
    pub page_types_len: c_uint,

    /// Memory page types, sorted by increasing page size
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::page_types")]
    pub page_types: *mut hwloc_memory_page_type_s,
}
//
impl Default for hwloc_numanode_attr_s {
    fn default() -> Self {
        Self {
            local_memory: 0,
            page_types_len: 0,
            page_types: std::ptr::null_mut(),
        }
    }
}

/// Local memory page type
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_numanode_attr_s::hwloc_memory_page_type_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::hwloc_memory_page_type_s")]
#[repr(C)]
pub struct hwloc_memory_page_type_s {
    /// Size of pages
    #[doc(alias = "hwloc_numanode_attr_s::hwloc_memory_page_type_s::size")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::hwloc_memory_page_type_s::size")]
    pub size: u64,

    /// Number of pages of this size
    #[doc(alias = "hwloc_numanode_attr_s::hwloc_memory_page_type_s::count")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::hwloc_memory_page_type_s::count")]
    pub count: u64,
}

/// Cache-specific attributes
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s")]
#[repr(C)]
pub struct hwloc_cache_attr_s {
    /// Size of the cache in bytes
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::size")]
    pub size: u64,

    /// Depth ofthe cache (e.g. L1, L2, ...)
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::depth")]
    pub depth: c_uint,

    /// Cache line size in bytes
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::linesize")]
    pub linesize: c_uint,

    /// Ways of associativity, -1 if fully associative, 0 if unknown
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::associativity")]
    pub associativity: c_int,

    /// Cache type
    #[doc(alias = "hwloc_cache_attr_s::type")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_cache_attr_s::type")]
    pub ty: hwloc_obj_cache_type_t,
}

/// [`HWLOC_OBJ_GROUP`]-specific attributes
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_obj_attr_u::hwloc_group_attr_s")]
#[repr(C)]
pub struct hwloc_group_attr_s {
    /// Depth of group object
    ///
    /// It may change if intermediate Group objects are added.
    #[doc(alias = "hwloc_obj_attr_u::hwloc_group_attr_s::depth")]
    pub depth: c_uint,

    /// Internally-used kind of group
    #[doc(alias = "hwloc_obj_attr_u::hwloc_group_attr_s::kind")]
    pub kind: c_uint,

    /// Internally-used subkind to distinguish different levels of groups with
    /// the same kind
    #[doc(alias = "hwloc_obj_attr_u::hwloc_group_attr_s::subkind")]
    pub subkind: c_uint,

    /// Flag preventing groups from being automatically merged with identical
    /// parent or children
    #[cfg(feature = "hwloc-2_0_4")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_group_attr_s::dont_merge")]
    pub dont_merge: c_uchar,
}

/// PCI domain width (depends on hwloc version)
#[cfg(feature = "hwloc-3_0_0")]
#[cfg_attr(docsrs, doc(cfg(all())))]
pub type PCIDomain = u32;

/// PCI domain width (depends on hwloc version)
#[cfg(not(feature = "hwloc-3_0_0"))]
#[cfg_attr(docsrs, doc(cfg(all())))]
pub type PCIDomain = u16;

/// [`HWLOC_OBJ_PCI_DEVICE`]-specific attributes
#[derive(Copy, Clone, Debug, Default, PartialEq)]
#[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s")]
#[repr(C)]
pub struct hwloc_pcidev_attr_s {
    /// PCI domain
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::domain")]
    pub domain: PCIDomain,

    /// PCI bus id
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::bus")]
    pub bus: c_uchar,

    /// PCI bus device
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::dev")]
    pub dev: c_uchar,

    /// PCI function
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::func")]
    pub func: c_uchar,

    /// PCI class ID
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::class_id")]
    pub class_id: c_ushort,

    /// PCI vendor ID
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::vendor_id")]
    pub vendor_id: c_ushort,

    /// PCI device ID
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::device_id")]
    pub device_id: c_ushort,

    /// PCI sub-vendor ID
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::subvendor_id")]
    pub subvendor_id: c_ushort,

    /// PCI sub-device ID
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::subdevice_id")]
    pub subdevice_id: c_ushort,

    /// PCI revision
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::revision")]
    pub revision: c_uchar,

    /// Link speed in GB/s
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::linkspeed")]
    pub linkspeed: c_float,
}

/// [`HWLOC_OBJ_BRIDGE`]-specific attributes
#[derive(Copy, Clone, Debug)]
#[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s")]
#[repr(C)]
pub struct hwloc_bridge_attr_s {
    /// Upstream attributes
    #[doc(alias = "hwloc_bridge_attr_s::upstream")]
    pub upstream: RawUpstreamAttributes,

    /// Upstream type
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::upstream_type")]
    pub upstream_type: hwloc_obj_bridge_type_t,

    /// Downstream attributes
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::downstream")]
    pub downstream: RawDownstreamAttributes,

    /// Downstream type
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::downstream_type")]
    pub downstream_type: hwloc_obj_bridge_type_t,

    /// Bridge depth
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::depth")]
    pub depth: c_uint,
}

/// Upstream device attributes
#[derive(Copy, Clone)]
#[repr(C)]
pub union RawUpstreamAttributes {
    /// PCI-specific attributes
    pub pci: hwloc_pcidev_attr_s,
}
//
impl Debug for RawUpstreamAttributes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RawUpstreamAttributes")
            .finish_non_exhaustive()
    }
}

/// Downstream PCI device attributes
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[repr(C)]
pub struct RawDownstreamPCIAttributes {
    /// Downstram domain
    pub domain: PCIDomain,

    /// Downstream secondary bus
    pub secondary_bus: c_uchar,

    /// Downstream subordinate bus
    pub subordinate_bus: c_uchar,
}

/// Downstream device attributes
#[derive(Copy, Clone)]
#[repr(C)]
pub union RawDownstreamAttributes {
    /// PCI-specific attributes
    pub pci: RawDownstreamPCIAttributes,
}
//
impl Debug for RawDownstreamAttributes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RawDownstreamAttributes")
            .finish_non_exhaustive()
    }
}

/// [`HWLOC_OBJ_OS_DEVICE`]-specific attributes
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_obj_attr_u::hwloc_osdev_attr_s")]
#[repr(C)]
pub struct hwloc_osdev_attr_s {
    /// OS device type
    #[doc(alias = "hwloc_osdev_attr_s::type")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_osdev_attr_s::type")]
    pub ty: hwloc_obj_osdev_type_t,
}

/// Key-value string attributes
///
/// Used in multiple places of the hwloc API for extensible metadata.
///
/// See also [Consulting and Adding Info
/// Attributes](https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__info__attr.html).
#[derive(Debug)]
#[repr(C)]
pub struct hwloc_info_s {
    /// Info name
    pub name: *mut c_char,

    /// Info value
    pub value: *mut c_char,
}

// === Topology Creation and Destruction: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__creation.html

/// Opaque topology struct
///
/// Models the incomplete type that [`hwloc_topology_t`] API pointers map to.
///
/// This type purposely implements no traits, not even Debug, because you should
/// never, ever deal with it directly, only with raw pointers to it that you
/// blindly pass to the hwloc API.
#[allow(missing_debug_implementations)]
#[repr(C)]
pub struct hwloc_topology(IncompleteType);

/// Topology context
///
/// To be initialized with [`hwloc_topology_init()`] and built with [`hwloc_topology_load()`].
pub type hwloc_topology_t = *mut hwloc_topology;

/// A non-modifiable [`hwloc_topology_t`]
pub type hwloc_const_topology_t = *const hwloc_topology;

// === Object levels, depths and types: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__levels.html

/// Depth of an object (or object type) in the topology
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
pub type hwloc_get_type_depth_e = c_int;

/// No object of given type exists in the topology
pub const HWLOC_TYPE_DEPTH_UNKNOWN: hwloc_get_type_depth_e = -1;

/// Objects of given type exist at different depth in the topology (only for Groups)
pub const HWLOC_TYPE_DEPTH_MULTIPLE: hwloc_get_type_depth_e = -2;

/// Virtual depth for [`HWLOC_OBJ_NUMANODE`]
pub const HWLOC_TYPE_DEPTH_NUMANODE: hwloc_get_type_depth_e = -3;

/// Virtual depth for [`HWLOC_OBJ_BRIDGE`]
pub const HWLOC_TYPE_DEPTH_BRIDGE: hwloc_get_type_depth_e = -4;

/// Virtual depth for [`HWLOC_OBJ_PCI_DEVICE`]
pub const HWLOC_TYPE_DEPTH_PCI_DEVICE: hwloc_get_type_depth_e = -5;

/// Virtual depth for [`HWLOC_OBJ_OS_DEVICE`]
pub const HWLOC_TYPE_DEPTH_OS_DEVICE: hwloc_get_type_depth_e = -6;

/// Virtual depth for [`HWLOC_OBJ_MISC`]
pub const HWLOC_TYPE_DEPTH_MISC: hwloc_get_type_depth_e = -7;

/// Virtual depth for [`HWLOC_OBJ_MEMCACHE`]
#[cfg(feature = "hwloc-2_1_0")]
pub const HWLOC_TYPE_DEPTH_MEMCACHE: hwloc_get_type_depth_e = -8;

// === CPU binding: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpubinding.html

/// Process/Thread binding flags
///
/// These bit flags can be used to refine the binding policy. All flags can be
/// OR'ed together with the exception of the binding targets flags
/// [`HWLOC_CPUBIND_THREAD`] and [`HWLOC_CPUBIND_PROCESS`], which are mutually
/// exclusive.
///
/// When using one of the functions that target the active process, you must use
/// at most one of these flags. The most portable binding targets are no flags,
/// which is interpreted as "assume a single-threaded process", followed by
/// [`HWLOC_CPUBIND_THREAD`] and [`HWLOC_CPUBIND_PROCESS`] in this order. These
/// flags must generally not be used with any other function, except on Linux
/// where flag [`HWLOC_CPUBIND_THREAD`] can also be used to turn
/// process-binding functions into thread-binding functions.
///
/// Individual CPU binding functions may not support all of these flags.
/// Please check the documentation of the function that you are
/// trying to call for more information.
pub type hwloc_cpubind_flags_t = c_int;

/// Bind the current thread of the current process
///
/// This is the second most portable option when the process is multi-threaded,
/// and specifying no flags would thus be incorrect.
///
/// On Linux, this flag can also be used to turn process-binding
/// functions into thread-binding functions.
///
/// This is mutually exclusive with [`HWLOC_CPUBIND_PROCESS`].
pub const HWLOC_CPUBIND_THREAD: hwloc_cpubind_flags_t = 1 << 1;

/// Bind all threads of the current process
///
/// This is mutually exclusive with [`HWLOC_CPUBIND_THREAD`].
pub const HWLOC_CPUBIND_PROCESS: hwloc_cpubind_flags_t = 1 << 0;

/// Request for strict binding from the OS
///
/// By default, when the designated CPUs are all busy while other CPUs
/// are idle, operating systems may execute the thread/process on those
/// other CPUs instead of the designated CPUs, to let them progress
/// anyway. Strict binding means that the thread/process will _never_
/// execute on other CPUs than the designated CPUs, even when those are
/// busy with other tasks and other CPUs are idle.
///
/// Depending on the operating system, strict binding may not be
/// possible (e.g. the OS does not implement it) or not allowed (e.g.
/// for an administrative reasons), and the binding function will fail
/// in that case.
///
/// When retrieving the binding of a process, this flag checks whether
/// all its threads actually have the same binding. If the flag is not
/// given, the binding of each thread will be accumulated.
///
/// This flag should not be used when retrieving the binding of a
/// thread or the CPU location of a process.
pub const HWLOC_CPUBIND_STRICT: hwloc_cpubind_flags_t = 1 << 2;

/// Avoid any effect on memory binding
///
/// On some operating systems, some CPU binding function would also bind
/// the memory on the corresponding NUMA node. It is often not a
/// problem for the application, but if it is, setting this flag will
/// make hwloc avoid using OS functions that would also bind memory.
/// This will however reduce the support of CPU bindings, i.e.
/// potentially result in the binding function erroring out.
///
/// This flag should only be used with functions that set the CPU
/// binding.
pub const HWLOC_CPUBIND_NOMEMBIND: hwloc_cpubind_flags_t = 1 << 3;

// === Memory binding: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__membinding.html

/// Memory binding flags.
///
/// These bit flags can be used to refine the binding policy. All flags can
/// be OR'ed together with the exception of the binding target flags
/// [`HWLOC_MEMBIND_THREAD`] and [`HWLOC_MEMBIND_PROCESS`], which are mutually
/// exclusive.
///
/// When using one of the methods that target a process, you must use
/// at most one of these flags. The most portable option is to specify no flags,
/// which means "assume the target process is single-threaded". These
/// flags must not be used with any other method.
///
/// Individual memory binding methods may not support all of these flags. Please
/// check the documentation of the function that you are trying to call for
/// more information.
pub type hwloc_membind_flags_t = c_int;

/// Apply command to all threads of the specified process
///
/// This is mutually exclusive with [`HWLOC_MEMBIND_THREAD`]
pub const HWLOC_MEMBIND_PROCESS: hwloc_membind_flags_t = 1 << 0;

/// Apply command to the current thread of the current process
///
/// This is mutually exclusive with [`HWLOC_MEMBIND_PROCESS`]
pub const HWLOC_MEMBIND_THREAD: hwloc_membind_flags_t = 1 << 1;

/// Request strict binding from the OS
///
/// If this flag is set, a binding method will fail if the binding can
/// not be guaranteed or completely enforced. Otherwise, hwloc will
/// attempt to achieve an approximation of the requested binding (e.g.
/// targeting more or less threads and NUMA nodes).
///
/// This flag has slightly different meanings depending on which
/// method it is used with.
pub const HWLOC_MEMBIND_STRICT: hwloc_membind_flags_t = 1 << 2;

/// Migrate existing allocated memory
///
/// If the memory cannot be migrated and the [`HWLOC_MEMBIND_STRICT`] flag is
/// set, an error will be returned.
///
/// This flag is only meaningful on operations that bind memory.
///
/// Only available if [`hwloc_topology_membind_support::migrate_membind`] is set.
pub const HWLOC_MEMBIND_MIGRATE: hwloc_membind_flags_t = 1 << 3;

/// Avoid any effect on CPU binding
///
/// On some operating systems, some underlying memory binding
/// methods also bind the application to the corresponding CPU(s).
/// Using this flag will cause hwloc to avoid using OS functions that
/// could potentially affect CPU bindings.
///
/// Note, however, that using this flag may reduce hwloc's overall
/// memory binding support.
pub const HWLOC_MEMBIND_NOCPUBIND: hwloc_membind_flags_t = 1 << 4;

/// Consider the bitmap argument as a nodeset.
///
/// The bitmap argument is considered a nodeset if this flag is given,
/// or a cpuset otherwise by default.
///
/// Memory binding by CPU set cannot work for CPU-less NUMA memory nodes.
/// Binding by nodeset should therefore be preferred whenever possible.
pub const HWLOC_MEMBIND_BYNODESET: hwloc_membind_flags_t = 1 << 5;

/// Memory binding policy.
///
/// Not all systems support all kinds of binding.
/// [`hwloc_topology_get_support()`] may be used to query the
/// actual memory binding support in the currently used operating system.
pub type hwloc_membind_policy_t = c_int;

/// Reset the memory allocation policy of the current process or thread to
/// the system default
///
/// Depending on the operating system, this may correspond to
/// [`HWLOC_MEMBIND_FIRSTTOUCH`] (Linux, FreeBSD) or [`HWLOC_MEMBIND_BIND`]
/// (AIX, HP-UX, Solaris, Windows).
///
/// This policy is never returned by get membind functions. The `nodeset`
/// argument is ignored.
pub const HWLOC_MEMBIND_DEFAULT: hwloc_membind_policy_t = 0;

/// Allocate each memory page individually on the local NUMA
/// node of the thread that touches it
///
/// The given nodeset should usually be
/// [`hwloc_topology_get_topology_nodeset()`] so that the touching thread may
/// run and allocate on any node in the system.
///
/// On AIX, if the nodeset is smaller, pages are allocated locally (if the
/// local node is in the nodeset) or from a random non-local node (otherwise).
///
/// Only available if [`hwloc_topology_membind_support::firsttouch_membind`] is
/// set.
pub const HWLOC_MEMBIND_FIRSTTOUCH: hwloc_membind_policy_t = 1;

/// Allocate memory on the specified nodes (most portable option)
///
/// The actual behavior may slightly vary between operating systems, especially
/// when (some of) the requested nodes are full. On Linux, by default, the
/// `MPOL_PREFERRED_MANY` (or `MPOL_PREFERRED`) policy is used. However, if
/// the [`HWLOC_MEMBIND_STRICT`] flag is also given, the Linux `MPOL_BIND`
/// policy is rather used.
///
/// Only available if [`hwloc_topology_membind_support::bind_membind`] is set.
pub const HWLOC_MEMBIND_BIND: hwloc_membind_policy_t = 2;

/// Allocate memory on the given nodes in an interleaved round-robin manner
///
/// The precise layout of the memory across multiple NUMA nodes is OS/system
/// specific.
///
/// Interleaving can be useful when threads distributed across the specified
/// NUMA nodes will all be accessing the whole memory range concurrently,
/// since the interleave will then balance the memory references.
///
/// Only available if [`hwloc_topology_membind_support::interleave_membind`] is
/// set.
pub const HWLOC_MEMBIND_INTERLEAVE: hwloc_membind_policy_t = 3;

/// Migrate pages on next touch
///
/// For each page bound with this policy, by next time it is touched (and
/// next time only), it is moved from its current location to the local NUMA
/// node of the thread where the memory reference occurred (if it needs to
/// be moved at all).
///
/// Only available if [`hwloc_topology_membind_support::nexttouch_membind`] is
/// set.
pub const HWLOC_MEMBIND_NEXTTOUCH: hwloc_membind_policy_t = 4;

/// Mixture of memory binding policies
///
/// Returned by `get_membind()` functions when multiple threads or parts of a
/// memory area have differing memory binding policies. Also returned when
/// binding is unknown because binding hooks are empty when the topology is
/// loaded from XML without `HWLOC_THISSYSTEM=1`, etc.
pub const HWLOC_MEMBIND_MIXED: hwloc_membind_policy_t = -1;

// === Changing the source of topology discovery: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__setsource.html

/// Flags to be passed to [`hwloc_topology_set_components()`]
#[cfg(feature = "hwloc-2_1_0")]
pub type hwloc_topology_components_flag_e = c_ulong;

/// Blacklist the target component from being used
#[cfg(feature = "hwloc-2_1_0")]
pub const HWLOC_TOPOLOGY_COMPONENTS_FLAG_BLACKLIST: hwloc_topology_components_flag_e = 1 << 0;

// === Topology detection configuration and query: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__configuration.html

/// Topology building configuration flags
pub type hwloc_topology_flags_e = c_ulong;

/// Detect the whole system, ignore reservations, include disallowed objects
///
/// Gather all online resources, even if some were disabled by the
/// administrator. For instance, ignore Linux Cgroup/Cpusets and gather
/// all processors and memory nodes. However offline PUs and NUMA nodes
/// are still ignored.
///
/// When this flag is not set, PUs and NUMA nodes that are disallowed
/// are not added to the topology. Parent objects (package, core, cache,
/// etc.) are added only if some of their children are allowed. All
/// existing PUs and NUMA nodes in the topology are allowed.
/// [`hwloc_topology_get_allowed_cpuset()`] and
/// [`hwloc_topology_get_allowed_nodeset()`] are equal to the root object cpuset
/// and nodeset.
///
/// When this flag is set, the actual sets of allowed PUs and NUMA nodes
/// are given by [`hwloc_topology_get_allowed_cpuset()`] and
/// [`hwloc_topology_get_allowed_nodeset()`]. They may be smaller than the root
/// object cpuset and nodeset.
///
/// If the current topology is exported to XML and reimported later,
/// this flag should be set again in the reimported topology so that
/// disallowed resources are reimported as well.
///
#[cfg_attr(
    feature = "hwloc-2_1_0",
    doc = "What additional objects could be detected with this flag depends on"
)]
#[cfg_attr(
    feature = "hwloc-2_1_0",
    doc = "[`hwloc_topology_discovery_support::disallowed_pu`] and"
)]
#[cfg_attr(
    feature = "hwloc-2_1_0",
    doc = "[`hwloc_topology_discovery_support::disallowed_numa`], which can be checked"
)]
#[cfg_attr(feature = "hwloc-2_1_0", doc = "after building the topology.")]
#[doc(alias = "HWLOC_TOPOLOGY_FLAG_WHOLE_SYSTEM")]
pub const HWLOC_TOPOLOGY_FLAG_INCLUDE_DISALLOWED: hwloc_topology_flags_e = 1 << 0;

/// Assume that the selected backend provides the topology for the
/// system on which we are running
///
/// This forces [`hwloc_topology_is_thissystem()`] to return true, i.e. makes
/// hwloc assume that the selected backend provides the topology for the system
/// on which we are running, even if it is not the OS-specific backend but the
/// XML backend for instance. This means making the binding functions actually
/// call the OS-specific system calls and really do binding, while the XML
/// backend would otherwise provide empty hooks just returning success.
///
/// Setting the environment variable `HWLOC_THISSYSTEM` may also result
/// in the same behavior.
///
/// This can be used for efficiency reasons to first detect the topology
/// once, save it to an XML file, and quickly reload it later through
/// the XML backend, but still having binding functions actually do bind.
pub const HWLOC_TOPOLOGY_FLAG_IS_THISSYSTEM: hwloc_topology_flags_e = 1 << 1;

/// Get the set of allowed resources from the local operating system
/// even if the topology was loaded from XML or synthetic description
///
/// If the topology was loaded from XML or from a synthetic string,
/// restrict it by applying the current process restrictions such as
/// Linux Cgroup/Cpuset.
///
/// This is useful when the topology is not loaded directly from the
/// local machine (e.g. for performance reason) and it comes with all
/// resources, while the running process is restricted to only parts of
/// the machine.
///
/// If this flag is set, [`HWLOC_TOPOLOGY_FLAG_IS_THISSYSTEM`] must also be set,
/// since the loaded topology must match the underlying machine where
/// restrictions will be gathered from.
///
/// Setting the environment variable `HWLOC_THISSYSTEM_ALLOWED_RESOURCES`
/// would result in the same behavior.
pub const HWLOC_TOPOLOGY_FLAG_THISSYSTEM_ALLOWED_RESOURCES: hwloc_topology_flags_e = 1 << 2;

/// Import support from the imported topology
///
/// When importing a XML topology from a remote machine, binding is disabled by
/// default (see [`HWLOC_TOPOLOGY_FLAG_IS_THISSYSTEM`]). This disabling is also
/// marked by putting zeroes in the corresponding supported feature bits
/// reported by [`hwloc_topology_get_support()`].
///
/// This flag allows you to actually import support bits from the remote
/// machine. It also sets the
/// [`hwloc_topology_misc_support::imported_support`] support flag. If the
/// imported XML did not contain any support information(exporter hwloc is too
/// old), this flag is not set.
///
/// Note that these supported features are only relevant for the hwloc
/// installation that actually exported the XML topology (it may vary
/// with the operating system, or with how hwloc was compiled).
///
/// Note that setting this flag however does not enable binding for the
/// locally imported hwloc topology, it only reports what the remote
/// hwloc and machine support.
#[cfg(feature = "hwloc-2_3_0")]
pub const HWLOC_TOPOLOGY_FLAG_IMPORT_SUPPORT: hwloc_topology_flags_e = 1 << 3;

/// Do not consider resources outside of the process CPU binding
///
/// If the binding of the process is limited to a subset of cores,
/// ignore the other cores during discovery.
///
/// The resulting topology is identical to what a call to
/// [`hwloc_topology_restrict()`] would generate, but this flag also
/// prevents hwloc from ever touching other resources during the
/// discovery.
///
/// This flag especially tells the x86 backend to never temporarily
/// rebind a thread on any excluded core. This is useful on Windows
/// because such temporary rebinding can change the process binding.
/// Another use-case is to avoid cores that would not be able to perform
/// the hwloc discovery anytime soon because they are busy executing
/// some high-priority real-time tasks.
///
/// If process CPU binding is not supported, the thread CPU binding is
/// considered instead if supported, or the flag is ignored.
///
/// This flag requires [`HWLOC_TOPOLOGY_FLAG_IS_THISSYSTEM`] as well since
/// binding support is required.
#[cfg(feature = "hwloc-2_5_0")]
pub const HWLOC_TOPOLOGY_FLAG_RESTRICT_TO_CPUBINDING: hwloc_topology_flags_e = 1 << 4;

/// Do not consider resources outside of the process memory binding
///
/// If the binding of the process is limited to a subset of NUMA nodes,
/// ignore the other NUMA nodes during discovery.
///
/// The resulting topology is identical to what a call to
/// [`hwloc_topology_restrict()`] would generate, but this flag also
/// prevents hwloc from ever touching other resources during the
/// discovery.
///
/// This flag is meant to be used together with
/// `RESTRICT_CPU_TO_THIS_PROCESS` when both cores and NUMA nodes should
/// be ignored outside of the process binding.
///
/// If process memory binding is not supported, the thread memory
/// binding is considered instead if supported, or the flag is ignored.
///
/// This flag requires [`HWLOC_TOPOLOGY_FLAG_IS_THISSYSTEM`] as well since
/// binding support is required.
#[cfg(feature = "hwloc-2_5_0")]
pub const HWLOC_TOPOLOGY_FLAG_RESTRICT_TO_MEMBINDING: hwloc_topology_flags_e = 1 << 5;

/// Do not ever modify the process or thread binding during discovery
///
/// This flag disables all hwloc discovery steps that require a change
/// of the process or thread binding. This currently only affects the
/// x86 backend which gets entirely disabled.
///
/// This is useful when a topology is loaded while the application also creates
/// additional threads or modifies the binding.
///
/// This flag is also a strict way to make sure the process binding will
/// not change to due thread binding changes on Windows (see
/// `RESTRICT_CPU_TO_THIS_PROCESS`).
#[cfg(feature = "hwloc-2_5_0")]
pub const HWLOC_TOPOLOGY_FLAG_DONT_CHANGE_BINDING: hwloc_topology_flags_e = 1 << 6;

/// Ignore distance information from the operating system (and from
/// XML)
///
/// Distances will not be used for grouping topology objects.
#[cfg(feature = "hwloc-2_8_0")]
pub const HWLOC_TOPOLOGY_FLAG_NO_DISTANCES: hwloc_topology_flags_e = 1 << 7;

/// Ignore memory attribues from the operating system (and from XML)
#[cfg(feature = "hwloc-2_8_0")]
pub const HWLOC_TOPOLOGY_FLAG_NO_MEMATTRS: hwloc_topology_flags_e = 1 << 8;

/// Ignore CPU kind information from the operating system (and from
/// XML)
#[cfg(feature = "hwloc-2_8_0")]
pub const HWLOC_TOPOLOGY_FLAG_NO_CPUKINDS: hwloc_topology_flags_e = 1 << 9;

/// Set of flags describing actual hwloc feature support for this topology
#[derive(Debug)]
#[repr(C)]
pub struct hwloc_topology_support {
    /// Support for discovering information about the topology
    pub discovery: *const hwloc_topology_discovery_support,

    /// Support for getting and setting thread/process CPU bindings
    pub cpubind: *const hwloc_topology_cpubind_support,

    /// Support for getting and setting thread/process NUMA node bindings
    pub membind: *const hwloc_topology_membind_support,

    /// Miscellaneous support information
    #[cfg(feature = "hwloc-2_3_0")]
    pub misc: *const hwloc_topology_misc_support,
}
//
impl Default for hwloc_topology_support {
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

/// Support for discovering information about the topology
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[repr(C)]
pub struct hwloc_topology_discovery_support {
    /// Detecting the number of PU objects is supported
    pub pu: c_uchar,

    /// Detecting the number of NUMA nodes is supported
    pub numa: c_uchar,

    /// Detecting the amount of memory in NUMA nodes is supported
    pub numa_memory: c_uchar,

    /// Detecting and identifying PU objects that are not available to the
    /// current process is supported
    #[cfg(feature = "hwloc-2_1_0")]
    pub disallowed_pu: c_uchar,

    /// Detecting and identifying NUMA nodes that are not available to the
    /// current process is supported
    #[cfg(feature = "hwloc-2_1_0")]
    pub disallowed_numa: c_uchar,

    /// Detecting the efficiency of CPU kinds is supported
    ///
    /// See also [Kinds of CPU cores](https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpukinds.html).
    #[cfg(feature = "hwloc-2_4_0")]
    pub cpukind_efficiency: c_uchar,
}

/// Support for getting and setting thread/process CPU bindings
///
/// A flag may be set even if the feature isn't supported in all cases
/// (e.g. binding to random sets of non-contiguous objects).
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[repr(C)]
pub struct hwloc_topology_cpubind_support {
    /// Binding the whole current process is supported
    pub set_thisproc_cpubind: c_uchar,

    /// Getting the binding of the whole current process is supported
    pub get_thisproc_cpubind: c_uchar,

    /// Binding a whole given process is supported
    pub set_proc_cpubind: c_uchar,

    /// Getting the binding of a whole given process is supported
    pub get_proc_cpubind: c_uchar,

    /// Binding the current thread only is supported
    pub set_thisthread_cpubind: c_uchar,

    /// Getting the binding of the current thread only is supported
    pub get_thisthread_cpubind: c_uchar,

    /// Binding a given thread only is supported
    pub set_thread_cpubind: c_uchar,

    /// Getting the binding of a given thread only is supported
    pub get_thread_cpubind: c_uchar,

    /// Getting the last processors where the whole current process ran is supported
    pub get_thisproc_last_cpu_location: c_uchar,

    /// Getting the last processors where a whole process ran is supported
    pub get_proc_last_cpu_location: c_uchar,

    /// Getting the last processors where the current thread ran is supported
    pub get_thisthread_last_cpu_location: c_uchar,
}

/// Support for getting and setting thread/process NUMA node bindings
///
/// A flag may be set even if the feature isn't supported in all cases
/// (e.g. binding to random sets of non-contiguous objects).
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[repr(C)]
pub struct hwloc_topology_membind_support {
    /// Binding the whole current process is supported
    pub set_thisproc_membind: c_uchar,

    /// Getting the binding of the whole current process is supported
    pub get_thisproc_membind: c_uchar,

    /// Binding a whole given process is supported
    pub set_proc_membind: c_uchar,

    /// Getting the binding of a whole given process is supported
    pub get_proc_membind: c_uchar,

    /// Binding the current thread only is supported
    pub set_thisthread_membind: c_uchar,

    /// Getting the binding of the current thread only is supported
    pub get_thisthread_membind: c_uchar,

    /// Binding a given memory area is supported
    pub set_area_membind: c_uchar,

    /// Getting the binding of a given memory area is supported
    pub get_area_membind: c_uchar,

    /// Allocating a bound memory area is supported
    pub alloc_membind: c_uchar,

    /// First-touch policy is supported
    pub firsttouch_membind: c_uchar,

    /// Bind policy is supported
    pub bind_membind: c_uchar,

    /// Interleave policy is supported
    pub interleave_membind: c_uchar,

    /// Next-touch migration policy is supported
    pub nexttouch_membind: c_uchar,

    /// Migration flag is supported
    pub migrate_membind: c_uchar,

    /// Getting the last NUMA nodes where a memory area was allocated is supported
    pub get_area_memlocation: c_uchar,
}

/// Miscellaneous support information
#[cfg(feature = "hwloc-2_3_0")]
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[repr(C)]
pub struct hwloc_topology_misc_support {
    /// Support was imported when importing another topology
    ///
    /// See also [`HWLOC_TOPOLOGY_FLAG_IMPORT_SUPPORT`].
    pub imported_support: c_uchar,
}

/// Type filtering flags
///
/// By default...
///
/// - Most objects are kept ([`HWLOC_TYPE_FILTER_KEEP_ALL`])
/// - Instruction caches, I/O and Misc objects are ignored (
///   [`HWLOC_TYPE_FILTER_KEEP_NONE`]).
/// - Die and Group levels are ignored unless they bring structure (
///   [`HWLOC_TYPE_FILTER_KEEP_STRUCTURE`]).
///
/// Note that group objects are also ignored individually (without the entire
/// level) when they do not bring structure.
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
pub type hwloc_type_filter_e = c_int;

/// Keep all objects of this type
///
/// Cannot be set for [`HWLOC_OBJ_GROUP`] (groups are designed only to add
/// more structure to the topology).
pub const HWLOC_TYPE_FILTER_KEEP_ALL: hwloc_type_filter_e = 0;

/// Ignore all objects of this type
///
/// The bottom-level type [`HWLOC_OBJ_PU`], the [`HWLOC_OBJ_NUMANODE`] type
/// and the top-level type [`HWLOC_OBJ_MACHINE`] may not be ignored.
pub const HWLOC_TYPE_FILTER_KEEP_NONE: hwloc_type_filter_e = 1;

/// Only ignore objects if their entire level does not bring any structure
///
/// Keep the entire level of objects if at least one of these objects adds
/// structure to the topology. An object brings structure when it has
/// multiple children and it is not the only child of its parent.
///
/// If all objects in the level are the only child of their parent, and if
/// none of them has multiple children, the entire level is removed.
///
/// Cannot be set for I/O and Misc objects since the topology structure does
/// not matter there.
pub const HWLOC_TYPE_FILTER_KEEP_STRUCTURE: hwloc_type_filter_e = 2;

/// Only keep likely-important objects of the given type.
///
/// This is only useful for I/O object types.
///
/// For [`HWLOC_OBJ_PCI_DEVICE`] and [`HWLOC_OBJ_OS_DEVICE`], it means that
/// only objects of major/common kinds are kept (storage, network,
/// OpenFabrics, CUDA, OpenCL, RSMI, NVML, and displays).
/// Also, only OS devices directly attached on PCI (e.g. no USB) are reported.
///
/// For [`HWLOC_OBJ_BRIDGE`], it means that bridges are kept only if they
/// have children.
///
/// This flag is equivalent to [`HWLOC_TYPE_FILTER_KEEP_ALL`] for Normal, Memory
/// and Misc types since they are likely important.
pub const HWLOC_TYPE_FILTER_KEEP_IMPORTANT: hwloc_type_filter_e = 3;

// === Modifying a loaded Topology: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__tinker.html

/// Module existing solely to apply a common hwloc version gate
#[allow(clippy::wildcard_imports)]
#[cfg(feature = "hwloc-2_3_0")]
mod topology_editing {
    use super::*;

    /// Flags to be given to [`hwloc_topology_restrict()`]
    pub type hwloc_restrict_flags_e = c_ulong;

    /// Remove all objects that became CPU-less
    ///
    /// By default, only objects that contain no PU and no memory are removed. This
    /// flag allows you to remove all objects that do not have access to any CPU
    /// anymore when restricting by CPU set.
    pub const HWLOC_RESTRICT_FLAG_REMOVE_CPULESS: hwloc_restrict_flags_e = 1 << 0;

    /// Restrict by NUMA node set insted of by CPU set
    pub const HWLOC_RESTRICT_FLAG_BYNODESET: hwloc_restrict_flags_e = 1 << 3;

    /// Remove all objects that became memory-less
    ///
    /// By default, only objects that contain no PU and no memory are removed. This
    /// flag allows you to remove all objects that do not have access to any memory
    /// anymore when restricting by NUMA node set.
    pub const HWLOC_RESTRICT_FLAG_REMOVE_MEMLESS: hwloc_restrict_flags_e = 1 << 4;

    /// Move Misc objects to ancestors if their parents are removed during
    /// restriction
    ///
    /// If this flag is not set, Misc objects are removed when their parents
    /// are removed.
    pub const HWLOC_RESTRICT_FLAG_ADAPT_MISC: hwloc_restrict_flags_e = 1 << 1;

    /// Move I/O objects to ancestors if their parents are removed
    /// during restriction
    ///
    /// If this flag is not set, I/O devices and bridges are removed when
    /// their parents are removed.
    pub const HWLOC_RESTRICT_FLAG_ADAPT_IO: hwloc_restrict_flags_e = 1 << 2;

    /// Flags to be given to [`hwloc_topology_allow()`]
    pub type hwloc_allow_flags_e = c_ulong;

    /// Mark all objects as allowed in the topology
    ///
    /// `cpuset` and `nodeset` given to [`hwloc_topology_allow()`] must be NULL.
    pub const HWLOC_ALLOW_FLAG_ALL: hwloc_allow_flags_e = 1 << 0;

    /// Only allow objects that are available to the current process
    ///
    /// Requires [`HWLOC_TOPOLOGY_FLAG_IS_THISSYSTEM`] so that the set of available
    /// resources can actually be retrieved from the operating system.
    ///
    /// `cpuset` and `nodeset` given to [`hwloc_topology_allow()`] must be NULL.
    pub const HWLOC_ALLOW_FLAG_LOCAL_RESTRICTIONS: hwloc_allow_flags_e = 1 << 1;

    /// Allow a custom set of objects, given to [`hwloc_topology_allow()`] as
    /// `cpuset` and/or `nodeset` parameters.
    pub const HWLOC_ALLOW_FLAG_CUSTOM: hwloc_allow_flags_e = 1 << 2;
}
#[cfg(feature = "hwloc-2_3_0")]
pub use topology_editing::*;

// === The bitmap API: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__bitmap.html

/// Opaque bitmap struct
///
/// Represents the private `hwloc_bitmap_s` type that `hwloc_bitmap_t` API
/// pointers map to.
///
/// This type purposely implements no traits, not even Debug, because you should
/// never, ever deal with it directly, only with raw pointers to it that you
/// blindly pass to the hwloc API.
#[allow(missing_debug_implementations)]
#[repr(C)]
pub struct hwloc_bitmap_s(IncompleteType);

/// Set of bits represented as an opaque pointer to an internal bitmap
pub type hwloc_bitmap_t = *mut hwloc_bitmap_s;

/// A non-modifiable [`hwloc_bitmap_t`]
pub type hwloc_const_bitmap_t = *const hwloc_bitmap_s;

// === Exporting Topologies to XML: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__xmlexport.html

/// Flags to be given to [`hwloc_topology_export_xml()`]
pub type hwloc_topology_export_xml_flags_e = c_ulong;

/// Export XML that is loadable by hwloc v1.x
///
/// The export may miss some details about the topology.
pub const HWLOC_TOPOLOGY_EXPORT_XML_FLAG_V1: hwloc_topology_export_xml_flags_e = 1 << 0;

// === Exporting Topologies to Synthetic: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__syntheticexport.html

/// Flags to be given to [`hwloc_topology_export_synthetic()`]
pub type hwloc_topology_export_synthetic_flags_e = c_ulong;

/// Export extended types such as L2dcache as basic types such as Cache
///
/// This is required if loading the synthetic description with hwloc < 1.9.
pub const HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_NO_EXTENDED_TYPES:
    hwloc_topology_export_synthetic_flags_e = 1 << 0;

/// Do not export level attributes
///
/// Ignore level attributes such as memory/cache sizes or PU indices.
///
/// This is required if loading the synthetic description with hwloc < 1.10.
pub const HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_NO_ATTRS: hwloc_topology_export_synthetic_flags_e =
    1 << 1;

/// Export the memory hierarchy as expected in hwloc 1.x
///
/// Instead of attaching memory children to levels, export single NUMA
/// node children as normal intermediate levels, when possible.
///
/// This is required if loading the synthetic description with hwloc 1.x.
/// However this may fail if some objects have multiple local NUMA nodes.
pub const HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_V1: hwloc_topology_export_synthetic_flags_e = 1 << 2;

/// Do not export memory information
///
/// Only export the actual hierarchy of normal CPU-side objects and
/// ignore where memory is attached.
///
/// This is useful for when the hierarchy of CPUs is what really matters,
/// but it behaves as if there was a single machine-wide NUMA node.
pub const HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_IGNORE_MEMORY:
    hwloc_topology_export_synthetic_flags_e = 1 << 3;

// === Retrieve distances between objects: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__get.html

/// Kinds of distance matrices
///
/// A kind with a name starting with "FROM_" specifies where the distance
/// information comes from, if known.
///
/// A kind with a name starting with "MEANS_" specifies whether values are
/// latencies or bandwidths, if applicable.
///
/// Only one of the "FROM_" and "MEANS_" kinds should be present.
pub type hwloc_distances_kind_e = c_ulong;

/// These distances were obtained from the operating system or hardware
pub const HWLOC_DISTANCES_KIND_FROM_OS: hwloc_distances_kind_e = 1 << 0;

/// These distances were provided by the user
pub const HWLOC_DISTANCES_KIND_FROM_USER: hwloc_distances_kind_e = 1 << 1;

/// Distance values are similar to latencies between objects
///
/// Values are smaller for closer objects, hence minimal on the diagonal
/// of the matrix (distance between an object and itself).
///
/// It could also be the number of network hops between objects, etc.
pub const HWLOC_DISTANCES_KIND_MEANS_LATENCY: hwloc_distances_kind_e = 1 << 2;

/// Distance values are similar to bandwidths between objects
///
/// Values are higher for closer objects, hence maximal on the diagonal
/// of the matrix (distance between an object and itself).
///
/// Such values are currently ignored for distance-based grouping.
pub const HWLOC_DISTANCES_KIND_MEANS_BANDWIDTH: hwloc_distances_kind_e = 1 << 3;

/// This distances structure covers objects of different types
///
/// This may apply to the "NVLinkBandwidth" structure in presence of a
/// NVSwitch or POWER processor NVLink port.
#[cfg(feature = "hwloc-2_1_0")]
pub const HWLOC_DISTANCES_KIND_HETEROGENEOUS_TYPES: hwloc_distances_kind_e = 1 << 4;

/// Module existing solely to apply a common hwloc version gate
#[allow(clippy::wildcard_imports)]
#[cfg(feature = "hwloc-2_5_0")]
mod distances_transform {
    use super::*;

    /// Transformations of distances structures
    ///
    /// We can't use Rust enums to model C enums in FFI because that results in
    /// undefined behavior if the C API gets new enum variants and sends them to us.
    pub type hwloc_distances_transform_e = c_uint;

    /// Remove NULL objects from the distances structure.
    ///
    /// Every object that was replaced with NULL in [`hwloc_distances_s::objs`]
    /// is removed and the matrix is updated accordingly.
    ///
    /// At least 2 objects must remain, otherwise [`hwloc_distances_transform()`]
    /// will fail.
    ///
    /// [`hwloc_distances_s::kind`] will be updated with or without
    /// [`HWLOC_DISTANCES_KIND_HETEROGENEOUS_TYPES`] according to the remaining
    /// objects.
    pub const HWLOC_DISTANCES_TRANSFORM_REMOVE_NULL: hwloc_distances_transform_e = 0;

    /// Replace bandwidth values with a number of links
    ///
    /// Usually all values will be either 0 (no link) or 1 (one link).
    /// However some matrices could get larger values if some pairs of
    /// peers are connected by different numbers of links.
    ///
    /// Values on the diagonal are set to 0.
    ///
    /// This transformation only applies to bandwidth matrices.
    pub const HWLOC_DISTANCES_TRANSFORM_LINKS: hwloc_distances_transform_e = 1;

    /// Merge switches with multiple ports into a single object
    ///
    /// This currently only applies to NVSwitches where GPUs seem connected to
    /// different separate switch ports in the NVLinkBandwidth matrix.
    ///
    /// This transformation will replace all switch ports with the same port
    /// connected to all GPUs.
    ///
    /// Other ports are removed by applying the
    /// [`HWLOC_DISTANCES_TRANSFORM_REMOVE_NULL`] transformation internally.
    pub const HWLOC_DISTANCES_TRANSFORM_MERGE_SWITCH_PORTS: hwloc_distances_transform_e = 2;

    /// Apply a transitive closure to the matrix to connect objects across
    /// switches.
    ///
    /// This currently only applies to GPUs and NVSwitches in the
    /// NVLinkBandwidth matrix.
    ///
    /// All pairs of GPUs will be reported as directly connected.
    pub const HWLOC_DISTANCES_TRANSFORM_TRANSITIVE_CLOSURE: hwloc_distances_transform_e = 3;
}
#[cfg(feature = "hwloc-2_5_0")]
pub use distances_transform::*;

/// Matrix of distances between a set of objects
///
/// This matrix often contains latencies between NUMA nodes (as reported in the
/// System Locality Distance Information Table (SLIT) in the ACPI
/// specification), which may or may not be physically accurate. It corresponds
/// to the latency for accessing the memory of one node from a core in another
/// node. The corresponding kind is [`HWLOC_DISTANCES_KIND_FROM_OS`] |
/// [`HWLOC_DISTANCES_KIND_FROM_USER`]. The name of this distances structure is
/// "NUMALatency".
///
/// The names and semantics of other distances matrices currently created by
/// hwloc may be found
/// [in the hwloc documentation](https://hwloc.readthedocs.io/en/v2.9/topoattrs.html#topoattrs_distances).
///
/// The matrix may also contain bandwidths between random sets of objects,
/// possibly provided by the user, as specified in the `kind` attribute.
///
/// Pointers `objs` and `values` should not be replaced, reallocated, freed, etc.
/// However callers are allowed to modify `kind` as well as the contents of `objs`
/// and `values` arrays.
///
#[cfg_attr(
    feature = "hwloc-2_5_0",
    doc = "For instance, on hwloc 2.5+, if there is a single NUMA node per Package,"
)]
#[cfg_attr(
    feature = "hwloc-2_5_0",
    doc = "[`hwloc_get_obj_with_same_locality()`] may be used to convert"
)]
#[cfg_attr(
    feature = "hwloc-2_5_0",
    doc = "between them and replace NUMA nodes in the objs array with the corresponding"
)]
#[cfg_attr(feature = "hwloc-2_5_0", doc = "Packages.")]
#[cfg_attr(feature = "hwloc-2_5_0", doc = "")]
#[cfg_attr(
    feature = "hwloc-2_5_0",
    doc = "See also [`hwloc_distances_transform()`] for applying some"
)]
#[cfg_attr(feature = "hwloc-2_5_0", doc = "transformations to the structure.")]
#[derive(Debug)]
#[repr(C)]
pub struct hwloc_distances_s {
    /// Number of objects described by the distance matrix
    pub nbobj: c_uint,

    /// Array of `nbobj` objects described by the distance matrix
    ///
    /// These objects are not in any particular order
    pub objs: *mut hwloc_obj_t,

    /// OR'ed set of [`hwloc_distances_kind_e`].
    pub kind: c_ulong,

    /// Matrix of distances between objects, stored as a
    /// one-dimension array of length `nbobj*nbobj`
    ///
    /// Distance from i-th to j-th object is stored in slot `i*nbobjs+j`. The
    /// meaning of the value depends on the `kind` attribute.
    pub values: *mut u64,
}
//
impl Default for hwloc_distances_s {
    fn default() -> Self {
        Self {
            nbobj: 0,
            objs: ptr::null_mut(),
            kind: 0,
            values: ptr::null_mut(),
        }
    }
}

// === Add distances between objects: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__add.html

/// Handle to a new distances structure during its addition to the topology
#[cfg(feature = "hwloc-2_5_0")]
pub type hwloc_distances_add_handle_t = *mut c_void;

/// Flags to be given to [`hwloc_distances_add_commit()`]
#[cfg(feature = "hwloc-2_5_0")]
pub type hwloc_distances_add_flag_e = c_ulong;

/// Try to group objects based on the newly provided distance information
///
/// This is ignored for distances between objects of different types.
#[cfg(feature = "hwloc-2_5_0")]
pub const HWLOC_DISTANCES_ADD_FLAG_GROUP: hwloc_distances_add_flag_e = 1 << 0;

/// If grouping, consider the distance values as inaccurate and relax
/// the comparisons during the grouping algorithms. The actual accuracy
/// may be modified through the `HWLOC_GROUPING_ACCURACY` environment
/// variable (see
/// [Environment Variables](https://hwloc.readthedocs.io/en/v2.9/envvar.html)).
#[cfg(feature = "hwloc-2_5_0")]
pub const HWLOC_DISTANCES_ADD_FLAG_GROUP_INACCURATE: hwloc_distances_add_flag_e = 1 << 1;

// === Memory attributes

/// Module existing solely to apply a common hwloc version gate
#[allow(clippy::wildcard_imports)]
#[cfg(feature = "hwloc-2_3_0")]
mod memory_attributes {
    use super::*;

    // === Comparing memory node attributes for finding where to allocate on: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs.html

    /// Memory attribute identifier
    ///
    /// May be one of the `HWLOC_MEMATTR_ID_` constants or a new id returned by
    /// [`hwloc_memattr_register()`].
    #[doc(alias = "hwloc_memattr_id_e")]
    pub type hwloc_memattr_id_t = c_uint;

    /// Node capacity in bytes (see [`hwloc_obj::total_memory`])
    ///
    /// This attribute involves no initiator.
    ///
    /// Requires [`hwloc_topology_discovery_support::numa_memory`] to be set.
    pub const HWLOC_MEMATTR_ID_CAPACITY: hwloc_memattr_id_t = 0;

    /// Number of PUs in that locality (i.e. cpuset weight)
    ///
    /// Smaller locality is better. This attribute involves no initiator.
    ///
    /// Requires [`hwloc_topology_discovery_support::pu`] to be set.
    pub const HWLOC_MEMATTR_ID_LOCALITY: hwloc_memattr_id_t = 1;

    /// Average bandwidth in MiB/s, as seen from the given initiator location
    ///
    /// This is the average bandwidth for read and write accesses. If the
    /// platform provides individual read and write bandwidths but no
    /// explicit average value, hwloc computes and returns the average.
    pub const HWLOC_MEMATTR_ID_BANDWIDTH: hwloc_memattr_id_t = 2;

    /// Read bandwidth in MiB/s, as seen from the given initiator location
    #[cfg(feature = "hwloc-2_8_0")]
    #[cfg_attr(docsrs, doc(cfg(feature = "hwloc-2_8_0")))]
    pub const HWLOC_MEMATTR_ID_READ_BANDWIDTH: hwloc_memattr_id_t = 4;

    /// Write bandwidth in MiB/s, as seen from the given initiator location
    #[cfg(feature = "hwloc-2_8_0")]
    #[cfg_attr(docsrs, doc(cfg(feature = "hwloc-2_8_0")))]
    pub const HWLOC_MEMATTR_ID_WRITE_BANDWIDTH: hwloc_memattr_id_t = 5;

    /// Latency in nanoseconds, as seen from the given initiator location
    ///
    /// This is the average latency for read and write accesses. If the
    /// platform value provides individual read and write latencies but no
    /// explicit average, hwloc computes and returns the average.
    pub const HWLOC_MEMATTR_ID_LATENCY: hwloc_memattr_id_t = 3;

    /// Read latency in nanoseconds, as seen from the given initiator location
    #[cfg(feature = "hwloc-2_8_0")]
    #[cfg_attr(docsrs, doc(cfg(feature = "hwloc-2_8_0")))]
    pub const HWLOC_MEMATTR_ID_READ_LATENCY: hwloc_memattr_id_t = 6;

    /// Write latency in nanoseconds, as seen from the given initiator location
    #[cfg(feature = "hwloc-2_8_0")]
    #[cfg_attr(docsrs, doc(cfg(feature = "hwloc-2_8_0")))]
    pub const HWLOC_MEMATTR_ID_WRITE_LATENCY: hwloc_memattr_id_t = 7;
    // NOTE: If you add new attributes, add support to hwlocality's
    //       hwloc_memattr_id_t, static_flags and MemoryAttribute constructors

    /// Flags for selecting more target NUMA nodes
    ///
    /// By default only NUMA nodes whose locality is exactly the given location
    /// are selected.
    pub type hwloc_local_numanode_flag_e = c_ulong;

    /// Select NUMA nodes whose locality is larger than the given cpuset
    ///
    /// For instance, if a single PU (or its cpuset) is given in `initiator`,
    /// select all nodes close to the package that contains this PU.
    pub const HWLOC_LOCAL_NUMANODE_FLAG_LARGER_LOCALITY: hwloc_local_numanode_flag_e = 1 << 0;

    /// Select NUMA nodes whose locality is smaller than the given cpuset
    ///
    /// For instance, if a package (or its cpuset) is given in `initiator`,
    /// also select nodes that are attached to only a half of that package.
    pub const HWLOC_LOCAL_NUMANODE_FLAG_SMALLER_LOCALITY: hwloc_local_numanode_flag_e = 1 << 1;

    /// Select all NUMA nodes in the topology
    ///
    /// The initiator is ignored.
    pub const HWLOC_LOCAL_NUMANODE_FLAG_ALL: hwloc_local_numanode_flag_e = 1 << 2;

    /// Where to measure attributes from
    #[derive(Copy, Clone, Debug)]
    #[repr(C)]
    pub struct hwloc_location {
        /// Type of location
        #[doc(alias = "hwloc_location::type")]
        pub ty: hwloc_location_type_e,

        /// Actual location
        pub location: hwloc_location_u,
    }

    /// Type of location
    ///
    /// C enums can't be modeled as Rust enums because new variants would be UB
    pub type hwloc_location_type_e = c_int;

    /// Location is given as a cpuset, in the [`hwloc_location_u::cpuset`] union field
    pub const HWLOC_LOCATION_TYPE_CPUSET: hwloc_location_type_e = 1;

    /// Location is given as an object, in the [`hwloc_location_u::object`] union field
    pub const HWLOC_LOCATION_TYPE_OBJECT: hwloc_location_type_e = 0;

    /// Actual location
    #[derive(Copy, Clone)]
    #[doc(alias = "hwloc_location::hwloc_location_u")]
    #[repr(C)]
    pub union hwloc_location_u {
        /// Directly provide CPU set to find NUMA nodes with corresponding
        /// locality
        ///
        /// This is the only initiator type supported by most memory attribute
        /// queries on hwloc-defined memory attributes, though `object` remains
        /// an option for user-defined memory attributes.
        pub cpuset: hwloc_const_cpuset_t,

        /// Use a topology object as an initiator
        ///
        /// Most memory attribute queries on hwloc-defined memory attributes do
        /// not support this initiator type, or translate it to a cpuset
        /// (going up the ancestor chain if necessary). But user-defined memory
        /// attributes may for instance use it to provide custom information
        /// about host memory accesses performed by GPUs.
        pub object: *const hwloc_obj,
    }
    //
    impl Debug for hwloc_location_u {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_struct("hwloc_location_u").finish_non_exhaustive()
        }
    }

    /// Memory attribute flags
    ///
    /// At least one of [`HWLOC_MEMATTR_FLAG_HIGHER_FIRST`] and
    /// [`HWLOC_MEMATTR_FLAG_LOWER_FIRST`] must be set.
    pub type hwloc_memattr_flag_e = c_ulong;

    /// The best nodes for this memory attribute are those with the higher
    /// values
    ///
    /// For instance [`HWLOC_MEMATTR_ID_BANDWIDTH`].
    pub const HWLOC_MEMATTR_FLAG_HIGHER_FIRST: hwloc_memattr_flag_e = 1 << 0;

    /// The best nodes for this memory attribute are those with the lower
    /// values
    ///
    /// For instance [`HWLOC_MEMATTR_ID_LATENCY`].
    pub const HWLOC_MEMATTR_FLAG_LOWER_FIRST: hwloc_memattr_flag_e = 1 << 1;

    /// The value returned for this memory attribute depends on the given
    /// initiator
    ///
    /// For instance [`HWLOC_MEMATTR_ID_BANDWIDTH`] and
    /// [`HWLOC_MEMATTR_ID_LATENCY`], but not[`HWLOC_MEMATTR_ID_CAPACITY`].
    pub const HWLOC_MEMATTR_FLAG_NEED_INITIATOR: hwloc_memattr_flag_e = 1 << 2;
}
#[cfg(feature = "hwloc-2_3_0")]
pub use memory_attributes::*;

// === TODO: Remaining sections

// === Entry points

/// Implement all the entry points with the right link name
macro_rules! extern_c_block {
    ($link_name:literal) => {
        #[link(name = $link_name)]
        extern "C" {
            // === API versioning: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__api__version.html

            /// Indicate at runtime which hwloc API version was used at build time
            ///
            /// This number is updated to `(X<<16)+(Y<<8)+Z` when a new release X.Y.Z
            /// actually modifies the API.
            #[must_use]
            pub fn hwloc_get_api_version() -> c_uint;

            // === Object types: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__object__types.html

            /// Compare the depth of two object types.
            ///
            /// Types shouldn't be compared as they are, since newer ones may be
            /// added in the future.
            ///
            /// # Returns
            ///
            /// - A negative integer if `type1` objects usually include `type2`
            ///   objects.
            /// - A positive integer if `type1` objects are usually included in
            ///   `type2` objects.
            /// - 0 if `type1` and `type2` objects are the same.
            /// - [`HWLOC_TYPE_UNORDERED`] if objects cannot be compared
            ///   (because neither is usually contained in the other).
            ///
            /// # Note
            ///
            /// - Object types containing CPUs can always be compared (usually,
            ///   a machine contains packages, which contain caches, which
            ///   contain cores, which contain PUs).
            /// - [`HWLOC_OBJ_PU`] will always be the deepest, while
            ///   [`HWLOC_OBJ_MACHINE`] is always the highest.
            /// - This does not mean that the actual topology will respect that
            ///   order: e.g. as of today cores may also contain caches, and
            ///   packages may also contain nodes. This is thus just to be seen
            ///   as a fallback comparison method.
            #[must_use]
            pub fn hwloc_compare_types(type1: hwloc_obj_type_t, type2: hwloc_obj_type_t) -> c_int;

            // === Topology creation and destruction: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__creation.html

            /// Allocate a topology context
            ///
            /// # Parameters
            ///
            /// `[out] topologyp` is assigned a pointer to the new allocated
            /// context.
            ///
            /// # Returns
            ///
            /// 0 on success, -1 on error
            #[must_use]
            pub fn hwloc_topology_init(topology: *mut hwloc_topology_t) -> c_int;

            /// Build the actual topology
            ///
            /// Build the actual topology once initialized with
            /// [`hwloc_topology_init()`] and tuned with[Topology Detection
            /// Configuration and
            /// Query](https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__configuration.html)
            /// and [Changing the Source of Topology
            /// Discovery](https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__setsource.html)
            /// routines. No other routine may be called earlier using this
            /// topology context.
            ///
            /// # Parameters
            ///
            /// `topology` is the topology to be loaded with objects.
            ///
            /// # Returns
            ///
            /// 0 on success, -1 on error
            ///
            /// # Note
            ///
            /// - On failure, the topology is reinitialized. It should be either
            ///   destroyed with [`hwloc_topology_destroy()`] or configured and
            ///   loaded again.
            /// - This function may be called only once per topology.
            /// - The binding of the current thread or process may temporarily
            ///   change during this call but it will be restored before it
            ///   returns.
            #[must_use]
            pub fn hwloc_topology_load(topology: hwloc_topology_t) -> c_int;

            /// Terminate and free a topology context
            ///
            /// # Parameters
            ///
            /// `topology` is the topology to be freed
            pub fn hwloc_topology_destroy(topology: hwloc_topology_t);

            /// Duplicate a topology
            ///
            /// The entire topology structure as well as its objects are
            /// duplicated into a new one.
            ///
            /// This is useful for keeping a backup while modifying a topology.
            ///
            /// # Returns
            ///
            /// 0 on success, -1 on error
            ///
            /// # Note
            ///
            /// Object userdata is not duplicated since hwloc does not know what
            /// it points to. The objects of both old and new topologies will
            /// point to the same userdata.
            #[must_use]
            pub fn hwloc_topology_dup(
                newtop: *mut hwloc_topology_t,
                oldtop: hwloc_const_topology_t,
            ) -> c_int;

            /// Check that this topology is compatible with the current hwloc
            /// library
            ///
            /// This is useful when using the same topology structure (in
            /// memory) in different libraries that may use different hwloc
            /// installations (for instance if one library embeds a specific
            /// version of hwloc, while another library uses a default
            /// system-wide hwloc installation).
            ///
            /// If all libraries/programs use the same hwloc installation, this
            /// function always returns 0.
            ///
            /// # Returns
            ///
            /// - `0` on success
            /// - `-1` with errno set to `EINVAL` if incompatible
            //
            // TODO: Propagate note about interprocess sharing from upstream docs
            //       once interprocess sharing is implemented.
            #[must_use]
            pub fn hwloc_topology_abi_check(topology: hwloc_const_topology_t) -> c_int;

            /// Run internal checks on a topology structure
            ///
            /// The program aborts if an inconsistency is detected in the given
            /// topology.
            ///
            /// # Parameters
            ///
            /// `topology` is the topology to be checked
            ///
            /// # Note
            ///
            /// - This routine is only useful to developers.
            /// - The input topology should have been previously loaded with
            ///   [`hwloc_topology_load()`].
            pub fn hwloc_topology_check(topology: hwloc_const_topology_t);

            // === Object levels, depths and types: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__levels.html

            #[must_use]
            pub fn hwloc_topology_get_depth(
                topology: hwloc_const_topology_t,
            ) -> hwloc_get_type_depth_e;
            #[must_use]
            pub fn hwloc_get_type_depth(
                topology: hwloc_const_topology_t,
                object_type: hwloc_obj_type_t,
            ) -> hwloc_get_type_depth_e;
            #[must_use]
            pub fn hwloc_get_memory_parents_depth(
                topology: hwloc_const_topology_t,
            ) -> hwloc_get_type_depth_e;
            #[must_use]
            pub fn hwloc_get_depth_type(
                topology: hwloc_const_topology_t,
                depth: hwloc_get_type_depth_e,
            ) -> hwloc_obj_type_t;
            #[must_use]
            pub fn hwloc_get_nbobjs_by_depth(
                topology: hwloc_const_topology_t,
                depth: hwloc_get_type_depth_e,
            ) -> c_uint;
            #[must_use]
            pub fn hwloc_get_obj_by_depth(
                topology: hwloc_const_topology_t,
                depth: hwloc_get_type_depth_e,
                idx: c_uint,
            ) -> hwloc_obj_t;

            // === Converting between object types, attributes and strings: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__object__strings.html

            #[must_use]
            pub fn hwloc_obj_type_snprintf(
                into: *mut c_char,
                size: usize,
                object: *const hwloc_obj,
                verbose: c_int,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_obj_attr_snprintf(
                into: *mut c_char,
                size: usize,
                object: *const hwloc_obj,
                separator: *const c_char,
                verbose: c_int,
            ) -> c_int;
            // NOTE: Not exposing type printf/scanf for now

            // === Consulting and adding Key-Value info attributes: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__info__attr.html

            #[must_use]
            pub fn hwloc_obj_add_info(
                obj: hwloc_obj_t,
                name: *const c_char,
                value: *const c_char,
            ) -> c_int;

            // === CPU binding: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpubinding.html

            #[must_use]
            pub fn hwloc_set_cpubind(
                topology: hwloc_const_topology_t,
                set: hwloc_const_cpuset_t,
                flags: hwloc_cpubind_flags_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_get_cpubind(
                topology: hwloc_const_topology_t,
                set: hwloc_cpuset_t,
                flags: hwloc_cpubind_flags_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_set_proc_cpubind(
                topology: hwloc_const_topology_t,
                pid: hwloc_pid_t,
                set: hwloc_const_cpuset_t,
                flags: hwloc_cpubind_flags_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_get_proc_cpubind(
                topology: hwloc_const_topology_t,
                pid: hwloc_pid_t,
                set: hwloc_cpuset_t,
                flags: hwloc_cpubind_flags_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_set_thread_cpubind(
                topology: hwloc_const_topology_t,
                thread: hwloc_thread_t,
                set: hwloc_const_cpuset_t,
                flags: hwloc_cpubind_flags_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_get_thread_cpubind(
                topology: hwloc_const_topology_t,
                pid: hwloc_thread_t,
                set: hwloc_cpuset_t,
                flags: hwloc_cpubind_flags_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_get_last_cpu_location(
                topology: hwloc_const_topology_t,
                set: hwloc_cpuset_t,
                flags: hwloc_cpubind_flags_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_get_proc_last_cpu_location(
                topology: hwloc_const_topology_t,
                pid: hwloc_pid_t,
                set: hwloc_cpuset_t,
                flags: hwloc_cpubind_flags_t,
            ) -> c_int;

            // === Memory binding: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__membinding.html

            #[must_use]
            pub fn hwloc_set_membind(
                topology: hwloc_const_topology_t,
                set: hwloc_const_bitmap_t,
                policy: hwloc_membind_policy_t,
                flags: hwloc_membind_flags_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_get_membind(
                topology: hwloc_const_topology_t,
                set: hwloc_bitmap_t,
                policy: *mut hwloc_membind_policy_t,
                flags: hwloc_membind_flags_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_set_proc_membind(
                topology: hwloc_const_topology_t,
                pid: hwloc_pid_t,
                set: hwloc_const_bitmap_t,
                policy: hwloc_membind_policy_t,
                flags: hwloc_membind_flags_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_get_proc_membind(
                topology: hwloc_const_topology_t,
                pid: hwloc_pid_t,
                set: hwloc_bitmap_t,
                policy: *mut hwloc_membind_policy_t,
                flags: hwloc_membind_flags_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_set_area_membind(
                topology: hwloc_const_topology_t,
                addr: *const c_void,
                len: usize,
                set: hwloc_const_bitmap_t,
                policy: hwloc_membind_policy_t,
                flags: hwloc_membind_flags_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_get_area_membind(
                topology: hwloc_const_topology_t,
                addr: *const c_void,
                len: usize,
                set: hwloc_bitmap_t,
                policy: *mut hwloc_membind_policy_t,
                flags: hwloc_membind_flags_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_get_area_memlocation(
                topology: hwloc_const_topology_t,
                addr: *const c_void,
                len: usize,
                set: hwloc_bitmap_t,
                flags: hwloc_membind_flags_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_alloc(topology: hwloc_const_topology_t, len: usize) -> *mut c_void;
            #[must_use]
            pub fn hwloc_alloc_membind(
                topology: hwloc_const_topology_t,
                len: usize,
                set: hwloc_const_bitmap_t,
                policy: hwloc_membind_policy_t,
                flags: hwloc_membind_flags_t,
            ) -> *mut c_void;
            #[must_use]
            pub fn hwloc_free(
                topology: hwloc_const_topology_t,
                addr: *mut c_void,
                len: usize,
            ) -> c_int;

            // === Changing the source of topology discovery: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__setsource.html

            #[must_use]
            pub fn hwloc_topology_set_pid(topology: hwloc_topology_t, pid: hwloc_pid_t) -> c_int;
            #[must_use]
            pub fn hwloc_topology_set_synthetic(
                topology: hwloc_topology_t,
                description: *const c_char,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_topology_set_xml(
                topology: hwloc_topology_t,
                xmlpath: *const c_char,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_topology_set_xmlbuffer(
                topology: hwloc_topology_t,
                buffer: *const c_char,
                size: c_int,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_1_0")]
            #[must_use]
            pub fn hwloc_topology_set_components(
                topology: hwloc_topology_t,
                flags: hwloc_topology_components_flag_e,
                name: *const c_char,
            ) -> c_int;

            // === Topology detection configuration and query: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__configuration.html

            #[must_use]
            pub fn hwloc_topology_set_flags(
                topology: hwloc_topology_t,
                flags: hwloc_topology_flags_e,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_topology_get_flags(
                topology: hwloc_const_topology_t,
            ) -> hwloc_topology_flags_e;
            #[must_use]
            pub fn hwloc_topology_is_thissystem(topology: hwloc_const_topology_t) -> c_int;
            #[must_use]
            pub fn hwloc_topology_get_support(
                topology: hwloc_const_topology_t,
            ) -> *const hwloc_topology_support;
            #[must_use]
            pub fn hwloc_topology_set_type_filter(
                topology: hwloc_topology_t,
                ty: hwloc_obj_type_t,
                filter: hwloc_type_filter_e,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_topology_get_type_filter(
                topology: hwloc_const_topology_t,
                ty: hwloc_obj_type_t,
                filter: *mut hwloc_type_filter_e,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_topology_set_all_types_filter(
                topology: hwloc_topology_t,
                filter: hwloc_type_filter_e,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_topology_set_cache_types_filter(
                topology: hwloc_topology_t,
                filter: hwloc_type_filter_e,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_topology_set_icache_types_filter(
                topology: hwloc_topology_t,
                filter: hwloc_type_filter_e,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_topology_set_io_types_filter(
                topology: hwloc_topology_t,
                filter: hwloc_type_filter_e,
            ) -> c_int;
            // NOTE: set_userdata and get_userdata are NOT exposed because they
            //       are hard to make work with copying, persistence and thread
            //       safety and are not so useful as to justify the effort.

            // === Modifying a loaded Topology: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__tinker.html

            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_topology_restrict(
                topology: hwloc_topology_t,
                set: hwloc_const_bitmap_t,
                flags: hwloc_restrict_flags_e,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_topology_allow(
                topology: hwloc_topology_t,
                cpuset: hwloc_const_cpuset_t,
                nodeset: hwloc_const_nodeset_t,
                flags: hwloc_allow_flags_e,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_topology_insert_misc_object(
                topology: hwloc_topology_t,
                parent: hwloc_obj_t,
                name: *const c_char,
            ) -> hwloc_obj_t;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_topology_alloc_group_object(topology: hwloc_topology_t) -> hwloc_obj_t;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_topology_insert_group_object(
                topology: hwloc_topology_t,
                group: hwloc_obj_t,
            ) -> hwloc_obj_t;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_obj_add_other_obj_sets(dst: hwloc_obj_t, src: *const hwloc_obj) -> c_int;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_topology_refresh(topology: hwloc_topology_t) -> c_int;

            // === Kinds of ObjectTypes: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__types.html

            #[must_use]
            pub fn hwloc_obj_type_is_normal(ty: hwloc_obj_type_t) -> c_int;
            #[must_use]
            pub fn hwloc_obj_type_is_io(ty: hwloc_obj_type_t) -> c_int;
            #[must_use]
            pub fn hwloc_obj_type_is_memory(ty: hwloc_obj_type_t) -> c_int;
            #[must_use]
            pub fn hwloc_obj_type_is_cache(ty: hwloc_obj_type_t) -> c_int;
            #[must_use]
            pub fn hwloc_obj_type_is_dcache(ty: hwloc_obj_type_t) -> c_int;
            #[must_use]
            pub fn hwloc_obj_type_is_icache(ty: hwloc_obj_type_t) -> c_int;

            // === Finding objects, miscellaneous helpers: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__find__misc.html

            #[cfg(feature = "hwloc-2_2_0")]
            #[must_use]
            pub fn hwloc_bitmap_singlify_per_core(
                topology: hwloc_const_topology_t,
                cpuset: hwloc_cpuset_t,
                which: c_uint,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_5_0")]
            #[must_use]
            pub fn hwloc_get_obj_with_same_locality(
                topology: hwloc_const_topology_t,
                src: *const hwloc_obj,
                ty: hwloc_obj_type_t,
                subtype: *const c_char,
                nameprefix: *const c_char,
                flags: c_ulong,
            ) -> *const hwloc_obj;

            // === CPU and node sets of entire topologies: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__topology__sets.html

            #[must_use]
            pub fn hwloc_topology_get_complete_cpuset(
                topology: hwloc_const_topology_t,
            ) -> hwloc_const_cpuset_t;
            #[must_use]
            pub fn hwloc_topology_get_topology_cpuset(
                topology: hwloc_const_topology_t,
            ) -> hwloc_const_cpuset_t;
            #[must_use]
            pub fn hwloc_topology_get_allowed_cpuset(
                topology: hwloc_const_topology_t,
            ) -> hwloc_const_cpuset_t;
            #[must_use]
            pub fn hwloc_topology_get_complete_nodeset(
                topology: hwloc_const_topology_t,
            ) -> hwloc_const_nodeset_t;
            #[must_use]
            pub fn hwloc_topology_get_topology_nodeset(
                topology: hwloc_const_topology_t,
            ) -> hwloc_const_nodeset_t;
            #[must_use]
            pub fn hwloc_topology_get_allowed_nodeset(
                topology: hwloc_const_topology_t,
            ) -> hwloc_const_nodeset_t;

            // === Bitmap API: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__bitmap.html

            #[must_use]
            pub fn hwloc_bitmap_alloc() -> hwloc_bitmap_t;
            #[must_use]
            pub fn hwloc_bitmap_alloc_full() -> hwloc_bitmap_t;
            pub fn hwloc_bitmap_free(bitmap: hwloc_bitmap_t);
            #[must_use]
            pub fn hwloc_bitmap_dup(src: hwloc_const_bitmap_t) -> hwloc_bitmap_t;
            #[must_use]
            pub fn hwloc_bitmap_copy(dst: hwloc_bitmap_t, src: hwloc_const_bitmap_t) -> c_int;

            #[must_use]
            pub fn hwloc_bitmap_list_snprintf(
                buf: *mut c_char,
                len: usize,
                bitmap: hwloc_const_bitmap_t,
            ) -> c_int;
            // NOTE: Not exposing other printfs and scanfs for now

            pub fn hwloc_bitmap_zero(bitmap: hwloc_bitmap_t);
            pub fn hwloc_bitmap_fill(bitmap: hwloc_bitmap_t);
            #[must_use]
            pub fn hwloc_bitmap_only(bitmap: hwloc_bitmap_t, id: c_uint) -> c_int;
            #[must_use]
            pub fn hwloc_bitmap_allbut(bitmap: hwloc_bitmap_t, id: c_uint) -> c_int;
            // NOTE: Not exposing ulong-based APIs for now, so no from_ulong, from_ith_ulong, from_ulongs
            //       If I decide to add them, gate from_ulongs with #[cfg(feature = "hwloc-2_1_0")]
            #[must_use]
            pub fn hwloc_bitmap_set(bitmap: hwloc_bitmap_t, id: c_uint) -> c_int;
            #[must_use]
            pub fn hwloc_bitmap_set_range(
                bitmap: hwloc_bitmap_t,
                begin: c_uint,
                end: c_int,
            ) -> c_int;
            // NOTE: Not exposing ulong-based APIs for now, so no set_ith_ulong
            #[must_use]
            pub fn hwloc_bitmap_clr(bitmap: hwloc_bitmap_t, id: c_uint) -> c_int;
            #[must_use]
            pub fn hwloc_bitmap_clr_range(
                bitmap: hwloc_bitmap_t,
                begin: c_uint,
                end: c_int,
            ) -> c_int;
            pub fn hwloc_bitmap_singlify(bitmap: hwloc_bitmap_t) -> c_int;
            // NOTE: Not exposing ulong-based APIs for now, so no to_ulong, to_ith_ulong, to_ulongs and nr_ulongs
            //       If I decide to add them, gate nr_ulongs and to_ulongs with #[cfg(feature = "hwloc-2_1_0")]

            #[must_use]
            pub fn hwloc_bitmap_isset(bitmap: hwloc_const_bitmap_t, id: c_uint) -> c_int;
            #[must_use]
            pub fn hwloc_bitmap_iszero(bitmap: hwloc_const_bitmap_t) -> c_int;
            #[must_use]
            pub fn hwloc_bitmap_isfull(bitmap: hwloc_const_bitmap_t) -> c_int;

            #[must_use]
            pub fn hwloc_bitmap_first(bitmap: hwloc_const_bitmap_t) -> c_int;
            #[must_use]
            pub fn hwloc_bitmap_next(bitmap: hwloc_const_bitmap_t, prev: c_int) -> c_int;
            #[must_use]
            pub fn hwloc_bitmap_last(bitmap: hwloc_const_bitmap_t) -> c_int;

            #[must_use]
            pub fn hwloc_bitmap_weight(bitmap: hwloc_const_bitmap_t) -> c_int;

            #[must_use]
            pub fn hwloc_bitmap_first_unset(bitmap: hwloc_const_bitmap_t) -> c_int;
            #[must_use]
            pub fn hwloc_bitmap_next_unset(bitmap: hwloc_const_bitmap_t, prev: c_int) -> c_int;
            #[must_use]
            pub fn hwloc_bitmap_last_unset(bitmap: hwloc_const_bitmap_t) -> c_int;

            #[must_use]
            pub fn hwloc_bitmap_or(
                result: hwloc_bitmap_t,
                bitmap1: hwloc_const_bitmap_t,
                bitmap2: hwloc_const_bitmap_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_bitmap_and(
                result: hwloc_bitmap_t,
                bitmap1: hwloc_const_bitmap_t,
                bitmap2: hwloc_const_bitmap_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_bitmap_andnot(
                result: hwloc_bitmap_t,
                bitmap1: hwloc_const_bitmap_t,
                bitmap2: hwloc_const_bitmap_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_bitmap_xor(
                result: hwloc_bitmap_t,
                bitmap1: hwloc_const_bitmap_t,
                bitmap2: hwloc_const_bitmap_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_bitmap_not(result: hwloc_bitmap_t, bitmap: hwloc_const_bitmap_t) -> c_int;

            #[must_use]
            pub fn hwloc_bitmap_intersects(
                left: hwloc_const_bitmap_t,
                right: hwloc_const_bitmap_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_bitmap_isincluded(
                left: hwloc_const_bitmap_t,
                right: hwloc_const_bitmap_t,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_bitmap_isequal(
                left: hwloc_const_bitmap_t,
                right: hwloc_const_bitmap_t,
            ) -> c_int;
            // NOTE: Not providing compare_first since it trivially follows from
            //       first_set and seems obscure.
            #[must_use]
            pub fn hwloc_bitmap_compare(
                left: hwloc_const_bitmap_t,
                right: hwloc_const_bitmap_t,
            ) -> c_int;

            // === Exporting Topologies to XML: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__xmlexport.html

            #[must_use]
            pub fn hwloc_topology_export_xml(
                topology: hwloc_const_topology_t,
                xmlpath: *const c_char,
                flags: hwloc_topology_export_xml_flags_e,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_topology_export_xmlbuffer(
                topology: hwloc_const_topology_t,
                xmlbuffer: *mut *mut c_char,
                buflen: *mut c_int,
                flags: hwloc_topology_export_xml_flags_e,
            ) -> c_int;
            pub fn hwloc_free_xmlbuffer(topology: hwloc_const_topology_t, xmlbuffer: *mut c_char);
            // NOTE: Not exposing userdata at the moment, so no need to bind
            //       associated API functions yet.

            // === Exporting Topologies to Synthetic: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__syntheticexport.html

            #[must_use]
            pub fn hwloc_topology_export_synthetic(
                topology: hwloc_const_topology_t,
                buffer: *mut c_char,
                buflen: usize,
                flags: hwloc_topology_export_synthetic_flags_e,
            ) -> c_int;

            // === Retrieve distances between objects: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__get.html

            #[must_use]
            pub fn hwloc_distances_get(
                topology: hwloc_const_topology_t,
                nr: *mut c_uint,
                distances: *mut *mut hwloc_distances_s,
                kind: hwloc_distances_kind_e,
                flags: c_ulong,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_distances_get_by_depth(
                topology: hwloc_const_topology_t,
                depth: c_int,
                nr: *mut c_uint,
                distances: *mut *mut hwloc_distances_s,
                kind: hwloc_distances_kind_e,
                flags: c_ulong,
            ) -> c_int;
            #[must_use]
            pub fn hwloc_distances_get_by_type(
                topology: hwloc_const_topology_t,
                ty: hwloc_obj_type_t,
                nr: *mut c_uint,
                distances: *mut *mut hwloc_distances_s,
                kind: hwloc_distances_kind_e,
                flags: c_ulong,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_1_0")]
            #[must_use]
            pub fn hwloc_distances_get_by_name(
                topology: hwloc_const_topology_t,
                name: *const c_char,
                nr: *mut c_uint,
                distances: *mut *mut hwloc_distances_s,
                flags: c_ulong,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_1_0")]
            #[must_use]
            pub fn hwloc_distances_get_name(
                topology: hwloc_const_topology_t,
                distances: *const hwloc_distances_s,
            ) -> *const c_char;
            pub fn hwloc_distances_release(
                topology: hwloc_const_topology_t,
                distances: *const hwloc_distances_s,
            );
            #[cfg(feature = "hwloc-2_5_0")]
            #[must_use]
            pub fn hwloc_distances_transform(
                topology: hwloc_const_topology_t,
                distances: *mut hwloc_distances_s,
                transform: hwloc_distances_transform_e,
                transform_attr: *mut c_void,
                flags: c_ulong,
            ) -> c_int;

            // === Add distances between objects: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__add.html

            #[cfg(feature = "hwloc-2_5_0")]
            #[must_use]
            pub fn hwloc_distances_add_create(
                topology: hwloc_topology_t,
                name: *const c_char,
                kind: hwloc_distances_kind_e,
                flags: c_ulong,
            ) -> hwloc_distances_add_handle_t;
            #[cfg(feature = "hwloc-2_5_0")]
            #[must_use]
            pub fn hwloc_distances_add_values(
                topology: hwloc_topology_t,
                handle: hwloc_distances_add_handle_t,
                nbobjs: c_uint,
                objs: *const *const hwloc_obj,
                values: *const u64,
                flags: c_ulong,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_5_0")]
            #[must_use]
            pub fn hwloc_distances_add_commit(
                topology: hwloc_topology_t,
                handle: hwloc_distances_add_handle_t,
                flags: hwloc_distances_add_flag_e,
            ) -> c_int;

            // === Remove distances between objects: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__remove.html

            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_distances_remove(topology: hwloc_topology_t) -> c_int;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_distances_remove_by_depth(
                topology: hwloc_topology_t,
                depth: hwloc_get_type_depth_e,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_distances_release_remove(
                topology: hwloc_topology_t,
                distances: *mut hwloc_distances_s,
            ) -> c_int;

            // === Comparing memory node attributes for finding where to allocate on: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs.html

            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_memattr_get_by_name(
                topology: hwloc_const_topology_t,
                name: *const c_char,
                id: *mut hwloc_memattr_id_t,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_get_local_numanode_objs(
                topology: hwloc_const_topology_t,
                location: *const hwloc_location,
                nr: *mut c_uint,
                nodes: *mut *const hwloc_obj,
                flags: hwloc_local_numanode_flag_e,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_memattr_get_value(
                topology: hwloc_const_topology_t,
                attribute: hwloc_memattr_id_t,
                target_node: *const hwloc_obj,
                initiator: *const hwloc_location,
                flags: c_ulong,
                value: *mut u64,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_memattr_get_best_target(
                topology: hwloc_const_topology_t,
                attribute: hwloc_memattr_id_t,
                initiator: *const hwloc_location,
                flags: c_ulong,
                best_target: *mut *const hwloc_obj,
                value: *mut u64,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_memattr_get_best_initiator(
                topology: hwloc_const_topology_t,
                attribute: hwloc_memattr_id_t,
                target: *const hwloc_obj,
                flags: c_ulong,
                best_initiator: *mut hwloc_location,
                value: *mut u64,
            ) -> c_int;

            // === Managing memory attributes: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__memattrs__manage.html

            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_memattr_get_name(
                topology: hwloc_const_topology_t,
                attribute: hwloc_memattr_id_t,
                name: *mut *const c_char,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_memattr_get_flags(
                topology: hwloc_const_topology_t,
                attribute: hwloc_memattr_id_t,
                flags: *mut hwloc_memattr_flag_e,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_memattr_register(
                topology: hwloc_const_topology_t,
                name: *const c_char,
                flags: hwloc_memattr_flag_e,
                id: *mut hwloc_memattr_id_t,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_memattr_set_value(
                topology: hwloc_const_topology_t,
                attribute: hwloc_memattr_id_t,
                target_node: *const hwloc_obj,
                initiator: *const hwloc_location,
                flags: c_ulong,
                value: u64,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_memattr_get_targets(
                topology: hwloc_const_topology_t,
                attribute: hwloc_memattr_id_t,
                initiator: *const hwloc_location,
                flags: c_ulong,
                nr: *mut c_uint,
                targets: *mut *const hwloc_obj,
                values: *mut u64,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_3_0")]
            #[must_use]
            pub fn hwloc_memattr_get_initiators(
                topology: hwloc_const_topology_t,
                attribute: hwloc_memattr_id_t,
                target_node: *const hwloc_obj,
                flags: c_ulong,
                nr: *mut c_uint,
                initiators: *mut hwloc_location,
                values: *mut u64,
            ) -> c_int;

            // === Kinds of CPU cores: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__cpukinds.html

            #[cfg(feature = "hwloc-2_4_0")]
            #[must_use]
            pub fn hwloc_cpukinds_get_nr(topology: hwloc_const_topology_t, flags: c_ulong)
                -> c_int;
            #[cfg(feature = "hwloc-2_4_0")]
            #[must_use]
            pub fn hwloc_cpukinds_get_by_cpuset(
                topology: hwloc_const_topology_t,
                cpuset: hwloc_const_cpuset_t,
                flags: c_ulong,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_4_0")]
            #[must_use]
            pub fn hwloc_cpukinds_get_info(
                topology: hwloc_const_topology_t,
                kind_index: c_uint,
                cpuset: hwloc_cpuset_t,
                efficiency: *mut c_int,
                nr_infos: *mut c_uint,
                infos: *mut *mut hwloc_info_s,
                flags: c_ulong,
            ) -> c_int;
            #[cfg(feature = "hwloc-2_4_0")]
            #[must_use]
            pub fn hwloc_cpukinds_register(
                topology: hwloc_topology_t,
                cpuset: hwloc_const_cpuset_t,
                forced_efficiency: c_int,
                nr_infos: c_uint,
                infos: *const hwloc_info_s,
                flags: c_ulong,
            ) -> c_int;

            // === Linux-specific helpers: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__linux.html

            #[cfg(any(doc, target_os = "linux"))]
            #[must_use]
            pub fn hwloc_linux_set_tid_cpubind(
                topology: hwloc_const_topology_t,
                tid: pid_t,
                set: hwloc_const_cpuset_t,
            ) -> c_int;
            #[cfg(any(doc, target_os = "linux"))]
            #[must_use]
            pub fn hwloc_linux_get_tid_cpubind(
                topology: hwloc_const_topology_t,
                tid: pid_t,
                set: hwloc_cpuset_t,
            ) -> c_int;
            #[cfg(any(doc, target_os = "linux"))]
            #[must_use]
            pub fn hwloc_linux_get_tid_last_cpu_location(
                topology: hwloc_const_topology_t,
                tid: pid_t,
                set: hwloc_cpuset_t,
            ) -> c_int;
            #[cfg(any(doc, target_os = "linux"))]
            #[must_use]
            pub fn hwloc_linux_read_path_as_cpumask(
                path: *const c_char,
                set: hwloc_cpuset_t,
            ) -> c_int;

            // NOTE: libnuma interop is waiting for higher quality libnuma bindings

            // === Windows-specific helpers: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__windows.html

            #[cfg(any(doc, all(feature = "hwloc-2_5_0", target_os = "windows")))]
            #[must_use]
            pub fn hwloc_windows_get_nr_processor_groups(
                topology: hwloc_const_topology_t,
                flags: c_ulong,
            ) -> c_int;
            #[cfg(any(doc, all(feature = "hwloc-2_5_0", target_os = "windows")))]
            #[must_use]
            pub fn hwloc_windows_get_processor_group_cpuset(
                topology: hwloc_const_topology_t,
                pg_index: c_uint,
                cpuset: hwloc_cpuset_t,
                flags: c_ulong,
            ) -> c_int;

            // NOTE: glibc interop is waiting for higher quality cpuset support
            //       in the libc crate: right now, it is not possible to safely
            //       crate a `cpu_set_t`, but functions that manipulate them
            //       expect `&mut cpu_set_t`...

            // TODO: Cover more later: interop, differences, sharing, etc...
            //       Beware that primitives that modify the topology should be
            //       exposed in the TopologyEditor, not Topology, because per
            //       hwloc documentation hwloc_topology_refresh() must be called
            //       before multithreaded access is thread-safe again.
        }
    };
}

#[cfg(all(not(feature = "bundled"), target_os = "windows"))]
extern_c_block!("libhwloc");

#[cfg(all(feature = "bundled", target_os = "windows"))]
extern_c_block!("hwloc");

#[cfg(not(target_os = "windows"))]
extern_c_block!("hwloc");

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hwloc_obj_attr_u() {
        let attr = super::hwloc_obj_attr_u {
            cache: hwloc_cache_attr_s::default(),
        };
        assert_eq!(format!("{attr:?}"), "hwloc_obj_attr_u { .. }");
    }

    #[test]
    fn hwloc_numanode_attr_s() {
        let hwloc_numanode_attr_s {
            local_memory,
            page_types_len,
            page_types,
        } = super::hwloc_numanode_attr_s::default();
        assert_eq!(local_memory, 0);
        assert_eq!(page_types_len, 0);
        assert!(page_types.is_null());
    }

    #[test]
    fn hwloc_bridge_attr_s() {
        let attr = super::hwloc_bridge_attr_s {
            upstream: RawUpstreamAttributes {
                pci: hwloc_pcidev_attr_s::default(),
            },
            upstream_type: HWLOC_OBJ_BRIDGE_PCI,
            downstream: RawDownstreamAttributes {
                pci: RawDownstreamPCIAttributes::default(),
            },
            downstream_type: HWLOC_OBJ_BRIDGE_PCI,
            depth: 0,
        };
        assert_eq!(
            format!("{attr:?}"),
            "hwloc_bridge_attr_s { upstream: RawUpstreamAttributes { .. }, \
                                   upstream_type: 1, \
                                   downstream: RawDownstreamAttributes { .. }, \
                                   downstream_type: 1, \
                                   depth: 0 }"
        );
    }

    #[test]
    fn hwloc_topology_support() {
        let default = super::hwloc_topology_support::default();
        #[cfg(not(feature = "hwloc-2_3_0"))]
        let hwloc_topology_support {
            discovery,
            cpubind,
            membind,
        } = default;
        #[cfg(feature = "hwloc-2_3_0")]
        let hwloc_topology_support {
            discovery,
            cpubind,
            membind,
            misc,
        } = default;
        assert!(discovery.is_null());
        assert!(cpubind.is_null());
        assert!(membind.is_null());
        #[cfg(feature = "hwloc-2_3_0")]
        assert!(misc.is_null());
    }

    #[test]
    fn hwloc_distances_s() {
        let hwloc_distances_s {
            nbobj,
            objs,
            kind,
            values,
        } = super::hwloc_distances_s::default();
        assert_eq!(nbobj, 0);
        assert!(objs.is_null());
        assert_eq!(kind, 0);
        assert!(values.is_null());
    }

    #[cfg(feature = "hwloc-2_3_0")]
    #[test]
    fn hwloc_location() {
        let location = super::hwloc_location {
            ty: HWLOC_LOCATION_TYPE_CPUSET,
            location: hwloc_location_u {
                cpuset: ptr::null(),
            },
        };
        assert_eq!(
            format!("{location:?}"),
            "hwloc_location { ty: 1, \
                              location: hwloc_location_u { .. } }"
        );
    }
}
