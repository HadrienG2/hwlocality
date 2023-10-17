#![allow(unknown_lints)]
#![doc = include_str!("../README.md")]
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
    missing_docs,
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
    clippy::print_stderr,
    clippy::use_debug,
    future_incompatible,
    keyword_idents,
    let_underscore,
    meta_variable_misuse,
    nonstandard_style,
    noop_method_call,
    rust_2018_idioms,
    unused
)]

pub mod bitmap;
pub mod cpu;
pub mod errors;
pub mod ffi;
pub mod info;
#[doc(hidden)] // Does not currently expose any public interface
pub mod interop;
pub mod memory;
pub mod object;
pub mod path;
pub mod topology;

/// Re-export `proptest` version we're built against
#[cfg(feature = "proptest")]
pub use proptest;

/// Re-export `enum_iterator` version we're built against
#[cfg(feature = "proptest")]
pub use enum_iterator;

use crate::ffi::int;
use hwlocality_sys::{hwloc_pid_t, hwloc_thread_t};
#[allow(unused)]
#[cfg(test)]
use pretty_assertions::{assert_eq, assert_ne};

/// Thread identifier (OS-specific)
///
/// This is `HANDLE` on Windows and `libc::pthread_t` on all other platforms.
pub type ThreadId = hwloc_thread_t;

/// Process identifier (OS-specific)
///
/// This is `u32` on Windows and `libc::pid_t` on all other platforms.
pub type ProcessId = hwloc_pid_t;

/// Indicate at runtime which hwloc API version was used at build time
///
/// This number is updated to `(X<<16)+(Y<<8)+Z` when a new release X.Y.Z
/// actually modifies the API.
#[doc(alias = "hwloc_get_api_version")]
pub fn hwloc_api_version() -> usize {
    // SAFETY: This hwloc entry point has no safety preconditions
    int::expect_usize(unsafe { hwlocality_sys::hwloc_get_api_version() })
}

// Disable the alias in test builds to make sure the implementation does not
// rely on it. It's better for use statements to point to the right place.
#[cfg(not(test))]
#[cfg_attr(docsrs, doc(cfg(all())))]
pub use topology::Topology;

/// This module is an implementation detail of [`Sealed`]
mod sealed {
    /// Traits with this bound can only be implemented inside this crate
    pub trait Sealed {}
}

/// Import of [`Sealed`] that only this crate can use
pub(crate) use sealed::Sealed;

/// Implement [`proptest::Arbitrary`] for a C-like enum that implements
/// [`enum_iterator::Sequence`]
#[doc(hidden)]
#[macro_export]
macro_rules! impl_arbitrary_for_sequence {
    ($sequence:ty) => {
        #[cfg(any(test, feature = "proptest"))]
        impl proptest::prelude::Arbitrary for $sequence {
            type Parameters = ();
            type Strategy = proptest::strategy::Map<std::ops::Range<usize>, fn(usize) -> Self>;

            fn arbitrary_with((): ()) -> Self::Strategy {
                use proptest::prelude::*;
                let cardinality = <Self as enum_iterator::Sequence>::CARDINALITY;
                (0..cardinality).prop_map(|idx| {
                    enum_iterator::all::<Self>()
                        .nth(idx)
                        .expect("idx is in range by definition")
                })
            }
        }
    };
}

/// Implement [`proptest::Arbitrary`] for bitflags
#[doc(hidden)]
#[macro_export]
macro_rules! impl_arbitrary_for_bitflags {
    ($flags:ty, $inner:ty) => {
        #[cfg(any(test, feature = "proptest"))]
        impl proptest::prelude::Arbitrary for $flags {
            type Parameters = ();
            type Strategy =
                proptest::strategy::Map<proptest::sample::Subsequence<Self>, fn(Vec<Self>) -> Self>;

            fn arbitrary_with((): ()) -> Self::Strategy {
                use proptest::prelude::*;
                let all_flags = Self::all().iter().collect::<Vec<_>>();
                let num_flags = all_flags.len();
                prop::sample::subsequence(all_flags, 0..num_flags)
                    .prop_map(|flags| flags.into_iter().collect::<Self>())
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused)]
    use pretty_assertions::{assert_eq, assert_ne};

    #[test]
    fn get_api_version() {
        fn api_version(major: usize, minor: usize, patch: usize) -> usize {
            (major << 16) + (minor << 8) + patch
        }
        let v3 = api_version(3, 0, 0);
        let version_range = if cfg!(feature = "hwloc-2_8_0") {
            api_version(2, 8, 0)..v3
        } else if cfg!(feature = "hwloc-2_5_0") {
            api_version(2, 5, 0)..v3
        } else if cfg!(feature = "hwloc-2_4_0") {
            api_version(2, 4, 0)..v3
        } else if cfg!(feature = "hwloc-2_3_0") {
            api_version(2, 3, 0)..v3
        } else if cfg!(feature = "hwloc-2_2_0") {
            api_version(2, 2, 0)..v3
        } else if cfg!(feature = "hwloc-2_1_0") {
            api_version(2, 1, 0)..v3
        } else if cfg!(feature = "hwloc-2_0_4") {
            api_version(2, 0, 4)..v3
        } else {
            api_version(2, 0, 0)..v3
        };
        let hwloc_version = hwloc_api_version();
        assert!(
            version_range.contains(&hwloc_version),
            "hwloc version {hwloc_version:x} is outside expected range {:x}..{:x}",
            version_range.start,
            version_range.end
        )
    }
}
