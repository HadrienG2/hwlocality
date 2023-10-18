//! Common strategies for property-based testing
//!
//! Every proptest [`Strategy`] which cannot be handled by an [`Arbitrary`] impl
//! or a function that is only used by a single module is centralized here.

use crate::bitmap::BitmapIndex;
use enum_iterator::Sequence;
use proptest::{
    collection::SizeRange,
    prelude::*,
    sample::Select,
    strategy::{Map, TupleUnion, WA},
    string::RegexGeneratorStrategy,
};
use std::{
    ffi::{c_uchar, c_uint},
    fmt::Debug,
    ops::{Range, RangeInclusive},
};

/// String generator that's actually exhaustive, unlike proptest's default
pub(crate) fn any_string() -> AnyString {
    prop::string::string_regex(".*").expect("this is a valid regex")
}

/// Strategy emitted by [`any_string()`]
pub(crate) type AnyString = RegexGeneratorStrategy<String>;

/// Generate an hwloc boolean with reasonable valid state probability
pub(crate) fn hwloc_bool() -> HwlocBool {
    prop_oneof![
        4 => prop::bool::ANY.prop_map(c_uchar::from),
        1 => 2..=c_uchar::MAX,
    ]
}

/// Strategy emitted by [`hwloc_bool()`]
pub(crate) type HwlocBool = TupleUnion<(
    WA<Map<prop::bool::Any, fn(bool) -> c_uchar>>,
    WA<RangeInclusive<c_uchar>>,
)>;

/// Generate an integer where the 0 value is special
pub(crate) fn int_special0<Int: Arbitrary + Copy>(zero: Int, one: Int, max: Int) -> IntSpecial0<Int>
where
    RangeInclusive<Int>: Strategy,
{
    prop_oneof![
        4 => one..=max,
        1 => Just(zero)
    ]
}

/// Strategy emitted by [`int_special0()`]
pub(crate) type IntSpecial0<Int> = TupleUnion<(WA<RangeInclusive<Int>>, WA<Just<Int>>)>;

/// Specialization of [`int_special0()`] for [`u64`]
pub(crate) fn u64_special0() -> IntSpecial0<u64> {
    int_special0(0, 1, u64::MAX)
}

/// Specialization of [`int_special0()`] for [`c_uint`]
pub(crate) fn uint_special0() -> IntSpecial0<c_uint> {
    int_special0(0, 1, c_uint::MAX)
}

/// Generate an hwloc enum repr with some reasonable odds of invalid value
pub(crate) fn enum_repr<Enum: Sequence, Repr: Copy + Debug + From<Enum> + TryInto<Enum>>(
    min_repr: Repr,
    max_repr: Repr,
) -> EnumRepr<Repr> {
    let valid_reprs = enum_iterator::all::<Enum>()
        .map(Repr::from)
        .collect::<Vec<_>>();
    prop_oneof![
        4 => prop::sample::select(valid_reprs),  // Valid enum repr
        1 => min_repr..=max_repr,
    ]
}

/// Strategy emitted by [`enum_repr()`]
pub(crate) type EnumRepr<Repr> = TupleUnion<(WA<Select<Repr>>, WA<RangeInclusive<Repr>>)>;

/// [`BitmapIndex`] that's generated like a container size
///
/// Many bitmap operations that take an index as a parameter have linear
/// complexity as a function of said index, and bitmaps use linear storage
/// proportional to their largest index, so it is not a good idea to use
/// truly arbitrary indices in tests. Rather, we should bias towards smaller
/// indices, like this strategy does.
pub(crate) fn bitmap_index() -> BitmapIndexStrategy {
    let max_idx = SizeRange::default().end_excl();
    (0..max_idx).prop_map(|idx| BitmapIndex::try_from(idx).unwrap_or(BitmapIndex::MAX))
}

/// Strategy emitted by [`bitmap_index()`]
pub(crate) type BitmapIndexStrategy = Map<Range<usize>, fn(usize) -> BitmapIndex>;
