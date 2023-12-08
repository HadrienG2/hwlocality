//! Common strategies for property-based testing
//!
//! Every proptest [`Strategy`] which cannot be handled by an [`Arbitrary`] impl
//! or a function that is only used by a single module is centralized here.

use crate::bitmap::BitmapIndex;
#[cfg(test)]
use crate::{
    bitmap::{Bitmap, SpecializedBitmap},
    object::TopologyObject,
    topology::Topology,
};
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

/// Pick a random object, mostly from [`Topology::test_instance()`] but
/// sometimes from [`Topology::foreign_instance()`] as well
#[cfg(test)]
pub(crate) fn any_object() -> impl Strategy<Value = &'static TopologyObject> {
    prop_oneof![
        4 => test_object(),
        1 => prop::sample::select(Topology::foreign_objects())
    ]
}

/// Pick a random object, from the test instance only
///
/// Any method which takes an [`&TopologyObject`] as input should be robust to
/// receiving inputs from foreign topologies, so unless there is a good reason
/// to do otherwise you should prefer [`any_object()`] over [`test_object()`].
#[cfg(test)]
pub(crate) fn test_object() -> impl Strategy<Value = &'static TopologyObject> {
    prop::sample::select(Topology::test_objects())
}

/// [`CpuSet`] and [`NodeSet`] generator that is biased towards covering all
/// set-theoretically interesting configurations with respect to a `reference`
/// set that is somehow special to the function being tested:
///
/// - Empty (nothing inside, nothing outside)
/// - Disjoint (nothing inside, some outside)
/// - Complement (nothing inside, everything outside)
/// - Subset (some inside, nothing outside)
/// - Intersects (some inside, some outside)
/// - Subset complement (some inside, everything outside)
/// - Equal (everything inside, nothing outside)
/// - Superset (everything inside, some outside)
/// - Everything (everything inside, everything outside)
#[cfg(test)]
pub(crate) fn set_with_reference<Set: SpecializedBitmap>(
    ref_set: &Set,
) -> impl Strategy<Value = Set::Owned> {
    // First, one of the reference set and its complement has to be finite
    let ref_set: &Bitmap = ref_set.as_ref();
    let finite_set = if ref_set.weight().is_some() {
        ref_set.clone()
    } else {
        !ref_set
    };
    assert!(
        finite_set.weight().is_some(),
        "since bitmaps can only be infinite in one direction, \
        the complement of an infinite bitmap must be finite"
    );

    // We can define a subset of the finite set that has a fair chance of
    // covering all finite set elements and none of them + other configurations
    let finite_elems = finite_set.iter_set().collect::<Vec<_>>();
    let num_finite_elems = finite_elems.len();
    let inside_elems = prop_oneof![
        3 => prop::sample::subsequence(finite_elems.clone(), 0..=num_finite_elems),
        1 => Just(Vec::new()),
        1 => Just(finite_elems)
    ]
    .prop_map(|seq| seq.into_iter().collect::<Bitmap>());

    // Next we can pick a random set within the complement of the finite set by
    // picking a random set and subtracting the finite set from it
    let outside_elems = any::<Bitmap>().prop_map(move |any_elems| any_elems - &finite_set);

    // By combining these two sets which each have good coverage of all three
    // (nothing inside, some inside, everything inside) configurations of their
    // reference set, we get good coverage of all desired set configurations
    (inside_elems, outside_elems)
        .prop_map(|(inside_elems, outside_elems)| Set::Owned::from(inside_elems | outside_elems))
}
