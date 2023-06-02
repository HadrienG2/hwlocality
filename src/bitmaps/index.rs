//! Facilities for indexing bitmaps

use crate::ffi::{self};
#[cfg(doc)]
use crate::{
    cpu::cpusets::CpuSet,
    memory::nodesets::NodeSet,
    objects::TopologyObject,
    topology::{builder::BuildFlags, Topology},
};
use derive_more::{
    Binary, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Display, Div,
    DivAssign, LowerExp, LowerHex, Octal, Rem, RemAssign, Shr, ShrAssign, UpperExp, UpperHex,
};
#[cfg(any(test, feature = "quickcheck"))]
use quickcheck::{Arbitrary, Gen};
#[cfg(any(test, feature = "quickcheck"))]
use rand::Rng;
use std::{
    clone::Clone,
    cmp::Ordering,
    convert::TryFrom,
    ffi::{c_int, c_uint},
    fmt::Debug,
    num::{ParseIntError, TryFromIntError},
    ops::Not,
};

/// Bitmap indices can range from 0 to an implementation-defined limit
///
/// The limit is the upper bound of C's int type. On all platforms currently
/// supported by Rust, it is at least 32767 (2^15-1), and outside of exotic
/// 16-bit hardware, it will usually be greater than 2147483647 (2^31-1).
///
/// An alternate way to view BitmapIndex is as the intersection of integer
/// values permitted by C's int and unsigned int types.
#[derive(
    Binary,
    BitAnd,
    BitAndAssign,
    BitOr,
    BitOrAssign,
    BitXor,
    BitXorAssign,
    Clone,
    Copy,
    Debug,
    Default,
    Display,
    Div,
    DivAssign,
    Eq,
    Hash,
    LowerExp,
    LowerHex,
    Octal,
    Ord,
    PartialEq,
    PartialOrd,
    Rem,
    RemAssign,
    Shr,
    ShrAssign,
    UpperExp,
    UpperHex,
)]
pub struct BitmapIndex(c_uint);
//
impl BitmapIndex {
    /// The smallest value that can be used as a bitmap index
    pub const MIN: Self = Self(0);

    /// The largest value that can be used as a bitmap index
    pub const MAX: Self = Self(c_int::MAX as c_uint);

    /// Effective size of this integer type in bits
    ///
    /// The actual storage uses more bits for hardware reasons, which is why
    /// this is not called BITS like the other integer::BITS as that could be
    /// misinterpreted by careless users.
    pub const EFFECTIVE_BITS: u32 = c_int::BITS - 1;

    /// Converts a string slice in a given base to an integer
    ///
    /// The string is expected to be an optional `+` sign followed by digits.
    /// Leading and trailing whitespace represent an error. Digits are a subset
    /// of these characters, depending on `radix`:
    ///
    /// * `0-9`
    /// * `a-z`
    /// * `A-Z`
    ///
    /// # Panics
    ///
    /// This function panics if `radix` is not in the range from 2 to 36.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(BitmapIndex::from_str_radix("0", 16), Ok(BitmapIndex::MIN));
    /// ```
    pub fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        // This convoluted impl is needed because I can't construct ParseIntError
        c_int::from_str_radix(src, radix).and_then(|_| c_uint::from_str_radix(src, radix).map(Self))
    }

    /// Returns the number of ones in the binary representation of `self`
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(BitmapIndex::MIN.count_ones(), 0);
    /// ```
    pub fn count_ones(self) -> u32 {
        self.0.count_ones()
    }

    /// Returns the number of zeros in the binary representation of `self`
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(BitmapIndex::MAX.count_zeros(), 0);
    /// ```
    pub fn count_zeros(self) -> u32 {
        self.0.count_zeros() - 1
    }

    // FIXME: Support more integer operations, see usize for inspiration. Don't
    //        forget Add, Sub, Mul, Shl, with Assign and ref versions, as well
    //        as FromStr (using from_str_radix), Sum and Product with ref versions,

    /// Like [`uN::checked_add(1)`], but enforces bitmap index limits
    pub const fn checked_succ(self) -> Option<Self> {
        if self.0 < Self::MAX.0 {
            Some(Self(self.0 + 1))
        } else {
            None
        }
    }

    /// Like [`uN::checked_sub(1)`], but enforces bitmap index limits
    pub const fn checked_pred(self) -> Option<Self> {
        if let Some(res) = self.0.checked_sub(1) {
            Some(Self(res))
        } else {
            None
        }
    }

    /// Convert from an hwloc-originated c_int
    ///
    /// This is not a TryFrom implementation because that would make Bitmap
    /// indexing accept negative indexing without a compile-time error.
    pub(crate) fn try_from_c_int(x: c_int) -> Result<Self, TryFromIntError> {
        x.try_into().map(Self)
    }

    /// Convert from an hwloc-originated c_uint
    ///
    /// This is not a TryFrom implementation because it would lead integer
    /// type inference to fall back to i32 in bitmap indexing, which is
    /// undesirable. Also, I'd rather avoid having an implementation-specific
    /// type in a public API like TryFrom...
    #[allow(unused)]
    fn try_from_c_uint(x: c_uint) -> Result<Self, TryFromIntError> {
        Self::try_from_c_int(x.try_into()?)
    }

    /// Convert into a c_int (okay by construction)
    pub(crate) fn into_c_int(self) -> c_int {
        self.0 as _
    }

    /// Convert into a c_uint (okay by construction)
    pub(crate) fn into_c_uint(self) -> c_uint {
        self.0
    }
}

#[cfg(any(test, feature = "quickcheck"))]
impl Arbitrary for BitmapIndex {
    fn arbitrary(g: &mut Gen) -> Self {
        // Many index-based hwloc APIs exhibit O(n) behavior depending on which
        // index is passed as input, so we enforce that indices used in tests
        // are "not too big", as per the quickcheck size parameter
        let mut rng = rand::thread_rng();
        let max = Self::try_from(g.size()).unwrap_or(Self::MAX);
        let value = rng.gen_range(0..max.0);
        Self(value)
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(
            self.0
                .shrink()
                .filter_map(|x: c_uint| Self::try_from_c_uint(x).ok()),
        )
    }
}

// NOTE: Guaranteed to succeed because C mandates that int is >=16 bits
//       u16 would not work because it allows u16::MAX > i16::MAX.
//       Not implementing From<u8> to avoid messing with integer type inference.
impl From<bool> for BitmapIndex {
    fn from(x: bool) -> Self {
        Self(x.into())
    }
}

// NOTE: Assumed to work, otherwise the whole premise of allowing users to use
//       usize instead of c_int for indexing falls flat.
impl From<BitmapIndex> for usize {
    fn from(x: BitmapIndex) -> usize {
        ffi::expect_usize(x.0)
    }
}

impl Not for BitmapIndex {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self(self.0 ^ Self::MAX.0)
    }
}
//
impl Not for &BitmapIndex {
    type Output = BitmapIndex;

    fn not(self) -> Self::Output {
        !*self
    }
}

impl PartialEq<usize> for BitmapIndex {
    fn eq(&self, other: &usize) -> bool {
        usize::from(*self) == *other
    }
}

impl PartialOrd<usize> for BitmapIndex {
    fn partial_cmp(&self, other: &usize) -> Option<Ordering> {
        usize::from(*self).partial_cmp(other)
    }
}

// NOTE: Only implementing TryFrom<usize> for the same reason slices can only be
//       indexed by usize, namely to avoid integer type inference fuck-up
impl TryFrom<usize> for BitmapIndex {
    type Error = TryFromIntError;

    fn try_from(value: usize) -> Result<Self, TryFromIntError> {
        Self::try_from_c_int(value.try_into()?)
    }
}

macro_rules! try_into {
    ( $( $int:ty ),* ) => { $(
        impl TryFrom<BitmapIndex> for $int {
            type Error = TryFromIntError;

            #[allow(clippy::needless_question_mark)]
            fn try_from(value: BitmapIndex) -> Result<Self, TryFromIntError> {
                Ok(value.0.try_into()?)
            }
        }
    )* };
}
//
try_into!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128);

// FIXME: Add tests
