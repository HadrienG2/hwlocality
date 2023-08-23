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
    /// assert_eq!(BitmapIndex::MAX.count_ones(), BitmapIndex::EFFECTIVE_BITS);
    /// ```
    pub const fn count_ones(self) -> u32 {
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
    /// assert_eq!(BitmapIndex::MIN.count_zeros(), BitmapIndex::EFFECTIVE_BITS);
    /// assert_eq!(BitmapIndex::MAX.count_zeros(), 0);
    /// ```
    pub const fn count_zeros(self) -> u32 {
        self.0.count_zeros() - 1
    }

    /// Returns the number of leading zeros in the binary representation of
    /// `self`.
    ///
    /// Depending on what you’re doing with the value, you might also be
    /// interested in the `ilog2` function which returns a consistent number,
    /// even if the type widens.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(BitmapIndex::MIN.leading_zeros(), BitmapIndex::EFFECTIVE_BITS);
    /// assert_eq!(BitmapIndex::MAX.leading_zeros(), 0);
    /// ```
    pub const fn leading_zeros(self) -> u32 {
        self.0.leading_zeros() - 1
    }

    /// Returns the number of trailing zeros in the binary representation of
    /// `self`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(BitmapIndex::MIN.trailing_zeros(), BitmapIndex::EFFECTIVE_BITS);
    /// assert_eq!(BitmapIndex::MAX.trailing_zeros(), 0);
    /// ```
    pub const fn trailing_zeros(self) -> u32 {
        if self.0 != 0 {
            self.0.trailing_zeros()
        } else {
            Self::EFFECTIVE_BITS
        }
    }

    /// Returns the number of leading ones in the binary representation of
    /// `self`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(BitmapIndex::MIN.leading_ones(), 0);
    /// assert_eq!(BitmapIndex::MAX.leading_ones(), BitmapIndex::EFFECTIVE_BITS);
    /// ```
    pub const fn leading_ones(self) -> u32 {
        (self.0 << 1).leading_ones()
    }

    /// Returns the number of trailing ones in the binary representation of
    /// `self`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(BitmapIndex::MIN.trailing_ones(), 0);
    /// assert_eq!(BitmapIndex::MAX.trailing_ones(), BitmapIndex::EFFECTIVE_BITS);
    /// ```
    pub const fn trailing_ones(self) -> u32 {
        self.0.trailing_ones()
    }

    /// Shifts the bits to the left by a specified amount, `n`, wrapping the
    /// truncated bits to the end of the resulting integer.
    ///
    /// Please note this isn’t the same operation as the `<<` shifting operator!
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(BitmapIndex::MIN.rotate_left(42), BitmapIndex::MIN);
    /// assert_eq!(BitmapIndex::MAX.rotate_left(42), BitmapIndex::MAX);
    /// ```
    pub const fn rotate_left(self, n: u32) -> Self {
        self.rotate_impl(n, true)
    }

    /// Shifts the bits to the right by a specified amount, `n`, wrapping the
    /// truncated bits to the beginning of the resulting integer.
    ///
    /// Please note this isn’t the same operation as the `>>` shifting operator!
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(BitmapIndex::MIN.rotate_right(42), BitmapIndex::MIN);
    /// assert_eq!(BitmapIndex::MAX.rotate_right(42), BitmapIndex::MAX);
    /// ```
    pub const fn rotate_right(self, n: u32) -> Self {
        self.rotate_impl(n, false)
    }

    // Common preparation of rotate_xyz operations
    #[inline]
    const fn rotate_impl(self, n: u32, left: bool) -> Self {
        // We model a rotation as the boolean OR of two bitshifts going in
        // opposite directions:
        // - The direct shift is applied to bits that are just being shifted in
        //   the direction of the rotation, in said direction.
        // - The opposite shift is applied the bits that are brought to the
        //   opposite side of the binary representation by the rotation process,
        //   pushing them in the opposite direction by the expected amount.
        let direct_shift = n % Self::EFFECTIVE_BITS;
        let opposite_shift = Self::EFFECTIVE_BITS - direct_shift;
        let (left_shift, right_shift) = if left {
            (direct_shift, opposite_shift)
        } else {
            (opposite_shift, direct_shift)
        };

        // Compute and composite the low and high order bits
        // Must mask out the high order bit to honor our expected
        // 15/31/63-bit unsigned integer semantics.
        let high_order_bits = (self.0 << left_shift) & Self::MAX.0;
        let low_order_bits = self.0 >> right_shift;
        Self(high_order_bits | low_order_bits)
    }

    // NOTE: No swap_bytes operation, the modeled integer is not made of an
    //       integral number of bytes so this operation does not make sense.

    /// Reverses the order of bits in the integer. The least significant bit
    /// becomes the most significant bit, second least-significant bit becomes
    /// second most-significant bit, etc.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(BitmapIndex::MIN.reverse_bits(), BitmapIndex::MIN);
    /// assert_eq!(BitmapIndex::MAX.reverse_bits(), BitmapIndex::MAX);
    /// ```
    pub const fn reverse_bits(self) -> Self {
        Self(self.0.reverse_bits() >> 1)
    }

    // NOTE: No (from|to)_(be|le) operation, the modeled integer is not made of
    //       an integral number of bytes so these operations do not make sense.

    /// Checked integer addition. Computes `self + rhs`, returning `None` if
    /// overflow occurred.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_add(BitmapIndex::MIN),
    ///     Some(BitmapIndex::MIN)
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_add(BitmapIndex::MAX),
    ///     Some(BitmapIndex::MAX)
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_add(BitmapIndex::MIN),
    ///     Some(BitmapIndex::MAX)
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_add(BitmapIndex::MAX),
    ///     None
    /// );
    /// ```
    pub const fn checked_add(self, rhs: Self) -> Option<Self> {
        let Some(inner) = self.0.checked_add(rhs.0) else { return None };
        Self::const_try_from_c_uint(inner)
    }

    /// Checked addition with a signed integer. Computes `self + rhs`, returning
    /// `None` if overflow occurred.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_add_signed(0),
    ///     Some(BitmapIndex::MIN)
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_add_signed(-1),
    ///     None
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_add_signed(0),
    ///     Some(BitmapIndex::MAX)
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_add_signed(1),
    ///     None
    /// );
    /// ```
    pub const fn checked_add_signed(self, rhs: isize) -> Option<Self> {
        let Some(rhs) = Self::try_c_int_from_isize(rhs) else { return None };
        let Some(inner) = self.0.checked_add_signed(rhs) else { return None };
        Self::const_try_from_c_uint(inner)
    }

    /// Try to convert from isize to c_int
    ///
    /// Will be dropped once TryFrom/TryInto is usable in const fn
    const fn try_c_int_from_isize(x: isize) -> Option<c_int> {
        if x >= c_int::MIN as isize && x <= c_int::MAX as isize {
            Some(x as c_int)
        } else {
            None
        }
    }

    /// Checked integer subtraction. Computes `self - rhs`, returning `None` if
    /// overflow occurred.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_sub(BitmapIndex::MIN),
    ///     Some(BitmapIndex::MIN)
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_sub(BitmapIndex::MAX),
    ///     None
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_sub(BitmapIndex::MIN),
    ///     Some(BitmapIndex::MAX)
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_sub(BitmapIndex::MAX),
    ///     Some(BitmapIndex::MIN)
    /// );
    /// ```
    pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
        if let Some(inner) = self.0.checked_sub(rhs.0) {
            Some(Self(inner))
        } else {
            None
        }
    }

    /// Checked integer multiplication. Computes `self * rhs`, returning `None`
    /// if overflow occurred.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_mul(BitmapIndex::MIN),
    ///     Some(BitmapIndex::MIN)
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_mul(BitmapIndex::MAX),
    ///     Some(BitmapIndex::MIN)
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_mul(BitmapIndex::MIN),
    ///     Some(BitmapIndex::MIN)
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_mul(BitmapIndex::MAX),
    ///     None
    /// );
    /// ```
    pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
        let Some(inner) = self.0.checked_mul(rhs.0) else { return None };
        Self::const_try_from_c_uint(inner)
    }

    /// Checked integer division. Computes `self / rhs`, returning `None`
    /// if `rhs == Self::MIN`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_div(BitmapIndex::MIN),
    ///     None
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_div(BitmapIndex::MAX),
    ///     Some(BitmapIndex::MIN)
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_div(BitmapIndex::MIN),
    ///     None
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_div(BitmapIndex::MAX),
    ///     BitmapIndex::try_from(1).ok()
    /// );
    /// ```
    pub const fn checked_div(self, rhs: Self) -> Option<Self> {
        if let Some(inner) = self.0.checked_div(rhs.0) {
            Some(Self(inner))
        } else {
            None
        }
    }

    /// Checked Euclidean division. Computes `self / rhs`, returning `None`
    /// if `rhs == Self::MIN`. Equivalent to integer division for this type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_div_euclid(BitmapIndex::MIN),
    ///     None
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_div_euclid(BitmapIndex::MAX),
    ///     Some(BitmapIndex::MIN)
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_div_euclid(BitmapIndex::MIN),
    ///     None
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_div_euclid(BitmapIndex::MAX),
    ///     BitmapIndex::try_from(1).ok()
    /// );
    /// ```
    pub const fn checked_div_euclid(self, rhs: Self) -> Option<Self> {
        self.checked_div(rhs)
    }

    /// Checked integer remainder. Computes `self % rhs`, returning `None`
    /// if `rhs == Self::MIN`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_rem(BitmapIndex::MIN),
    ///     None
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_rem(BitmapIndex::MAX),
    ///     Some(BitmapIndex::MIN)
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_rem(BitmapIndex::MIN),
    ///     None
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_rem(BitmapIndex::MAX),
    ///     Some(BitmapIndex::MIN)
    /// );
    /// ```
    pub const fn checked_rem(self, rhs: Self) -> Option<Self> {
        if let Some(inner) = self.0.checked_rem(rhs.0) {
            Some(Self(inner))
        } else {
            None
        }
    }

    /// Checked Euclidean remainder. Computes `self % rhs`, returning `None`
    /// if `rhs == Self::MIN`. Equivalent to integer division for this type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_rem_euclid(BitmapIndex::MIN),
    ///     None
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_rem_euclid(BitmapIndex::MAX),
    ///     Some(BitmapIndex::MIN)
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_rem_euclid(BitmapIndex::MIN),
    ///     None
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_rem_euclid(BitmapIndex::MAX),
    ///     Some(BitmapIndex::MIN)
    /// );
    /// ```
    pub const fn checked_rem_euclid(self, rhs: Self) -> Option<Self> {
        self.checked_rem(rhs)
    }

    /// Returns the logarithm of the number with respect to an arbitrary base,
    /// rounded down.
    ///
    /// This method might not be optimized owing to implementation details;
    /// `ilog2` can produce results more efficiently for base 2, and `ilog10`
    /// can produce results more efficiently for base 10.
    ///
    /// # Panics
    ///
    /// This function will panic if `self` is zero, or if `base` is less than 2.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(
    ///     BitmapIndex::MAX.ilog(BitmapIndex::MAX),
    ///     1
    /// );
    /// ```
    pub const fn ilog(self, base: Self) -> u32 {
        self.0.ilog(base.0)
    }

    /// Returns the base 2 logarithm of the number, rounded down.
    ///
    /// # Panics
    ///
    /// This function will panic if `self` is zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(
    ///     BitmapIndex::MAX.ilog2(),
    ///     BitmapIndex::EFFECTIVE_BITS - 1
    /// );
    /// ```
    pub const fn ilog2(self) -> u32 {
        self.0.ilog2()
    }

    /// Returns the base 10 logarithm of the number, rounded down.
    ///
    /// # Panics
    ///
    /// This function will panic if `self` is zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(
    ///     BitmapIndex::try_from(10).unwrap().ilog10(),
    ///     1
    /// );
    /// ```
    pub const fn ilog10(self) -> u32 {
        self.0.ilog10()
    }

    /// Returns the logarithm of the number with respect to an arbitrary base,
    /// rounded down.
    ///
    /// Returns `None` if the number is zero, or if the base is not at least 2.
    ///
    /// This method might not be optimized owing to implementation details;
    /// `checked_ilog2` can produce results more efficiently for base 2, and
    /// `checked_ilog10` can produce results more efficiently for base 10.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_ilog(BitmapIndex::MIN),
    ///     None
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_ilog(BitmapIndex::MAX),
    ///     None
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_ilog(BitmapIndex::MIN),
    ///     None
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_ilog(BitmapIndex::MAX),
    ///     Some(1)
    /// );
    /// ```
    pub const fn checked_ilog(self, base: Self) -> Option<u32> {
        self.0.checked_ilog(base.0)
    }

    /// Returns the base 2 logarithm of the number, rounded down.
    ///
    /// Returns `None` if the number is zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_ilog2(),
    ///     None
    /// );
    /// assert_eq!(
    ///     BitmapIndex::MAX.checked_ilog2(),
    ///     Some(BitmapIndex::EFFECTIVE_BITS - 1)
    /// );
    /// ```
    pub const fn checked_ilog2(self) -> Option<u32> {
        self.0.checked_ilog2()
    }

    /// Returns the base 10 logarithm of the number, rounded down.
    ///
    /// Returns `None` if the number is zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hwlocality::bitmaps::BitmapIndex;
    /// assert_eq!(
    ///     BitmapIndex::MIN.checked_ilog10(),
    ///     None
    /// );
    /// assert_eq!(
    ///     BitmapIndex::try_from(10).ok().and_then(BitmapIndex::checked_ilog10),
    ///     Some(1)
    /// );
    /// ```
    pub const fn checked_ilog10(self) -> Option<u32> {
        self.0.checked_ilog10()
    }

    // FIXME: Support more integer operations, see u16 for inspiration.
    //
    //        Don't forget traits : Add, Sub, Mul, Div, Rem, Shl, Not, with
    //        Assign and ref versions, as well as FromStr using from_str_radix.
    //        Also, Sum and Product with ref version.
    //
    //        Offsets should be isize, so Add<isize> and Sub<isize> should be a
    //        thing (unlike usize, we don't break integer literal type inference
    //        by having that).
    //
    //        Multiplicands and divisors should be unsigned since sign changes
    //        are illegal. In addition to Mul/Div/Rem ops internal to
    //        BitmapIndex, BitmapIndex * or / or % usize should be a thing.

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

    /// Const version of `try_from_c_uint`
    ///
    /// Will be dropped once TryFrom/TryInto is usable in const fn
    const fn const_try_from_c_uint(x: c_uint) -> Option<Self> {
        if x <= Self::MAX.0 {
            Some(Self(x))
        } else {
            None
        }
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
//       indexed by usize, namely to avoid integer type inference issues
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
