//! [`c_int`]-related concerns
//!
//! As an idiomatic C API, hwloc uses the `int` C type, which unfortunately
//! comes with various type-safety problems :
//!
//! - The C specification does not define its size, and thus its range
//! - It is commonly used in a pattern where only positive values and _some_
//!   negative values are accepted
//!
//! Further, attempting to use [`c_int`] in a type-safe language like Rust comes
//! with the extra woe of needing some sort of explicit type conversion from
//! whichever idiomatic integer type you were actually using.
//!
//! All these things being considered, it is probably best to design Rust
//! bindings in terms of either [`isize`]/[`usize`] (more idiomatic, less
//! type-safe) or a type that models the set of positive [`c_int`] values
//! (more type-safe, less idiomatic), possibly extended into an enum to account
//! for the negative special values that any given API may accept.
//!
//! This module helps you implement both of these strategies.

use derive_more::{Binary, Display, LowerExp, LowerHex, Octal, UpperExp, UpperHex};
#[allow(unused)]
#[cfg(test)]
use pretty_assertions::{assert_eq, assert_ne};
#[cfg(any(test, feature = "quickcheck"))]
use quickcheck::{Arbitrary, Gen};
#[cfg(any(test, feature = "quickcheck"))]
use rand::Rng;
#[cfg(doc)]
use std::ops::{Range, RangeFrom, RangeInclusive};
use std::{
    borrow::Borrow,
    clone::Clone,
    cmp::Ordering,
    convert::TryFrom,
    ffi::{c_int, c_uint},
    fmt::Debug,
    iter::{FusedIterator, Product, Sum},
    num::{ParseIntError, TryFromIntError},
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
    str::FromStr,
};

/// Assert that a [`c_int`] can be converted to a [`isize`]
///
/// As far as I can tell, this is only false on very weird platforms that aren't
/// supported by hwloc. However, counter-examples are welcome!
pub(crate) fn expect_isize(x: c_int) -> isize {
    x.try_into()
        .expect("Expected on any platform supported by hwloc")
}

/// Assert that a [`c_uint`] can be converted to a [`usize`]
///
/// As far as I can tell, this is only false on very weird platforms that aren't
/// supported by hwloc. However, counter-examples are welcome!
pub(crate) fn expect_usize(x: c_uint) -> usize {
    x.try_into()
        .expect("Expected on any platform supported by hwloc")
}

/// Integer ranging from 0 to the implementation-defined [`c_int::MAX`] limit
///
/// On all platforms currently supported by Rust, the upper limit is at least
/// 32767 (`2^15-1`). If we leave aside the edge case of 16-bit hardware, it
/// will usually be equal to 2147483647 (`2^31-1`), but could potentially be
/// greater.
///
/// # External operators
///
/// Almost all binary operators have an overload with exactly one of isize or
/// usize (depending on whether a negative operand makes sense) in order to
/// allow them to be used with integer literals without the type inference
/// errors that implementations for multiple integer types would bring.
///
/// The exception is left and right shifts: following the example of primitive
/// integer types, we overload these for all integer types and references
/// thereof.
///
/// Like primitive integer types, we overload all arithmetic operators for
/// references and values of each operand type for convenience. This
/// convenience does not extend to non-arithmetic operations like type
/// conversions and comparisons.
///
/// Assuming a binary operator `A op B` is defined for two different types A and
/// B, we also define `B op A` if both operands play a symmetric role. We do
/// not generally do so otherwise as the result could be confusing (e.g. it
/// seems fair to expect `PositiveInt << usize` to be a `PositiveInt`, but by
/// the same logic `usize << PositiveInt` should be an `usize`, not a
/// `PositiveInt`).
#[derive(
    Binary,
    Clone,
    Copy,
    Debug,
    Default,
    Display,
    Eq,
    Hash,
    LowerExp,
    LowerHex,
    Octal,
    Ord,
    PartialEq,
    PartialOrd,
    UpperExp,
    UpperHex,
)]
pub struct PositiveInt(c_uint);
//
impl PositiveInt {
    /// The smallest value of this integer type
    pub const MIN: Self = Self(0);

    /// The zero of this integer type
    pub const ZERO: Self = Self(0);

    /// The 1 of this integer type
    pub const ONE: Self = Self(1);

    /// The largest value of this integer type
    pub const MAX: Self = Self(c_int::MAX as c_uint);

    /// Effective size of this integer type in bits
    ///
    /// The actual storage uses more bits for hardware reasons, which is why
    /// this is not called `BITS` like the other `integer::BITS` as such naming
    /// could be misinterpreted by careless users.
    pub const EFFECTIVE_BITS: u32 = c_uint::BITS - 1;

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
    /// # Errors
    ///
    /// [`ParseIntError`] if `src` is not a base-`radix` number smaller than
    /// `PositiveInt::MAX`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(PositiveInt::from_str_radix("0", 16), Ok(PositiveInt::ZERO));
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(PositiveInt::ZERO.count_ones(), 0);
    /// assert_eq!(PositiveInt::ONE.count_ones(), 1);
    /// assert_eq!(PositiveInt::MAX.count_ones(), PositiveInt::EFFECTIVE_BITS);
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(PositiveInt::ZERO.count_zeros(), PositiveInt::EFFECTIVE_BITS);
    /// assert_eq!(PositiveInt::ONE.count_zeros(), PositiveInt::EFFECTIVE_BITS - 1);
    /// assert_eq!(PositiveInt::MAX.count_zeros(), 0);
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(PositiveInt::ZERO.leading_zeros(), PositiveInt::EFFECTIVE_BITS);
    /// assert_eq!(PositiveInt::ONE.leading_zeros(), PositiveInt::EFFECTIVE_BITS - 1);
    /// assert_eq!(PositiveInt::MAX.leading_zeros(), 0);
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(PositiveInt::ZERO.trailing_zeros(), PositiveInt::EFFECTIVE_BITS);
    /// assert_eq!(PositiveInt::ONE.trailing_zeros(), 0);
    /// assert_eq!(PositiveInt::MAX.trailing_zeros(), 0);
    /// ```
    pub const fn trailing_zeros(self) -> u32 {
        if self.0 == 0 {
            Self::EFFECTIVE_BITS
        } else {
            self.0.trailing_zeros()
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(PositiveInt::ZERO.leading_ones(), 0);
    /// assert_eq!(PositiveInt::ONE.leading_ones(), 0);
    /// assert_eq!(PositiveInt::MAX.leading_ones(), PositiveInt::EFFECTIVE_BITS);
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(PositiveInt::ZERO.trailing_ones(), 0);
    /// assert_eq!(PositiveInt::ONE.trailing_ones(), 1);
    /// assert_eq!(PositiveInt::MAX.trailing_ones(), PositiveInt::EFFECTIVE_BITS);
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.rotate_left(129),
    ///     PositiveInt::ZERO
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.rotate_left(129),
    ///     PositiveInt::ONE << (129 % PositiveInt::EFFECTIVE_BITS)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.rotate_left(129),
    ///     PositiveInt::MAX
    /// );
    /// ```
    pub const fn rotate_left(self, n: u32) -> Self {
        self.rotate_impl::<true>(n)
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.rotate_right(129),
    ///     PositiveInt::ZERO
    /// );
    /// let effective_rotate = 129 % PositiveInt::EFFECTIVE_BITS;
    /// assert_eq!(
    ///     PositiveInt::ONE.rotate_right(129),
    ///     PositiveInt::ONE << (PositiveInt::EFFECTIVE_BITS - effective_rotate)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.rotate_right(129),
    ///     PositiveInt::MAX
    /// );
    /// ```
    pub const fn rotate_right(self, n: u32) -> Self {
        self.rotate_impl::<false>(n)
    }

    /// Common preparation of `rotate_xyz` operations
    const fn rotate_impl<const LEFT: bool>(self, n: u32) -> Self {
        // We model a rotation as the boolean OR of two bitshifts going in
        // opposite directions:
        // - The direct shift is applied to bits that are just being shifted in
        //   the direction of the rotation, in said direction.
        // - The opposite shift is applied the bits that are brought to the
        //   opposite side of the binary representation by the rotation process,
        //   pushing them in the opposite direction by the expected amount.
        let direct_shift = n % Self::EFFECTIVE_BITS;
        let opposite_shift = Self::EFFECTIVE_BITS - direct_shift;
        let (left_shift, right_shift) = if LEFT {
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.reverse_bits(),
    ///     PositiveInt::ZERO
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.reverse_bits(),
    ///     PositiveInt::ONE << PositiveInt::EFFECTIVE_BITS - 1
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.reverse_bits(),
    ///     PositiveInt::MAX
    /// );
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_add(PositiveInt::ZERO),
    ///     Some(PositiveInt::ZERO)
    /// );
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_add(PositiveInt::MAX),
    ///     Some(PositiveInt::MAX)
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.checked_add(PositiveInt::ONE),
    ///     PositiveInt::try_from(2).ok()
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.checked_add(PositiveInt::MAX),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_add(PositiveInt::ZERO),
    ///     Some(PositiveInt::MAX)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_add(PositiveInt::ONE),
    ///     None
    /// );
    /// ```
    pub const fn checked_add(self, rhs: Self) -> Option<Self> {
        // Even int::MAX + int::MAX fits in our inner uint
        Self::const_try_from_c_uint(self.0 + rhs.0)
    }

    /// Checked addition with a signed integer. Computes `self + rhs`, returning
    /// `None` if overflow occurred.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_add_signed(0),
    ///     Some(PositiveInt::ZERO)
    /// );
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_add_signed(1),
    ///     Some(PositiveInt::ONE)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MIN.checked_add_signed(-1),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_add_signed(0),
    ///     Some(PositiveInt::MAX)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_add_signed(1),
    ///     None
    /// );
    /// ```
    pub const fn checked_add_signed(self, rhs: isize) -> Option<Self> {
        let Some(rhs) = Self::try_c_int_from_isize(rhs) else {
            return None;
        };
        let Some(inner) = self.0.checked_add_signed(rhs) else {
            return None;
        };
        Self::const_try_from_c_uint(inner)
    }

    /// Try to convert from [`isize`] to [`c_int`]
    ///
    /// Will be dropped once [`TryFrom`]/[`TryInto`] is usable in const fn
    #[allow(clippy::cast_possible_truncation, clippy::if_then_some_else_none)]
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_sub(PositiveInt::ZERO),
    ///     Some(PositiveInt::ZERO)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MIN.checked_sub(PositiveInt::ONE),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_sub(PositiveInt::ZERO),
    ///     Some(PositiveInt::MAX)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_sub(PositiveInt::MAX),
    ///     Some(PositiveInt::ZERO)
    /// );
    /// ```
    #[allow(clippy::if_then_some_else_none)]
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_mul(PositiveInt::ONE),
    ///     Some(PositiveInt::ZERO)
    /// );
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_mul(PositiveInt::MAX),
    ///     Some(PositiveInt::ZERO)
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.checked_mul(PositiveInt::ONE),
    ///     Some(PositiveInt::ONE)
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.checked_mul(PositiveInt::MAX),
    ///     Some(PositiveInt::MAX)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_mul(PositiveInt::ZERO),
    ///     Some(PositiveInt::ZERO)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_mul(PositiveInt::MAX),
    ///     None
    /// );
    /// ```
    pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
        if let Some(inner) = self.0.checked_mul(rhs.0) {
            Self::const_try_from_c_uint(inner)
        } else {
            None
        }
    }

    /// Checked integer division. Computes `self / rhs`, returning `None`
    /// if `rhs == Self::ZERO`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_div(PositiveInt::ZERO),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_div(PositiveInt::ONE),
    ///     Some(PositiveInt::ZERO)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_div(PositiveInt::ZERO),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_div(PositiveInt::MAX),
    ///     Some(PositiveInt::ONE)
    /// );
    /// ```
    #[allow(clippy::if_then_some_else_none)]
    pub const fn checked_div(self, rhs: Self) -> Option<Self> {
        if let Some(inner) = self.0.checked_div(rhs.0) {
            Some(Self(inner))
        } else {
            None
        }
    }

    /// Checked Euclidean division. Computes `self / rhs`, returning `None`
    /// if `rhs == Self::ZERO`. Equivalent to integer division for this type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_div_euclid(PositiveInt::ZERO),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_div_euclid(PositiveInt::ONE),
    ///     Some(PositiveInt::ZERO)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_div_euclid(PositiveInt::ZERO),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_div_euclid(PositiveInt::MAX),
    ///     Some(PositiveInt::ONE)
    /// );
    /// ```
    pub const fn checked_div_euclid(self, rhs: Self) -> Option<Self> {
        self.checked_div(rhs)
    }

    /// Checked integer remainder. Computes `self % rhs`, returning `None`
    /// if `rhs == Self::ZERO`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_rem(PositiveInt::ZERO),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_rem(PositiveInt::ONE),
    ///     Some(PositiveInt::ZERO)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_rem(PositiveInt::ZERO),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_rem(PositiveInt::MAX),
    ///     Some(PositiveInt::ZERO)
    /// );
    /// ```
    #[allow(clippy::if_then_some_else_none)]
    pub const fn checked_rem(self, rhs: Self) -> Option<Self> {
        if let Some(inner) = self.0.checked_rem(rhs.0) {
            Some(Self(inner))
        } else {
            None
        }
    }

    /// Checked Euclidean remainder. Computes `self % rhs`, returning `None`
    /// if `rhs == Self::ZERO`. Equivalent to integer remainder for this type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_rem_euclid(PositiveInt::ZERO),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_rem_euclid(PositiveInt::ONE),
    ///     Some(PositiveInt::ZERO)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_rem_euclid(PositiveInt::ZERO),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_rem_euclid(PositiveInt::MAX),
    ///     Some(PositiveInt::ZERO)
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ONE.ilog(PositiveInt::MAX),
    ///     0
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.ilog(PositiveInt::MAX),
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ONE.ilog2(),
    ///     0
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.ilog2(),
    ///     PositiveInt::EFFECTIVE_BITS - 1
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ONE.ilog10(),
    ///     0
    /// );
    /// assert_eq!(
    ///     PositiveInt::try_from(100).unwrap().ilog10(),
    ///     2
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_ilog(PositiveInt::ONE),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.checked_ilog(PositiveInt::MAX),
    ///     Some(0)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_ilog(PositiveInt::ZERO),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_ilog(PositiveInt::MAX),
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_ilog2(),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.checked_ilog2(),
    ///     Some(0)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_ilog2(),
    ///     Some(PositiveInt::EFFECTIVE_BITS - 1)
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
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_ilog10(),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.checked_ilog10(),
    ///     Some(0)
    /// );
    /// assert_eq!(
    ///     PositiveInt::try_from(100).ok().and_then(PositiveInt::checked_ilog10),
    ///     Some(2)
    /// );
    /// ```
    pub const fn checked_ilog10(self) -> Option<u32> {
        self.0.checked_ilog10()
    }

    /// Checked negation. Computes `-self`, returning `None` unless `self == 0`.
    ///
    /// Note that negating any positive integer will overflow.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_neg(),
    ///     Some(PositiveInt::ZERO)
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.checked_neg(),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_neg(),
    ///     None
    /// );
    /// ```
    #[allow(clippy::if_then_some_else_none)]
    pub const fn checked_neg(self) -> Option<Self> {
        if self.0 == 0 {
            Some(Self(0))
        } else {
            None
        }
    }

    /// Checked shift left. Computes `self << rhs`, returning `None` if `rhs` is
    /// larger than or equal to `Self::EFFECTIVE_BITS`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_shl(1),
    ///     Some(PositiveInt::ZERO)
    /// );
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_shl(PositiveInt::EFFECTIVE_BITS),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.checked_shl(1),
    ///     PositiveInt::try_from(2).ok()
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_shl(0),
    ///     Some(PositiveInt::MAX)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_shl(1),
    ///     Some((PositiveInt::MAX / 2) * 2)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_shl(PositiveInt::EFFECTIVE_BITS),
    ///     None
    /// );
    /// ```
    #[allow(clippy::if_then_some_else_none)]
    pub const fn checked_shl(self, rhs: u32) -> Option<Self> {
        if rhs < Self::EFFECTIVE_BITS {
            Some(Self((self.0 << rhs) & Self::MAX.0))
        } else {
            None
        }
    }

    /// Checked shift right. Computes `self >> rhs`, returning `None` if `rhs`
    /// is larger than or equal to `Self::EFFECTIVE_BITS`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_shr(1),
    ///     Some(PositiveInt::ZERO)
    /// );
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_shr(PositiveInt::EFFECTIVE_BITS),
    ///     None
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.checked_shr(1),
    ///     Some(PositiveInt::ZERO)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_shr(0),
    ///     Some(PositiveInt::MAX)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_shr(1),
    ///     Some(PositiveInt::MAX / 2)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_shr(PositiveInt::EFFECTIVE_BITS),
    ///     None
    /// );
    /// ```
    #[allow(clippy::if_then_some_else_none)]
    pub const fn checked_shr(self, rhs: u32) -> Option<Self> {
        if rhs < Self::EFFECTIVE_BITS {
            Some(Self(self.0 >> rhs))
        } else {
            None
        }
    }

    /// Checked exponentiation. Computes `self.pow(exp)`, returning `None` if
    /// overflow occurred.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_pow(0),
    ///     Some(PositiveInt::ONE)
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.checked_pow(3),
    ///     Some(PositiveInt::ONE)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_pow(1),
    ///     Some(PositiveInt::MAX)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_pow(2),
    ///     None
    /// );
    /// ```
    #[allow(clippy::if_then_some_else_none)]
    pub const fn checked_pow(self, exp: u32) -> Option<Self> {
        if let Some(inner) = self.0.checked_pow(exp) {
            Self::const_try_from_c_uint(inner)
        } else {
            None
        }
    }

    /// Saturating integer addition. Computes `self + rhs`, saturating at the
    /// numeric bounds instead of overflowing.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::MIN.saturating_add(PositiveInt::ZERO),
    ///     PositiveInt::MIN
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.saturating_add(PositiveInt::ZERO),
    ///     PositiveInt::ONE
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.saturating_add(PositiveInt::MAX),
    ///     PositiveInt::MAX
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.saturating_add(PositiveInt::MAX),
    ///     PositiveInt::MAX
    /// );
    /// ```
    pub const fn saturating_add(self, rhs: Self) -> Self {
        let inner = self.0.saturating_add(rhs.0);
        Self::const_sat_from_c_uint(inner)
    }

    /// Saturating addition with a signed integer. Computes `self + rhs`,
    /// saturating at the numeric bounds instead of overflowing.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::MIN.saturating_add_signed(0),
    ///     PositiveInt::MIN
    /// );
    /// assert_eq!(
    ///     PositiveInt::MIN.saturating_add_signed(-1),
    ///     PositiveInt::MIN
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.saturating_add_signed(0),
    ///     PositiveInt::MAX
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.saturating_add_signed(1),
    ///     PositiveInt::MAX
    /// );
    /// ```
    #[allow(
        clippy::cast_possible_truncation,
        clippy::missing_docs_in_private_items
    )]
    pub const fn saturating_add_signed(self, rhs: isize) -> Self {
        const C_INT_MIN: isize = c_int::MIN as isize;
        const C_INT_MAX: isize = c_int::MAX as isize;
        let rhs = match rhs {
            C_INT_MIN..=C_INT_MAX => rhs as c_int,
            under if under < 0 => c_int::MIN,
            _over => c_int::MAX,
        };
        let inner = self.0.saturating_add_signed(rhs);
        Self::const_sat_from_c_uint(inner)
    }

    /// Saturating integer subtraction. Computes `self - rhs`, saturating at the
    /// numeric bounds instead of overflowing.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::MIN.saturating_sub(PositiveInt::ZERO),
    ///     PositiveInt::MIN
    /// );
    /// assert_eq!(
    ///     PositiveInt::MIN.saturating_sub(PositiveInt::MAX),
    ///     PositiveInt::MIN
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.saturating_sub(PositiveInt::ZERO),
    ///     PositiveInt::MAX
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.saturating_sub(PositiveInt::MAX),
    ///     PositiveInt::ZERO
    /// );
    /// ```
    pub const fn saturating_sub(self, rhs: Self) -> Self {
        Self(self.0.saturating_sub(rhs.0))
    }

    /// Saturating integer multiplication. Computes `self * rhs`, saturating at
    /// the numeric bounds instead of overflowing.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.saturating_mul(PositiveInt::ZERO),
    ///     PositiveInt::ZERO
    /// );
    /// assert_eq!(
    ///     PositiveInt::ZERO.saturating_mul(PositiveInt::MAX),
    ///     PositiveInt::ZERO
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.saturating_mul(PositiveInt::ONE),
    ///     PositiveInt::MAX
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.saturating_mul(PositiveInt::MAX),
    ///     PositiveInt::MAX
    /// );
    /// ```
    pub const fn saturating_mul(self, rhs: Self) -> Self {
        let inner = self.0.saturating_mul(rhs.0);
        Self::const_sat_from_c_uint(inner)
    }

    /// Saturating integer division. Identical to `self / rhs` for this
    /// unsigned integer type
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ONE.saturating_div(PositiveInt::MAX),
    ///     PositiveInt::ZERO
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.saturating_div(PositiveInt::MAX),
    ///     PositiveInt::ONE
    /// );
    /// ```
    pub const fn saturating_div(self, rhs: Self) -> Self {
        Self(self.0 / rhs.0)
    }

    /// Saturating integer exponentiation. Computes `self.pow(rhs)`, saturating
    /// at the numeric bounds instead of overflowing.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.saturating_pow(0),
    ///     PositiveInt::ONE
    /// );
    /// assert_eq!(
    ///     PositiveInt::ZERO.saturating_pow(2),
    ///     PositiveInt::ZERO
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.saturating_pow(3),
    ///     PositiveInt::ONE
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.saturating_pow(1),
    ///     PositiveInt::MAX
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.saturating_pow(2),
    ///     PositiveInt::MAX
    /// );
    /// ```
    pub const fn saturating_pow(self, exp: u32) -> Self {
        let inner = self.0.saturating_pow(exp);
        Self::const_sat_from_c_uint(inner)
    }

    /// Saturating version of [`const_try_from_c_uint()`]
    const fn const_sat_from_c_uint(inner: c_uint) -> Self {
        if inner <= Self::MAX.0 {
            Self(inner)
        } else {
            Self::MAX
        }
    }

    /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at
    /// the boundary of the type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.wrapping_add(PositiveInt::ZERO),
    ///     PositiveInt::ZERO
    /// );
    /// assert_eq!(
    ///     PositiveInt::ZERO.wrapping_add(PositiveInt::MAX),
    ///     PositiveInt::MAX
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.wrapping_add(PositiveInt::MAX),
    ///     PositiveInt::ZERO
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_add(PositiveInt::ZERO),
    ///     PositiveInt::MAX
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_add(PositiveInt::MAX),
    ///     PositiveInt::MAX - 1
    /// );
    /// ```
    pub const fn wrapping_add(self, rhs: Self) -> Self {
        Self(self.0.wrapping_add(rhs.0) & Self::MAX.0)
    }

    /// Wrapping (modular) addition with a signed integer. Computes `self +
    /// rhs`, wrapping around at the boundary of the type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::MIN.wrapping_add_signed(0),
    ///     PositiveInt::MIN
    /// );
    /// assert_eq!(
    ///     PositiveInt::MIN.wrapping_add_signed(-1),
    ///     PositiveInt::MAX
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_add_signed(0),
    ///     PositiveInt::MAX
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_add_signed(1),
    ///     PositiveInt::MIN
    /// );
    /// ```
    #[allow(clippy::cast_possible_truncation)]
    pub const fn wrapping_add_signed(self, rhs: isize) -> Self {
        Self(self.0.wrapping_add_signed(rhs as c_int) & Self::MAX.0)
    }

    /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around
    /// at the boundary of the type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::MIN.wrapping_sub(PositiveInt::ZERO),
    ///     PositiveInt::MIN
    /// );
    /// assert_eq!(
    ///     PositiveInt::MIN.wrapping_sub(PositiveInt::ONE),
    ///     PositiveInt::MAX
    /// );
    /// assert_eq!(
    ///     PositiveInt::MIN.wrapping_sub(PositiveInt::MAX),
    ///     PositiveInt::ONE
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_sub(PositiveInt::ZERO),
    ///     PositiveInt::MAX
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_sub(PositiveInt::MAX),
    ///     PositiveInt::ZERO
    /// );
    /// ```
    pub const fn wrapping_sub(self, rhs: Self) -> Self {
        Self(self.0.wrapping_sub(rhs.0) & Self::MAX.0)
    }

    /// Wrapping (modular) multiplication. Computes `self * rhs`, wrapping
    /// around at the boundary of the type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.wrapping_mul(PositiveInt::ZERO),
    ///     PositiveInt::ZERO
    /// );
    /// assert_eq!(
    ///     PositiveInt::ZERO.wrapping_mul(PositiveInt::MAX),
    ///     PositiveInt::ZERO
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_mul(PositiveInt::ZERO),
    ///     PositiveInt::ZERO
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_mul(PositiveInt::MAX),
    ///     PositiveInt::ONE
    /// );
    /// ```
    pub const fn wrapping_mul(self, rhs: Self) -> Self {
        Self(self.0.wrapping_mul(rhs.0) & Self::MAX.0)
    }

    /// Wrapping (modular) division. Computes `self / rhs`. Wrapped division on
    /// unsigned types is just normal division. There’s no way wrapping could
    /// ever happen. This function exists, so that all operations are accounted
    /// for in the wrapping operations.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ONE.wrapping_div(PositiveInt::MAX),
    ///     PositiveInt::ZERO
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_div(PositiveInt::MAX),
    ///     PositiveInt::ONE
    /// );
    /// ```
    pub const fn wrapping_div(self, rhs: Self) -> Self {
        Self(self.0 / rhs.0)
    }

    /// Wrapping Euclidean division. Computes `self.div_euclid(rhs)`. Wrapped
    /// division on unsigned types is just normal division. There’s no way
    /// wrapping could ever happen. This function exists, so that all
    /// operations are accounted for in the wrapping operations. Since, for the
    /// positive integers, all common definitions of division are equal, this
    /// is exactly equal to `self.wrapping_div(rhs)`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ONE.wrapping_div_euclid(PositiveInt::MAX),
    ///     PositiveInt::ZERO
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_div_euclid(PositiveInt::MAX),
    ///     PositiveInt::ONE
    /// );
    /// ```
    pub const fn wrapping_div_euclid(self, rhs: Self) -> Self {
        Self(self.0 / rhs.0)
    }

    /// Wrapping (modular) remainder. Computes `self % rhs`. Wrapped remainder
    /// calculation on unsigned types is just the regular remainder
    /// calculation. There’s no way wrapping could ever happen. This function
    /// exists, so that all operations are accounted for in the wrapping
    /// operations.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ONE.wrapping_rem(PositiveInt::MAX),
    ///     PositiveInt::ONE
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_rem(PositiveInt::MAX),
    ///     PositiveInt::ZERO
    /// );
    /// ```
    pub const fn wrapping_rem(self, rhs: Self) -> Self {
        Self(self.0 % rhs.0)
    }

    /// Wrapping Euclidean modulo. Computes `self.rem_euclid(rhs)`. Wrapped
    /// modulo calculation on unsigned types is just the regular remainder
    /// calculation. There’s no way wrapping could ever happen. This function
    /// exists, so that all operations are accounted for in the wrapping
    /// operations. Since, for the positive integers, all common definitions of
    /// division are equal, this is exactly equal to `self.wrapping_rem(rhs)`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ONE.wrapping_rem_euclid(PositiveInt::MAX),
    ///     PositiveInt::ONE
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_rem_euclid(PositiveInt::MAX),
    ///     PositiveInt::ZERO
    /// );
    /// ```
    pub const fn wrapping_rem_euclid(self, rhs: Self) -> Self {
        Self(self.0 % rhs.0)
    }

    /// Wrapping (modular) negation. Computes `-self`, wrapping around at the
    /// boundary of the type.
    ///
    /// Since unsigned types do not have negative equivalents all applications
    /// of this function will wrap (except for `-0`). For values smaller than
    /// the corresponding signed type’s maximum the result is the same as
    /// casting the corresponding signed value. Any larger values are
    /// equivalent to `MAX + 1 - (val - MAX - 1)` where `MAX` is the
    /// corresponding signed type’s maximum.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.wrapping_neg(),
    ///     PositiveInt::ZERO
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.wrapping_neg(),
    ///     PositiveInt::MAX
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_neg(),
    ///     PositiveInt::ONE
    /// );
    /// ```
    pub const fn wrapping_neg(self) -> Self {
        Self(self.0.wrapping_neg() & Self::MAX.0)
    }

    /// Panic-free bitwise shift-left; yields `self <<
    /// (rhs % Self::EFFECTIVE_BITS)`.
    ///
    /// Note that this is _not_ the same as a rotate-left; the RHS of a wrapping
    /// shift-left is restricted to the range of the type, rather than the bits
    /// shifted out of the LHS being returned to the other end. This type also
    /// implements a `rotate_left` function, which may be what
    /// you want instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_shl(PositiveInt::EFFECTIVE_BITS - 1),
    ///     PositiveInt::MAX << (PositiveInt::EFFECTIVE_BITS - 1)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_shl(PositiveInt::EFFECTIVE_BITS),
    ///     PositiveInt::MAX
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_shl(PositiveInt::EFFECTIVE_BITS + 1),
    ///     PositiveInt::MAX << 1
    /// );
    /// ```
    pub const fn wrapping_shl(self, rhs: u32) -> Self {
        let wrapped_rhs = rhs % Self::EFFECTIVE_BITS;
        Self((self.0 << wrapped_rhs) & Self::MAX.0)
    }

    /// Panic-free bitwise shift-right; yields `self >>
    /// (rhs % Self::EFFECTIVE_BITS)`.
    ///
    /// Note that this is _not_ the same as a rotate-right; the RHS of a
    /// wrapping shift-right is restricted to the range of the type, rather
    /// than the bits shifted out of the LHS being returned to the other end.
    /// This type also implements a `rotate_right` function, which may be what
    /// you want instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_shr(PositiveInt::EFFECTIVE_BITS - 1),
    ///     PositiveInt::MAX >> (PositiveInt::EFFECTIVE_BITS - 1)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_shr(PositiveInt::EFFECTIVE_BITS),
    ///     PositiveInt::MAX
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_shr(PositiveInt::EFFECTIVE_BITS + 1),
    ///     PositiveInt::MAX >> 1
    /// );
    /// ```
    pub const fn wrapping_shr(self, rhs: u32) -> Self {
        Self(self.0 >> (rhs % Self::EFFECTIVE_BITS))
    }

    /// Wrapping (modular) exponentiation. Computes `self.pow(exp)`, wrapping
    /// around at the boundary of the type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.wrapping_pow(0),
    ///     PositiveInt::ONE
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.wrapping_pow(3),
    ///     PositiveInt::ONE
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_pow(1),
    ///     PositiveInt::MAX
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.wrapping_pow(2),
    ///     PositiveInt::ONE
    /// );
    /// ```
    pub const fn wrapping_pow(self, exp: u32) -> Self {
        Self(self.0.wrapping_pow(exp) & Self::MAX.0)
    }

    /// Calculates `self` + `rhs`
    ///
    /// Returns a tuple of the addition along with a boolean indicating whether
    /// an arithmetic overflow would occur. If an overflow would have occurred
    /// then the wrapped value is returned.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::MIN.overflowing_add(PositiveInt::ZERO),
    ///     (PositiveInt::MIN, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::ZERO.overflowing_add(PositiveInt::MAX),
    ///     (PositiveInt::MAX, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_add(PositiveInt::ZERO),
    ///     (PositiveInt::MAX, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_add(PositiveInt::ONE),
    ///     (PositiveInt::MIN, true)
    /// );
    /// ```
    pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        let overflow = rhs.0 > Self::MAX.0 - self.0;
        (self.wrapping_add(rhs), overflow)
    }

    /// Calculates `self` + `rhs` with a signed `rhs`.
    ///
    /// Returns a tuple of the addition along with a boolean indicating whether
    /// an arithmetic overflow would occur. If an overflow would have occurred
    /// then the wrapped value is returned.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::MIN.overflowing_add_signed(0),
    ///     (PositiveInt::MIN, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MIN.overflowing_add_signed(-1),
    ///     (PositiveInt::MAX, true)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_add_signed(0),
    ///     (PositiveInt::MAX, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_add_signed(1),
    ///     (PositiveInt::MIN, true)
    /// );
    /// ```
    #[allow(clippy::cast_possible_wrap)]
    pub const fn overflowing_add_signed(self, rhs: isize) -> (Self, bool) {
        let overflow = (rhs > (Self::MAX.0 - self.0) as isize) || (rhs < -(self.0 as isize));
        (self.wrapping_add_signed(rhs), overflow)
    }

    /// Calculates `self` - `rhs`
    ///
    /// Returns a tuple of the addition along with a boolean indicating whether
    /// an arithmetic overflow would occur. If an overflow would have occurred
    /// then the wrapped value is returned.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::MIN.overflowing_sub(PositiveInt::ZERO),
    ///     (PositiveInt::MIN, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MIN.overflowing_sub(PositiveInt::ONE),
    ///     (PositiveInt::MAX, true)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_sub(PositiveInt::ZERO),
    ///     (PositiveInt::MAX, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_sub(PositiveInt::MAX),
    ///     (PositiveInt::ZERO, false)
    /// );
    /// ```
    pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        (self.wrapping_sub(rhs), rhs.0 > self.0)
    }

    /// Computes the absolute difference between `self` and `other`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// let big = PositiveInt::MAX;
    /// let small = PositiveInt::ONE;
    /// assert_eq!(
    ///     big.abs_diff(small),
    ///     big - small
    /// );
    /// assert_eq!(
    ///     small.abs_diff(big),
    ///     big - small
    /// );
    /// ```
    pub const fn abs_diff(self, other: Self) -> Self {
        Self(self.0.abs_diff(other.0))
    }

    /// Calculates the multiplication of `self` and `rhs`.
    ///
    /// Returns a tuple of the multiplication along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would have
    /// occurred then the wrapped value is returned.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.overflowing_mul(PositiveInt::ZERO),
    ///     (PositiveInt::ZERO, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::ZERO.overflowing_mul(PositiveInt::MAX),
    ///     (PositiveInt::ZERO, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_mul(PositiveInt::ZERO),
    ///     (PositiveInt::ZERO, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_mul(PositiveInt::MAX),
    ///     (PositiveInt::ONE, true)
    /// );
    /// ```
    pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        let (inner, mut overflow) = self.0.overflowing_mul(rhs.0);
        overflow |= inner > Self::MAX.0;
        (Self(inner & Self::MAX.0), overflow)
    }

    /// Calculates the divisor when `self` is divided by `rhs`.
    ///
    /// Returns a tuple of the divisor along with a boolean indicating whether
    /// an arithmetic overflow would occur. Note that for unsigned integers
    /// overflow never occurs, so the second value is always `false`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ONE.overflowing_div(PositiveInt::MAX),
    ///     (PositiveInt::ZERO, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_div(PositiveInt::MAX),
    ///     (PositiveInt::ONE, false)
    /// );
    /// ```
    pub const fn overflowing_div(self, rhs: Self) -> (Self, bool) {
        (Self(self.0 / rhs.0), false)
    }

    /// Calculates the quotient of Euclidean division `self.div_euclid(rhs)`.
    ///
    /// Returns a tuple of the divisor along with a boolean indicating whether
    /// an arithmetic overflow would occur. Note that for unsigned integers
    /// overflow never occurs, so the second value is always `false`. Since,
    /// for the positive integers, all common definitions of division are
    /// equal, this is exactly equal to `self.overflowing_div(rhs)`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ONE.overflowing_div_euclid(PositiveInt::MAX),
    ///     (PositiveInt::ZERO, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_div_euclid(PositiveInt::MAX),
    ///     (PositiveInt::ONE, false)
    /// );
    /// ```
    pub const fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool) {
        (Self(self.0 / rhs.0), false)
    }

    /// Calculates the remainder when `self is divided by rhs`.
    ///
    /// Returns a tuple of the remainder along with a boolean indicating whether
    /// an arithmetic overflow would occur. Note that for unsigned integers
    /// overflow never occurs, so the second value is always `false`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ONE.overflowing_rem(PositiveInt::MAX),
    ///     (PositiveInt::ONE, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_rem(PositiveInt::MAX),
    ///     (PositiveInt::ZERO, false)
    /// );
    /// ```
    pub const fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
        (Self(self.0 % rhs.0), false)
    }

    /// Calculates the remainder `self.rem_euclid(rhs)` as if by Euclidean
    /// division.
    ///
    /// Returns a tuple of the remainder along with a boolean indicating whether
    /// an arithmetic overflow would occur. Note that for unsigned integers
    /// overflow never occurs, so the second value is always `false`. Since,
    /// for the positive integers, all common definitions of division are
    /// equal, this operation is exactly equal to `self.overflowing_rem(rhs)`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ONE.overflowing_rem_euclid(PositiveInt::MAX),
    ///     (PositiveInt::ONE, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_rem_euclid(PositiveInt::MAX),
    ///     (PositiveInt::ZERO, false)
    /// );
    /// ```
    pub const fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool) {
        (Self(self.0 % rhs.0), false)
    }

    /// Negates `self` in an overflowing fashion.
    ///
    /// Returns `!self + PositiveInt::ONE` using wrapping operations to return
    /// the value that represents the negation of this unsigned value. Note
    /// that for positive unsigned values overflow always occurs, but negating
    /// `PositiveInt::ZERO` does not overflow.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.overflowing_neg(),
    ///     (PositiveInt::ZERO, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.overflowing_neg(),
    ///     (PositiveInt::MAX, true)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_neg(),
    ///     (PositiveInt::ONE, true)
    /// );
    /// ```
    pub const fn overflowing_neg(self) -> (Self, bool) {
        (self.wrapping_neg(), self.0 != 0)
    }

    /// Shifts `self` left by `rhs` bits.
    ///
    /// Returns a tuple of the shifted version of `self` along with a boolean
    /// indicating whether the shift value was larger than or equal to the
    /// number of bits. If the shift value is too large, then it is wrapped
    /// around through `rhs % Self::EFFECTIVE_BITS`, and this value is then
    /// used to perform the shift.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_shl(PositiveInt::EFFECTIVE_BITS - 1),
    ///     (PositiveInt::MAX << (PositiveInt::EFFECTIVE_BITS - 1), false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_shl(PositiveInt::EFFECTIVE_BITS),
    ///     (PositiveInt::MAX, true)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_shl(PositiveInt::EFFECTIVE_BITS + 1),
    ///     (PositiveInt::MAX << 1, true)
    /// );
    /// ```
    pub const fn overflowing_shl(self, rhs: u32) -> (Self, bool) {
        (self.wrapping_shl(rhs), rhs >= Self::EFFECTIVE_BITS)
    }

    /// Shifts `self` right by `rhs` bits.
    ///
    /// Returns a tuple of the shifted version of `self` along with a boolean
    /// indicating whether the shift value was larger than or equal to the
    /// number of bits. If the shift value is too large, then it is wrapped
    /// around through `rhs % Self::EFFECTIVE_BITS`, and this value is then
    /// used to perform the shift.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_shr(PositiveInt::EFFECTIVE_BITS - 1),
    ///     (PositiveInt::MAX >> (PositiveInt::EFFECTIVE_BITS - 1), false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_shr(PositiveInt::EFFECTIVE_BITS),
    ///     (PositiveInt::MAX, true)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_shr(PositiveInt::EFFECTIVE_BITS + 1),
    ///     (PositiveInt::MAX >> 1, true)
    /// );
    /// ```
    pub const fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
        (self.wrapping_shr(rhs), rhs >= Self::EFFECTIVE_BITS)
    }

    /// Raises `self` to the power of `exp`, using exponentiation by squaring.
    ///
    /// Returns a tuple of the exponentiation along with a `bool` indicating
    /// whether an overflow happened.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.overflowing_pow(0),
    ///     (PositiveInt::ONE, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.overflowing_pow(3),
    ///     (PositiveInt::ONE, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_pow(1),
    ///     (PositiveInt::MAX, false)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.overflowing_pow(2),
    ///     (PositiveInt::ONE, true)
    /// );
    /// ```
    pub const fn overflowing_pow(self, exp: u32) -> (Self, bool) {
        let (inner, mut overflow) = self.0.overflowing_pow(exp);
        overflow |= inner > Self::MAX.0;
        (Self(inner & Self::MAX.0), overflow)
    }

    /// Raises `self` to the power of `exp`, using exponentiation by squaring.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.pow(0),
    ///     PositiveInt::ONE
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.pow(3),
    ///     PositiveInt::ONE
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.pow(1),
    ///     PositiveInt::MAX
    /// );
    /// ```
    pub const fn pow(self, exp: u32) -> Self {
        if cfg!(debug_assertions) {
            if let Some(res) = self.checked_pow(exp) {
                res
            } else {
                panic!("Attempted to call PositiveInt::pow() with overflow")
            }
        } else {
            self.wrapping_pow(exp)
        }
    }

    /// Performs Euclidean division.
    ///
    /// Since, for the positive integers, all common definitions of division are
    /// equal, this is exactly equal to `self / rhs`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is `PositiveInt::ZERO`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ONE.div_euclid(PositiveInt::MAX),
    ///     PositiveInt::ZERO
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.div_euclid(PositiveInt::MAX),
    ///     PositiveInt::ONE
    /// );
    /// ```
    pub const fn div_euclid(self, rhs: Self) -> Self {
        Self(self.0 / rhs.0)
    }

    /// Calculates the least remainder of `self (mod rhs)`.
    ///
    /// Since, for the positive integers, all common definitions of division are
    /// equal, this is exactly equal to `self % rhs`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is `PositiveInt::ZERO`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ONE.rem_euclid(PositiveInt::MAX),
    ///     PositiveInt::ONE
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.rem_euclid(PositiveInt::MAX),
    ///     PositiveInt::ZERO
    /// );
    /// ```
    pub const fn rem_euclid(self, rhs: Self) -> Self {
        Self(self.0 % rhs.0)
    }

    /// Returns `true` if and only if `self == 2^k` for some `k`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hwlocality::ffi::PositiveInt;
    /// assert!(!PositiveInt::ZERO.is_power_of_two());
    /// assert!(PositiveInt::ONE.is_power_of_two());
    /// assert!(!PositiveInt::MAX.is_power_of_two());
    /// ```
    pub const fn is_power_of_two(self) -> bool {
        self.0.is_power_of_two()
    }

    /// Returns the smallest power of two greater than or equal to `self`.
    ///
    /// When return value overflows (i.e., `self > (PositiveInt::ONE <<
    /// (PositiveInt::EFFECTIVE_BITS - 1))`, it panics in debug mode and the
    /// return value is wrapped to 0 in release mode (the only situation in
    /// which method can return 0).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.next_power_of_two(),
    ///     PositiveInt::ONE
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.next_power_of_two(),
    ///     PositiveInt::ONE
    /// );
    /// ```
    pub const fn next_power_of_two(self) -> Self {
        if cfg!(debug_assertions) {
            if let Some(res) = self.checked_next_power_of_two() {
                res
            } else {
                panic!("Attempted to compute next power of two with overflow")
            }
        } else {
            Self(self.0.next_power_of_two() & Self::MAX.0)
        }
    }

    /// Returns the smallest power of two greater than or equal to `self`. If
    /// the next power of two is greater than the type’s maximum value, `None`
    /// is returned, otherwise the power of two is wrapped in `Some`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hwlocality::ffi::PositiveInt;
    /// assert_eq!(
    ///     PositiveInt::ZERO.checked_next_power_of_two(),
    ///     Some(PositiveInt::ONE)
    /// );
    /// assert_eq!(
    ///     PositiveInt::ONE.checked_next_power_of_two(),
    ///     Some(PositiveInt::ONE)
    /// );
    /// assert_eq!(
    ///     PositiveInt::MAX.checked_next_power_of_two(),
    ///     None
    /// );
    /// ```
    #[allow(clippy::if_then_some_else_none)]
    pub const fn checked_next_power_of_two(self) -> Option<Self> {
        // Even int::MAX has a next-power-of-two in our inner uint
        let inner = self.0.next_power_of_two();
        if inner <= Self::MAX.0 {
            Some(Self(inner))
        } else {
            None
        }
    }

    // NOTE: No (from|to)_(be|le)_bytes, the modeled integer is not made of an
    //       integral number of bytes so these operations do not make sense.

    // === PositiveInt-specific functionality ===

    /// Construct a [`Range`]-like iterator of this integer type
    ///
    /// Unfortunately, `Range<PositiveInt>` does not implement [`Iterator`]
    /// due to that impl's dependency on the rustc-private `Step` trait.
    /// This method is the workaround.
    pub fn iter_range(
        start: Self,
        end: Self,
    ) -> impl DoubleEndedIterator<Item = Self> + Clone + ExactSizeIterator + FusedIterator {
        PositiveIntRangeIter { start, end }
    }

    /// Construct a [`RangeInclusive`]-like iterator of this integer type
    ///
    /// This needs to exist for the same reason that [`iter_range()`] does.
    ///
    /// [`iter_range()`]: Self::iter_range()
    pub fn iter_range_inclusive(
        start: Self,
        end: Self,
    ) -> impl DoubleEndedIterator<Item = Self> + Clone + ExactSizeIterator + FusedIterator {
        PositiveIntRangeInclusiveIter {
            start,
            end,
            exhausted: start > end,
        }
    }

    /// Construct a [`RangeFrom`]-like iterator of this integer type
    ///
    /// This needs to exist for the same reason that [`iter_range()`] does.
    ///
    /// [`iter_range()`]: Self::iter_range()
    pub fn iter_range_from(start: Self) -> impl FusedIterator<Item = Self> + Clone {
        PositiveIntRangeFromIter(start)
    }

    /// Convert from an hwloc-originated [`c_int`]
    ///
    /// This is not a [`TryFrom`] implementation because that would make bitmap
    /// indexing accept negative indexing without a compile-time error.
    pub(crate) fn try_from_c_int(x: c_int) -> Result<Self, TryFromIntError> {
        x.try_into().map(Self)
    }

    /// Convert from a [`c_uint`]
    ///
    /// Will be dropped once [`TryFrom`]/[`TryInto`] is usable in `const fn`
    #[allow(clippy::if_then_some_else_none)]
    const fn const_try_from_c_uint(x: c_uint) -> Option<Self> {
        if x <= Self::MAX.0 {
            Some(Self(x))
        } else {
            None
        }
    }

    /// Convert into a [`c_int`] (okay by construction)
    #[allow(clippy::cast_possible_wrap)]
    pub(crate) const fn into_c_int(self) -> c_int {
        self.0 as c_int
    }

    /// Convert into a [`c_uint`] (okay by construction)
    pub(crate) const fn into_c_uint(self) -> c_uint {
        self.0
    }
}

impl<B: Borrow<Self>> Add<B> for PositiveInt {
    type Output = Self;

    fn add(self, rhs: B) -> Self {
        if cfg!(debug_assertions) {
            self.checked_add(*rhs.borrow())
                .expect("Attempted to add with overflow")
        } else {
            self.wrapping_add(*rhs.borrow())
        }
    }
}

impl Add<isize> for PositiveInt {
    type Output = Self;

    fn add(self, rhs: isize) -> Self {
        if cfg!(debug_assertions) {
            self.checked_add_signed(rhs)
                .expect("Attempted to add with overflow")
        } else {
            self.wrapping_add_signed(rhs)
        }
    }
}

impl Add<PositiveInt> for isize {
    type Output = PositiveInt;

    fn add(self, rhs: PositiveInt) -> PositiveInt {
        rhs + self
    }
}

impl Add<&isize> for PositiveInt {
    type Output = Self;

    fn add(self, rhs: &isize) -> Self {
        self + (*rhs)
    }
}

impl Add<PositiveInt> for &isize {
    type Output = PositiveInt;

    fn add(self, rhs: PositiveInt) -> PositiveInt {
        rhs + (*self)
    }
}

impl<B: Borrow<PositiveInt>> Add<B> for &PositiveInt {
    type Output = PositiveInt;

    fn add(self, rhs: B) -> PositiveInt {
        *self + rhs
    }
}

impl Add<isize> for &PositiveInt {
    type Output = PositiveInt;

    fn add(self, rhs: isize) -> PositiveInt {
        *self + rhs
    }
}

impl Add<&PositiveInt> for isize {
    type Output = PositiveInt;

    fn add(self, rhs: &PositiveInt) -> PositiveInt {
        *rhs + self
    }
}

impl Add<&isize> for &PositiveInt {
    type Output = PositiveInt;

    fn add(self, rhs: &isize) -> PositiveInt {
        *self + (*rhs)
    }
}

impl Add<&PositiveInt> for &isize {
    type Output = PositiveInt;

    fn add(self, rhs: &PositiveInt) -> PositiveInt {
        *rhs + (*self)
    }
}

impl<Rhs> AddAssign<Rhs> for PositiveInt
where
    Self: Add<Rhs, Output = Self>,
{
    fn add_assign(&mut self, rhs: Rhs) {
        *self = *self + rhs
    }
}

#[cfg(any(test, feature = "quickcheck"))]
impl Arbitrary for PositiveInt {
    fn arbitrary(g: &mut Gen) -> Self {
        // Many index-based hwloc APIs exhibit O(n) behavior depending on which
        // index is passed as input, so we enforce that ints used in tests
        // are "not too big", as per the quickcheck size parameter
        let mut rng = rand::thread_rng();
        let max = Self::try_from(g.size()).unwrap_or(Self::MAX);
        let value = rng.gen_range(0..max.0);
        Self(value)
    }

    #[cfg(not(tarpaulin_include))]
    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(self.0.shrink().filter_map(Self::const_try_from_c_uint))
    }
}

impl<B: Borrow<Self>> BitAnd<B> for PositiveInt {
    type Output = Self;

    fn bitand(self, rhs: B) -> Self {
        Self(self.0 & rhs.borrow().0)
    }
}

impl BitAnd<usize> for PositiveInt {
    type Output = Self;

    #[allow(clippy::cast_possible_truncation)]
    fn bitand(self, rhs: usize) -> Self {
        // This is ok because AND cannot set bits which are unset in self
        Self(self.0 & (rhs as c_uint))
    }
}

impl BitAnd<PositiveInt> for usize {
    type Output = PositiveInt;

    fn bitand(self, rhs: PositiveInt) -> PositiveInt {
        rhs & self
    }
}

impl BitAnd<&usize> for PositiveInt {
    type Output = Self;

    fn bitand(self, rhs: &usize) -> Self {
        self & (*rhs)
    }
}

impl BitAnd<PositiveInt> for &usize {
    type Output = PositiveInt;

    fn bitand(self, rhs: PositiveInt) -> PositiveInt {
        rhs & (*self)
    }
}

impl<B: Borrow<PositiveInt>> BitAnd<B> for &PositiveInt {
    type Output = PositiveInt;

    fn bitand(self, rhs: B) -> PositiveInt {
        *self & rhs
    }
}

impl BitAnd<usize> for &PositiveInt {
    type Output = PositiveInt;

    fn bitand(self, rhs: usize) -> PositiveInt {
        *self & rhs
    }
}

impl BitAnd<&PositiveInt> for usize {
    type Output = PositiveInt;

    fn bitand(self, rhs: &PositiveInt) -> PositiveInt {
        *rhs & self
    }
}

impl BitAnd<&usize> for &PositiveInt {
    type Output = PositiveInt;

    fn bitand(self, rhs: &usize) -> PositiveInt {
        *self & (*rhs)
    }
}

impl BitAnd<&PositiveInt> for &usize {
    type Output = PositiveInt;

    fn bitand(self, rhs: &PositiveInt) -> PositiveInt {
        *rhs & (*self)
    }
}

impl<Rhs> BitAndAssign<Rhs> for PositiveInt
where
    Self: BitAnd<Rhs, Output = Self>,
{
    fn bitand_assign(&mut self, rhs: Rhs) {
        *self = *self & rhs
    }
}

impl<B: Borrow<Self>> BitOr<B> for PositiveInt {
    type Output = Self;

    fn bitor(self, rhs: B) -> Self {
        Self(self.0 | rhs.borrow().0)
    }
}

impl BitOr<usize> for PositiveInt {
    type Output = Self;

    #[allow(clippy::cast_possible_truncation)]
    fn bitor(self, rhs: usize) -> Self {
        // This is only ok if rhs is in range because OR can set bits which are
        // unset in self. We go the usual debug-panic/release-truncate way.
        debug_assert!(rhs <= usize::from(Self::MAX), "RHS out of range");
        Self(self.0 | ((rhs as c_uint) & Self::MAX.0))
    }
}

impl BitOr<PositiveInt> for usize {
    type Output = PositiveInt;

    fn bitor(self, rhs: PositiveInt) -> PositiveInt {
        rhs | self
    }
}

impl BitOr<&usize> for PositiveInt {
    type Output = Self;

    fn bitor(self, rhs: &usize) -> Self {
        self | (*rhs)
    }
}

impl BitOr<PositiveInt> for &usize {
    type Output = PositiveInt;

    fn bitor(self, rhs: PositiveInt) -> PositiveInt {
        rhs | (*self)
    }
}

impl<B: Borrow<PositiveInt>> BitOr<B> for &PositiveInt {
    type Output = PositiveInt;

    fn bitor(self, rhs: B) -> PositiveInt {
        *self | rhs
    }
}

impl BitOr<usize> for &PositiveInt {
    type Output = PositiveInt;

    fn bitor(self, rhs: usize) -> PositiveInt {
        *self | rhs
    }
}

impl BitOr<&PositiveInt> for usize {
    type Output = PositiveInt;

    fn bitor(self, rhs: &PositiveInt) -> PositiveInt {
        *rhs | self
    }
}

impl BitOr<&usize> for &PositiveInt {
    type Output = PositiveInt;

    fn bitor(self, rhs: &usize) -> PositiveInt {
        *self | (*rhs)
    }
}

impl BitOr<&PositiveInt> for &usize {
    type Output = PositiveInt;

    fn bitor(self, rhs: &PositiveInt) -> PositiveInt {
        *rhs | (*self)
    }
}

impl<Rhs> BitOrAssign<Rhs> for PositiveInt
where
    Self: BitOr<Rhs, Output = Self>,
{
    fn bitor_assign(&mut self, rhs: Rhs) {
        *self = *self | rhs
    }
}

impl<B: Borrow<Self>> BitXor<B> for PositiveInt {
    type Output = Self;

    fn bitxor(self, rhs: B) -> Self {
        Self(self.0 ^ rhs.borrow().0)
    }
}

impl BitXor<usize> for PositiveInt {
    type Output = Self;

    #[allow(clippy::cast_possible_truncation)]
    fn bitxor(self, rhs: usize) -> Self {
        // This is only ok if rhs is in range because XOR can set bits which are
        // unset in self. We go the usual debug-panic/release-truncate way.
        debug_assert!(rhs <= usize::from(Self::MAX), "RHS out of range");
        Self(self.0 ^ ((rhs as c_uint) & Self::MAX.0))
    }
}

impl BitXor<PositiveInt> for usize {
    type Output = PositiveInt;

    fn bitxor(self, rhs: PositiveInt) -> PositiveInt {
        rhs ^ self
    }
}

impl BitXor<&usize> for PositiveInt {
    type Output = Self;

    fn bitxor(self, rhs: &usize) -> Self {
        self ^ (*rhs)
    }
}

impl BitXor<PositiveInt> for &usize {
    type Output = PositiveInt;

    fn bitxor(self, rhs: PositiveInt) -> PositiveInt {
        rhs ^ (*self)
    }
}

impl<B: Borrow<PositiveInt>> BitXor<B> for &PositiveInt {
    type Output = PositiveInt;

    fn bitxor(self, rhs: B) -> PositiveInt {
        *self ^ rhs
    }
}

impl BitXor<usize> for &PositiveInt {
    type Output = PositiveInt;

    fn bitxor(self, rhs: usize) -> PositiveInt {
        *self ^ rhs
    }
}

impl BitXor<&PositiveInt> for usize {
    type Output = PositiveInt;

    fn bitxor(self, rhs: &PositiveInt) -> PositiveInt {
        *rhs ^ self
    }
}

impl BitXor<&usize> for &PositiveInt {
    type Output = PositiveInt;

    fn bitxor(self, rhs: &usize) -> PositiveInt {
        *self ^ (*rhs)
    }
}

impl BitXor<&PositiveInt> for &usize {
    type Output = PositiveInt;

    fn bitxor(self, rhs: &PositiveInt) -> PositiveInt {
        *rhs ^ (*self)
    }
}

impl<Rhs> BitXorAssign<Rhs> for PositiveInt
where
    Self: BitXor<Rhs, Output = Self>,
{
    fn bitxor_assign(&mut self, rhs: Rhs) {
        *self = *self ^ rhs
    }
}

impl<B: Borrow<Self>> Div<B> for PositiveInt {
    type Output = Self;

    fn div(self, rhs: B) -> Self {
        Self(self.0 / rhs.borrow().0)
    }
}

impl Div<usize> for PositiveInt {
    type Output = Self;

    fn div(self, rhs: usize) -> Self {
        Self::try_from(rhs).map_or(Self::ZERO, |rhs| self / rhs)
    }
}

impl Div<&usize> for PositiveInt {
    type Output = Self;

    fn div(self, rhs: &usize) -> Self {
        self / *rhs
    }
}

impl<B: Borrow<PositiveInt>> Div<B> for &PositiveInt {
    type Output = PositiveInt;

    fn div(self, rhs: B) -> PositiveInt {
        *self / rhs
    }
}

impl Div<usize> for &PositiveInt {
    type Output = PositiveInt;

    fn div(self, rhs: usize) -> PositiveInt {
        *self / rhs
    }
}

impl Div<&usize> for &PositiveInt {
    type Output = PositiveInt;

    fn div(self, rhs: &usize) -> PositiveInt {
        *self / *rhs
    }
}

impl<Rhs> DivAssign<Rhs> for PositiveInt
where
    Self: Div<Rhs, Output = Self>,
{
    fn div_assign(&mut self, rhs: Rhs) {
        *self = *self / rhs
    }
}

// NOTE: Guaranteed to succeed because C mandates that int is >=16 bits
//       u16 would not work because it allows u16::MAX > i16::MAX.
//       From<u8> would also be safe to implement, but would break integer type
//       inference when an integer literal is passed to a function that expects
//       T with PositiveInt: TryFrom<T>.
impl From<bool> for PositiveInt {
    fn from(x: bool) -> Self {
        Self(x.into())
    }
}

// NOTE: Assumed to work, otherwise the whole premise of allowing users to use
//       usize/isize instead of c_u?int for indexing falls flat.
impl From<PositiveInt> for isize {
    fn from(x: PositiveInt) -> Self {
        expect_isize(x.into_c_int())
    }
}
//
impl From<PositiveInt> for usize {
    fn from(x: PositiveInt) -> Self {
        expect_usize(x.into_c_uint())
    }
}

impl FromStr for PositiveInt {
    type Err = ParseIntError;

    fn from_str(src: &str) -> Result<Self, ParseIntError> {
        Self::from_str_radix(src, 10)
    }
}

impl<B: Borrow<Self>> Mul<B> for PositiveInt {
    type Output = Self;

    fn mul(self, rhs: B) -> Self {
        if cfg!(debug_assertions) {
            self.checked_mul(*rhs.borrow())
                .expect("Attempted to multiply with overflow")
        } else {
            self.wrapping_mul(*rhs.borrow())
        }
    }
}

impl Mul<usize> for PositiveInt {
    type Output = Self;

    #[allow(clippy::cast_possible_truncation)]
    fn mul(self, rhs: usize) -> Self {
        if cfg!(debug_assertions) {
            if self == Self::ZERO {
                Self::ZERO
            } else {
                Self::try_from(rhs)
                    .ok()
                    .and_then(|rhs| self.checked_mul(rhs))
                    .expect("Attempted to multiply with overflow")
            }
        } else {
            let usize_result = usize::from(self) * rhs;
            let truncated = usize_result & (Self::MAX.0 as usize);
            Self(truncated as c_uint)
        }
    }
}

impl Mul<PositiveInt> for usize {
    type Output = PositiveInt;

    fn mul(self, rhs: PositiveInt) -> PositiveInt {
        rhs * self
    }
}

impl Mul<&usize> for PositiveInt {
    type Output = Self;

    fn mul(self, rhs: &usize) -> Self {
        self * (*rhs)
    }
}

impl Mul<PositiveInt> for &usize {
    type Output = PositiveInt;

    fn mul(self, rhs: PositiveInt) -> PositiveInt {
        rhs * (*self)
    }
}

impl<B: Borrow<PositiveInt>> Mul<B> for &PositiveInt {
    type Output = PositiveInt;

    fn mul(self, rhs: B) -> PositiveInt {
        *self * rhs
    }
}

impl Mul<usize> for &PositiveInt {
    type Output = PositiveInt;

    fn mul(self, rhs: usize) -> PositiveInt {
        *self * rhs
    }
}

impl Mul<&PositiveInt> for usize {
    type Output = PositiveInt;

    fn mul(self, rhs: &PositiveInt) -> PositiveInt {
        *rhs * self
    }
}

impl Mul<&usize> for &PositiveInt {
    type Output = PositiveInt;

    fn mul(self, rhs: &usize) -> PositiveInt {
        (*self) * (*rhs)
    }
}

impl Mul<&PositiveInt> for &usize {
    type Output = PositiveInt;

    fn mul(self, rhs: &PositiveInt) -> PositiveInt {
        (*rhs) * (*self)
    }
}

impl<Rhs> MulAssign<Rhs> for PositiveInt
where
    Self: Mul<Rhs, Output = Self>,
{
    fn mul_assign(&mut self, rhs: Rhs) {
        *self = *self * rhs
    }
}

impl Not for PositiveInt {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self(self.0 ^ Self::MAX.0)
    }
}
//
impl Not for &PositiveInt {
    type Output = PositiveInt;

    fn not(self) -> Self::Output {
        !*self
    }
}

impl PartialEq<usize> for PositiveInt {
    fn eq(&self, other: &usize) -> bool {
        usize::from(*self) == *other
    }
}

impl PartialEq<PositiveInt> for usize {
    #[allow(clippy::use_self)]
    fn eq(&self, other: &PositiveInt) -> bool {
        *self == usize::from(*other)
    }
}

impl PartialOrd<usize> for PositiveInt {
    fn partial_cmp(&self, other: &usize) -> Option<Ordering> {
        usize::from(*self).partial_cmp(other)
    }
}

impl PartialOrd<PositiveInt> for usize {
    #[allow(clippy::use_self)]
    fn partial_cmp(&self, other: &PositiveInt) -> Option<Ordering> {
        self.partial_cmp(&usize::from(*other))
    }
}

impl<B: Borrow<Self>> Product<B> for PositiveInt {
    fn product<I: Iterator<Item = B>>(iter: I) -> Self {
        iter.fold(Self::ONE, |acc, contrib| acc * contrib.borrow())
    }
}

impl<B: Borrow<Self>> Rem<B> for PositiveInt {
    type Output = Self;

    fn rem(self, rhs: B) -> Self {
        Self(self.0 % rhs.borrow().0)
    }
}

impl Rem<usize> for PositiveInt {
    type Output = Self;

    fn rem(self, rhs: usize) -> Self {
        Self::try_from(rhs).map(|rhs| self % rhs).unwrap_or(self)
    }
}

impl Rem<&usize> for PositiveInt {
    type Output = Self;

    fn rem(self, rhs: &usize) -> Self {
        self % (*rhs)
    }
}

impl<B: Borrow<PositiveInt>> Rem<B> for &PositiveInt {
    type Output = PositiveInt;

    fn rem(self, rhs: B) -> PositiveInt {
        *self % rhs
    }
}

impl Rem<usize> for &PositiveInt {
    type Output = PositiveInt;

    fn rem(self, rhs: usize) -> PositiveInt {
        *self % rhs
    }
}

impl Rem<&usize> for &PositiveInt {
    type Output = PositiveInt;

    fn rem(self, rhs: &usize) -> PositiveInt {
        *self % (*rhs)
    }
}

impl<Rhs> RemAssign<Rhs> for PositiveInt
where
    Self: Rem<Rhs, Output = Self>,
{
    fn rem_assign(&mut self, rhs: Rhs) {
        *self = *self % rhs
    }
}

impl Shl<Self> for PositiveInt {
    type Output = Self;

    fn shl(self, rhs: Self) -> Self {
        self << usize::from(rhs)
    }
}

impl Shl<&Self> for PositiveInt {
    type Output = Self;

    fn shl(self, rhs: &Self) -> Self {
        self << *rhs
    }
}

impl Shl<PositiveInt> for &PositiveInt {
    type Output = PositiveInt;

    fn shl(self, rhs: PositiveInt) -> PositiveInt {
        *self << rhs
    }
}

#[allow(clippy::use_self)]
impl Shl<&PositiveInt> for &PositiveInt {
    type Output = PositiveInt;

    fn shl(self, rhs: &PositiveInt) -> PositiveInt {
        *self << *rhs
    }
}

/// Generate heterogeneous `positive_int << machine_integer` ops
macro_rules! shl_with_int {
    ( $( $int:ty ),* ) => { $(
        impl Shl<$int> for PositiveInt {
            type Output = Self;

            #[allow(trivial_numeric_casts)]
            fn shl(self, mut rhs: $int) -> Self {
                if cfg!(debug_assertions) {
                    // Debug mode checks if the shift is in range
                    assert_eq!(
                        rhs.div_euclid(Self::EFFECTIVE_BITS as $int), 0,
                        "Attempted to shift left with overflow"
                    );
                } else {
                    // Release mode wraps around the shift operand
                    rhs = rhs.rem_euclid(Self::EFFECTIVE_BITS as $int);
                }
                Self((self.0 << rhs) & Self::MAX.0)
            }
        }

        impl Shl<&$int> for PositiveInt {
            type Output = Self;

            fn shl(self, rhs: &$int) -> Self {
                self << *rhs
            }
        }

        impl Shl<$int> for &PositiveInt {
            type Output = PositiveInt;

            fn shl(self, rhs: $int) -> PositiveInt {
                *self << rhs
            }
        }

        impl Shl<&$int> for &PositiveInt {
            type Output = PositiveInt;

            fn shl(self, rhs: &$int) -> PositiveInt {
                *self << *rhs
            }
        }
    )* };
}
//
shl_with_int!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

impl<Rhs> ShlAssign<Rhs> for PositiveInt
where
    Self: Shl<Rhs, Output = Self>,
{
    fn shl_assign(&mut self, rhs: Rhs) {
        *self = *self << rhs
    }
}

impl Shr<Self> for PositiveInt {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self {
        self >> usize::from(rhs)
    }
}

impl Shr<&Self> for PositiveInt {
    type Output = Self;

    fn shr(self, rhs: &Self) -> Self {
        self >> *rhs
    }
}

impl Shr<PositiveInt> for &PositiveInt {
    type Output = PositiveInt;

    fn shr(self, rhs: PositiveInt) -> PositiveInt {
        *self >> rhs
    }
}

#[allow(clippy::use_self)]
impl Shr<&PositiveInt> for &PositiveInt {
    type Output = PositiveInt;

    fn shr(self, rhs: &PositiveInt) -> PositiveInt {
        *self >> *rhs
    }
}

/// Generate heterogeneous `positive_int >> machine_integer` ops
macro_rules! shr_with_int {
    ( $( $int:ty ),* ) => { $(
        impl Shr<$int> for PositiveInt {
            type Output = Self;

            #[allow(trivial_numeric_casts)]
            fn shr(self, mut rhs: $int) -> Self {
                if cfg!(debug_assertions) {
                    // Debug mode checks if the shift is in range
                    assert_eq!(
                        rhs.div_euclid(Self::EFFECTIVE_BITS as $int), 0,
                        "Attempted to shift right with overflow"
                    );
                } else {
                    // Release mode wraps around the shift operand
                    rhs = rhs.rem_euclid(Self::EFFECTIVE_BITS as $int);
                }
                Self((self.0 >> rhs) & Self::MAX.0)
            }
        }

        impl Shr<&$int> for PositiveInt {
            type Output = Self;

            fn shr(self, rhs: &$int) -> Self {
                self >> *rhs
            }
        }

        impl Shr<$int> for &PositiveInt {
            type Output = PositiveInt;

            fn shr(self, rhs: $int) -> PositiveInt {
                *self >> rhs
            }
        }

        impl Shr<&$int> for &PositiveInt {
            type Output = PositiveInt;

            fn shr(self, rhs: &$int) -> PositiveInt {
                *self >> *rhs
            }
        }
    )* };
}
//
shr_with_int!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

impl<Rhs> ShrAssign<Rhs> for PositiveInt
where
    Self: Shr<Rhs, Output = Self>,
{
    fn shr_assign(&mut self, rhs: Rhs) {
        *self = *self >> rhs
    }
}

impl<B: Borrow<Self>> Sub<B> for PositiveInt {
    type Output = Self;

    fn sub(self, rhs: B) -> Self {
        if cfg!(debug_assertions) {
            self.checked_sub(*rhs.borrow())
                .expect("Attempted to subtract with overflow")
        } else {
            self.wrapping_sub(*rhs.borrow())
        }
    }
}

impl Sub<isize> for PositiveInt {
    type Output = Self;

    fn sub(self, rhs: isize) -> Self {
        if cfg!(debug_assertions) {
            rhs.checked_neg()
                .and_then(|minus_rhs| self.checked_add_signed(minus_rhs))
                .expect("Attempted to subtract with overflow")
        } else if rhs != isize::MIN {
            self.wrapping_add_signed(-rhs)
        } else {
            // isize::MIN is -2^(isize::BITS - 1).
            // So -isize::MIN is 2^(isize::BITS - 1).
            // A core assumption of ours is that (isize::BITS >= c_int::BITS)
            // Thus 2^(isize::BITS - 1) is a power of two greater than or
            // equal to 2^(Self::EFFECTIVE_BITS), and thus adding it does
            // nothing in the presence of wraparound
            self
        }
    }
}

impl Sub<&isize> for PositiveInt {
    type Output = Self;

    fn sub(self, rhs: &isize) -> Self {
        self - (*rhs)
    }
}

impl<B: Borrow<PositiveInt>> Sub<B> for &PositiveInt {
    type Output = PositiveInt;

    fn sub(self, rhs: B) -> PositiveInt {
        *self - rhs
    }
}

impl Sub<isize> for &PositiveInt {
    type Output = PositiveInt;

    fn sub(self, rhs: isize) -> PositiveInt {
        *self - rhs
    }
}

impl Sub<&isize> for &PositiveInt {
    type Output = PositiveInt;

    fn sub(self, rhs: &isize) -> PositiveInt {
        *self - (*rhs)
    }
}

impl<Rhs> SubAssign<Rhs> for PositiveInt
where
    Self: Sub<Rhs, Output = Self>,
{
    fn sub_assign(&mut self, rhs: Rhs) {
        *self = *self - rhs
    }
}

impl<B: Borrow<Self>> Sum<B> for PositiveInt {
    fn sum<I: Iterator<Item = B>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, contrib| acc + contrib.borrow())
    }
}

// NOTE: Only implementing TryFrom<usize> for the same reason slices can only be
//       indexed by usize, namely to avoid integer type inference issues
impl TryFrom<usize> for PositiveInt {
    type Error = TryFromIntError;

    fn try_from(value: usize) -> Result<Self, TryFromIntError> {
        Self::try_from_c_int(value.try_into()?)
    }
}

/// Implement conversions from machine integer types to [`PositiveInt`]
macro_rules! try_into {
    ( $( $int:ty ),* ) => { $(
        impl TryFrom<PositiveInt> for $int {
            type Error = TryFromIntError;

            #[allow(clippy::needless_question_mark)]
            fn try_from(value: PositiveInt) -> Result<Self, TryFromIntError> {
                Ok(value.0.try_into()?)
            }
        }
    )* };
}
//
try_into!(i8, i16, i32, i64, i128, u8, u16, u32, u64, u128);

/// [`Range`]-like iterator for [`PositiveInt`]
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
struct PositiveIntRangeIter {
    /// Start of the range
    start: PositiveInt,

    /// End of the range (exclusive)
    end: PositiveInt,
}
//
impl DoubleEndedIterator for PositiveIntRangeIter {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.nth_back(0)
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if self.len() > n {
            self.end -= PositiveInt::try_from(n + 1).expect(
                "Cannot happen: len > n implies len >= n+1 \
                 and len < PositiveInt::MAX by construction, \
                 therefore n+1 < PositiveInt::MAX",
            );
            Some(self.end)
        } else {
            self.end = self.start;
            None
        }
    }
}
//
impl ExactSizeIterator for PositiveIntRangeIter {
    fn len(&self) -> usize {
        usize::from(self.end).saturating_sub(usize::from(self.start))
    }
}
//
impl FusedIterator for PositiveIntRangeIter {}
//
impl Iterator for PositiveIntRangeIter {
    type Item = PositiveInt;

    fn next(&mut self) -> Option<PositiveInt> {
        self.nth(0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }

    fn count(self) -> usize {
        self.len()
    }

    fn last(self) -> Option<PositiveInt> {
        (self.len() != 0).then(|| self.end - 1)
    }

    fn nth(&mut self, n: usize) -> Option<PositiveInt> {
        if self.len() > n {
            self.start += PositiveInt::try_from(n + 1).expect(
                "Cannot happen: len > n implies len >= n+1 \
                 and len < PositiveInt::MAX by construction, \
                 therefore n+1 < PositiveInt::MAX",
            );
            Some(self.start - 1)
        } else {
            self.start = self.end;
            None
        }
    }
}

/// [`RangeInclusive`]-like iterator for [`PositiveInt`]
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
struct PositiveIntRangeInclusiveIter {
    /// Start of the range
    start: PositiveInt,

    /// End of the range (inclusive)
    end: PositiveInt,

    /// Truth that there are elements left
    exhausted: bool,
}
//
impl PositiveIntRangeInclusiveIter {
    /// Like [`Iterator::next()`], but assumes there are items left
    fn next_unchecked(&mut self) -> PositiveInt {
        debug_assert!(
            !self.exhausted,
            "Should not be called on an exhausted iterator"
        );
        if self.start == self.end {
            self.exhausted = true;
            self.start
        } else {
            self.start += 1;
            self.start - 1
        }
    }

    /// Like [`DoubleEndedIterator::next_back()`], but assumes there are items left
    fn next_back_unchecked(&mut self) -> PositiveInt {
        debug_assert!(
            !self.exhausted,
            "Should not be called on an exhausted iterator"
        );
        if self.start == self.end {
            self.exhausted = true;
            self.end
        } else {
            self.end -= 1;
            self.end + 1
        }
    }
}
//
impl DoubleEndedIterator for PositiveIntRangeInclusiveIter {
    fn next_back(&mut self) -> Option<Self::Item> {
        (!self.exhausted).then(|| self.next_back_unchecked())
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if self.len() > n {
            self.end -= PositiveInt::try_from(n).expect(
                "Cannot happen: len > n and len <= PositiveInt::MAX, \
                 therefore n < PositiveInt::MAX",
            );
            Some(self.next_back_unchecked())
        } else {
            self.end = self.start;
            self.exhausted = true;
            None
        }
    }
}
//
impl ExactSizeIterator for PositiveIntRangeInclusiveIter {
    fn len(&self) -> usize {
        if self.exhausted {
            0
        } else {
            usize::from(self.end) - usize::from(self.start) + 1
        }
    }
}
//
impl FusedIterator for PositiveIntRangeInclusiveIter {}
//
impl Iterator for PositiveIntRangeInclusiveIter {
    type Item = PositiveInt;

    fn next(&mut self) -> Option<PositiveInt> {
        (!self.exhausted).then(|| self.next_unchecked())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }

    fn count(self) -> usize {
        self.len()
    }

    fn last(self) -> Option<PositiveInt> {
        (!self.exhausted).then_some(self.end)
    }

    fn nth(&mut self, n: usize) -> Option<PositiveInt> {
        if self.len() > n {
            self.start += PositiveInt::try_from(n).expect(
                "Cannot happen: len > n and len <= PositiveInt::MAX, \
                 therefore n < PositiveInt::MAX",
            );
            Some(self.next_unchecked())
        } else {
            self.start = self.end;
            self.exhausted = true;
            None
        }
    }
}

/// [`RangeFrom`]-like iterator for [`PositiveInt`]
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
struct PositiveIntRangeFromIter(PositiveInt);
//
impl FusedIterator for PositiveIntRangeFromIter {}
//
impl Iterator for PositiveIntRangeFromIter {
    type Item = PositiveInt;

    #[inline]
    fn next(&mut self) -> Option<PositiveInt> {
        self.0 += 1;
        Some(self.0 - 1)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }

    fn count(self) -> usize {
        panic!("Attempted to consume an iterator with infinite elements")
    }

    fn last(self) -> Option<PositiveInt> {
        panic!("Attempted to consume an iterator with infinite elements")
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<PositiveInt> {
        self.0 += PositiveInt::try_from(n).expect("Increment is out of range");
        self.next()
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::cognitive_complexity, clippy::op_ref, clippy::too_many_lines)]
    use super::*;
    #[allow(unused)]
    use pretty_assertions::{assert_eq, assert_ne};
    use quickcheck_macros::quickcheck;
    use std::{
        collections::hash_map::DefaultHasher,
        ffi::c_uint,
        hash::{Hash, Hasher},
        num::IntErrorKind,
        panic::{RefUnwindSafe, UnwindSafe},
    };

    /// Inner bits of [`PositiveInt`] that are not used by the implementation
    const UNUSED_BITS: c_uint = 1 << PositiveInt::EFFECTIVE_BITS;

    /// Number of bits that are not used
    const NUM_UNUSED_BITS: u32 = UNUSED_BITS.count_ones();

    /// Maximum number of exploratory iterations to run for infinite iterators
    const INFINITE_ITERS: usize = 10;

    /// Assert that calling some code panics
    #[track_caller]
    fn assert_panics<R: Debug>(f: impl FnOnce() -> R + UnwindSafe) {
        std::panic::catch_unwind(f).expect_err("Operation should have panicked, but didn't");
    }

    /// Assert that calling some code panics in debug builds and does not do so
    /// in release builds
    #[track_caller]
    fn assert_debug_panics<R: Debug + Eq>(f: impl FnOnce() -> R + UnwindSafe, release_result: R) {
        let res = std::panic::catch_unwind(f);
        if cfg!(debug_assertions) {
            res.expect_err("Operation should have panicked, but didn't panic");
        } else {
            let result = res.expect("Operation should not have panicked, but did panic");
            assert_eq!(
                result, release_result,
                "Operation does not produce the expected result in release builds"
            );
        }
    }

    /// Compare a [`PositiveInt`] and a [`c_uint`] iterator in a certain iteration scheme,
    /// stopping after a certain number of elements
    #[track_caller]
    fn compare_iters_infinite<Actual, Expected>(
        mut actual: Actual,
        mut next_actual: impl FnMut(&mut Actual) -> Option<PositiveInt>,
        mut expected: Expected,
        mut next_expected: impl FnMut(&mut Expected) -> Option<c_uint>,
    ) {
        for _ in 0..INFINITE_ITERS {
            match (next_actual(&mut actual), next_expected(&mut expected)) {
                (Some(actual), Some(expected)) => assert_eq!(actual, PositiveInt(expected)),
                (None, None) => panic!("Infinite iterators shouldn't end"),
                (Some(_), None) | (None, Some(_)) => panic!("Length shouldn't differ"),
            }
        }
    }

    /// Compare a [`PositiveInt`] and a [`c_uint`] iterator in a certain iteration scheme
    #[track_caller]
    fn compare_iters_finite<Actual, Expected>(
        mut actual: Actual,
        mut next_actual: impl FnMut(&mut Actual) -> Option<PositiveInt>,
        mut expected: Expected,
        mut next_expected: impl FnMut(&mut Expected) -> Option<c_uint>,
    ) {
        loop {
            match (next_actual(&mut actual), next_expected(&mut expected)) {
                (Some(actual), Some(expected)) => assert_eq!(actual, PositiveInt(expected)),
                (None, None) => break,
                (Some(_), None) | (None, Some(_)) => panic!("Length shouldn't differ"),
            }
        }
    }

    /// Hash something
    fn hash(x: impl Hash) -> u64 {
        let mut hasher = DefaultHasher::new();
        x.hash(&mut hasher);
        hasher.finish()
    }

    /// Test basic properties of our constants
    #[test]
    fn constants() {
        // Constants and conversions to/from bool
        assert_eq!(PositiveInt::MIN, PositiveInt::ZERO);
        assert_eq!(PositiveInt::ZERO, 0);
        assert_eq!(PositiveInt::ONE, 1);
        assert_eq!(
            PositiveInt::MAX,
            (1usize << PositiveInt::EFFECTIVE_BITS) - 1
        );
        assert_eq!(PositiveInt::default(), 0);
        assert_eq!(PositiveInt::from(false), 0);
        assert_eq!(PositiveInt::from(true), 1);

        // Now let's test some properties that are specific to zero
        let zero = PositiveInt::ZERO;

        // Logarithm fails for zero
        assert_panics(|| zero.ilog2());
        assert_panics(|| zero.ilog10());
        assert_eq!(zero.checked_ilog2(), None);
        assert_eq!(zero.checked_ilog10(), None);

        // Negation succeeds for zero
        assert_eq!(zero.wrapping_neg(), zero);
        assert_eq!(zero.checked_neg(), Some(zero));
        assert_eq!(zero.overflowing_neg(), (zero, false));
    }

    /// Test properties of unary operations on positive ints
    #[quickcheck]
    fn unary_int(int: PositiveInt) {
        // Version of int's payload with the unused bits set
        let set_unused = int.0 | UNUSED_BITS;

        // Make sure clone is trivial and equality works early on
        assert_eq!(int.clone(), int);

        // Bit fiddling
        assert_eq!(int.count_ones(), int.0.count_ones());
        assert_eq!(int.count_zeros(), set_unused.count_zeros());
        assert_eq!(int.leading_zeros(), int.0.leading_zeros() - NUM_UNUSED_BITS);
        assert_eq!(int.trailing_zeros(), set_unused.trailing_zeros());
        assert_eq!(
            int.leading_ones(),
            set_unused.leading_ones() - NUM_UNUSED_BITS
        );
        assert_eq!(int.trailing_ones(), int.0.trailing_ones());
        assert_eq!(
            int.reverse_bits().0,
            int.0.reverse_bits() >> NUM_UNUSED_BITS
        );
        assert_eq!(int.is_power_of_two(), int.0.is_power_of_two());
        assert_eq!((!int).0, !(int.0 | set_unused));
        assert_eq!((!&int).0, !(int.0 | set_unused));

        // Infaillible conversion to isize and usize
        assert_eq!(isize::from(int), isize::try_from(int.0).unwrap());
        assert_eq!(usize::from(int), usize::try_from(int.0).unwrap());

        // Faillible conversions to all primitive integer types
        #[allow(clippy::useless_conversion)]
        {
            assert_eq!(i8::try_from(int).ok(), i8::try_from(int.0).ok());
            assert_eq!(u8::try_from(int).ok(), u8::try_from(int.0).ok());
            assert_eq!(i16::try_from(int).ok(), i16::try_from(int.0).ok());
            assert_eq!(u16::try_from(int).ok(), u16::try_from(int.0).ok());
            assert_eq!(i32::try_from(int).ok(), i32::try_from(int.0).ok());
            assert_eq!(u32::try_from(int).ok(), u32::try_from(int.0).ok());
            assert_eq!(i64::try_from(int).ok(), i64::try_from(int.0).ok());
            assert_eq!(u64::try_from(int).ok(), u64::try_from(int.0).ok());
            assert_eq!(i128::try_from(int).ok(), i128::try_from(int.0).ok());
            assert_eq!(u128::try_from(int).ok(), u128::try_from(int.0).ok());
        }

        // Formatting
        assert_eq!(format!("{int:?}"), format!("PositiveInt({:})", int.0));
        assert_eq!(format!("{int}"), format!("{:}", int.0));
        assert_eq!(format!("{int:b}"), format!("{:b}", int.0));
        assert_eq!(format!("{int:e}"), format!("{:e}", int.0));
        assert_eq!(format!("{int:o}"), format!("{:o}", int.0));
        assert_eq!(format!("{int:x}"), format!("{:x}", int.0));
        assert_eq!(format!("{int:E}"), format!("{:E}", int.0));
        assert_eq!(format!("{int:X}"), format!("{:X}", int.0));

        // Hashing
        assert_eq!(hash(int), hash(int.0));

        // Division and remainder by zero
        {
            // With PositiveInt denominator
            let zero = PositiveInt::ZERO;
            assert_eq!(int.checked_div(zero), None);
            assert_panics(|| int.overflowing_div(zero));
            assert_panics(|| int.saturating_div(zero));
            assert_panics(|| int.wrapping_div(zero));
            assert_panics(|| int / zero);
            assert_panics(|| &int / zero);
            assert_panics(|| int / &zero);
            assert_panics(|| &int / &zero);
            assert_panics(|| {
                let mut tmp = int;
                tmp /= zero
            });
            assert_panics(|| {
                let mut tmp = int;
                tmp /= &zero
            });
            assert_eq!(int.checked_div_euclid(zero), None);
            assert_panics(|| int.overflowing_div_euclid(zero));
            assert_panics(|| int.wrapping_div_euclid(zero));
            assert_eq!(int.checked_rem(zero), None);
            assert_panics(|| int.overflowing_rem(zero));
            assert_panics(|| int.wrapping_rem(zero));
            assert_panics(|| int % zero);
            assert_panics(|| &int % zero);
            assert_panics(|| int % &zero);
            assert_panics(|| &int % &zero);
            assert_panics(|| {
                let mut tmp = int;
                tmp %= zero
            });
            assert_panics(|| {
                let mut tmp = int;
                tmp %= &zero
            });
            assert_eq!(int.checked_rem_euclid(zero), None);
            assert_panics(|| int.overflowing_rem_euclid(zero));
            assert_panics(|| int.wrapping_rem_euclid(zero));

            // With usize denominator
            assert_panics(|| int / 0);
            assert_panics(|| &int / 0);
            assert_panics(|| int / &0);
            assert_panics(|| &int / &0);
            assert_panics(|| {
                let mut tmp = int;
                tmp /= 0
            });
            assert_panics(|| {
                let mut tmp = int;
                tmp /= &0
            });
            assert_panics(|| int % 0);
            assert_panics(|| &int % 0);
            assert_panics(|| int % &0);
            assert_panics(|| &int % &0);
            assert_panics(|| {
                let mut tmp = int;
                tmp %= 0
            });
            assert_panics(|| {
                let mut tmp = int;
                tmp %= &0
            });
        }

        // Logarithm of zero should fail/panic
        {
            // ...with base >= 2
            let base_above2 = int.saturating_add(PositiveInt(2));
            assert_panics(|| PositiveInt::ZERO.ilog(base_above2));
            assert_eq!(PositiveInt::ZERO.checked_ilog(base_above2), None);

            // ...with base < 2
            let base_below2 = int % 2;
            assert_panics(|| PositiveInt::ZERO.ilog(base_below2));
            assert_eq!(PositiveInt::ZERO.checked_ilog(base_below2), None);
        }

        // Considerations specific to positive numbers
        if int != 0 {
            // Based logarithms succeed for positive numbers
            let expected_log2 = int.0.ilog2();
            let expected_log10 = int.0.ilog10();
            assert_eq!(int.ilog2(), expected_log2);
            assert_eq!(int.ilog10(), expected_log10);
            assert_eq!(int.checked_ilog2(), Some(expected_log2));
            assert_eq!(int.checked_ilog10(), Some(expected_log10));

            // Negation fails or wraps around for positive numbers
            let wrapping_neg = (!int).wrapping_add(PositiveInt(1));
            assert_eq!(int.checked_neg(), None);
            assert_eq!(int.wrapping_neg(), wrapping_neg);
            assert_eq!(int.overflowing_neg(), (wrapping_neg, true));
        }

        // Considerations specific to numbers that have a next power of 2
        let last_pow2 = PositiveInt::ONE << (PositiveInt::EFFECTIVE_BITS - 1);
        let has_next_pow2 = int & (!last_pow2);
        let next_pow2 = PositiveInt(has_next_pow2.0.next_power_of_two());
        assert_eq!(has_next_pow2.next_power_of_two(), next_pow2);
        assert_eq!(has_next_pow2.checked_next_power_of_two(), Some(next_pow2));

        // Considerations specific to numbers that don't have a next power of 2
        let mut no_next_pow2 = int | last_pow2;
        if no_next_pow2 == last_pow2 {
            no_next_pow2 += 1;
        }
        assert_debug_panics(|| no_next_pow2.next_power_of_two(), PositiveInt::ZERO);
        assert_eq!(no_next_pow2.checked_next_power_of_two(), None);

        // Check RangeFrom-like PositiveInt iterator
        let actual = PositiveInt::iter_range_from(int);
        let expected = (int.0)..;
        assert_eq!(actual.size_hint(), expected.size_hint());
        assert_panics(|| actual.clone().count());
        assert_panics(|| actual.clone().last());
        compare_iters_infinite(actual, Iterator::next, expected, Iterator::next);
    }

    /// Test usize -> PositiveInt conversion and special positive-usize ops
    #[quickcheck]
    fn unary_usize(x: usize) {
        // usize -> PositiveInt conversion
        assert_eq!(
            PositiveInt::try_from(x),
            c_int::try_from(x).map(|i| PositiveInt(i.try_into().unwrap()))
        );

        // Multiplying ZERO by any usize works
        let zero = PositiveInt::ZERO;
        assert_eq!(zero * x, zero);
        assert_eq!(x * zero, zero);
        assert_eq!(&zero * x, zero);
        assert_eq!(x * (&zero), zero);
        assert_eq!(zero * (&x), zero);
        assert_eq!(&x * zero, zero);
        assert_eq!(&zero * (&x), zero);
        assert_eq!(&x * (&zero), zero);
        let mut tmp = zero;
        tmp *= x;
        assert_eq!(tmp, zero);
        tmp = zero;
        tmp *= &x;
        assert_eq!(tmp, zero);
    }

    /// Test [`str`] -> [`PositiveInt`] conversion (common harness)
    fn test_from_str_radix(
        src: &str,
        radix: u32,
        parse: impl FnOnce() -> Result<PositiveInt, ParseIntError> + UnwindSafe,
    ) {
        // Handle excessive radix
        if !(2..=36).contains(&radix) {
            assert_panics(parse);
            return;
        }
        let result = parse();

        // Use known-good parser to usize
        let Ok(as_usize) = usize::from_str_radix(src, radix) else {
            // If it fails for usize, it should fail for PositiveInt
            assert!(result.is_err());
            return;
        };

        // Handle the fact that valid PositiveInt is a subset of usize
        const MAX: usize = PositiveInt::MAX.0 as usize;
        match as_usize {
            0..=MAX => {
                assert_eq!(result.unwrap(), as_usize);
            }
            _overflow => {
                assert_eq!(result.unwrap_err().kind(), &IntErrorKind::PosOverflow);
            }
        }
    }

    /// Test str -> PositiveInt conversion via the FromStr trait
    #[quickcheck]
    fn from_str(src: String) {
        test_from_str_radix(&src, 10, || PositiveInt::from_str(&src))
    }

    /// Test str -> PositiveInt conversion via the from_str_radix() method
    #[quickcheck]
    fn from_str_radix(src: String, radix: u32) {
        let radix = radix % 37;
        test_from_str_radix(&src, radix, || PositiveInt::from_str_radix(&src, radix))
    }

    /// Test a faillible operation, produce the checked result for verification
    ///
    /// If `release_result` is `Some(result)`, it indicates that in release
    /// builds, the faillible operation will return `result` instead of
    /// panicking. This is the behavior of most built-in arithmetic operations.
    ///
    /// If `release_result` is `None`, it indicates that the faillible operation
    /// should panick even in release mode, as e.g. ilog() does.
    fn test_faillible<Rhs: Copy + RefUnwindSafe, const LEN: usize>(
        int: PositiveInt,
        rhs: Rhs,
        checked_op: impl FnOnce(PositiveInt, Rhs) -> Option<PositiveInt>,
        faillible_ops: [Box<dyn Fn(PositiveInt, Rhs) -> PositiveInt + RefUnwindSafe>; LEN],
        release_result: Option<PositiveInt>,
    ) -> Option<PositiveInt> {
        let checked_result = checked_op(int, rhs);
        match (checked_result, release_result) {
            (Some(result), _) => {
                for faillible_op in faillible_ops {
                    assert_eq!(faillible_op(int, rhs), result);
                }
            }
            (None, Some(release_result)) => {
                for faillible_op in faillible_ops {
                    assert_debug_panics(|| faillible_op(int, rhs), release_result);
                }
            }
            (None, None) => {
                for faillible_op in faillible_ops {
                    assert_panics(|| faillible_op(int, rhs));
                }
            }
        }
        checked_result
    }

    /// Test an overflowing operation, produce the overflowing result for verification
    fn test_overflowing<Rhs: Copy + RefUnwindSafe, const LEN: usize>(
        int: PositiveInt,
        rhs: Rhs,
        checked_op: impl Fn(PositiveInt, Rhs) -> Option<PositiveInt>,
        overflowing_op: impl Fn(PositiveInt, Rhs) -> (PositiveInt, bool),
        wrapping_op: impl Fn(PositiveInt, Rhs) -> PositiveInt,
        faillible_ops: [Box<dyn Fn(PositiveInt, Rhs) -> PositiveInt + RefUnwindSafe>; LEN],
    ) -> (PositiveInt, bool) {
        let overflowing_result = overflowing_op(int, rhs);
        let (wrapped_result, overflow) = overflowing_result;
        assert_eq!(wrapping_op(int, rhs), wrapped_result);
        let checked_result =
            test_faillible(int, rhs, checked_op, faillible_ops, Some(wrapped_result));
        if overflow {
            assert_eq!(checked_result, None);
        } else {
            assert_eq!(checked_result, Some(wrapped_result));
        }
        overflowing_result
    }

    /// Predict the result of an overflowing [`PositiveInt`] operation from the
    /// result of the equivalent overflowing usize operation.
    fn predict_overflowing_result<IntRhs, UsizeRhs: From<IntRhs>>(
        i1: PositiveInt,
        i2: IntRhs,
        usize_op: fn(usize, UsizeRhs) -> (usize, bool),
    ) -> (PositiveInt, bool) {
        let used_bits_usize = (1usize << PositiveInt::EFFECTIVE_BITS) - 1;
        let max_usize = usize::from(PositiveInt::MAX);
        let (wrapped_usize, overflow_usize) = usize_op(usize::from(i1), UsizeRhs::from(i2));
        let expected_wrapped = PositiveInt::try_from(wrapped_usize & used_bits_usize).unwrap();
        let expected_overflow = overflow_usize || (wrapped_usize > max_usize);
        (expected_wrapped, expected_overflow)
    }

    /// Test int-int binary operations
    #[quickcheck]
    fn int_int(i1: PositiveInt, i2: PositiveInt) {
        // Ordering passes through
        assert_eq!(i1 == i2, i1.0 == i2.0);
        assert_eq!(i1.cmp(&i2), i1.0.cmp(&i2.0));

        // Bitwise AND passes through (no risk of setting high-order bit)
        let expected = PositiveInt(i1.0 & i2.0);
        assert_eq!(i1 & i2, expected);
        assert_eq!(&i1 & i2, expected);
        assert_eq!(i1 & (&i2), expected);
        assert_eq!(&i1 & (&i2), expected);
        let mut tmp = i1;
        tmp &= i2;
        assert_eq!(tmp, expected);
        tmp = i1;
        tmp &= &i2;
        assert_eq!(tmp, expected);

        // Bitwise OR passes through (no risk of setting high-order bit)
        let expected = PositiveInt(i1.0 | i2.0);
        assert_eq!(i1 | i2, expected);
        assert_eq!(&i1 | i2, expected);
        assert_eq!(i1 | (&i2), expected);
        assert_eq!(&i1 | (&i2), expected);
        tmp = i1;
        tmp |= i2;
        assert_eq!(tmp, expected);
        tmp = i1;
        tmp |= &i2;
        assert_eq!(tmp, expected);

        // Bitwise XOR passes through (no risk of setting high-order bit)
        let expected = PositiveInt(i1.0 ^ i2.0);
        assert_eq!(i1 ^ i2, expected);
        assert_eq!(&i1 ^ i2, expected);
        assert_eq!(i1 ^ (&i2), expected);
        assert_eq!(&i1 ^ (&i2), expected);
        let mut tmp = i1;
        tmp ^= i2;
        assert_eq!(tmp, expected);
        tmp = i1;
        tmp ^= &i2;
        assert_eq!(tmp, expected);

        // Addition
        let (expected_wrapped, expected_overflow) =
            predict_overflowing_result(i1, i2, usize::overflowing_add);
        let (wrapped, overflow) = test_overflowing(
            i1,
            i2,
            PositiveInt::checked_add,
            PositiveInt::overflowing_add,
            PositiveInt::wrapping_add,
            [
                Box::new(|i1, i2| i1 + i2),
                Box::new(|i1, i2| &i1 + i2),
                Box::new(|i1, i2| i1 + &i2),
                Box::new(|i1, i2| &i1 + &i2),
                Box::new(|mut i1, i2| {
                    i1 += i2;
                    i1
                }),
                Box::new(|mut i1, i2| {
                    i1 += &i2;
                    i1
                }),
            ],
        );
        assert_eq!(wrapped, expected_wrapped);
        assert_eq!(overflow, expected_overflow);
        if overflow {
            assert_eq!(i1.saturating_add(i2), PositiveInt::MAX);
        } else {
            assert_eq!(i1.saturating_add(i2), wrapped);
        }

        // Subtraction
        let (expected_wrapped, expected_overflow) =
            predict_overflowing_result(i1, i2, usize::overflowing_sub);
        let (wrapped, overflow) = test_overflowing(
            i1,
            i2,
            PositiveInt::checked_sub,
            PositiveInt::overflowing_sub,
            PositiveInt::wrapping_sub,
            [
                Box::new(|i1, i2| i1 - i2),
                Box::new(|i1, i2| &i1 - i2),
                Box::new(|i1, i2| i1 - &i2),
                Box::new(|i1, i2| &i1 - &i2),
                Box::new(|mut i1, i2| {
                    i1 -= i2;
                    i1
                }),
                Box::new(|mut i1, i2| {
                    i1 -= &i2;
                    i1
                }),
            ],
        );
        assert_eq!(wrapped, expected_wrapped);
        assert_eq!(overflow, expected_overflow);
        if overflow {
            assert_eq!(i1.saturating_sub(i2), PositiveInt::MIN);
        } else {
            assert_eq!(i1.saturating_sub(i2), wrapped);
        }

        // Absolute difference
        assert_eq!(i1.abs_diff(i2), PositiveInt(i1.0.abs_diff(i2.0)));

        // Multiplication
        let (expected_wrapped, expected_overflow) =
            predict_overflowing_result(i1, i2, usize::overflowing_mul);
        let (wrapped, overflow) = test_overflowing(
            i1,
            i2,
            PositiveInt::checked_mul,
            PositiveInt::overflowing_mul,
            PositiveInt::wrapping_mul,
            [
                Box::new(|i1, i2| i1 * i2),
                Box::new(|i1, i2| &i1 * i2),
                Box::new(|i1, i2| i1 * &i2),
                Box::new(|i1, i2| &i1 * &i2),
                Box::new(|mut i1, i2| {
                    i1 *= i2;
                    i1
                }),
                Box::new(|mut i1, i2| {
                    i1 *= &i2;
                    i1
                }),
            ],
        );
        assert_eq!(wrapped, expected_wrapped);
        assert_eq!(overflow, expected_overflow);
        if overflow {
            assert_eq!(i1.saturating_mul(i2), PositiveInt::MAX);
        } else {
            assert_eq!(i1.saturating_mul(i2), wrapped);
        }

        // Division and remainder by nonzero (zero case tested in unary tests)
        {
            // Division
            let nonzero = i2.saturating_add(PositiveInt::ONE);
            let (expected_wrapped, expected_overflow) =
                predict_overflowing_result(i1, nonzero, usize::overflowing_div);
            let res1 = test_overflowing(
                i1,
                nonzero,
                PositiveInt::checked_div,
                PositiveInt::overflowing_div,
                PositiveInt::wrapping_div,
                [
                    Box::new(|i1, nonzero| i1 / nonzero),
                    Box::new(|i1, nonzero| &i1 / nonzero),
                    Box::new(|i1, nonzero| i1 / &nonzero),
                    Box::new(|i1, nonzero| &i1 / &nonzero),
                    Box::new(|mut i1, nonzero| {
                        i1 /= nonzero;
                        i1
                    }),
                    Box::new(|mut i1, nonzero| {
                        i1 /= &nonzero;
                        i1
                    }),
                ],
            );
            let res2 = test_overflowing(
                i1,
                nonzero,
                PositiveInt::checked_div_euclid,
                PositiveInt::overflowing_div_euclid,
                PositiveInt::wrapping_div_euclid,
                [Box::new(PositiveInt::div_euclid)],
            );
            assert_eq!(i1.saturating_div(nonzero), expected_wrapped);
            for (wrapped, overflow) in [res1, res2] {
                assert_eq!(wrapped, expected_wrapped);
                assert_eq!(overflow, expected_overflow);
            }

            // Remainder
            let (expected_wrapped, expected_overflow) =
                predict_overflowing_result(i1, nonzero, usize::overflowing_rem);
            let res1 = test_overflowing(
                i1,
                nonzero,
                PositiveInt::checked_rem,
                PositiveInt::overflowing_rem,
                PositiveInt::wrapping_rem,
                [
                    Box::new(|i1, nonzero| i1 % nonzero),
                    Box::new(|i1, nonzero| &i1 % nonzero),
                    Box::new(|i1, nonzero| i1 % &nonzero),
                    Box::new(|i1, nonzero| &i1 % &nonzero),
                    Box::new(|mut i1, nonzero| {
                        i1 %= nonzero;
                        i1
                    }),
                    Box::new(|mut i1, nonzero| {
                        i1 %= &nonzero;
                        i1
                    }),
                ],
            );
            let res2 = test_overflowing(
                i1,
                nonzero,
                PositiveInt::checked_rem_euclid,
                PositiveInt::overflowing_rem_euclid,
                PositiveInt::wrapping_rem_euclid,
                [Box::new(PositiveInt::rem_euclid)],
            );
            for (wrapped, overflow) in [res1, res2] {
                assert_eq!(wrapped, expected_wrapped);
                assert_eq!(overflow, expected_overflow);
            }
        }

        // Checked logarithm
        {
            // Should succeed for a number >= 0 with a basis >= 2
            let number_above0 = i1.saturating_add(PositiveInt::ONE);
            let base_above2 = i2.saturating_add(PositiveInt(2));
            let expected = number_above0.0.ilog(base_above2.0);
            assert_eq!(number_above0.ilog(base_above2), expected);
            assert_eq!(number_above0.checked_ilog(base_above2), Some(expected));

            // Should fail if the basis is below 2
            let base_below2 = i2 % 2;
            assert_panics(|| PositiveInt::ZERO.ilog(base_below2));
            assert_eq!(PositiveInt::ZERO.checked_ilog(base_below2), None);
        }

        // Non-overflowing left shift must keep high-order bit cleared
        #[allow(trivial_numeric_casts)]
        let effective_bits = PositiveInt(PositiveInt::EFFECTIVE_BITS as c_uint);
        let wrapped_shift = i2 % effective_bits;
        let wrapped_result = PositiveInt((i1.0 << wrapped_shift.0) & PositiveInt::MAX.0);
        assert_eq!(i1 << wrapped_shift, wrapped_result);
        assert_eq!(&i1 << wrapped_shift, wrapped_result);
        assert_eq!(i1 << (&wrapped_shift), wrapped_result);
        assert_eq!(&i1 << (&wrapped_shift), wrapped_result);
        tmp = i1;
        tmp <<= wrapped_shift;
        assert_eq!(tmp, wrapped_result);
        tmp = i1;
        tmp <<= &wrapped_shift;
        assert_eq!(tmp, wrapped_result);

        // Overflowing left shift should panic or wraparound
        let overflown_shift = i2.saturating_add(effective_bits);
        assert_debug_panics(|| i1 << overflown_shift, wrapped_result);
        assert_debug_panics(|| &i1 << overflown_shift, wrapped_result);
        assert_debug_panics(|| i1 << (&overflown_shift), wrapped_result);
        assert_debug_panics(|| &i1 << (&overflown_shift), wrapped_result);
        assert_debug_panics(
            || {
                let mut tmp = i1;
                tmp <<= overflown_shift;
                tmp
            },
            wrapped_result,
        );
        assert_debug_panics(
            || {
                let mut tmp = i1;
                tmp <<= &overflown_shift;
                tmp
            },
            wrapped_result,
        );

        // Non-overflowing right shift can pass through
        let wrapped_result = PositiveInt(i1.0 >> wrapped_shift.0);
        assert_eq!(i1 >> wrapped_shift, wrapped_result);
        assert_eq!(&i1 >> wrapped_shift, wrapped_result);
        assert_eq!(i1 >> (&wrapped_shift), wrapped_result);
        assert_eq!(&i1 >> (&wrapped_shift), wrapped_result);
        tmp = i1;
        tmp >>= wrapped_shift;
        assert_eq!(tmp, wrapped_result);
        tmp = i1;
        tmp >>= &wrapped_shift;
        assert_eq!(tmp, wrapped_result);

        // Overflowing right shift should panic or wraparound
        assert_debug_panics(|| i1 >> overflown_shift, wrapped_result);
        assert_debug_panics(|| &i1 >> overflown_shift, wrapped_result);
        assert_debug_panics(|| i1 >> (&overflown_shift), wrapped_result);
        assert_debug_panics(|| &i1 >> (&overflown_shift), wrapped_result);
        assert_debug_panics(
            || {
                let mut tmp = i1;
                tmp >>= overflown_shift;
                tmp
            },
            wrapped_result,
        );
        assert_debug_panics(
            || {
                let mut tmp = i1;
                tmp >>= &overflown_shift;
                tmp
            },
            wrapped_result,
        );

        // Check Range-like PositiveInt iterator
        let actual = PositiveInt::iter_range(i1, i2);
        let expected = (i1.0)..(i2.0);
        assert_eq!(actual.len(), expected.len());
        assert_eq!(actual.size_hint(), expected.size_hint());
        assert_eq!(actual.clone().count(), expected.len());
        assert_eq!(
            actual.clone().last(),
            expected.clone().last().map(PositiveInt)
        );
        compare_iters_finite(
            actual.clone(),
            Iterator::next,
            expected.clone(),
            Iterator::next,
        );
        compare_iters_finite(
            actual,
            DoubleEndedIterator::next_back,
            expected,
            DoubleEndedIterator::next_back,
        );

        // Check RangeInclusive-like PositiveInt iterator
        let actual = PositiveInt::iter_range_inclusive(i1, i2);
        let expected = (i1.0)..=(i2.0);
        assert_eq!(actual.len(), expected.clone().count());
        assert_eq!(actual.size_hint(), expected.size_hint());
        assert_eq!(actual.clone().count(), expected.clone().count());
        assert_eq!(
            actual.clone().last(),
            expected.clone().last().map(PositiveInt)
        );
        compare_iters_finite(
            actual.clone(),
            Iterator::next,
            expected.clone(),
            Iterator::next,
        );
        compare_iters_finite(
            actual,
            DoubleEndedIterator::next_back,
            expected,
            DoubleEndedIterator::next_back,
        );
    }

    /// Test int-u32 binary operations
    #[quickcheck]
    fn int_u32(int: PositiveInt, rhs: u32) {
        // Elevation to an integer power
        let (expected_wrapped, expected_overflow) =
            predict_overflowing_result(int, rhs, usize::overflowing_pow);
        let (wrapped, overflow) = test_overflowing(
            int,
            rhs,
            PositiveInt::checked_pow,
            PositiveInt::overflowing_pow,
            PositiveInt::wrapping_pow,
            [Box::new(PositiveInt::pow)],
        );
        assert_eq!(wrapped, expected_wrapped);
        assert_eq!(overflow, expected_overflow);
        if overflow {
            assert_eq!(int.saturating_pow(rhs), PositiveInt::MAX);
        } else {
            assert_eq!(int.saturating_pow(rhs), wrapped);
        }

        // Non-overflowing left shift
        let test_left_shift = |rhs| {
            test_overflowing(
                int,
                rhs,
                PositiveInt::checked_shl,
                PositiveInt::overflowing_shl,
                PositiveInt::wrapping_shl,
                [
                    Box::new(|int, rhs| int << rhs),
                    Box::new(|int, rhs| &int << rhs),
                    Box::new(|int, rhs| int << &rhs),
                    Box::new(|int, rhs| &int << &rhs),
                    Box::new(|mut int, rhs| {
                        int <<= rhs;
                        int
                    }),
                    Box::new(|mut int, rhs| {
                        int <<= &rhs;
                        int
                    }),
                ],
            )
        };
        let wrapped_shift = rhs % PositiveInt::EFFECTIVE_BITS;
        let expected_wrapped = PositiveInt((int.0 << wrapped_shift) & PositiveInt::MAX.0);
        let (wrapped, overflow) = test_left_shift(wrapped_shift);
        assert_eq!(wrapped, expected_wrapped);
        assert!(!overflow);

        // Overflowing left shift
        let overflown_shift = rhs.saturating_add(PositiveInt::EFFECTIVE_BITS);
        let (wrapped, overflow) = test_left_shift(overflown_shift);
        assert_eq!(wrapped, expected_wrapped);
        assert!(overflow);

        // Non-overflowing right shift
        let test_right_shift = |rhs| {
            test_overflowing(
                int,
                rhs,
                PositiveInt::checked_shr,
                PositiveInt::overflowing_shr,
                PositiveInt::wrapping_shr,
                [
                    Box::new(|int, rhs| int >> rhs),
                    Box::new(|int, rhs| &int >> rhs),
                    Box::new(|int, rhs| int >> &rhs),
                    Box::new(|int, rhs| &int >> &rhs),
                    Box::new(|mut int, rhs| {
                        int >>= rhs;
                        int
                    }),
                    Box::new(|mut int, rhs| {
                        int >>= &rhs;
                        int
                    }),
                ],
            )
        };
        let expected_wrapped = PositiveInt(int.0 >> wrapped_shift);
        let (wrapped, overflow) = test_right_shift(wrapped_shift);
        assert_eq!(wrapped, expected_wrapped);
        assert!(!overflow);

        // Overflowing right shift
        let (wrapped, overflow) = test_right_shift(overflown_shift);
        assert_eq!(wrapped, expected_wrapped);
        assert!(overflow);

        // Rotate can be expressed in terms of shifts and binary ops
        assert_eq!(
            int.rotate_left(rhs),
            (int << wrapped_shift) | int.wrapping_shr(PositiveInt::EFFECTIVE_BITS - wrapped_shift)
        );
        assert_eq!(
            int.rotate_right(rhs),
            (int >> wrapped_shift) | int.wrapping_shl(PositiveInt::EFFECTIVE_BITS - wrapped_shift)
        );
    }

    /// Test int-usize binary operations
    #[quickcheck]
    fn int_usize(int: PositiveInt, other: usize) {
        // Ordering passes through
        assert_eq!(int == other, usize::from(int) == other);
        assert_eq!(
            int.partial_cmp(&other),
            usize::from(int).partial_cmp(&other)
        );
        assert_eq!(other == int, other == usize::from(int));
        assert_eq!(
            other.partial_cmp(&int),
            other.partial_cmp(&usize::from(int))
        );

        // Bitwise AND passes through (no risk of setting high-order bit)
        #[allow(clippy::cast_possible_truncation)]
        let expected = PositiveInt(int.0 & (other as c_uint));
        assert_eq!(int & other, expected);
        assert_eq!(other & int, expected);
        assert_eq!(&int & other, expected);
        assert_eq!(&other & int, expected);
        assert_eq!(int & (&other), expected);
        assert_eq!(other & (&int), expected);
        assert_eq!(&int & (&other), expected);
        assert_eq!(&other & (&int), expected);
        let mut tmp = int;
        tmp &= other;
        assert_eq!(tmp, expected);
        tmp = int;
        tmp &= &other;
        assert_eq!(tmp, expected);

        // Non-overflowing bitwise OR
        let small_other = other & usize::from(PositiveInt::MAX);
        let small_other_unsigned = c_uint::try_from(small_other).unwrap();
        let expected = PositiveInt(int.0 | small_other_unsigned);
        assert_eq!(int | small_other, expected);
        assert_eq!(small_other | int, expected);
        assert_eq!(&int | small_other, expected);
        assert_eq!(small_other | &int, expected);
        assert_eq!(int | &small_other, expected);
        assert_eq!(&small_other | int, expected);
        assert_eq!(&int | &small_other, expected);
        assert_eq!(&small_other | &int, expected);
        tmp = int;
        tmp |= small_other;
        assert_eq!(tmp, expected);
        tmp = int;
        tmp |= &small_other;
        assert_eq!(tmp, expected);

        // Overflowing bitwise OR
        let first_large_bit = 1usize << PositiveInt::EFFECTIVE_BITS;
        let mut large_other = other;
        if other < first_large_bit {
            large_other |= first_large_bit
        };
        assert_debug_panics(|| int | large_other, expected);
        assert_debug_panics(|| large_other | int, expected);
        assert_debug_panics(|| &int | large_other, expected);
        assert_debug_panics(|| large_other | &int, expected);
        assert_debug_panics(|| int | &large_other, expected);
        assert_debug_panics(|| &large_other | int, expected);
        assert_debug_panics(|| &int | &large_other, expected);
        assert_debug_panics(|| &large_other | &int, expected);
        assert_debug_panics(
            || {
                let mut tmp = int;
                tmp |= large_other;
                tmp
            },
            expected,
        );
        assert_debug_panics(
            || {
                let mut tmp = int;
                tmp |= &large_other;
                tmp
            },
            expected,
        );

        // Non-overflowing bitwise XOR
        let expected = PositiveInt(int.0 ^ small_other_unsigned);
        assert_eq!(int ^ small_other, expected);
        assert_eq!(small_other ^ int, expected);
        assert_eq!(&int ^ small_other, expected);
        assert_eq!(small_other ^ &int, expected);
        assert_eq!(int ^ &small_other, expected);
        assert_eq!(&small_other ^ int, expected);
        assert_eq!(&int ^ &small_other, expected);
        assert_eq!(&small_other ^ &int, expected);
        tmp = int;
        tmp ^= small_other;
        assert_eq!(tmp, expected);
        tmp = int;
        tmp ^= &small_other;
        assert_eq!(tmp, expected);

        // Overflowing bitwise XOR
        assert_debug_panics(|| int ^ large_other, expected);
        assert_debug_panics(|| large_other ^ int, expected);
        assert_debug_panics(|| &int ^ large_other, expected);
        assert_debug_panics(|| large_other ^ &int, expected);
        assert_debug_panics(|| int ^ &large_other, expected);
        assert_debug_panics(|| &large_other ^ int, expected);
        assert_debug_panics(|| &int ^ &large_other, expected);
        assert_debug_panics(|| &large_other ^ &int, expected);
        assert_debug_panics(
            || {
                let mut tmp = int;
                tmp ^= large_other;
                tmp
            },
            expected,
        );
        assert_debug_panics(
            || {
                let mut tmp = int;
                tmp ^= &large_other;
                tmp
            },
            expected,
        );

        // Multiplication by an usize in PositiveInt range works as usual
        let small_other_int = PositiveInt::try_from(small_other).unwrap();
        let (wrapped, overflow) = int.overflowing_mul(small_other_int);
        if overflow {
            assert_debug_panics(|| int * small_other, wrapped);
            assert_debug_panics(|| small_other * int, wrapped);
            assert_debug_panics(|| &int * small_other, wrapped);
            assert_debug_panics(|| small_other * (&int), wrapped);
            assert_debug_panics(|| int * (&small_other), wrapped);
            assert_debug_panics(|| &small_other * int, wrapped);
            assert_debug_panics(|| &int * (&small_other), wrapped);
            assert_debug_panics(|| &small_other * (&int), wrapped);
            assert_debug_panics(
                || {
                    let mut tmp = int;
                    tmp *= small_other;
                    tmp
                },
                wrapped,
            );
            assert_debug_panics(
                || {
                    let mut tmp = int;
                    tmp *= &small_other;
                    tmp
                },
                wrapped,
            );
        } else {
            assert_eq!(int * small_other, wrapped);
            assert_eq!(small_other * int, wrapped);
            assert_eq!(&int * small_other, wrapped);
            assert_eq!(small_other * (&int), wrapped);
            assert_eq!(int * (&small_other), wrapped);
            assert_eq!(&small_other * int, wrapped);
            assert_eq!(&int * (&small_other), wrapped);
            assert_eq!(&small_other * (&int), wrapped);
            tmp = int;
            tmp *= small_other;
            assert_eq!(tmp, wrapped);
            tmp = int;
            tmp *= &small_other;
            assert_eq!(tmp, wrapped);
        }

        // Multiplication by an out-of-range usize fails for all ints but
        // zero (which is tested elsewhere)
        let zero = PositiveInt::ZERO;
        if int != zero {
            assert_debug_panics(|| int * large_other, wrapped);
            assert_debug_panics(|| large_other * int, wrapped);
            assert_debug_panics(|| &int * large_other, wrapped);
            assert_debug_panics(|| large_other * (&int), wrapped);
            assert_debug_panics(|| int * (&large_other), wrapped);
            assert_debug_panics(|| &large_other * int, wrapped);
            assert_debug_panics(|| &int * (&large_other), wrapped);
            assert_debug_panics(|| &large_other * (&int), wrapped);
            assert_debug_panics(
                || {
                    let mut tmp = int;
                    tmp *= large_other;
                    tmp
                },
                wrapped,
            );
            assert_debug_panics(
                || {
                    let mut tmp = int;
                    tmp *= &large_other;
                    tmp
                },
                wrapped,
            );
        }

        // Division by an in-range nonzero usize passes through
        if other != 0 {
            let expected = int / small_other_int;
            assert_eq!(int / small_other, expected);
            assert_eq!(&int / small_other, expected);
            assert_eq!(int / &small_other, expected);
            assert_eq!(&int / &small_other, expected);
            tmp = int;
            tmp /= small_other;
            assert_eq!(tmp, expected);
            tmp = int;
            tmp /= &small_other;
            assert_eq!(tmp, expected);
        }

        // Division by an out-of-range usize always returns zero
        assert_eq!(int / large_other, zero);
        assert_eq!(&int / large_other, zero);
        assert_eq!(int / &large_other, zero);
        assert_eq!(&int / &large_other, zero);
        tmp = int;
        tmp /= large_other;
        assert_eq!(tmp, zero);
        tmp = int;
        tmp /= &large_other;
        assert_eq!(tmp, zero);

        // Remainder from an in-range nonzero usize passes through
        if other != 0 {
            let expected = int % small_other_int;
            assert_eq!(int % small_other, expected);
            assert_eq!(&int % small_other, expected);
            assert_eq!(int % &small_other, expected);
            assert_eq!(&int % &small_other, expected);
            tmp = int;
            tmp %= small_other;
            assert_eq!(tmp, expected);
            tmp = int;
            tmp %= &small_other;
            assert_eq!(tmp, expected);
        }

        // Remainder from an out-of-range usize is identity
        assert_eq!(int % large_other, int);
        assert_eq!(&int % large_other, int);
        assert_eq!(int % &large_other, int);
        assert_eq!(&int % &large_other, int);
        tmp = int;
        tmp %= large_other;
        assert_eq!(tmp, int);
        tmp = int;
        tmp %= &large_other;
        assert_eq!(tmp, int);

        // Non-overflowing left shift must keep high-order bit cleared
        let effective_bits = PositiveInt::EFFECTIVE_BITS as usize;
        let wrapped_shift = other % effective_bits;
        let wrapped_result = PositiveInt((int.0 << wrapped_shift) & PositiveInt::MAX.0);
        assert_eq!(int << wrapped_shift, wrapped_result);
        assert_eq!(&int << wrapped_shift, wrapped_result);
        assert_eq!(int << (&wrapped_shift), wrapped_result);
        assert_eq!(&int << (&wrapped_shift), wrapped_result);
        tmp = int;
        tmp <<= wrapped_shift;
        assert_eq!(tmp, wrapped_result);
        tmp = int;
        tmp <<= &wrapped_shift;
        assert_eq!(tmp, wrapped_result);

        // Overflowing left shift should panic or wraparound
        let overflown_shift = other.saturating_add(effective_bits);
        assert_debug_panics(|| int << overflown_shift, wrapped_result);
        assert_debug_panics(|| &int << overflown_shift, wrapped_result);
        assert_debug_panics(|| int << (&overflown_shift), wrapped_result);
        assert_debug_panics(|| &int << (&overflown_shift), wrapped_result);
        assert_debug_panics(
            || {
                let mut tmp = int;
                tmp <<= overflown_shift;
                tmp
            },
            wrapped_result,
        );
        assert_debug_panics(
            || {
                let mut tmp = int;
                tmp <<= &overflown_shift;
                tmp
            },
            wrapped_result,
        );

        // Non-overflowing right shift can pass through
        let wrapped_result = PositiveInt(int.0 >> wrapped_shift);
        assert_eq!(int >> wrapped_shift, wrapped_result);
        assert_eq!(&int >> wrapped_shift, wrapped_result);
        assert_eq!(int >> (&wrapped_shift), wrapped_result);
        assert_eq!(&int >> (&wrapped_shift), wrapped_result);
        tmp = int;
        tmp >>= wrapped_shift;
        assert_eq!(tmp, wrapped_result);
        tmp = int;
        tmp >>= &wrapped_shift;
        assert_eq!(tmp, wrapped_result);

        // Overflowing right shift should panic or wraparound
        assert_debug_panics(|| int >> overflown_shift, wrapped_result);
        assert_debug_panics(|| &int >> overflown_shift, wrapped_result);
        assert_debug_panics(|| int >> (&overflown_shift), wrapped_result);
        assert_debug_panics(|| &int >> (&overflown_shift), wrapped_result);
        assert_debug_panics(
            || {
                let mut tmp = int;
                tmp >>= overflown_shift;
                tmp
            },
            wrapped_result,
        );
        assert_debug_panics(
            || {
                let mut tmp = int;
                tmp >>= &overflown_shift;
                tmp
            },
            wrapped_result,
        );

        // Check RangeFrom-like PositiveInt iterator in strided pattern
        let actual = PositiveInt::iter_range_from(int);
        let expected = (int.0)..;
        let remaining_iters = usize::from(PositiveInt::MAX - int);
        let max_stride = remaining_iters / INFINITE_ITERS;
        let stride = other % max_stride;
        compare_iters_infinite(actual, |i| i.nth(stride), expected, |i| i.nth(stride));
    }

    /// Test int-isize binary operations
    #[quickcheck]
    fn int_isize(int: PositiveInt, other: isize) {
        // Addition
        let (expected_wrapped, expected_overflow) =
            predict_overflowing_result(int, other, usize::overflowing_add_signed);
        let (wrapped, overflow) = test_overflowing(
            int,
            other,
            PositiveInt::checked_add_signed,
            PositiveInt::overflowing_add_signed,
            PositiveInt::wrapping_add_signed,
            [
                Box::new(|int, other| int + other),
                Box::new(|int, other| other + int),
                Box::new(|int, other| &int + other),
                Box::new(|int, other| other + &int),
                Box::new(|int, other| int + &other),
                Box::new(|int, other| &other + int),
                Box::new(|int, other| &int + &other),
                Box::new(|int, other| &other + &int),
                Box::new(|mut int, other| {
                    int += other;
                    int
                }),
                Box::new(|mut int, other| {
                    int += &other;
                    int
                }),
            ],
        );
        assert_eq!(wrapped, expected_wrapped);
        assert_eq!(overflow, expected_overflow);
        if overflow {
            if other > 0 {
                assert_eq!(int.saturating_add_signed(other), PositiveInt::MAX);
            } else {
                assert_eq!(int.saturating_add_signed(other), PositiveInt::MIN);
            }
        } else {
            assert_eq!(int.saturating_add_signed(other), wrapped);
        }

        // Subtraction
        let (wrapped, overflow) = if other == isize::MIN {
            predict_overflowing_result(
                int,
                // iN::MIN is -(1 << (iN::BITS - 1)
                // e.g. i8::MIN is -(1 << (8 - 1)) = -(1 << 7).
                1usize << (isize::BITS - 1),
                usize::overflowing_sub,
            )
        } else {
            predict_overflowing_result(int, -other, usize::overflowing_add_signed)
        };
        if overflow {
            assert_debug_panics(|| int - other, wrapped);
            assert_debug_panics(|| &int - other, wrapped);
            assert_debug_panics(|| int - &other, wrapped);
            assert_debug_panics(|| &int - &other, wrapped);
            assert_debug_panics(
                || {
                    let mut tmp = int;
                    tmp -= other;
                    tmp
                },
                wrapped,
            );
            assert_debug_panics(
                || {
                    let mut tmp = int;
                    tmp -= &other;
                    tmp
                },
                wrapped,
            );
        } else {
            assert_eq!(int - other, wrapped);
            assert_eq!(&int - other, wrapped);
            assert_eq!(int - &other, wrapped);
            assert_eq!(&int - &other, wrapped);
            let mut tmp = int;
            tmp -= other;
            assert_eq!(tmp, wrapped);
            tmp = int;
            tmp -= &other;
            assert_eq!(tmp, wrapped);
        }

        // Non-overflowing left shift must keep high-order bit cleared
        let effective_bits = isize::try_from(PositiveInt::EFFECTIVE_BITS).unwrap();
        let wrapped_shift = other.rem_euclid(effective_bits);
        let wrapped_result = PositiveInt((int.0 << wrapped_shift) & PositiveInt::MAX.0);
        assert_eq!(int << wrapped_shift, wrapped_result);
        assert_eq!(&int << wrapped_shift, wrapped_result);
        assert_eq!(int << (&wrapped_shift), wrapped_result);
        assert_eq!(&int << (&wrapped_shift), wrapped_result);
        let mut tmp = int;
        tmp <<= wrapped_shift;
        assert_eq!(tmp, wrapped_result);
        tmp = int;
        tmp <<= &wrapped_shift;
        assert_eq!(tmp, wrapped_result);

        // Overflowing left shift should panic or wraparound
        let overflown_shift = other.saturating_add(effective_bits);
        assert_debug_panics(|| int << overflown_shift, wrapped_result);
        assert_debug_panics(|| &int << overflown_shift, wrapped_result);
        assert_debug_panics(|| int << (&overflown_shift), wrapped_result);
        assert_debug_panics(|| &int << (&overflown_shift), wrapped_result);
        assert_debug_panics(
            || {
                let mut tmp = int;
                tmp <<= overflown_shift;
                tmp
            },
            wrapped_result,
        );
        assert_debug_panics(
            || {
                let mut tmp = int;
                tmp <<= &overflown_shift;
                tmp
            },
            wrapped_result,
        );

        // Non-overflowing right shift must keep high-order bit cleared as well
        // (with signed operands, a shift of -EFFECTIVE_BITS is possible!)
        let wrapped_result = PositiveInt((int.0 >> wrapped_shift) & PositiveInt::MAX.0);
        assert_eq!(int >> wrapped_shift, wrapped_result);
        assert_eq!(&int >> wrapped_shift, wrapped_result);
        assert_eq!(int >> (&wrapped_shift), wrapped_result);
        assert_eq!(&int >> (&wrapped_shift), wrapped_result);
        tmp = int;
        tmp >>= wrapped_shift;
        assert_eq!(tmp, wrapped_result);
        tmp = int;
        tmp >>= &wrapped_shift;
        assert_eq!(tmp, wrapped_result);

        // Overflowing right shift should panic or wraparound
        assert_debug_panics(|| int >> overflown_shift, wrapped_result);
        assert_debug_panics(|| &int >> overflown_shift, wrapped_result);
        assert_debug_panics(|| int >> (&overflown_shift), wrapped_result);
        assert_debug_panics(|| &int >> (&overflown_shift), wrapped_result);
        assert_debug_panics(
            || {
                let mut tmp = int;
                tmp >>= overflown_shift;
                tmp
            },
            wrapped_result,
        );
        assert_debug_panics(
            || {
                let mut tmp = int;
                tmp >>= &overflown_shift;
                tmp
            },
            wrapped_result,
        );
    }

    /// Test int-int-usize ternary operations
    #[quickcheck]
    fn int_int_usize(i1: PositiveInt, i2: PositiveInt, step: usize) {
        // Check Range-like PositiveInt iterator in strided pattern
        let actual = PositiveInt::iter_range(i1, i2);
        let expected = (i1.0)..(i2.0);
        compare_iters_finite(
            actual.clone(),
            |i| i.nth(step),
            expected.clone(),
            |i| i.nth(step),
        );
        compare_iters_finite(actual, |i| i.nth_back(step), expected, |i| i.nth_back(step));

        // Check RangeInclusive-like PositiveInt iterator in strided pattern
        let actual = PositiveInt::iter_range_inclusive(i1, i2);
        let expected = (i1.0)..=(i2.0);
        compare_iters_finite(
            actual.clone(),
            |i| i.nth(step),
            expected.clone(),
            |i| i.nth(step),
        );
        compare_iters_finite(actual, |i| i.nth_back(step), expected, |i| i.nth_back(step));
    }

    /// Test iterator reductions
    #[allow(clippy::redundant_closure_for_method_calls)]
    #[quickcheck]
    fn reductions(ints: Vec<PositiveInt>) {
        use std::iter::Copied;
        type IntRefIter<'a> = std::slice::Iter<'a, PositiveInt>;

        fn test_reduction(
            ints: &[PositiveInt],
            neutral: PositiveInt,
            overflowing_op: impl Fn(PositiveInt, PositiveInt) -> (PositiveInt, bool),
            reduce_by_ref: impl Fn(IntRefIter<'_>) -> PositiveInt + RefUnwindSafe,
            reduce_by_value: impl Fn(Copied<IntRefIter<'_>>) -> PositiveInt + RefUnwindSafe,
        ) {
            // Perform reduction using the overflowing operator
            let (wrapping_result, overflow) = ints.iter().copied().fold(
                (neutral, false),
                |(wrapping_acc, prev_overflow), elem| {
                    let (wrapping_acc, new_overflow) = overflowing_op(wrapping_acc, elem);
                    (wrapping_acc, prev_overflow || new_overflow)
                },
            );

            // Test the standard reductions accordingly
            let reductions: [&(dyn Fn() -> PositiveInt + RefUnwindSafe); 2] =
                [&|| reduce_by_ref(ints.iter()), &|| {
                    reduce_by_value(ints.iter().copied())
                }];
            for reduction in reductions {
                if overflow {
                    assert_debug_panics(reduction, wrapping_result);
                } else {
                    assert_eq!(reduction(), wrapping_result);
                }
            }
        }

        test_reduction(
            &ints,
            PositiveInt::ZERO,
            PositiveInt::overflowing_add,
            |ref_iter| ref_iter.sum::<PositiveInt>(),
            |value_iter| value_iter.sum::<PositiveInt>(),
        );
        test_reduction(
            &ints,
            PositiveInt::ONE,
            PositiveInt::overflowing_mul,
            |ref_iter| ref_iter.product::<PositiveInt>(),
            |value_iter| value_iter.product::<PositiveInt>(),
        );
    }
}
