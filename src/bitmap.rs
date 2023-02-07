//! Safe interface to the hwloc bitmap API

use crate::ffi;
use libc::c_char;
use std::{
    clone::Clone,
    cmp::Ordering,
    convert::TryFrom,
    ffi::CStr,
    fmt,
    iter::FromIterator,
    marker::{PhantomData, PhantomPinned},
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Bound, Not, RangeBounds,
    },
    ptr,
};

/// Opaque bitmap struct
///
/// Represents the private `hwloc_bitmap_s` type that `hwloc_bitmap_t` API
/// pointers map to.
#[repr(C)]
pub(crate) struct IntHwlocBitmap {
    _data: [u8; 0],
    _marker: PhantomData<(*mut u8, PhantomPinned)>,
}

/// A generic bitmap, understood by hwloc.
///
/// The `Bitmap` represents a set of objects, typically OS processors – which may actually be
/// hardware threads (represented by `CpuSet`, which is a type alias for `Bitmap` – or memory
/// nodes (represented by `NodeSet`, which is also a typedef for `Bitmap`).
///
/// Both `CpuSet` and `NodeSet` are always indexed by OS physical number.
///
/// A `Bitmap` may be of infinite size.
#[repr(transparent)]
pub struct Bitmap(*mut IntHwlocBitmap);

/// A `CpuSet` is a `Bitmap` whose bits are set according to CPU physical OS indexes.
pub type CpuSet = Bitmap;
/// A `NodeSet` is a `Bitmap` whose bits are set according to NUMA memory node physical OS indexes.
pub type NodeSet = Bitmap;

impl Bitmap {
    /// Wraps an owned bitmap from hwloc
    ///
    /// The pointer must target a valid bitmap that we will acquire ownership of
    /// and automatically free on Drop.
    ///
    pub(crate) unsafe fn from_raw(bitmap: *mut IntHwlocBitmap) -> Option<Self> {
        (!bitmap.is_null()).then_some(Self(bitmap))
    }

    /// Wraps an hwloc-originated borrowed bitmap pointer into the `Bitmap` representation.
    ///
    /// The pointer must target a valid bitmap, but unlike with from_raw, it
    /// will not be automatically freed on Drop.
    ///
    pub(crate) unsafe fn borrow_from_raw(bitmap: &*const IntHwlocBitmap) -> Option<&Self> {
        (!bitmap.is_null()).then_some(std::mem::transmute::<&*const IntHwlocBitmap, &Self>(bitmap))
    }

    /// Wraps an hwloc-originated borrowed bitmap pointer into the `Bitmap` representation.
    ///
    /// The pointer must target a valid bitmap, but unlike with from_raw, it
    /// will not be automatically freed on Drop.
    ///
    pub(crate) unsafe fn borrow_from_raw_mut(bitmap: &*mut IntHwlocBitmap) -> Option<&Self> {
        (!bitmap.is_null()).then_some(std::mem::transmute::<&*mut IntHwlocBitmap, &Self>(bitmap))
    }

    /// Returns the containted hwloc bitmap pointer for interaction with hwloc.
    pub(crate) fn as_ptr(&self) -> *const IntHwlocBitmap {
        self.0 as *const IntHwlocBitmap
    }

    /// Returns the containted hwloc bitmap pointer for interaction with hwloc.
    pub(crate) fn as_mut_ptr(&mut self) -> *mut IntHwlocBitmap {
        self.0
    }

    /// Creates an empty `Bitmap`.
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let bitmap = Bitmap::new();
    /// assert_eq!("", format!("{}", bitmap));
    /// assert_eq!(true, bitmap.is_empty());
    // ```
    pub fn new() -> Self {
        unsafe { Self::from_raw(ffi::hwloc_bitmap_alloc()).unwrap() }
    }

    /// Creates a full `Bitmap`.
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let bitmap = Bitmap::full();
    /// assert_eq!("0-", format!("{}", bitmap));
    /// assert_eq!(false, bitmap.is_empty());
    // ```
    pub fn full() -> Self {
        unsafe { Self::from_raw(ffi::hwloc_bitmap_alloc_full()).unwrap() }
    }

    /// Creates a new `Bitmap` with the given range.
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(0..=5);
    /// assert_eq!("0-5", format!("{}", bitmap));
    // ```
    pub fn from_range(range: impl RangeBounds<u32>) -> Self {
        let mut bitmap = Self::new();
        bitmap.set_range(range);
        bitmap
    }

    /// Turn this bitmap into a copy of another bitmap
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(0..=5);
    /// let mut bitmap2 = Bitmap::new();
    /// bitmap2.copy_from(&bitmap);
    /// assert_eq!("0-5", format!("{}", bitmap2));
    // ```
    pub fn copy_from(&mut self, other: &Self) {
        assert!(unsafe { ffi::hwloc_bitmap_copy(self.as_mut_ptr(), other.as_ptr()) } >= 0);
    }

    /// Set index `id` in this `Bitmap`.
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let mut bitmap = Bitmap::new();
    /// bitmap.set(4);
    /// assert_eq!("4", format!("{}", bitmap));
    // ```
    pub fn set(&mut self, id: u32) {
        assert!(unsafe { ffi::hwloc_bitmap_set(self.as_mut_ptr(), id) } >= 0)
    }

    /// Add indexes from this Rust range to the specified bitmap
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let mut bitmap = Bitmap::new();
    /// bitmap.set_range(3..=5);
    /// assert_eq!("3-5", format!("{}", bitmap));
    ///
    /// bitmap.set_range(2..);
    /// assert_eq!("2-", format!("{}", bitmap));
    // ```
    pub fn set_range(&mut self, range: impl RangeBounds<u32>) {
        if (range.start_bound(), range.end_bound()) == (Bound::Unbounded, Bound::Unbounded) {
            self.fill();
            return;
        }

        let (begin, end) = Self::hwloc_range(range);
        assert!(unsafe { ffi::hwloc_bitmap_set_range(self.as_mut_ptr(), begin, end) } >= 0)
    }

    /// Remove index `id` from the `Bitmap`.
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(1..=3);
    /// bitmap.unset(1);
    /// assert_eq!("2-3", format!("{}", bitmap));
    // ```
    pub fn unset(&mut self, id: u32) {
        assert!(unsafe { ffi::hwloc_bitmap_clr(self.as_mut_ptr(), id) } >= 0)
    }

    /// Remove indexes from `begin` to `end` in this `Bitmap`.
    ///
    /// If end is -1, the range is infinite.
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(1..=5);
    /// bitmap.unset_range(4..6);
    /// assert_eq!("1-3", format!("{}", bitmap));
    ///
    /// bitmap.unset_range(2..);
    /// assert_eq!("1", format!("{}", bitmap));
    // ```
    pub fn unset_range(&mut self, range: impl RangeBounds<u32>) {
        if (range.start_bound(), range.end_bound()) == (Bound::Unbounded, Bound::Unbounded) {
            self.clear();
            return;
        }

        let (begin, end) = Self::hwloc_range(range);
        assert!(unsafe { ffi::hwloc_bitmap_clr_range(self.as_mut_ptr(), begin, end) } >= 0)
    }

    /// The number of indexes that are set in the bitmap.
    ///
    /// None means that an infinite number of indices are set.
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(1..=5);
    /// assert_eq!(Some(5), bitmap.weight());
    /// bitmap.unset(3);
    /// assert_eq!(Some(4), bitmap.weight());
    /// ```
    pub fn weight(&self) -> Option<u32> {
        let result = unsafe { ffi::hwloc_bitmap_weight(self.as_ptr()) };
        assert!(result >= -1);
        u32::try_from(result).ok()
    }

    /// Fill the `Bitmap`.
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(1..=5);
    /// assert_eq!(Some(5), bitmap.weight());
    ///
    /// bitmap.fill();
    /// assert_eq!(None, bitmap.weight());
    /// ```
    pub fn fill(&mut self) {
        unsafe { ffi::hwloc_bitmap_fill(self.as_mut_ptr()) }
    }

    /// Clears the `Bitmap`.
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(1..=5);
    /// assert_eq!(Some(5), bitmap.weight());
    /// assert_eq!(false, bitmap.is_empty());
    ///
    /// bitmap.clear();
    /// assert_eq!(Some(0), bitmap.weight());
    /// assert_eq!(true, bitmap.is_empty());
    /// ```
    pub fn clear(&mut self) {
        unsafe { ffi::hwloc_bitmap_zero(self.as_mut_ptr()) }
    }

    /// Checks if this `Bitmap` has indexes set.
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let mut bitmap = Bitmap::new();
    /// assert_eq!(true, bitmap.is_empty());
    ///
    /// bitmap.set(3);
    /// assert_eq!(false, bitmap.is_empty());
    ///
    /// bitmap.clear();
    /// assert_eq!(true, bitmap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        let result = unsafe { ffi::hwloc_bitmap_iszero(self.as_ptr()) };
        assert!(result == 0 || result == 1);
        result == 1
    }

    /// Check if the field with the given id is set.
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let mut bitmap = Bitmap::new();
    /// assert_eq!(false, bitmap.is_set(2));
    ///
    /// bitmap.set(2);
    /// assert_eq!(true, bitmap.is_set(2));
    /// ```
    pub fn is_set(&self, id: u32) -> bool {
        let result = unsafe { ffi::hwloc_bitmap_isset(self.as_ptr(), id) };
        assert!(result == 0 || result == 1);
        result == 1
    }

    /// Keep a single index among those set in the bitmap.
    ///
    /// May be useful before binding so that the process does not have a
    /// chance of migrating between multiple logical CPUs in the original mask.
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let mut bitmap = Bitmap::new();
    /// bitmap.set_range(0..=127);
    /// assert_eq!(Some(128), bitmap.weight());
    ///
    /// bitmap.invert();
    /// assert_eq!(None, bitmap.weight());
    ///
    /// bitmap.singlify();
    /// assert_eq!(Some(1), bitmap.weight());
    /// ```
    pub fn singlify(&mut self) {
        unsafe { ffi::hwloc_bitmap_singlify(self.as_mut_ptr()) }
    }

    /// Inverts the current `Bitmap`.
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let mut bitmap = Bitmap::new();
    /// bitmap.set(3);
    ///
    /// assert_eq!("3", format!("{}", bitmap));
    /// assert_eq!("0-2,4-", format!("{}", !bitmap));
    /// ```
    pub fn invert(&mut self) {
        assert!(unsafe { ffi::hwloc_bitmap_not(self.as_mut_ptr(), self.as_ptr()) } >= 0)
    }

    /// Compute the first index (least significant bit) in this `Bitmap`, if any.
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(4..=10);
    /// assert_eq!(Some(4), bitmap.first());
    /// ```
    pub fn first(&self) -> Option<u32> {
        let result = unsafe { ffi::hwloc_bitmap_first(self.as_ptr()) };
        assert!(result >= -1);
        u32::try_from(result).ok()
    }

    /// Compute the last index (most significant bit) in this `Bitmap`, if any.
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(4..=10);
    /// assert_eq!(Some(10), bitmap.last());
    /// ```
    pub fn last(&self) -> Option<u32> {
        let result = unsafe { ffi::hwloc_bitmap_last(self.as_ptr()) };
        assert!(result >= -1);
        u32::try_from(result).ok()
    }

    /// Test whether this `Bitmap` is completely full.
    ///
    /// Examples:
    ///
    /// ```
    /// use hwloc2::Bitmap;
    ///
    /// let empty_bitmap = Bitmap::new();
    /// assert_eq!(false, empty_bitmap.is_full());
    ///
    /// let full_bitmap = Bitmap::full();
    /// assert_eq!(true, full_bitmap.is_full());
    /// ```
    pub fn is_full(&self) -> bool {
        let result = unsafe { ffi::hwloc_bitmap_isfull(self.as_ptr()) };
        assert!(result == 0 || result == 1);
        result == 1
    }

    // Convert a Rust range to an hwloc range
    fn hwloc_range(range: impl RangeBounds<u32>) -> (u32, i32) {
        let start = match range.start_bound() {
            Bound::Unbounded => 0,
            Bound::Included(i) => *i,
            Bound::Excluded(i) => i.checked_add(1).unwrap(),
        };
        let end = match range.end_bound() {
            Bound::Unbounded => -1,
            Bound::Included(i) => i32::try_from(*i).unwrap(),
            Bound::Excluded(i) => i32::try_from(i.checked_add(1).unwrap()).unwrap(),
        };
        (start, end)
    }

    // Iterator building block
    fn next(&self, index: Option<u32>) -> Option<u32> {
        let result = unsafe {
            ffi::hwloc_bitmap_next(
                self.as_ptr(),
                index.map(|v| i32::try_from(v).unwrap()).unwrap_or(-1),
            )
        };
        assert!(result >= -1);
        u32::try_from(result).ok()
    }
}

impl Not for Bitmap {
    type Output = Self;

    fn not(self) -> Self {
        let mut result = Self::new();
        assert!(unsafe { ffi::hwloc_bitmap_not(result.as_mut_ptr(), self.as_ptr()) } >= 0);
        result
    }
}

impl BitOr for Bitmap {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        let mut result = Self::new();
        assert!(
            unsafe { ffi::hwloc_bitmap_or(result.as_mut_ptr(), self.as_ptr(), rhs.as_ptr()) } >= 0
        );
        result
    }
}

impl BitOrAssign for Bitmap {
    fn bitor_assign(&mut self, rhs: Self) {
        assert!(
            unsafe { ffi::hwloc_bitmap_or(self.as_mut_ptr(), self.as_ptr(), rhs.as_ptr()) } >= 0
        )
    }
}

impl BitAnd for Bitmap {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self {
        let mut result = Self::new();
        assert!(
            unsafe { ffi::hwloc_bitmap_and(result.as_mut_ptr(), self.as_ptr(), rhs.as_ptr()) } >= 0
        );
        result
    }
}

impl BitAndAssign for Bitmap {
    fn bitand_assign(&mut self, rhs: Self) {
        assert!(
            unsafe { ffi::hwloc_bitmap_and(self.as_mut_ptr(), self.as_ptr(), rhs.as_ptr()) } >= 0
        )
    }
}

impl BitXor for Bitmap {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self {
        let mut result = Self::new();
        assert!(
            unsafe { ffi::hwloc_bitmap_xor(result.as_mut_ptr(), self.as_ptr(), rhs.as_ptr()) } >= 0
        );
        result
    }
}

impl BitXorAssign for Bitmap {
    fn bitxor_assign(&mut self, rhs: Self) {
        assert!(
            unsafe { ffi::hwloc_bitmap_xor(self.as_mut_ptr(), self.as_ptr(), rhs.as_ptr()) } >= 0
        )
    }
}

impl Drop for Bitmap {
    fn drop(&mut self) {
        unsafe { ffi::hwloc_bitmap_free(self.as_mut_ptr()) }
    }
}

impl fmt::Display for Bitmap {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut buf: *mut c_char = ptr::null_mut();
        unsafe {
            assert!(ffi::hwloc_bitmap_list_asprintf(&mut buf, self.as_ptr()) >= 0);
            let result = write!(f, "{}", CStr::from_ptr(buf).to_str().unwrap());
            libc::free(buf as _);
            result
        }
    }
}

impl fmt::Debug for Bitmap {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl Clone for Bitmap {
    fn clone(&self) -> Bitmap {
        unsafe { Self::from_raw(ffi::hwloc_bitmap_dup(self.as_ptr())) }.unwrap()
    }
}

impl PartialEq for Bitmap {
    fn eq(&self, other: &Self) -> bool {
        let result = unsafe { ffi::hwloc_bitmap_isequal(self.as_ptr(), other.as_ptr()) };
        assert!(result == 0 || result == 1);
        result == 1
    }
}

impl Eq for Bitmap {}

impl PartialOrd for Bitmap {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Bitmap {
    fn cmp(&self, other: &Self) -> Ordering {
        let result = unsafe { ffi::hwloc_bitmap_compare(self.as_ptr(), other.as_ptr()) };
        match result {
            -1 => Ordering::Less,
            0 => Ordering::Equal,
            1 => Ordering::Greater,
            _ => unreachable!(),
        }
    }
}

/// Owned iterator over set bitmap indices
pub struct BitmapIntoIterator {
    bitmap: Bitmap,
    index: Option<u32>,
}
//
impl Iterator for BitmapIntoIterator {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        self.index = self.bitmap.next(self.index);
        self.index
    }
}
//
impl IntoIterator for Bitmap {
    type Item = u32;
    type IntoIter = BitmapIntoIterator;

    fn into_iter(self) -> Self::IntoIter {
        BitmapIntoIterator {
            bitmap: self,
            index: None,
        }
    }
}

/// Borrowed iterator over set bitmap indices
pub struct BitmapIterator<'bitmap> {
    bitmap: &'bitmap Bitmap,
    index: Option<u32>,
}
//
impl Iterator for BitmapIterator<'_> {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        self.index = self.bitmap.next(self.index);
        self.index
    }
}
//
impl<'bitmap> IntoIterator for &'bitmap Bitmap {
    type Item = u32;
    type IntoIter = BitmapIterator<'bitmap>;

    fn into_iter(self) -> Self::IntoIter {
        BitmapIterator {
            bitmap: self,
            index: None,
        }
    }
}

impl From<u32> for Bitmap {
    fn from(value: u32) -> Self {
        let mut bitmap = Self::new();
        bitmap.set(value);
        bitmap
    }
}

impl FromIterator<u32> for Bitmap {
    fn from_iter<I: IntoIterator<Item = u32>>(iter: I) -> Bitmap {
        let mut bitmap = Self::new();
        for i in iter {
            bitmap.set(i);
        }
        bitmap
    }
}

impl Default for Bitmap {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn should_check_if_bitmap_is_empty() {
        let mut bitmap = Bitmap::new();

        assert!(bitmap.is_empty());
        bitmap.set(1);
        assert!(!bitmap.is_empty());
        bitmap.unset(1);
        assert!(bitmap.is_empty());
    }

    #[test]
    fn should_create_by_range() {
        let bitmap = Bitmap::from_range(0..=5);
        assert_eq!("0-5", format!("{bitmap}"));
    }

    #[test]
    fn should_set_and_unset_bitmap_index() {
        let mut bitmap = Bitmap::new();
        assert_eq!("", format!("{bitmap}"));

        assert!(bitmap.is_empty());

        bitmap.set(1);
        bitmap.set(3);
        bitmap.set(8);
        assert_eq!("1,3,8", format!("{bitmap}"));
        assert!(!bitmap.is_empty());

        bitmap.unset(3);
        assert_eq!("1,8", format!("{bitmap}"));
        assert!(!bitmap.is_empty());
    }

    #[test]
    fn should_check_if_is_set() {
        let mut bitmap = Bitmap::new();

        assert!(!bitmap.is_set(3));
        bitmap.set(3);
        assert!(bitmap.is_set(3));
        bitmap.unset(3);
        assert!(!bitmap.is_set(3));
    }

    #[test]
    fn should_set_and_unset_range() {
        let mut bitmap = Bitmap::new();
        assert_eq!("", format!("{bitmap}"));

        bitmap.set_range(2..=5);
        assert_eq!("2-5", format!("{bitmap}"));

        bitmap.set_range(4..=7);
        assert_eq!("2-7", format!("{bitmap}"));

        bitmap.set(9);
        assert_eq!("2-7,9", format!("{bitmap}"));

        bitmap.unset_range(6..=10);
        assert_eq!("2-5", format!("{bitmap}"));
    }

    #[test]
    fn should_clear_the_bitmap() {
        let mut bitmap = Bitmap::new();

        assert!(bitmap.is_empty());
        bitmap.set_range(4..=7);
        assert!(!bitmap.is_empty());
        assert!(bitmap.is_set(5));

        bitmap.clear();
        assert!(!bitmap.is_set(5));
        assert!(bitmap.is_empty());
    }

    #[test]
    fn should_get_weight() {
        let mut bitmap = Bitmap::new();

        assert_eq!(Some(0), bitmap.weight());

        bitmap.set(9);
        assert_eq!(Some(1), bitmap.weight());

        bitmap.set_range(2..=5);
        assert_eq!(Some(5), bitmap.weight());

        bitmap.unset(4);
        assert_eq!(Some(4), bitmap.weight());

        bitmap.clear();
        assert_eq!(Some(0), bitmap.weight());
    }

    #[test]
    fn should_invert() {
        let mut bitmap = Bitmap::new();
        bitmap.set(3);

        assert_eq!("3", format!("{bitmap}"));
        assert_eq!("0-2,4-", format!("{}", !bitmap));
    }

    #[test]
    fn should_singlify() {
        let mut bitmap = Bitmap::new();
        bitmap.set_range(0..=127);
        assert_eq!(Some(128), bitmap.weight());

        bitmap.invert();
        assert_eq!(None, bitmap.weight());

        bitmap.singlify();
        assert_eq!(Some(1), bitmap.weight());

        assert_eq!(Some(128), bitmap.first());
        assert_eq!(Some(128), bitmap.last());
    }

    #[test]
    fn should_check_equality() {
        let mut bitmap1 = Bitmap::new();
        bitmap1.set_range(0..=3);

        let mut bitmap2 = Bitmap::new();
        bitmap2.set_range(0..=3);

        let mut bitmap3 = Bitmap::new();
        bitmap3.set_range(1..=5);

        assert_eq!(bitmap1, bitmap2);
        assert!(bitmap2 == bitmap1);
        assert!(bitmap1 != bitmap3);
        assert!(bitmap3 != bitmap2);
    }

    #[test]
    fn should_clone() {
        let mut src = Bitmap::new();
        src.set_range(0..=3);

        let dst = src.clone();
        assert_eq!(src, dst);
    }

    #[test]
    fn should_support_into_iter() {
        let mut bitmap = Bitmap::from_range(4..=8);
        bitmap.set(2);

        let collected = bitmap.into_iter().collect::<Vec<u32>>();
        assert_eq!(6, collected.len());
        assert_eq!(vec![2, 4, 5, 6, 7, 8], collected);
    }

    #[test]
    fn should_support_from_iter() {
        let bitmap = (1..10).collect::<Bitmap>();
        assert_eq!("1-9", format!("{bitmap}"));
    }
}
