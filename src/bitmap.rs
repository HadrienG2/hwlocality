//! Bitmap API

// Main docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__bitmap.html

use crate::{ffi, Topology};
use derive_more::*;
use std::{
    borrow::Borrow,
    clone::Clone,
    cmp::Ordering,
    convert::TryFrom,
    ffi::c_int,
    fmt,
    iter::{FromIterator, FusedIterator},
    marker::{PhantomData, PhantomPinned},
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Bound, Not, RangeBounds,
    },
};

/// Trait for manipulating specialized bitmaps in a homogeneous way
pub trait SpecializedBitmap: AsRef<Bitmap> + AsMut<Bitmap> + From<Bitmap> + Into<Bitmap> {
    /// What kind of bitmap is this?
    const BITMAP_KIND: BitmapKind;
}

/// Kind of bitmap
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum BitmapKind {
    /// [`CpuSet`]
    CpuSet,

    /// [`NodeSet`]
    NodeSet,
}

macro_rules! impl_newtype_ops {
    ($newtype:ident) => {
        /// # Re-export of the Bitmap API
        ///
        /// Only documentation headers are repeated here, you will find the
        /// build of the documentation in identically named `Bitmap` methods.
        impl $newtype {
            /// Wrap an owned bitmap from hwloc
            ///
            /// See [`Bitmap::from_raw`].
            #[allow(unused)]
            pub(crate) unsafe fn from_raw(bitmap: *mut RawBitmap) -> Option<Self> {
                Bitmap::from_raw(bitmap).map(Self::from)
            }

            /// Wrap an hwloc-originated borrowed bitmap pointer
            ///
            /// See [`Bitmap::borrow_from_raw`].
            #[allow(unused)]
            pub(crate) unsafe fn borrow_from_raw(bitmap: &*mut RawBitmap) -> Option<&Self> {
                std::mem::transmute::<Option<&Bitmap>, Option<&Self>>(Bitmap::borrow_from_raw(
                    bitmap,
                ))
            }

            /// Returns the containted hwloc bitmap pointer for interaction with hwloc.
            ///
            /// See [`Bitmap::as_ptr`].
            pub(crate) fn as_ptr(&self) -> *const RawBitmap {
                self.0.as_ptr()
            }

            /// Returns the containted hwloc bitmap pointer for interaction with hwloc.
            ///
            /// See [`Bitmap::as_mut_ptr`].
            #[allow(unused)]
            pub(crate) fn as_mut_ptr(&mut self) -> *mut RawBitmap {
                self.0.as_mut_ptr()
            }

            /// Create an empty bitmap
            ///
            /// See [`Bitmap::new`].
            pub fn new() -> Self {
                Self::from(Bitmap::new())
            }

            /// Create a full bitmap
            ///
            /// See [`Bitmap::full`].
            pub fn full() -> Self {
                Self::from(Bitmap::full())
            }

            /// Creates a new bitmap with the given range of indices set
            ///
            /// See [`Bitmap::from_range`].
            pub fn from_range(range: impl RangeBounds<u32>) -> Self {
                Self::from(Bitmap::from_range(range))
            }

            /// Turn this bitmap into a copy of another bitmap
            ///
            /// See [`Bitmap::copy_from`].
            pub fn copy_from(&mut self, other: &Self) {
                self.0.copy_from(&other.0)
            }

            /// Clear all indices
            ///
            /// See [`Bitmap::clear`].
            pub fn clear(&mut self) {
                self.0.clear()
            }

            /// Set all indices
            ///
            /// See [`Bitmap::fill`].
            pub fn fill(&mut self) {
                self.0.fill()
            }

            /// Clear all indices except for the `id`, which is set
            ///
            /// See [`Bitmap::set_only`].
            pub fn set_only(&mut self, id: u32) {
                self.0.set_only(id)
            }

            /// Set all indices except for `id`, which is cleared
            ///
            /// See [`Bitmap::set_all_but`].
            pub fn set_all_but(&mut self, id: u32) {
                self.0.set_all_but(id)
            }

            /// Set index `id`
            ///
            /// See [`Bitmap::set`].
            pub fn set(&mut self, id: u32) {
                self.0.set(id)
            }

            /// Set indexes covered by `range`
            ///
            /// See [`Bitmap::set_range`].
            pub fn set_range(&mut self, range: impl RangeBounds<u32>) {
                self.0.set_range(range)
            }

            /// Clear index `id`
            ///
            /// See [`Bitmap::unset`].
            pub fn unset(&mut self, id: u32) {
                self.0.unset(id)
            }

            /// Clear indexes covered by `range`
            ///
            /// See [`Bitmap::unset_range`].
            pub fn unset_range(&mut self, range: impl RangeBounds<u32>) {
                self.0.unset_range(range)
            }

            /// Keep a single index among those set in the bitmap
            ///
            /// See [`Bitmap::singlify`].
            pub fn singlify(&mut self) {
                self.0.singlify()
            }

            /// Check if index `id` is set
            ///
            /// See [`Bitmap::is_set`].
            pub fn is_set(&self, id: u32) -> bool {
                self.0.is_set(id)
            }

            /// Check if all indices are unset
            ///
            /// See [`Bitmap::is_empty`].
            pub fn is_empty(&self) -> bool {
                self.0.is_empty()
            }

            /// Check if all indices are set
            ///
            /// See [`Bitmap::is_full`].
            pub fn is_full(&self) -> bool {
                self.0.is_full()
            }

            /// Check the first set index, if any
            ///
            /// See [`Bitmap::first_set`].
            pub fn first_set(&self) -> Option<u32> {
                self.0.first_set()
            }

            /// Iterate over set indices
            ///
            /// See [`Bitmap::iter_set`].
            pub fn iter_set(&self) -> BitmapIterator<&Bitmap> {
                self.0.iter_set()
            }

            /// Check the last set index, if any
            ///
            /// See [`Bitmap::last_set`].
            pub fn last_set(&self) -> Option<u32> {
                self.0.last_set()
            }

            /// The number of indexes that are set in the bitmap.
            ///
            /// See [`Bitmap::weight`].
            pub fn weight(&self) -> Option<u32> {
                self.0.weight()
            }

            /// Check the first unset index, if any
            ///
            /// See [`Bitmap::first_unset`].
            pub fn first_unset(&self) -> Option<u32> {
                self.0.first_unset()
            }

            /// Iterate over unset indices
            ///
            /// See [`Bitmap::iter_unset`].
            pub fn iter_unset(&self) -> BitmapIterator<&Bitmap> {
                self.0.iter_unset()
            }

            /// Check the last unset index, if any
            ///
            /// See [`Bitmap::last_unset`].
            pub fn last_unset(&self) -> Option<u32> {
                self.0.last_unset()
            }

            /// Optimized `self & !rhs`
            ///
            /// See [`Bitmap::and_not`].
            pub fn and_not(&self, rhs: &Self) -> Self {
                Self(self.0.and_not(&rhs.0))
            }

            /// Optimized `*self &= !rhs`
            ///
            /// See [`Bitmap::and_not_assign`].
            pub fn and_not_assign(&mut self, rhs: &Self) {
                self.0.and_not_assign(&rhs.0)
            }

            /// Inverts the current `Bitmap`.
            ///
            /// See [`Bitmap::invert`].
            pub fn invert(&mut self) {
                self.0.invert()
            }

            /// Truth that `self` and `rhs` have some set indices in common
            ///
            /// See [`Bitmap::intersects`].
            pub fn intersects(&self, rhs: &Self) -> bool {
                self.0.intersects(&rhs.0)
            }

            /// Truth that the indices set in `inner` are a subset of those set in `self`
            ///
            /// See [`Bitmap::includes`].
            pub fn includes(&self, inner: &Self) -> bool {
                self.0.includes(&inner.0)
            }
        }

        impl Not for &$newtype {
            type Output = $newtype;

            fn not(self) -> $newtype {
                $newtype(!&self.0)
            }
        }

        impl BitOr<&$newtype> for &$newtype {
            type Output = $newtype;

            fn bitor(self, rhs: &$newtype) -> $newtype {
                $newtype(&self.0 | &rhs.0)
            }
        }

        impl BitOr<$newtype> for &$newtype {
            type Output = $newtype;

            fn bitor(self, rhs: $newtype) -> $newtype {
                $newtype(&self.0 | &rhs.0)
            }
        }

        impl BitOr<&$newtype> for $newtype {
            type Output = $newtype;

            fn bitor(self, rhs: &$newtype) -> $newtype {
                $newtype(&self.0 | &rhs.0)
            }
        }

        impl BitOrAssign<&$newtype> for $newtype {
            fn bitor_assign(&mut self, rhs: &$newtype) {
                self.0 |= &rhs.0
            }
        }

        impl BitAnd<&$newtype> for &$newtype {
            type Output = $newtype;

            fn bitand(self, rhs: &$newtype) -> $newtype {
                $newtype((&self.0) & (&rhs.0))
            }
        }

        impl BitAnd<$newtype> for &$newtype {
            type Output = $newtype;

            fn bitand(self, rhs: $newtype) -> $newtype {
                $newtype((&self.0) & (&rhs.0))
            }
        }

        impl BitAnd<&$newtype> for $newtype {
            type Output = $newtype;

            fn bitand(self, rhs: &$newtype) -> $newtype {
                $newtype((&self.0) & (&rhs.0))
            }
        }

        impl BitAndAssign<&$newtype> for $newtype {
            fn bitand_assign(&mut self, rhs: &$newtype) {
                self.0 &= &rhs.0
            }
        }

        impl BitXor<&$newtype> for &$newtype {
            type Output = $newtype;

            fn bitxor(self, rhs: &$newtype) -> $newtype {
                $newtype((&self.0) ^ (&rhs.0))
            }
        }

        impl BitXor<$newtype> for &$newtype {
            type Output = $newtype;

            fn bitxor(self, rhs: $newtype) -> $newtype {
                $newtype((&self.0) ^ (&rhs.0))
            }
        }

        impl BitXor<&$newtype> for $newtype {
            type Output = $newtype;

            fn bitxor(self, rhs: &$newtype) -> $newtype {
                $newtype((&self.0) ^ (&rhs.0))
            }
        }

        impl BitXorAssign<&$newtype> for $newtype {
            fn bitxor_assign(&mut self, rhs: &$newtype) {
                self.0 ^= &rhs.0
            }
        }

        impl Extend<u32> for $newtype {
            fn extend<T: IntoIterator<Item = u32>>(&mut self, iter: T) {
                self.0.extend(iter)
            }
        }
    };
}

/// A `CpuSet` is a [`Bitmap`] whose bits are set according to CPU physical OS indexes.
#[derive(
    AsMut,
    AsRef,
    BitAnd,
    BitAndAssign,
    BitOr,
    BitOrAssign,
    BitXor,
    BitXorAssign,
    Clone,
    Debug,
    Default,
    Display,
    Eq,
    From,
    Into,
    IntoIterator,
    Not,
    Ord,
    PartialEq,
    PartialOrd,
)]
#[repr(transparent)]
pub struct CpuSet(Bitmap);

impl SpecializedBitmap for CpuSet {
    const BITMAP_KIND: BitmapKind = BitmapKind::CpuSet;
}

/// # CpuSet-specific API
impl CpuSet {
    /// Remove simultaneous multithreading PUs from a CPU set
    ///
    /// For each core in `topology`, if this cpuset contains several PUs of that
    /// core, modify it to only keep a single PU for that core.
    ///
    /// `which` specifies which PU will be kept, in physical index order. If it
    /// is set to 0, for each core, the function keeps the first PU that was
    /// originally set in `cpuset`. If it is larger than the number of PUs in a
    /// core there were originally set in `cpuset`, no PU is kept for that core.
    ///
    /// PUs that are not below a Core object (for instance if the topology does
    /// not contain any Core object) are kept in the cpuset.
    pub fn singlify_per_core(&mut self, topology: &Topology, which: u32) {
        let result = unsafe {
            ffi::hwloc_bitmap_singlify_per_core(topology.as_ptr(), self.as_mut_ptr(), which)
        };
        assert!(
            result >= 0,
            "Unexpected result from hwloc_bitmap_singlify_per_core"
        )
    }
}

impl_newtype_ops!(CpuSet);

/// A `NodeSet` is a [`Bitmap`] whose bits are set according to NUMA memory node
/// physical OS indexes.
#[derive(
    AsMut,
    AsRef,
    BitAnd,
    BitAndAssign,
    BitOr,
    BitOrAssign,
    BitXor,
    BitXorAssign,
    Clone,
    Debug,
    Default,
    Display,
    Eq,
    From,
    Into,
    IntoIterator,
    Not,
    Ord,
    PartialEq,
    PartialOrd,
)]
#[repr(transparent)]
pub struct NodeSet(Bitmap);

impl SpecializedBitmap for NodeSet {
    const BITMAP_KIND: BitmapKind = BitmapKind::NodeSet;
}

impl_newtype_ops!(NodeSet);

/// Opaque bitmap struct
///
/// Represents the private `hwloc_bitmap_s` type that `hwloc_bitmap_t` API
/// pointers map to.
#[repr(C)]
pub(crate) struct RawBitmap {
    _data: [u8; 0],
    _marker: PhantomData<(*mut u8, PhantomPinned)>,
}

/// A generic bitmap, understood by hwloc.
///
/// The `Bitmap` represents a set of objects, typically OS processors – which
/// may actually be hardware threads (represented by the [`CpuSet`] specialized
/// newtype) or memory nodes (represented by the [`NodeSet`] specialized newtype).
///
/// Both [`CpuSet`] and [`NodeSet`] are always indexed by OS physical number.
///
/// A `Bitmap` may be of infinite size.
#[repr(transparent)]
pub struct Bitmap(*mut RawBitmap);

// NOTE: Remember to keep the method signatures and first doc lines in
//       impl_newtype_ops in sync with what's going on below.
impl Bitmap {
    // === FFI interoperability ===

    /// Wraps an owned bitmap from hwloc
    ///
    /// If non-null, the pointer must target a valid bitmap that we will acquire
    /// ownership of and automatically free on Drop.
    ///
    pub(crate) unsafe fn from_raw(bitmap: *mut RawBitmap) -> Option<Self> {
        (!bitmap.is_null()).then_some(Self(bitmap))
    }

    /// Wraps an hwloc-originated borrowed bitmap pointer into the `Bitmap` representation.
    ///
    /// If non-null, the pointer must target a valid bitmap, but unlike with
    /// from_raw, it will not be automatically freed on Drop.
    ///
    pub(crate) unsafe fn borrow_from_raw(bitmap: &*mut RawBitmap) -> Option<&Self> {
        (!bitmap.is_null()).then_some(std::mem::transmute::<&*mut RawBitmap, &Self>(bitmap))
    }

    // NOTE: There is no borrow_mut_from_raw because it would not be safe as if
    //       you expose an &mut Bitmap, the user can trigger Drop.

    /// Returns the containted hwloc bitmap pointer for interaction with hwloc.
    pub(crate) fn as_ptr(&self) -> *const RawBitmap {
        self.0
    }

    /// Returns the containted hwloc bitmap pointer for interaction with hwloc.
    pub(crate) fn as_mut_ptr(&mut self) -> *mut RawBitmap {
        self.0
    }

    // === Constructors ===

    /// Creates an empty `Bitmap`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let bitmap = Bitmap::new();
    /// assert_eq!("", format!("{}", bitmap));
    /// assert_eq!(true, bitmap.is_empty());
    // ```
    pub fn new() -> Self {
        unsafe {
            Self::from_raw(ffi::hwloc_bitmap_alloc())
                .expect("Got null pointer from hwloc_bitmap_alloc")
        }
    }

    /// Creates a full `Bitmap`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let bitmap = Bitmap::full();
    /// assert_eq!("0-", format!("{}", bitmap));
    /// assert_eq!(false, bitmap.is_empty());
    // ```
    pub fn full() -> Self {
        unsafe {
            Self::from_raw(ffi::hwloc_bitmap_alloc_full())
                .expect("Got null pointer from hwloc_bitmap_alloc_full")
        }
    }

    /// Creates a new `Bitmap` with the given range
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(0..=5);
    /// assert_eq!("0-5", format!("{}", bitmap));
    // ```
    pub fn from_range(range: impl RangeBounds<u32>) -> Self {
        let mut bitmap = Self::new();
        bitmap.set_range(range);
        bitmap
    }

    // === Getters and setters ===

    /// Turn this `Bitmap` into a copy of another `Bitmap`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(0..=5);
    /// let mut bitmap2 = Bitmap::new();
    /// bitmap2.copy_from(&bitmap);
    /// assert_eq!("0-5", format!("{}", bitmap2));
    // ```
    pub fn copy_from(&mut self, other: &Self) {
        let result = unsafe { ffi::hwloc_bitmap_copy(self.as_mut_ptr(), other.as_ptr()) };
        assert!(
            result >= 0,
            "hwloc_bitmap_copy returned error code {result}"
        );
    }

    /// Clear all indices
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
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

    /// Set all indices
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
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

    /// Clear all indices except for the `id`, which is set
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(1..=5);
    /// assert_eq!(Some(5), bitmap.weight());
    ///
    /// bitmap.set_only(0);
    /// assert_eq!(Some(1), bitmap.weight());
    /// ```
    pub fn set_only(&mut self, id: u32) {
        let result = unsafe { ffi::hwloc_bitmap_only(self.as_mut_ptr(), id) };
        assert!(
            result >= 0,
            "hwloc_bitmap_only returned error code {result}"
        );
    }

    /// Set all indices except for `id`, which is cleared
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(1..=5);
    /// assert_eq!(Some(5), bitmap.weight());
    ///
    /// bitmap.set_all_but(42);
    /// assert_eq!(None, bitmap.weight());
    /// assert!(!bitmap.is_set(42));
    /// assert!(bitmap.is_set(43));
    /// ```
    pub fn set_all_but(&mut self, id: u32) {
        let result = unsafe { ffi::hwloc_bitmap_allbut(self.as_mut_ptr(), id) };
        assert!(
            result >= 0,
            "hwloc_bitmap_allbut returned error code {result}"
        );
    }

    /// Set index `id`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::new();
    /// bitmap.set(4);
    /// assert_eq!("4", format!("{}", bitmap));
    // ```
    pub fn set(&mut self, id: u32) {
        let result = unsafe { ffi::hwloc_bitmap_set(self.as_mut_ptr(), id) };
        assert!(result >= 0, "hwloc_bitmap_set returned error code {result}");
    }

    /// Set indexes covered by `range`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
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
        let result = unsafe { ffi::hwloc_bitmap_set_range(self.as_mut_ptr(), begin, end) };
        assert!(
            result >= 0,
            "hwloc_bitmap_set_range returned error code {result}"
        );
    }

    /// Clear index `id`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(1..=3);
    /// bitmap.unset(1);
    /// assert_eq!("2-3", format!("{}", bitmap));
    // ```
    pub fn unset(&mut self, id: u32) {
        let result = unsafe { ffi::hwloc_bitmap_clr(self.as_mut_ptr(), id) };
        assert!(result >= 0, "hwloc_bitmap_clr returned error code {result}");
    }

    /// Clear indexes covered by `range`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
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
        let result = unsafe { ffi::hwloc_bitmap_clr_range(self.as_mut_ptr(), begin, end) };
        assert!(
            result >= 0,
            "hwloc_bitmap_clr_range returned error code {result}"
        );
    }

    /// Keep a single index among those set in the bitmap
    ///
    /// May be useful before binding so that the process does not have a
    /// chance of migrating between multiple logical CPUs in the original mask.
    /// Instead of running the task on any PU inside the given CPU set, the
    /// operating system scheduler will be forced to run it on a single of these
    /// PUs. It avoids a migration overhead and cache-line ping-pongs between PUs.
    ///
    /// This function is NOT meant to distribute multiple processes within a
    /// single CPU set. It always return the same single bit when called
    /// multiple times on the same input set. hwloc_distrib() (TODO wrap and link)
    /// may be used for generating CPU sets to distribute multiple tasks below a
    /// single multi-PU object.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
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

    /// Check if index `id` is set
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::new();
    /// assert_eq!(false, bitmap.is_set(2));
    ///
    /// bitmap.set(2);
    /// assert_eq!(true, bitmap.is_set(2));
    /// ```
    pub fn is_set(&self, id: u32) -> bool {
        let result = unsafe { ffi::hwloc_bitmap_isset(self.as_ptr(), id) };
        assert!(
            result == 0 || result == 1,
            "hwloc_bitmap_isset returned unexpected result {result}"
        );
        result == 1
    }

    /// Check if all indices are unset
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
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
        assert!(
            result == 0 || result == 1,
            "hwloc_bitmap_iszero returned unexpected result {result}"
        );
        result == 1
    }

    /// Check if all indices are set
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let empty_bitmap = Bitmap::new();
    /// assert_eq!(false, empty_bitmap.is_full());
    ///
    /// let full_bitmap = Bitmap::full();
    /// assert_eq!(true, full_bitmap.is_full());
    /// ```
    pub fn is_full(&self) -> bool {
        let result = unsafe { ffi::hwloc_bitmap_isfull(self.as_ptr()) };
        assert!(
            result == 0 || result == 1,
            "hwloc_bitmap_isfull returned unexpected result {result}"
        );
        result == 1
    }

    /// Check the first set index, if any
    ///
    /// You can iterate over set indices with [`Bitmap::iter_set()`].
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(4..=10);
    /// assert_eq!(Some(4), bitmap.first_set());
    /// ```
    pub fn first_set(&self) -> Option<u32> {
        let result = unsafe { ffi::hwloc_bitmap_first(self.as_ptr()) };
        assert!(
            result >= -1,
            "hwloc_bitmap_first returned error code {result}"
        );
        u32::try_from(result).ok()
    }

    /// Iterate over set indices
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(4..=10);
    /// let indices = bitmap.iter_set().collect::<Vec<_>>();
    /// assert_eq!(indices, &[4, 5, 6, 7, 8, 9, 10]);
    /// ```
    pub fn iter_set(&self) -> BitmapIterator<&Bitmap> {
        BitmapIterator::new(self, Bitmap::next_set)
    }

    /// Check the last set index, if any
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(4..=10);
    /// assert_eq!(Some(10), bitmap.last_set());
    /// ```
    pub fn last_set(&self) -> Option<u32> {
        let result = unsafe { ffi::hwloc_bitmap_last(self.as_ptr()) };
        assert!(
            result >= -1,
            "hwloc_bitmap_last returned error code {result}"
        );
        u32::try_from(result).ok()
    }

    /// The number of indexes that are set in the bitmap.
    ///
    /// None means that an infinite number of indices are set.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(1..=5);
    /// assert_eq!(Some(5), bitmap.weight());
    /// bitmap.unset(3);
    /// assert_eq!(Some(4), bitmap.weight());
    /// ```
    pub fn weight(&self) -> Option<u32> {
        let result = unsafe { ffi::hwloc_bitmap_weight(self.as_ptr()) };
        assert!(
            result >= -1,
            "hwloc_bitmap_weight returned error code {result}"
        );
        u32::try_from(result).ok()
    }

    /// Check the first unset index, if any
    ///
    /// You can iterate over set indices with [`Bitmap::iter_unset()`].
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(..10);
    /// assert_eq!(Some(10), bitmap.first_unset());
    /// ```
    pub fn first_unset(&self) -> Option<u32> {
        let result = unsafe { ffi::hwloc_bitmap_first_unset(self.as_ptr()) };
        assert!(
            result >= -1,
            "hwloc_bitmap_first_unset returned error code {result}"
        );
        u32::try_from(result).ok()
    }

    /// Iterate over unset indices
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(4..);
    /// let indices = bitmap.iter_unset().collect::<Vec<_>>();
    /// assert_eq!(indices, &[0, 1, 2, 3]);
    /// ```
    pub fn iter_unset(&self) -> BitmapIterator<&Bitmap> {
        BitmapIterator::new(self, Bitmap::next_unset)
    }

    /// Check the last unset index, if any
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(4..);
    /// assert_eq!(Some(3), bitmap.last_unset());
    /// ```
    pub fn last_unset(&self) -> Option<u32> {
        let result = unsafe { ffi::hwloc_bitmap_last_unset(self.as_ptr()) };
        assert!(
            result >= -1,
            "hwloc_bitmap_last_unset returned error code {result}"
        );
        u32::try_from(result).ok()
    }

    /// Optimized `self & !rhs`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(4..=10);
    /// let bitmap2 = Bitmap::from_range(5..=6);
    /// let result = bitmap.and_not(&bitmap2);
    /// assert_eq!(bitmap.and_not(&bitmap2), bitmap & !bitmap2);
    /// ```
    pub fn and_not(&self, rhs: &Self) -> Self {
        let mut result = Self::new();
        let code =
            unsafe { ffi::hwloc_bitmap_andnot(result.as_mut_ptr(), self.as_ptr(), rhs.as_ptr()) };
        assert!(code >= 0, "hwloc_bitmap_andnot returned error code {code}");
        result
    }

    /// Optimized `*self &= !rhs`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(4..=10);
    /// let mut bitmap2 = bitmap.clone();
    /// let rhs = Bitmap::from_range(5..=6);
    /// bitmap2.and_not_assign(&rhs);
    /// assert_eq!(bitmap2, bitmap.and_not(&rhs));
    /// ```
    pub fn and_not_assign(&mut self, rhs: &Self) {
        let code =
            unsafe { ffi::hwloc_bitmap_andnot(self.as_mut_ptr(), self.as_ptr(), rhs.as_ptr()) };
        assert!(code >= 0, "hwloc_bitmap_andnot returned error code {code}");
    }

    /// Inverts the current `Bitmap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::new();
    /// bitmap.set(3);
    ///
    /// assert_eq!("3", format!("{}", bitmap));
    /// assert_eq!("0-2,4-", format!("{}", !bitmap));
    /// ```
    pub fn invert(&mut self) {
        let result = unsafe { ffi::hwloc_bitmap_not(self.as_mut_ptr(), self.as_ptr()) };
        assert!(result >= 0, "hwloc_bitmap_not returned error code {result}");
    }

    /// Truth that `self` and `rhs` have some set indices in common
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let bitmap1 = Bitmap::from_range(1..3);
    /// let bitmap2 = Bitmap::from_range(3..6);
    /// assert!(!bitmap1.intersects(&bitmap2));
    ///
    /// let bitmap3 = Bitmap::from_range(2..4);
    /// assert!(bitmap1.intersects(&bitmap3));
    /// assert!(bitmap2.intersects(&bitmap3));
    /// ```
    pub fn intersects(&self, rhs: &Self) -> bool {
        let result = unsafe { ffi::hwloc_bitmap_intersects(self.as_ptr(), rhs.as_ptr()) };
        assert!(
            result == 0 || result == 1,
            "hwloc_bitmap_intersects returned unexpected result {result}"
        );
        result == 1
    }

    /// Truth that the indices set in `inner` are a subset of those set in `self`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwloc2::bitmap::Bitmap;
    ///
    /// let bitmap1 = Bitmap::from_range(3..8);
    /// let bitmap2 = Bitmap::from_range(5..9);
    /// assert!(!bitmap1.includes(&bitmap2));
    ///
    /// let bitmap3 = Bitmap::from_range(4..8);
    /// assert!(bitmap1.includes(&bitmap3));
    /// assert!(!bitmap2.includes(&bitmap3));
    /// ```
    pub fn includes(&self, inner: &Self) -> bool {
        let result = unsafe { ffi::hwloc_bitmap_isincluded(inner.as_ptr(), self.as_ptr()) };
        assert!(
            result == 0 || result == 1,
            "hwloc_bitmap_isincluded returned unexpected result {result}"
        );
        result == 1
    }

    // NOTE: When adding new methodes, remember to add them to impl_newtype_ops too

    // === Implementation details ===

    /// Convert a Rust range to an hwloc range
    fn hwloc_range(range: impl RangeBounds<u32>) -> (u32, i32) {
        let start = match range.start_bound() {
            Bound::Unbounded => Some(0),
            Bound::Included(i) => Some(*i),
            Bound::Excluded(i) => i.checked_add(1),
        }
        .expect("Range start is too high for hwloc");
        let end = match range.end_bound() {
            Bound::Unbounded => Some(-1),
            Bound::Included(i) => i32::try_from(*i).ok(),
            Bound::Excluded(i) => i.checked_sub(1).and_then(|i| i32::try_from(i).ok()),
        }
        .expect("Range end is too high for hwloc");
        (start, end)
    }

    /// Iterator building block
    fn next(
        &self,
        index: Option<u32>,
        next_fn: impl FnOnce(*const RawBitmap, c_int) -> c_int,
    ) -> Option<u32> {
        let result = next_fn(
            self.as_ptr(),
            index
                .map(|v| i32::try_from(v).expect("Index is too high for hwloc"))
                .unwrap_or(-1),
        );
        assert!(
            result >= -1,
            "hwloc bitmap iterator returned error code {result}"
        );
        u32::try_from(result).ok()
    }

    /// Set index iterator building block
    fn next_set(&self, index: Option<u32>) -> Option<u32> {
        self.next(index, |bitmap, prev| unsafe {
            ffi::hwloc_bitmap_next(bitmap, prev)
        })
    }

    /// Unset index iterator building block
    fn next_unset(&self, index: Option<u32>) -> Option<u32> {
        self.next(index, |bitmap, prev| unsafe {
            ffi::hwloc_bitmap_next_unset(bitmap, prev)
        })
    }
}

unsafe impl Send for Bitmap {}
unsafe impl Sync for Bitmap {}

impl BitAnd<&Bitmap> for &Bitmap {
    type Output = Bitmap;

    fn bitand(self, rhs: &Bitmap) -> Bitmap {
        let mut result = Bitmap::new();
        let code =
            unsafe { ffi::hwloc_bitmap_and(result.as_mut_ptr(), self.as_ptr(), rhs.as_ptr()) };
        assert!(code >= 0, "hwloc_bitmap_and returned error code {code}");
        result
    }
}

impl BitAnd<Bitmap> for &Bitmap {
    type Output = Bitmap;

    fn bitand(self, rhs: Bitmap) -> Bitmap {
        self & (&rhs)
    }
}

impl BitAnd<&Bitmap> for Bitmap {
    type Output = Bitmap;

    fn bitand(self, rhs: &Bitmap) -> Bitmap {
        (&self) & rhs
    }
}

impl BitAnd<Bitmap> for Bitmap {
    type Output = Bitmap;

    fn bitand(self, rhs: Bitmap) -> Bitmap {
        (&self) & (&rhs)
    }
}

impl BitAndAssign<&Bitmap> for Bitmap {
    fn bitand_assign(&mut self, rhs: &Bitmap) {
        let code = unsafe { ffi::hwloc_bitmap_and(self.as_mut_ptr(), self.as_ptr(), rhs.as_ptr()) };
        assert!(code >= 0, "hwloc_bitmap_and returned error code {code}");
    }
}

impl BitAndAssign<Bitmap> for Bitmap {
    fn bitand_assign(&mut self, rhs: Bitmap) {
        *self &= &rhs
    }
}

impl BitOr<&Bitmap> for &Bitmap {
    type Output = Bitmap;

    fn bitor(self, rhs: &Bitmap) -> Bitmap {
        let mut result = Bitmap::new();
        let code =
            unsafe { ffi::hwloc_bitmap_or(result.as_mut_ptr(), self.as_ptr(), rhs.as_ptr()) };
        assert!(code >= 0, "hwloc_bitmap_or returned error code {code}");
        result
    }
}

impl BitOr<Bitmap> for &Bitmap {
    type Output = Bitmap;

    fn bitor(self, rhs: Bitmap) -> Bitmap {
        self | &rhs
    }
}

impl BitOr<&Bitmap> for Bitmap {
    type Output = Bitmap;

    fn bitor(self, rhs: &Bitmap) -> Bitmap {
        &self | rhs
    }
}

impl BitOr<Bitmap> for Bitmap {
    type Output = Bitmap;

    fn bitor(self, rhs: Bitmap) -> Bitmap {
        &self | &rhs
    }
}

impl BitOrAssign<&Bitmap> for Bitmap {
    fn bitor_assign(&mut self, rhs: &Bitmap) {
        let code = unsafe { ffi::hwloc_bitmap_or(self.as_mut_ptr(), self.as_ptr(), rhs.as_ptr()) };
        assert!(code >= 0, "hwloc_bitmap_or returned error code {code}");
    }
}

impl BitOrAssign<Bitmap> for Bitmap {
    fn bitor_assign(&mut self, rhs: Bitmap) {
        *self |= &rhs
    }
}

impl BitXor<&Bitmap> for &Bitmap {
    type Output = Bitmap;

    fn bitxor(self, rhs: &Bitmap) -> Bitmap {
        let mut result = Bitmap::new();
        let code =
            unsafe { ffi::hwloc_bitmap_xor(result.as_mut_ptr(), self.as_ptr(), rhs.as_ptr()) };
        assert!(code >= 0, "hwloc_bitmap_xor returned error code {code}");
        result
    }
}

impl BitXor<Bitmap> for &Bitmap {
    type Output = Bitmap;

    fn bitxor(self, rhs: Bitmap) -> Bitmap {
        self ^ (&rhs)
    }
}

impl BitXor<&Bitmap> for Bitmap {
    type Output = Bitmap;

    fn bitxor(self, rhs: &Bitmap) -> Bitmap {
        (&self) ^ rhs
    }
}

impl BitXor<Bitmap> for Bitmap {
    type Output = Bitmap;

    fn bitxor(self, rhs: Bitmap) -> Bitmap {
        (&self) ^ (&rhs)
    }
}

impl BitXorAssign<&Bitmap> for Bitmap {
    fn bitxor_assign(&mut self, rhs: &Bitmap) {
        let code = unsafe { ffi::hwloc_bitmap_xor(self.as_mut_ptr(), self.as_ptr(), rhs.as_ptr()) };
        assert!(code >= 0, "hwloc_bitmap_xor returned error code {code}");
    }
}

impl BitXorAssign<Bitmap> for Bitmap {
    fn bitxor_assign(&mut self, rhs: Bitmap) {
        *self ^= &rhs
    }
}

impl Clone for Bitmap {
    fn clone(&self) -> Bitmap {
        unsafe { Self::from_raw(ffi::hwloc_bitmap_dup(self.as_ptr())) }
            .expect("Got null pointer from hwloc_bitmap_dup")
    }
}

impl fmt::Debug for Bitmap {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl Default for Bitmap {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for Bitmap {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        ffi::write_snprintf(f, |buf, len| unsafe {
            ffi::hwloc_bitmap_list_snprintf(buf, len, self.as_ptr())
        })
    }
}

impl Drop for Bitmap {
    fn drop(&mut self) {
        unsafe { ffi::hwloc_bitmap_free(self.as_mut_ptr()) }
    }
}

impl Eq for Bitmap {}

impl Extend<u32> for Bitmap {
    fn extend<T: IntoIterator<Item = u32>>(&mut self, iter: T) {
        for i in iter {
            self.set(i);
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
        bitmap.extend(iter);
        bitmap
    }
}

/// Borrowed iterator over set [`Bitmap`] indices
#[derive(Copy, Clone)]
pub struct BitmapIterator<B> {
    /// Bitmap over which we're iterating
    bitmap: B,

    /// Last explored index
    prev: Option<u32>,

    /// Mapping from last index to next index
    next: fn(&Bitmap, Option<u32>) -> Option<u32>,
}
//
impl<B: Borrow<Bitmap>> BitmapIterator<B> {
    fn new(bitmap: B, next: fn(&Bitmap, Option<u32>) -> Option<u32>) -> Self {
        Self {
            bitmap,
            prev: None,
            next,
        }
    }
}
//
impl<B: Borrow<Bitmap>> Iterator for BitmapIterator<B> {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        self.prev = (self.next)(self.bitmap.borrow(), self.prev);
        self.prev
    }
}
//
impl<B: Borrow<Bitmap>> FusedIterator for BitmapIterator<B> {}
//
impl<'bitmap> IntoIterator for &'bitmap Bitmap {
    type Item = u32;
    type IntoIter = BitmapIterator<&'bitmap Bitmap>;

    fn into_iter(self) -> Self::IntoIter {
        BitmapIterator::new(self, Bitmap::next_set)
    }
}
//
impl IntoIterator for Bitmap {
    type Item = u32;
    type IntoIter = BitmapIterator<Bitmap>;

    fn into_iter(self) -> Self::IntoIter {
        BitmapIterator::new(self, Bitmap::next_set)
    }
}

impl Not for &Bitmap {
    type Output = Bitmap;

    fn not(self) -> Bitmap {
        let mut result = Bitmap::new();
        let code = unsafe { ffi::hwloc_bitmap_not(result.as_mut_ptr(), self.as_ptr()) };
        assert!(code >= 0, "hwloc_bitmap_or returned error code {code}");
        result
    }
}

impl Not for Bitmap {
    type Output = Bitmap;

    fn not(self) -> Self {
        !&self
    }
}

impl Ord for Bitmap {
    fn cmp(&self, other: &Self) -> Ordering {
        let result = unsafe { ffi::hwloc_bitmap_compare(self.as_ptr(), other.as_ptr()) };
        match result {
            -1 => Ordering::Less,
            0 => Ordering::Equal,
            1 => Ordering::Greater,
            _ => unreachable!("hwloc_bitmap_compare returned unexpected result {result}"),
        }
    }
}

impl PartialEq for Bitmap {
    fn eq(&self, other: &Self) -> bool {
        let result = unsafe { ffi::hwloc_bitmap_isequal(self.as_ptr(), other.as_ptr()) };
        assert!(
            result == 0 || result == 1,
            "hwloc_bitmap_isequal returned unexpected result {result}"
        );
        result == 1
    }
}

impl PartialOrd for Bitmap {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
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

        assert_eq!(Some(128), bitmap.first_set());
        assert_eq!(Some(128), bitmap.last_set());
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
