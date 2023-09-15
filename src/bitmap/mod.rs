//! Facilities for manipulating bitmaps
//!
//! # Bitmaps
//!
//! The hwloc library extensively uses bitmaps to model the concept of sets of
//! CPU cores that threads and processes can be bound to, and that of sets of
//! NUMA nodes that memory allocations can be bound to.
//!
//! In this module, we directly re-export this API via the [`Bitmap`] type.
//! However, other methods of the hwlocality binding do not directly accept or
//! emit bitmaps, as they do in the underlying hwloc C library. Instead they
//! use specialized variants of [`Bitmap`] called [`CpuSet`] and [`NodeSet`].
//!
//! These types are trivial wrappers around [`Bitmap`] that have basically the
//! same API, but provide improved type safety (you cannot use a
//! [`NodeSet`] where a [`CpuSet`] is expected, nor can you mistakenly mix CPU
//! indices with NUMA node indices). They also make the few APIs that accept
//! either cpusets or nodesets easier to use with respect to upstream hwloc, as
//! you don't need to remember to set or clear flags depending on which one of
//! these you are passing to the function.
//!
//! # Bitmap indices
//!
//! The range of indices that can be set or cleared in an hwloc bitmap
//! unfortunately does not neatly map into any machine integer type. It is
//! therefore modeled via the dedicated [`BitmapIndex`] integer type, which you
//! can use for optimal type safety, at the expense of facing some awkward API
//! ergonomics since user-defined integer types unfortunately cannot perfectly
//! match the ergonomics of machine types in Rust (for one thing, they don't
//! have literals).
//!
//! If this proves to be too cumbersome for you, an escape hatch is provided so
//! that you can easily use [`usize`] in almost every place where
//! [`BitmapIndex`] is expected, at the cost of risking a panic if the
//! provided [`usize`] is out of the [`BitmapIndex`] range. This design puts you
//! in control of the underlying compromise between type safety and ergonomics,
//! letting you choose what works best for you depending on your requirements.
//!
//! # Bitmap references and polymorphism
//!
//! For obscure implementation reasons, references to bitmaps that are owned by
//! hwloc cannot be provided as simple `&'target Target` references. Instead, a
//! dedicated [`BitmapRef`] type which behaves analogously must be used.
//!
//! For convenience, many hwlocality methods achieve genericity with respect to
//! [`BitmapRef`] and the specialized [`CpuSet`] and [`NodeSet`] bitmap types
//! by leveraging the [`OwnedBitmap`] and [`SpecializedBitmap`] traits, along
//! with their [`OwnedSpecializedBitmap`] combination.
//
// Main docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__bitmap.html

mod index;

#[cfg(doc)]
use crate::{
    cpu::cpuset::CpuSet,
    memory::nodeset::NodeSet,
    object::TopologyObject,
    topology::{builder::BuildFlags, Topology},
};
use crate::{
    errors,
    ffi::{self, IncompleteType},
    Sealed,
};
#[cfg(any(test, feature = "quickcheck"))]
use quickcheck::{Arbitrary, Gen};
#[cfg(doc)]
use std::collections::BTreeSet;
use std::{
    borrow::{Borrow, BorrowMut},
    clone::Clone,
    cmp::Ordering,
    convert::TryFrom,
    ffi::{c_int, c_uint},
    fmt::{self, Debug, Display},
    iter::{FromIterator, FusedIterator},
    marker::PhantomData,
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Bound, Deref, Not,
        RangeBounds, Sub, SubAssign,
    },
    ptr::NonNull,
};

// Re-export BitmapIndex, the fact that it's in a separate module is an
// implementation detail / valiant attempt to fight source file growth
pub use index::BitmapIndex;

/// Opaque bitmap struct
///
/// Represents the private `hwloc_bitmap_s` type that `hwloc_bitmap_t` API
/// pointers map to.
#[doc(alias = "hwloc_bitmap_s")]
#[doc(hidden)]
#[repr(C)]
pub struct RawBitmap(IncompleteType);
//
impl Debug for RawBitmap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <str as Debug>::fmt("RawBitmap", f)
    }
}

/// A generic bitmap, understood by hwloc
///
/// The `Bitmap` type represents a set of integers (positive or null). A bitmap
/// may be of infinite size (all bits are set after some point). A bitmap may
/// even be full if all bits are set.
///
/// Bitmaps are used by hwloc to represent sets of OS processors (which may
/// actually be hardware threads), via the [`CpuSet`] newtype, or to represent
/// sets of NUMA memory nodes via the [`NodeSet`] newtype.
///
/// Both [`CpuSet`] and [`NodeSet`] are always indexed by OS physical number.
/// However, users should usually not build CPU and node sets manually (e.g.
/// with [`Bitmap::set()`]). One should rather use the cpu/node sets of existing
/// [`TopologyObject`]s and combine them through boolean operations. For
/// instance, binding the current thread on a pair of cores may be performed
/// with:
///
/// ```
/// # use anyhow::Context;
/// # use hwlocality::{
/// #     cpu::{binding::CpuBindingFlags, cpuset::CpuSet},
/// #     object::{types::ObjectType},
/// #     topology::support::{CpuBindingSupport, FeatureSupport},
/// # };
/// #
/// # let topology = hwlocality::Topology::test_instance();
/// #
/// // We want Cores, but we tolerate PUs on platforms that don't expose Cores
/// // (either there are no hardware threads or hwloc could not detect them)
/// let core_depth = topology.depth_or_below_for_type(ObjectType::Core)?;
///
/// // Yields the first two cores of a multicore system, or
/// // the only core of a single-core system
/// let cores = topology.objects_at_depth(core_depth).take(2);
///
/// // Compute the union of these cores' CPUsets, that's our CPU binding bitmap
/// let set = cores.fold(
///     CpuSet::new(),
///     |acc, core| { acc | core.cpuset().expect("Cores should have CPUsets") }
/// );
///
/// // Only actually bind if the platform supports it (macOS notably doesn't)
/// if topology.supports(FeatureSupport::cpu_binding, CpuBindingSupport::set_thread) {
///     topology.bind_cpu(&set, CpuBindingFlags::THREAD)?;
/// }
/// #
/// # Ok::<(), anyhow::Error>(())
/// ```
///
/// # Panics
///
/// Unlike most hwloc entry points in this crate, `Bitmap` functions always
/// handle unexpected hwloc errors by panicking. The rationale for this is that
/// the bitmap is just a simple data structures, without any kind of
/// complicated interactions with the operating system, for which the only
/// failure mode should be running out of memory. And panicking is the normal
/// way to handle this in Rust.
///
/// [`CpuSet`]: crate::cpu::cpuset::CpuSet
/// [`NodeSet`]: crate::memory::nodeset::NodeSet
//
// --- Implementation details ---
//
// # Safety
//
// Bitmaps should always hold a pointer to a valid hwloc-allocated,
// non-deallocated bitmap.
#[doc(alias = "hwloc_bitmap_t")]
#[doc(alias = "hwloc_const_bitmap_t")]
#[repr(transparent)]
pub struct Bitmap(NonNull<RawBitmap>);

// NOTE: Remember to keep the method signatures and first doc lines in
//       impl_newtype_ops in sync with what's going on below.
impl Bitmap {
    // === FFI interoperability ===

    /// Wraps an owned `hwloc_bitmap_t`
    ///
    /// # Safety
    ///
    /// If non-null, the pointer must target a valid bitmap that we will acquire
    /// ownership of and automatically free on Drop.
    pub(crate) unsafe fn from_owned_raw_mut(bitmap: *mut RawBitmap) -> Option<Self> {
        // SAFETY: Safe per function input precondition
        NonNull::new(bitmap).map(|ptr| unsafe { Self::from_owned_nonnull(ptr) })
    }

    /// Wraps an owned hwloc bitmap
    ///
    /// # Safety
    ///
    /// The pointer must target a valid bitmap that we will acquire ownership of
    /// and automatically free on Drop.
    pub(crate) unsafe fn from_owned_nonnull(bitmap: NonNull<RawBitmap>) -> Self {
        Self(bitmap)
    }

    /// Wraps a borrowed `hwloc_const_bitmap_t`
    ///
    /// # Safety
    ///
    /// If non-null, the pointer must target a bitmap that is valid for 'target.
    /// Unlike with [`Bitmap::from_raw()`], it will not be automatically freed
    /// on Drop.
    pub(crate) unsafe fn borrow_from_raw<'target>(
        bitmap: *const RawBitmap,
    ) -> Option<BitmapRef<'target, Self>> {
        // SAFETY: Safe per function input precondition
        unsafe { Self::borrow_from_raw_mut(bitmap.cast_mut()) }
    }

    /// Wraps a borrowed `hwloc_bitmap_t`
    ///
    /// # Safety
    ///
    /// If non-null, the pointer must target a bitmap that is valid for 'target.
    /// Unlike with [`Bitmap::from_raw()`], it will not be automatically freed
    /// on Drop.
    pub(crate) unsafe fn borrow_from_raw_mut<'target>(
        bitmap: *mut RawBitmap,
    ) -> Option<BitmapRef<'target, Self>> {
        // SAFETY: Safe per function input precondition
        NonNull::new(bitmap).map(|ptr| unsafe { Self::borrow_from_nonnull(ptr) })
    }

    /// Wraps a borrowed hwloc bitmap
    ///
    /// # Safety
    ///
    /// The pointer must target a bitmap that is valid for 'target. Unlike with
    /// [`Bitmap::from_raw()`], it will not be automatically freed on Drop.
    pub(crate) unsafe fn borrow_from_nonnull<'target>(
        bitmap: NonNull<RawBitmap>,
    ) -> BitmapRef<'target, Self> {
        BitmapRef(bitmap, PhantomData)
    }

    // NOTE: There is no borrow_mut_from_raw because it would not be safe as if
    //       you expose an &mut Bitmap, the user can trigger Drop.

    /// Contained bitmap pointer (for interaction with hwloc)
    pub(crate) fn as_ptr(&self) -> *const RawBitmap {
        self.0.as_ptr()
    }

    /// Contained mutable bitmap pointer (for interaction with hwloc)
    pub(crate) fn as_mut_ptr(&mut self) -> *mut RawBitmap {
        self.0.as_ptr()
    }

    // === Constructors ===

    /// Creates an empty `Bitmap`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let empty = Bitmap::new();
    /// assert!(empty.is_empty());
    /// ```
    #[doc(alias = "hwloc_bitmap_alloc")]
    pub fn new() -> Self {
        // SAFETY: hwloc_bitmap_alloc should always be safe to call
        unsafe {
            let ptr =
                errors::call_hwloc_ptr_mut("hwloc_bitmap_alloc", || ffi::hwloc_bitmap_alloc())
                    .expect("Bitmap operation failures are handled via panics");
            Self::from_owned_nonnull(ptr)
        }
    }

    /// Creates a full `Bitmap`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let full = Bitmap::full();
    /// assert!(full.is_full());
    /// ```
    #[doc(alias = "hwloc_bitmap_alloc_full")]
    pub fn full() -> Self {
        // SAFETY: hwloc_bitmap_alloc_full should always be safe to call
        unsafe {
            let ptr = errors::call_hwloc_ptr_mut("hwloc_bitmap_alloc_full", || {
                ffi::hwloc_bitmap_alloc_full()
            })
            .expect("Bitmap operation failures are handled via panics");
            Self::from_owned_nonnull(ptr)
        }
    }

    /// Creates a new `Bitmap` with the given range of indices set
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(12..=34);
    /// assert_eq!(format!("{bitmap}"), "12-34");
    /// ```
    ///
    /// # Panics
    ///
    /// If `range` goes beyond the implementation-defined maximum index (at
    /// least 2^15-1, usually 2^31-1).
    pub fn from_range<Idx>(range: impl RangeBounds<Idx>) -> Self
    where
        Idx: Copy + PartialEq + TryInto<BitmapIndex>,
        <Idx as TryInto<BitmapIndex>>::Error: Debug,
    {
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
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(12..=34);
    /// let mut bitmap2 = Bitmap::new();
    /// bitmap2.copy_from(&bitmap);
    /// assert_eq!(format!("{bitmap2}"), "12-34");
    /// ```
    #[doc(alias = "hwloc_bitmap_copy")]
    pub fn copy_from(&mut self, other: &Self) {
        // SAFETY: Safe because both bitmaps are trusted to contain a valid pointer
        errors::call_hwloc_int_normal("hwloc_bitmap_copy", || unsafe {
            ffi::hwloc_bitmap_copy(self.as_mut_ptr(), other.as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
    }

    /// Clear all indices
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(12..=34);
    /// bitmap.clear();
    /// assert!(bitmap.is_empty());
    /// ```
    #[doc(alias = "hwloc_bitmap_zero")]
    pub fn clear(&mut self) {
        // SAFETY: Safe because this bitmap is trusted to contain a valid pointer
        unsafe { ffi::hwloc_bitmap_zero(self.as_mut_ptr()) }
    }

    /// Set all indices
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(12..=34);
    /// bitmap.fill();
    /// assert!(bitmap.is_full());
    /// ```
    #[doc(alias = "hwloc_bitmap_fill")]
    pub fn fill(&mut self) {
        // SAFETY: Safe because this bitmap is trusted to contain a valid pointer
        unsafe { ffi::hwloc_bitmap_fill(self.as_mut_ptr()) }
    }

    /// Clear all indices except for `idx`, which is set
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(12..=34);
    /// bitmap.set_only(42);
    /// assert_eq!(format!("{bitmap}"), "42");
    /// ```
    ///
    /// # Panics
    ///
    /// If `idx` is above the implementation-defined maximum index (at least
    /// 2^15-1, usually 2^31-1).
    #[doc(alias = "hwloc_bitmap_only")]
    pub fn set_only<Idx>(&mut self, idx: Idx)
    where
        Idx: TryInto<BitmapIndex>,
        <Idx as TryInto<BitmapIndex>>::Error: Debug,
    {
        let idx = idx.try_into().expect("Unsupported bitmap index");
        // SAFETY: Safe because this bitmap is trusted to contain a valid
        //         pointer and idx has been checked to be in range.
        errors::call_hwloc_int_normal("hwloc_bitmap_only", || unsafe {
            ffi::hwloc_bitmap_only(self.as_mut_ptr(), idx.into_c_uint())
        })
        .expect("Bitmap operation failures are handled via panics");
    }

    /// Set all indices except for `idx`, which is cleared
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(12..=34);
    /// bitmap.set_all_but(42);
    /// assert_eq!(format!("{bitmap}"), "0-41,43-");
    /// ```
    ///
    /// # Panics
    ///
    /// If `idx` is above the implementation-defined maximum index (at least
    /// 2^15-1, usually 2^31-1).
    #[doc(alias = "hwloc_bitmap_allbut")]
    pub fn set_all_but<Idx>(&mut self, idx: Idx)
    where
        Idx: TryInto<BitmapIndex>,
        <Idx as TryInto<BitmapIndex>>::Error: Debug,
    {
        let idx = idx.try_into().expect("Unsupported bitmap index");
        // SAFETY: Safe because this bitmap is trusted to contain a valid
        //         pointer and idx has been checked to be in range.
        errors::call_hwloc_int_normal("hwloc_bitmap_allbut", || unsafe {
            ffi::hwloc_bitmap_allbut(self.as_mut_ptr(), idx.into_c_uint())
        })
        .expect("Bitmap operation failures are handled via panics");
    }

    /// Set index `idx`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(12..=34);
    /// bitmap.set(42);
    /// assert_eq!(format!("{bitmap}"), "12-34,42");
    /// ```
    ///
    /// # Panics
    ///
    /// If `idx` is above the implementation-defined maximum index (at least
    /// 2^15-1, usually 2^31-1).
    #[doc(alias = "hwloc_bitmap_set")]
    pub fn set<Idx>(&mut self, idx: Idx)
    where
        Idx: TryInto<BitmapIndex>,
        <Idx as TryInto<BitmapIndex>>::Error: Debug,
    {
        let idx = idx.try_into().expect("Unsupported bitmap index");
        // SAFETY: Safe because this bitmap is trusted to contain a valid
        //         pointer and idx has been checked to be in range.
        errors::call_hwloc_int_normal("hwloc_bitmap_set", || unsafe {
            ffi::hwloc_bitmap_set(self.as_mut_ptr(), idx.into_c_uint())
        })
        .expect("Bitmap operation failures are handled via panics");
    }

    /// Set indices covered by `range`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(12..=56);
    /// bitmap.set_range(34..=78);
    /// assert_eq!(format!("{bitmap}"), "12-78");
    ///
    /// bitmap.set_range(2..);
    /// assert_eq!(format!("{bitmap}"), "2-");
    /// ```
    ///
    /// # Panics
    ///
    /// If `range` goes beyond the implementation-defined maximum index (at
    /// least 2^15-1, usually 2^31-1).
    #[doc(alias = "hwloc_bitmap_set_range")]
    pub fn set_range<Idx>(&mut self, range: impl RangeBounds<Idx>)
    where
        Idx: Copy + PartialEq + TryInto<BitmapIndex>,
        <Idx as TryInto<BitmapIndex>>::Error: Debug,
    {
        if (range.start_bound(), range.end_bound()) == (Bound::Unbounded, Bound::Unbounded) {
            self.fill();
            return;
        }

        let (begin, end) = Self::hwloc_range(range);
        // SAFETY: Safe because this bitmap is trusted to contain a valid
        //         pointer and hwloc_range is trusted to produce correct hwloc
        //         range bounds.
        errors::call_hwloc_int_normal("hwloc_bitmap_set_range", || unsafe {
            ffi::hwloc_bitmap_set_range(self.as_mut_ptr(), begin, end)
        })
        .expect("Bitmap operation failures are handled via panics");
    }

    /// Clear index `idx`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(12..=34);
    /// bitmap.unset(24);
    /// assert_eq!(format!("{bitmap}"), "12-23,25-34");
    /// ```
    ///
    /// # Panics
    ///
    /// If `idx` is above the implementation-defined maximum index (at least
    /// 2^15-1, usually 2^31-1).
    #[doc(alias = "hwloc_bitmap_clr")]
    pub fn unset<Idx>(&mut self, idx: Idx)
    where
        Idx: TryInto<BitmapIndex>,
        <Idx as TryInto<BitmapIndex>>::Error: Debug,
    {
        let idx = idx.try_into().expect("Unsupported bitmap index");
        // SAFETY: Safe because this bitmap is trusted to contain a valid pointer.
        errors::call_hwloc_int_normal("hwloc_bitmap_clr", || unsafe {
            ffi::hwloc_bitmap_clr(self.as_mut_ptr(), idx.into_c_uint())
        })
        .expect("Bitmap operation failures are handled via panics");
    }

    /// Clear indices covered by `range`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(12..=34);
    /// bitmap.unset_range(14..=18);
    /// assert_eq!(format!("{bitmap}"), "12-13,19-34");
    ///
    /// bitmap.unset_range(26..);
    /// assert_eq!(format!("{bitmap}"), "12-13,19-25");
    /// ```
    ///
    /// # Panics
    ///
    /// If `range` goes beyond the implementation-defined maximum index (at
    /// least 2^15-1, usually 2^31-1).
    #[doc(alias = "hwloc_bitmap_clr_range")]
    pub fn unset_range<Idx>(&mut self, range: impl RangeBounds<Idx>)
    where
        Idx: Copy + PartialEq + TryInto<BitmapIndex>,
        <Idx as TryInto<BitmapIndex>>::Error: Debug,
    {
        if (range.start_bound(), range.end_bound()) == (Bound::Unbounded, Bound::Unbounded) {
            self.clear();
            return;
        }

        let (begin, end) = Self::hwloc_range(range);
        // SAFETY: Safe because this bitmap is trusted to contain a valid
        //         pointer and hwloc_range is trusted to produce correct hwloc
        //         range bounds.
        errors::call_hwloc_int_normal("hwloc_bitmap_clr_range", || unsafe {
            ffi::hwloc_bitmap_clr_range(self.as_mut_ptr(), begin, end)
        })
        .expect("Bitmap operation failures are handled via panics");
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
    /// multiple times on the same input set. [`Topology::distribute_items()`]
    /// may be used for generating CPU sets to distribute multiple tasks below a
    /// single multi-PU object.
    ///
    /// The effect of singlifying an empty bitmap is not specified by hwloc.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(12..=34);
    /// bitmap.singlify();
    /// assert_eq!(bitmap.weight(), Some(1));
    /// ```
    #[doc(alias = "hwloc_bitmap_singlify")]
    pub fn singlify(&mut self) {
        // SAFETY: Safe because this bitmap is trusted to contain a valid pointer.
        errors::call_hwloc_int_normal("hwloc_bitmap_singlify", || unsafe {
            ffi::hwloc_bitmap_singlify(self.as_mut_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
    }

    /// Check if index `idx` is set
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(12..=34);
    /// assert!((0..12).all(|idx| !bitmap.is_set(idx)));
    /// assert!((12..=34).all(|idx| bitmap.is_set(idx)));
    /// assert!(!bitmap.is_set(35));
    /// ```
    ///
    /// # Panics
    ///
    /// If `idx` is above the implementation-defined maximum index (at least
    /// 2^15-1, usually 2^31-1).
    #[doc(alias = "hwloc_bitmap_isset")]
    pub fn is_set<Idx>(&self, idx: Idx) -> bool
    where
        Idx: TryInto<BitmapIndex>,
        <Idx as TryInto<BitmapIndex>>::Error: Debug,
    {
        let idx = idx.try_into().expect("Unsupported bitmap index");
        // SAFETY: Safe because this bitmap is trusted to contain a valid
        //         pointer and idx has been checked to be in range.
        errors::call_hwloc_bool("hwloc_bitmap_isset", || unsafe {
            ffi::hwloc_bitmap_isset(self.as_ptr(), idx.into_c_uint())
        })
        .expect("Should not involve faillible syscalls")
    }

    /// Check if all indices are unset
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// assert!(Bitmap::new().is_empty());
    /// assert!(!Bitmap::from_range(12..=34).is_empty());
    /// assert!(!Bitmap::full().is_empty());
    /// ```
    #[doc(alias = "hwloc_bitmap_iszero")]
    pub fn is_empty(&self) -> bool {
        // SAFETY: Safe because this bitmap is trusted to contain a valid pointer.
        errors::call_hwloc_bool("hwloc_bitmap_iszero", || unsafe {
            ffi::hwloc_bitmap_iszero(self.as_ptr())
        })
        .expect("Should not involve faillible syscalls")
    }

    /// Check if all indices are set
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// assert!(!Bitmap::new().is_full());
    /// assert!(!Bitmap::from_range(12..=34).is_full());
    /// assert!(Bitmap::full().is_full());
    /// ```
    #[doc(alias = "hwloc_bitmap_isfull")]
    pub fn is_full(&self) -> bool {
        // SAFETY: Safe because this bitmap is trusted to contain a valid pointer.
        errors::call_hwloc_bool("hwloc_bitmap_isfull", || unsafe {
            ffi::hwloc_bitmap_isfull(self.as_ptr())
        })
        .expect("Should not involve faillible syscalls")
    }

    /// Check the first set index, if any
    ///
    /// You can iterate over set indices with [`Bitmap::iter_set()`].
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let first_set_usize = |b: Bitmap| b.first_set().map(usize::from);
    /// assert_eq!(Bitmap::new().first_set(), None);
    /// assert_eq!(first_set_usize(Bitmap::from_range(12..=34)), Some(12));
    /// assert_eq!(first_set_usize(Bitmap::full()), Some(0));
    /// ```
    #[doc(alias = "hwloc_bitmap_first")]
    pub fn first_set(&self) -> Option<BitmapIndex> {
        // SAFETY: Safe because this bitmap is trusted to contain a valid pointer.
        let result = unsafe { ffi::hwloc_bitmap_first(self.as_ptr()) };
        assert!(
            result >= -1,
            "hwloc_bitmap_first returned error code {result}"
        );
        BitmapIndex::try_from_c_int(result).ok()
    }

    /// Iterate over set indices
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(12..=21);
    /// let indices = bitmap.iter_set().map(usize::from).collect::<Vec<_>>();
    /// assert_eq!(indices, &[12, 13, 14, 15, 16, 17, 18, 19, 20, 21]);
    /// ```
    #[doc(alias = "hwloc_bitmap_foreach_begin")]
    #[doc(alias = "hwloc_bitmap_foreach_end")]
    #[doc(alias = "hwloc_bitmap_next")]
    pub fn iter_set(&self) -> Iter<&Self> {
        Iter::new(self, Self::next_set)
    }

    /// Check the last set index, if any
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let last_set_usize = |b: Bitmap| b.last_set().map(usize::from);
    /// assert_eq!(Bitmap::new().last_set(), None);
    /// assert_eq!(last_set_usize(Bitmap::from_range(12..=34)), Some(34));
    /// assert_eq!(Bitmap::full().last_set(), None);
    /// ```
    #[doc(alias = "hwloc_bitmap_last")]
    pub fn last_set(&self) -> Option<BitmapIndex> {
        // SAFETY: Safe because this bitmap is trusted to contain a valid pointer.
        let result = unsafe { ffi::hwloc_bitmap_last(self.as_ptr()) };
        assert!(
            result >= -1,
            "hwloc_bitmap_last returned error code {result}"
        );
        BitmapIndex::try_from_c_int(result).ok()
    }

    /// The number of indices that are set in the bitmap
    ///
    /// None means that an infinite number of indices are set.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// assert_eq!(Bitmap::new().weight(), Some(0));
    /// assert_eq!(Bitmap::from_range(12..34).weight(), Some(34-12));
    /// assert_eq!(Bitmap::full().weight(), None);
    /// ```
    #[doc(alias = "hwloc_bitmap_weight")]
    pub fn weight(&self) -> Option<usize> {
        // SAFETY: Safe because this bitmap is trusted to contain a valid pointer.
        let result = unsafe { ffi::hwloc_bitmap_weight(self.as_ptr()) };
        assert!(
            result >= -1,
            "hwloc_bitmap_weight returned error code {result}"
        );
        usize::try_from(result).ok()
    }

    /// Check the first unset index, if any
    ///
    /// You can iterate over set indices with [`Bitmap::iter_unset()`].
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let first_unset_usize = |b: Bitmap| b.first_unset().map(usize::from);
    /// assert_eq!(first_unset_usize(Bitmap::new()), Some(0));
    /// assert_eq!(first_unset_usize(Bitmap::from_range(..12)), Some(12));
    /// assert_eq!(Bitmap::full().first_unset(), None);
    /// ```
    #[doc(alias = "hwloc_bitmap_first_unset")]
    pub fn first_unset(&self) -> Option<BitmapIndex> {
        // SAFETY: Safe because this bitmap is trusted to contain a valid pointer.
        let result = unsafe { ffi::hwloc_bitmap_first_unset(self.as_ptr()) };
        assert!(
            result >= -1,
            "hwloc_bitmap_first_unset returned error code {result}"
        );
        BitmapIndex::try_from_c_int(result).ok()
    }

    /// Iterate over unset indices
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(12..);
    /// let indices = bitmap.iter_unset().map(usize::from).collect::<Vec<_>>();
    /// assert_eq!(indices, &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]);
    /// ```
    #[doc(alias = "hwloc_bitmap_next_unset")]
    pub fn iter_unset(&self) -> Iter<&Self> {
        Iter::new(self, Self::next_unset)
    }

    /// Check the last unset index, if any
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let last_unset_usize = |b: Bitmap| b.last_unset().map(usize::from);
    /// assert_eq!(Bitmap::new().last_unset(), None);
    /// assert_eq!(last_unset_usize(Bitmap::from_range(12..)), Some(11));
    /// assert_eq!(Bitmap::full().last_unset(), None);
    /// ```
    #[doc(alias = "hwloc_bitmap_last_unset")]
    pub fn last_unset(&self) -> Option<BitmapIndex> {
        // SAFETY: Safe because this bitmap is trusted to contain a valid pointer.
        let result = unsafe { ffi::hwloc_bitmap_last_unset(self.as_ptr()) };
        assert!(
            result >= -1,
            "hwloc_bitmap_last_unset returned error code {result}"
        );
        BitmapIndex::try_from_c_int(result).ok()
    }

    /// Optimized version of `*self = !self`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(12..=34);
    /// bitmap.invert();
    /// assert_eq!(format!("{bitmap}"), "0-11,35-");
    /// ```
    pub fn invert(&mut self) {
        // SAFETY: Safe because this bitmap is trusted to contain a valid pointer.
        errors::call_hwloc_int_normal("hwloc_bitmap_not", || unsafe {
            ffi::hwloc_bitmap_not(self.as_mut_ptr(), self.as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
    }

    /// Truth that `self` and `rhs` have some set indices in common
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let bitmap1 = Bitmap::from_range(12..=34);
    /// let bitmap2 = Bitmap::from_range(56..=78);
    /// assert!(!bitmap1.intersects(&bitmap2));
    ///
    /// let bitmap3 = Bitmap::from_range(34..=56);
    /// assert!(bitmap1.intersects(&bitmap3));
    /// assert!(bitmap2.intersects(&bitmap3));
    /// ```
    #[doc(alias = "hwloc_bitmap_intersects")]
    pub fn intersects(&self, rhs: &Self) -> bool {
        // SAFETY: Safe because both bitmaps are trusted to contain a valid pointer
        errors::call_hwloc_bool("hwloc_bitmap_intersects", || unsafe {
            ffi::hwloc_bitmap_intersects(self.as_ptr(), rhs.as_ptr())
        })
        .expect("Should not involve faillible syscalls")
    }

    /// Truth that the indices set in `inner` are a subset of those set in `self`
    ///
    /// The empty bitmap is considered included in any other bitmap.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmap::Bitmap;
    ///
    /// let bitmap1 = Bitmap::from_range(12..=78);
    /// let bitmap2 = Bitmap::from_range(34..=56);
    /// assert!(bitmap1.includes(&bitmap2));
    /// assert!(!bitmap2.includes(&bitmap1));
    /// ```
    #[doc(alias = "hwloc_bitmap_isincluded")]
    pub fn includes(&self, inner: &Self) -> bool {
        // SAFETY: Safe because both bitmaps are trusted to contain a valid pointer
        errors::call_hwloc_bool("hwloc_bitmap_isincluded", || unsafe {
            ffi::hwloc_bitmap_isincluded(inner.as_ptr(), self.as_ptr())
        })
        .expect("Should not involve faillible syscalls")
    }

    // NOTE: When adding new methods, remember to add them to impl_newtype_ops too

    // === Implementation details ===

    /// Convert a Rust range to an hwloc range
    ///
    /// # Panics
    ///
    /// If `range` goes beyond the implementation-defined maximum index (at
    /// least 2^15-1, usually 2^31-1).
    fn hwloc_range<Idx>(range: impl RangeBounds<Idx>) -> (c_uint, c_int)
    where
        Idx: Copy + TryInto<BitmapIndex>,
        <Idx as TryInto<BitmapIndex>>::Error: Debug,
    {
        // Helper that literally translates the Rust range to an hwloc range if
        // possible (shifting indices forwards/backwards to account for
        // exclusive bounds). Panics if the user-specified bounds are too high,
        // return None if they're fine but a literal translation cannot be done.
        let helper = || -> Option<(c_uint, c_int)> {
            let convert_idx = |idx: Idx| idx.try_into().ok();
            let start_idx = |idx| convert_idx(idx).expect("Range start is too high for hwloc");
            let start = match range.start_bound() {
                Bound::Unbounded => BitmapIndex::MIN,
                Bound::Included(i) => start_idx(*i),
                Bound::Excluded(i) => start_idx(*i).checked_add_signed(1)?,
            };
            let end_idx = |idx| convert_idx(idx).expect("Range end is too high for hwloc");
            let end = match range.end_bound() {
                Bound::Unbounded => -1,
                Bound::Included(i) => end_idx(*i).into_c_int(),
                Bound::Excluded(i) => end_idx(*i).checked_add_signed(-1)?.into_c_int(),
            };
            Some((start.into_c_uint(), end))
        };

        // If a literal translation is not possible, it means either the start
        // bound is BitmapIndex::MAX exclusive or the end bound is
        // BitmapIndex::MIN exclusive. In both cases, the range covers no
        // indices and can be replaced by any other empty range, including 1..=0
        helper().unwrap_or((1, 0))
    }

    /// Iterator building block
    fn next(
        &self,
        index: Option<BitmapIndex>,
        next_fn: impl FnOnce(*const RawBitmap, c_int) -> c_int,
    ) -> Option<BitmapIndex> {
        let result = next_fn(self.as_ptr(), index.map_or(-1, BitmapIndex::into_c_int));
        assert!(
            result >= -1,
            "hwloc bitmap iterator returned error code {result}"
        );
        BitmapIndex::try_from_c_int(result).ok()
    }

    /// Set index iterator building block
    fn next_set(&self, index: Option<BitmapIndex>) -> Option<BitmapIndex> {
        // SAFETY: Safe because this bitmap is trusted to contain a valid
        //         pointer and index has been checked to be in range.
        self.next(index, |bitmap, prev| unsafe {
            ffi::hwloc_bitmap_next(bitmap, prev)
        })
    }

    /// Unset index iterator building block
    fn next_unset(&self, index: Option<BitmapIndex>) -> Option<BitmapIndex> {
        // SAFETY: Safe because this bitmap is trusted to contain a valid
        //         pointer and index has been checked to be in range.
        self.next(index, |bitmap, prev| unsafe {
            ffi::hwloc_bitmap_next_unset(bitmap, prev)
        })
    }
}

#[cfg(any(test, feature = "quickcheck"))]
impl Arbitrary for Bitmap {
    fn arbitrary(g: &mut Gen) -> Self {
        use std::collections::HashSet;

        // Start with an arbitrary finite bitmap
        let mut result = HashSet::<BitmapIndex>::arbitrary(g)
            .into_iter()
            .collect::<Bitmap>();

        // Decide by coin flip to extend infinitely on the right or not
        if bool::arbitrary(g) {
            let last = result.last_set().unwrap_or(BitmapIndex::MIN);
            result.set_range(last..);
        }

        result
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        // If this is infinite, start by removing the infinite part
        let mut local = self.clone();
        if local.weight().is_none() {
            local.unset_range(self.last_unset().unwrap_or(BitmapIndex::MIN)..);
        }

        // Now this is finite, can convert to Vec<BitmapIndex> and use Vec's shrinker
        let vec = local.into_iter().collect::<Vec<_>>();
        Box::new(vec.shrink().map(|vec| vec.into_iter().collect::<Bitmap>()))
    }
}

impl<B: Borrow<Bitmap>> BitAnd<B> for &Bitmap {
    type Output = Bitmap;

    #[doc(alias = "hwloc_bitmap_and")]
    fn bitand(self, rhs: B) -> Bitmap {
        let mut result = Bitmap::new();
        // SAFETY: Safe because all bitmaps are trusted to contain a valid pointer
        errors::call_hwloc_int_normal("hwloc_bitmap_and", || unsafe {
            ffi::hwloc_bitmap_and(result.as_mut_ptr(), self.as_ptr(), rhs.borrow().as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
        result
    }
}

impl<B: Borrow<Self>> BitAnd<B> for Bitmap {
    type Output = Self;

    fn bitand(mut self, rhs: B) -> Self {
        self &= rhs.borrow();
        self
    }
}

impl<B: Borrow<Self>> BitAndAssign<B> for Bitmap {
    fn bitand_assign(&mut self, rhs: B) {
        // SAFETY: Safe because both bitmaps are trusted to contain a valid pointer
        errors::call_hwloc_int_normal("hwloc_bitmap_and", || unsafe {
            ffi::hwloc_bitmap_and(self.as_mut_ptr(), self.as_ptr(), rhs.borrow().as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
    }
}

impl<B: Borrow<Bitmap>> BitOr<B> for &Bitmap {
    type Output = Bitmap;

    #[doc(alias = "hwloc_bitmap_or")]
    fn bitor(self, rhs: B) -> Bitmap {
        let mut result = Bitmap::new();
        // SAFETY: Safe because all bitmaps are trusted to contain a valid pointer
        errors::call_hwloc_int_normal("hwloc_bitmap_or", || unsafe {
            ffi::hwloc_bitmap_or(result.as_mut_ptr(), self.as_ptr(), rhs.borrow().as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
        result
    }
}

impl<B: Borrow<Self>> BitOr<B> for Bitmap {
    type Output = Self;

    fn bitor(mut self, rhs: B) -> Self {
        self |= rhs.borrow();
        self
    }
}

impl<B: Borrow<Self>> BitOrAssign<B> for Bitmap {
    fn bitor_assign(&mut self, rhs: B) {
        // SAFETY: Safe because both bitmaps are trusted to contain a valid pointer
        errors::call_hwloc_int_normal("hwloc_bitmap_or", || unsafe {
            ffi::hwloc_bitmap_or(self.as_mut_ptr(), self.as_ptr(), rhs.borrow().as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
    }
}

impl<B: Borrow<Bitmap>> BitXor<B> for &Bitmap {
    type Output = Bitmap;

    #[doc(alias = "hwloc_bitmap_xor")]
    fn bitxor(self, rhs: B) -> Bitmap {
        let mut result = Bitmap::new();
        // SAFETY: Safe because all bitmaps are trusted to contain a valid pointer
        errors::call_hwloc_int_normal("hwloc_bitmap_xor", || unsafe {
            ffi::hwloc_bitmap_xor(result.as_mut_ptr(), self.as_ptr(), rhs.borrow().as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
        result
    }
}

impl<B: Borrow<Self>> BitXor<B> for Bitmap {
    type Output = Self;

    fn bitxor(mut self, rhs: B) -> Self {
        self ^= rhs.borrow();
        self
    }
}

impl<B: Borrow<Self>> BitXorAssign<B> for Bitmap {
    fn bitxor_assign(&mut self, rhs: B) {
        // SAFETY: Safe because both bitmaps are trusted to contain a valid pointer
        errors::call_hwloc_int_normal("hwloc_bitmap_xor", || unsafe {
            ffi::hwloc_bitmap_xor(self.as_mut_ptr(), self.as_ptr(), rhs.borrow().as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
    }
}

impl Clone for Bitmap {
    #[doc(alias = "hwloc_bitmap_dup")]
    fn clone(&self) -> Self {
        // SAFETY: Safe because this bitmaps is trusted to contain a valid pointer
        unsafe {
            let ptr = errors::call_hwloc_ptr_mut("hwloc_bitmap_dup", || {
                ffi::hwloc_bitmap_dup(self.as_ptr())
            })
            .expect("Bitmap operation failures are handled via panics");
            Self::from_owned_nonnull(ptr)
        }
    }
}

impl Debug for Bitmap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl Default for Bitmap {
    fn default() -> Self {
        Self::new()
    }
}

impl Display for Bitmap {
    #[doc(alias = "hwloc_bitmap_list_snprintf")]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // SAFETY: Safe because this bitmap is trusted to contain a valid pointer
        ffi::write_snprintf(f, |buf, len| unsafe {
            ffi::hwloc_bitmap_list_snprintf(buf, len, self.as_ptr())
        })
    }
}

impl Drop for Bitmap {
    #[doc(alias = "hwloc_bitmap_free")]
    fn drop(&mut self) {
        // SAFETY: Safe because this bitmap is trusted to contain a valid pointer
        unsafe { ffi::hwloc_bitmap_free(self.as_mut_ptr()) }
    }
}

impl Eq for Bitmap {}

impl<BI: Borrow<BitmapIndex>> Extend<BI> for Bitmap {
    fn extend<T: IntoIterator<Item = BI>>(&mut self, iter: T) {
        for i in iter {
            self.set(*i.borrow());
        }
    }
}

impl<BI: Borrow<BitmapIndex>> From<BI> for Bitmap {
    fn from(value: BI) -> Self {
        Self::from_range(*value.borrow()..=*value.borrow())
    }
}

impl<BI: Borrow<BitmapIndex>> FromIterator<BI> for Bitmap {
    fn from_iter<I: IntoIterator<Item = BI>>(iter: I) -> Self {
        let mut bitmap = Self::new();
        bitmap.extend(iter);
        bitmap
    }
}

/// Iterator over set or unset [`Bitmap`] indices
#[derive(Copy, Clone, Debug)]
pub struct Iter<B> {
    /// Bitmap over which we're iterating
    bitmap: B,

    /// Last explored index
    prev: Option<BitmapIndex>,

    /// Mapping from last index to next index
    next: fn(&Bitmap, Option<BitmapIndex>) -> Option<BitmapIndex>,
}
//
impl<B> Iter<B> {
    /// Set up a bitmap iterator
    fn new(bitmap: B, next: fn(&Bitmap, Option<BitmapIndex>) -> Option<BitmapIndex>) -> Self {
        Self {
            bitmap,
            prev: None,
            next,
        }
    }
}
//
impl<B: Borrow<Bitmap>> Iterator for Iter<B> {
    type Item = BitmapIndex;

    fn next(&mut self) -> Option<BitmapIndex> {
        self.prev = (self.next)(self.bitmap.borrow(), self.prev);
        self.prev
    }
}
//
impl<B: Borrow<Bitmap>> FusedIterator for Iter<B> {}
//
impl<'bitmap> IntoIterator for &'bitmap Bitmap {
    type Item = BitmapIndex;
    type IntoIter = Iter<Self>;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self, Bitmap::next_set)
    }
}
//
impl IntoIterator for Bitmap {
    type Item = BitmapIndex;
    type IntoIter = Iter<Self>;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self, Self::next_set)
    }
}

impl Not for &Bitmap {
    type Output = Bitmap;

    #[doc(alias = "hwloc_bitmap_not")]
    fn not(self) -> Bitmap {
        let mut result = Bitmap::new();
        // SAFETY: Safe because this bitmap is trusted to contain a valid pointer
        errors::call_hwloc_int_normal("hwloc_bitmap_not", || unsafe {
            ffi::hwloc_bitmap_not(result.as_mut_ptr(), self.as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
        result
    }
}

impl Not for Bitmap {
    type Output = Self;

    fn not(mut self) -> Self {
        self.invert();
        self
    }
}

impl Ord for Bitmap {
    #[doc(alias = "hwloc_bitmap_compare")]
    fn cmp(&self, other: &Self) -> Ordering {
        // SAFETY: Safe because both bitmaps are trusted to contain a valid pointer
        let result = unsafe { ffi::hwloc_bitmap_compare(self.as_ptr(), other.as_ptr()) };
        match result {
            -1 => Ordering::Less,
            0 => Ordering::Equal,
            1 => Ordering::Greater,
            _ => unreachable!("hwloc_bitmap_compare returned unexpected result {result}"),
        }
    }
}

impl<B: Borrow<Self>> PartialEq<B> for Bitmap {
    #[doc(alias = "hwloc_bitmap_isequal")]
    fn eq(&self, other: &B) -> bool {
        // SAFETY: Safe because both bitmaps are trusted to contain a valid pointer
        errors::call_hwloc_bool("hwloc_bitmap_isequal", || unsafe {
            ffi::hwloc_bitmap_isequal(self.as_ptr(), other.borrow().as_ptr())
        })
        .expect("Should not involve faillible syscalls")
    }
}

impl<B: Borrow<Self>> PartialOrd<B> for Bitmap {
    fn partial_cmp(&self, other: &B) -> Option<Ordering> {
        Some(self.cmp(other.borrow()))
    }
}

// SAFETY: Safe because Bitmap exposes no internal mutability
unsafe impl Send for Bitmap {}

impl<B: Borrow<Bitmap>> Sub<B> for &Bitmap {
    type Output = Bitmap;

    #[doc(alias = "hwloc_bitmap_andnot")]
    fn sub(self, rhs: B) -> Bitmap {
        let mut result = Bitmap::new();
        // SAFETY: Safe because all bitmaps are trusted to contain a valid pointer
        errors::call_hwloc_int_normal("hwloc_bitmap_andnot", || unsafe {
            ffi::hwloc_bitmap_andnot(result.as_mut_ptr(), self.as_ptr(), rhs.borrow().as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
        result
    }
}

impl<B: Borrow<Self>> Sub<B> for Bitmap {
    type Output = Self;

    fn sub(mut self, rhs: B) -> Self {
        self -= rhs.borrow();
        self
    }
}

impl<B: Borrow<Self>> SubAssign<B> for Bitmap {
    fn sub_assign(&mut self, rhs: B) {
        // SAFETY: Safe because both bitmaps are trusted to contain a valid pointer
        errors::call_hwloc_int_normal("hwloc_bitmap_andnot", || unsafe {
            ffi::hwloc_bitmap_andnot(self.as_mut_ptr(), self.as_ptr(), rhs.borrow().as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
    }
}

// SAFETY: Safe because Bitmap exposes no internal mutability
unsafe impl Sync for Bitmap {}

/// A [`Bitmap`] or a specialized form thereof ([`CpuSet`], [`NodeSet`]...)
///
/// This type cannot be implemented outside of this crate as it relies on
/// hwlocality implementation details. It is only meant to be used in the
/// signature of generic methods that accept the aforementioned set of types
/// and then go on to process them homogeneously.
//
// --- Implementation details ---
//
// # Safety
//
// Implementations of this type must be a `repr(transparent)` wrapper of
// `NonNull<RawBitmap>`, possibly with some ZSTs added.
#[allow(clippy::missing_safety_doc)]
pub unsafe trait OwnedBitmap:
    Borrow<Bitmap>
    + BorrowMut<Bitmap>
    + Clone
    + Debug
    + Display
    + From<Bitmap>
    + Into<Bitmap>
    + Sealed
    + 'static
{
    /// Access the inner `NonNull<RawBitmap>`
    ///
    /// # Safety
    ///
    /// The client must not use this pointer to mutate the target object
    #[doc(hidden)]
    unsafe fn as_raw(&self) -> NonNull<RawBitmap>;
}
//
impl Sealed for Bitmap {}
//
// SAFETY: Bitmap is a repr(transparent) newtype of NonNull<RawBitmap>
unsafe impl OwnedBitmap for Bitmap {
    unsafe fn as_raw(&self) -> NonNull<RawBitmap> {
        self.0
    }
}

/// Read-only reference to a [`Bitmap`]-like `Target` that is owned by hwloc
///
/// For most intents and purposes, you can think of this as an
/// `&'target Target` and use it as such. But it cannot literally be an
/// `&'target Target` due to annoying details of the underlying C API.
//
// --- Implementation details ---
//
// The reason why `BitmapRef` needs to be a thing is that...
//
// - In the underlying hwloc API, everything is done using `hwloc_bitmap_t`,
//   which is actually a pointer to `hwloc_bitmap_s`, that is itself an opaque
//   incomplete type that is modeled on the Rust side via `RawBitmap`.
// - We can't directly expose `RawBitmap` to user code because if they move it
//   around it won't do what they want (and if you have an `&mut` or an owned
//   value you can always move in Rust). Therefore, hwlocality functions that
//   return bitmaps like hwloc would return an `hwloc_bitmap_t` cannot return
//   standard Rust pointers/refs like `&RawBitmap`, `&mut RawBitmap`,
//   `Box<RawBitmap>`, they must instead return some kind of
//   `NonNull<RawBitmap>` wrapper that implements the bitmap API without
//   exposing the inner RawBitmap.
// - We need two such wrappers because sometimes we need to return an owned
//   bitmap that must be liberated, and sometimes we need to return a borrowed
//   bitmap that must not outlive its parent.
//
// Technically, we could also have a `BitmapMut` that models `&mut RawBitmap`,
// but so far the need for this has not materialized.
//
// # Safety
//
// `BitmapRef<Target>` must never allow mutating the target because it is
// constructible from `&Target`.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct BitmapRef<'target, Target>(NonNull<RawBitmap>, PhantomData<&'target Target>);

impl<'target, Target: OwnedBitmap> BitmapRef<'target, Target> {
    /// Make a copy of the target bitmap
    ///
    /// Rust references are special in that `ref.clone()` calls the [`Clone`]
    /// implementation of the pointee, and not that of the reference.
    /// [`BitmapRef`] does not enjoy this magic, and thus needs to expose target
    /// cloning via a dedicated method.
    pub fn clone_target(&self) -> Target {
        self.as_ref().clone()
    }

    /// Cast to another bitmap newtype
    pub(crate) fn cast<Other: OwnedBitmap>(self) -> BitmapRef<'target, Other> {
        BitmapRef(self.0, PhantomData)
    }
}

impl<'target, Target: OwnedBitmap> AsRef<Target> for BitmapRef<'target, Target> {
    fn as_ref(&self) -> &Target {
        // SAFETY: - Both Target and BitmapRef are effectively repr(transparent)
        //           newtypes of NonNull<RawBitmap>, so &Target and &BitmapRef
        //           are effectively the same thing after compilation.
        //         - The borrow checker ensures that one cannot construct an
        //           &'a BitmapRef<'target> which does not verify 'target: 'a,
        //           so one cannot use this AsRef impl to build an excessively
        //           long-lived &'a Target.
        unsafe {
            let ptr: *const Self = self;
            &*ptr.cast::<Target>()
        }
    }
}

impl<Target, Rhs> BitAnd<Rhs> for &BitmapRef<'_, Target>
where
    Target: OwnedBitmap,
    Rhs: Borrow<Target>,
    for<'a, 'b> &'a Target: BitAnd<&'b Target, Output = Target>,
{
    type Output = Target;

    fn bitand(self, rhs: Rhs) -> Target {
        self.as_ref() & rhs.borrow()
    }
}

impl<Target, Rhs> BitAnd<Rhs> for BitmapRef<'_, Target>
where
    Target: OwnedBitmap,
    Rhs: Borrow<Target>,
    for<'a, 'b> &'a Target: BitAnd<&'b Target, Output = Target>,
{
    type Output = Target;

    fn bitand(self, rhs: Rhs) -> Target {
        self.as_ref() & rhs.borrow()
    }
}

impl<Target, Rhs> BitOr<Rhs> for &BitmapRef<'_, Target>
where
    Target: OwnedBitmap,
    Rhs: Borrow<Target>,
    for<'a, 'b> &'a Target: BitOr<&'b Target, Output = Target>,
{
    type Output = Target;

    fn bitor(self, rhs: Rhs) -> Target {
        self.as_ref() | rhs.borrow()
    }
}

impl<Target, Rhs> BitOr<Rhs> for BitmapRef<'_, Target>
where
    Target: OwnedBitmap,
    Rhs: Borrow<Target>,
    for<'a, 'b> &'a Target: BitOr<&'b Target, Output = Target>,
{
    type Output = Target;

    fn bitor(self, rhs: Rhs) -> Target {
        self.as_ref() | rhs.borrow()
    }
}

impl<Target, Rhs> BitXor<Rhs> for &BitmapRef<'_, Target>
where
    Target: OwnedBitmap,
    Rhs: Borrow<Target>,
    for<'a, 'b> &'a Target: BitXor<&'b Target, Output = Target>,
{
    type Output = Target;

    fn bitxor(self, rhs: Rhs) -> Target {
        self.as_ref() ^ rhs.borrow()
    }
}

impl<Target, Rhs> BitXor<Rhs> for BitmapRef<'_, Target>
where
    Target: OwnedBitmap,
    Rhs: Borrow<Target>,
    for<'a, 'b> &'a Target: BitXor<&'b Target, Output = Target>,
{
    type Output = Target;

    fn bitxor(self, rhs: Rhs) -> Target {
        self.as_ref() ^ rhs.borrow()
    }
}

// NOTE: This seemingly useless impl is needed in order to have impls of
//       BitXyz<&BitmapRef> for Target
impl<Target: OwnedBitmap> Borrow<Target> for &BitmapRef<'_, Target> {
    fn borrow(&self) -> &Target {
        self.as_ref()
    }
}

impl<Target: OwnedBitmap> Borrow<Target> for BitmapRef<'_, Target> {
    fn borrow(&self) -> &Target {
        self.as_ref()
    }
}

// NOTE: `Target` cannot implement `Borrow<BitmapRef<'target, Target>>` because
//       it would have to do so for all `'target` which is not correct: you
//       should not be able to create, say, a `BitmapRef<'static, Bitmap>` from
//       a `&'a Bitmap` of finite lifetime, as otherwise you would be able
//       to clone this `BitmapRef`, drop the original `Bitmap`, and then you
//       would have a dangling `BitmapRef`, resulting in UB.

impl<Target: OwnedBitmap + Debug> Debug for BitmapRef<'_, Target> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Target as Debug>::fmt(self.as_ref(), f)
    }
}

impl<Target: OwnedBitmap> Deref for BitmapRef<'_, Target> {
    type Target = Target;

    fn deref(&self) -> &Target {
        self.as_ref()
    }
}

impl<Target: OwnedBitmap + Display> Display for BitmapRef<'_, Target> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Target as Display>::fmt(self.as_ref(), f)
    }
}

impl<Target: OwnedBitmap + Eq + PartialEq<Self>> Eq for BitmapRef<'_, Target> {}

impl<'target, Target: OwnedBitmap> From<&'target Target> for BitmapRef<'target, Target> {
    fn from(input: &'target Target) -> Self {
        // SAFETY: A `BitmapRef` does not allow mutating the target object
        Self(unsafe { input.as_raw() }, PhantomData)
    }
}

impl<'target, 'self_, Target> IntoIterator for &'self_ BitmapRef<'target, Target>
where
    'target: 'self_,
    Target: OwnedBitmap,
    &'self_ Target: Borrow<Bitmap>,
{
    type Item = BitmapIndex;
    type IntoIter = Iter<&'self_ Target>;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self.as_ref(), Bitmap::next_set)
    }
}

impl<'target, Target> IntoIterator for BitmapRef<'target, Target>
where
    Target: OwnedBitmap,
{
    type Item = BitmapIndex;
    type IntoIter = Iter<BitmapRef<'target, Bitmap>>;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self.cast(), Bitmap::next_set)
    }
}

impl<Target> Not for &BitmapRef<'_, Target>
where
    Target: OwnedBitmap,
    for<'target> &'target Target: Not<Output = Target>,
{
    type Output = Target;

    fn not(self) -> Target {
        !(self.as_ref())
    }
}

impl<Target> Not for BitmapRef<'_, Target>
where
    Target: OwnedBitmap,
    for<'target> &'target Target: Not<Output = Target>,
{
    type Output = Target;

    fn not(self) -> Target {
        !(self.as_ref())
    }
}

impl<Target: OwnedBitmap + Ord + PartialOrd<Self>> Ord for BitmapRef<'_, Target> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_ref().cmp(other.as_ref())
    }
}

impl<Target, Rhs> PartialEq<Rhs> for BitmapRef<'_, Target>
where
    Target: OwnedBitmap + PartialEq<Rhs>,
{
    fn eq(&self, other: &Rhs) -> bool {
        self.as_ref() == other
    }
}

impl<Target, Rhs> PartialOrd<Rhs> for BitmapRef<'_, Target>
where
    Target: OwnedBitmap + PartialOrd<Rhs>,
{
    fn partial_cmp(&self, other: &Rhs) -> Option<Ordering> {
        self.as_ref().partial_cmp(other)
    }
}

impl<Target> fmt::Pointer for BitmapRef<'_, Target> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <NonNull<RawBitmap> as fmt::Pointer>::fmt(&self.0, f)
    }
}

// SAFETY: BitmapRef exposes no internal mutability
unsafe impl<Target: OwnedBitmap + Sync> Send for BitmapRef<'_, Target> {}

impl<Target, Rhs> Sub<Rhs> for &BitmapRef<'_, Target>
where
    Target: OwnedBitmap,
    Rhs: Borrow<Target>,
    for<'a, 'b> &'a Target: Sub<&'b Target, Output = Target>,
{
    type Output = Target;

    fn sub(self, rhs: Rhs) -> Target {
        self.as_ref() - rhs.borrow()
    }
}

impl<Target, Rhs> Sub<Rhs> for BitmapRef<'_, Target>
where
    Target: OwnedBitmap,
    Rhs: Borrow<Target>,
    for<'a, 'b> &'a Target: Sub<&'b Target, Output = Target>,
{
    type Output = Target;

    fn sub(self, rhs: Rhs) -> Target {
        self.as_ref() - rhs.borrow()
    }
}

// SAFETY: BitmapRef exposes no internal mutability
unsafe impl<Target: OwnedBitmap + Sync> Sync for BitmapRef<'_, Target> {}

// NOTE: `BitmapRef` cannot implement `ToOwned` because it would require
//       `Target` to implement `Borrow<BitmapRef<'target, Target>>`, which is
//       wrong as outlined above.

/// A specialized bitmap ([`CpuSet`], [`NodeSet`]) or a [`BitmapRef`] thereof
///
/// hwlocality avoids the need for error-prone hwloc-style `BYNODESET` flags by
/// making [`CpuSet`] and [`NodeSet`] full-blown types, not typedefs. Functions
/// which accept either of these specialized bitmap types can be made generic
/// over this [`SpecializedBitmap`] trait, which can be used to query which
/// specialized bitmap type was passed in.
#[doc(alias = "HWLOC_MEMBIND_BYNODESET")]
#[doc(alias = "HWLOC_RESTRICT_FLAG_BYNODESET")]
pub trait SpecializedBitmap: AsRef<Bitmap> {
    /// Tag used to discriminate between specialized bitmaps in code
    const BITMAP_KIND: BitmapKind;

    /// Owned form of this specialized bitmap
    type Owned: OwnedSpecializedBitmap;

    /// Construct an owned specialized bitmap from a borrowed one
    ///
    /// This is a generalization of [`Clone`] that also works for [`BitmapRef`].
    fn to_owned(&self) -> Self::Owned;
}

/// An owned specialized bitmaps ([`CpuSet`], [`NodeSet`])
///
/// This is a little bit more than an alias for `OwnedBitmap +
/// SpecializedBitmap` because if `Self` is owned, we know that `Self::Owned`
/// will be `Self` and can use this to hint type inference and simplify method
/// signatures.
pub trait OwnedSpecializedBitmap: OwnedBitmap + SpecializedBitmap<Owned = Self> {}
//
impl<B: OwnedBitmap + SpecializedBitmap<Owned = Self>> OwnedSpecializedBitmap for B {}

/// Kind of specialized bitmap
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum BitmapKind {
    /// This bitmap is a [`CpuSet`]
    CpuSet,

    /// This bitmap is a [`NodeSet`]
    NodeSet,
}

/// Implement a specialized bitmap
#[macro_export]
#[doc(hidden)]
macro_rules! impl_bitmap_newtype {
    (
        $(#[$attr:meta])*
        $newtype:ident
    ) => {
        $(#[$attr])*
        #[derive(
            derive_more::AsMut,
            derive_more::AsRef,
            Clone,
            Default,
            Eq,
            derive_more::From,
            derive_more::Into,
            derive_more::IntoIterator,
            derive_more::Not,
            Ord,
        )]
        #[repr(transparent)]
        pub struct $newtype($crate::bitmap::Bitmap);

        impl $crate::bitmap::SpecializedBitmap for $newtype {
            const BITMAP_KIND: $crate::bitmap::BitmapKind =
                $crate::bitmap::BitmapKind::$newtype;

            type Owned = Self;

            fn to_owned(&self) -> Self {
                self.clone()
            }
        }

        impl $crate::bitmap::SpecializedBitmap for $crate::bitmap::BitmapRef<'_, $newtype> {
            const BITMAP_KIND: $crate::bitmap::BitmapKind =
                $crate::bitmap::BitmapKind::$newtype;

            type Owned = $newtype;

            fn to_owned(&self) -> $newtype {
                self.clone_target()
            }
        }

        /// # Re-export of the Bitmap API
        ///
        /// Only documentation headers are repeated here, you will find most of
        /// the documentation attached to identically named `Bitmap` methods.
        impl $newtype {
            /// Wraps an owned `hwloc_bitmap_t`
            ///
            /// See [`Bitmap::from_owned_raw_mut`](crate::bitmap::Bitmap::from_owned_raw_mut).
            #[allow(unused)]
            pub(crate) unsafe fn from_owned_raw_mut(
                bitmap: *mut $crate::bitmap::RawBitmap
            ) -> Option<Self> {
                // SAFETY: Safety contract inherited from identical Bitmap method
                unsafe {
                    $crate::bitmap::Bitmap::from_owned_raw_mut(bitmap).map(Self::from)
                }
            }

            /// Wraps an owned hwloc bitmap
            ///
            /// See [`Bitmap::from_owned_nonnull`](crate::bitmap::Bitmap::from_owned_nonnull).
            #[allow(unused)]
            pub(crate) unsafe fn from_owned_nonnull(
                bitmap: std::ptr::NonNull<$crate::bitmap::RawBitmap>
            ) -> Self {
                // SAFETY: Safety contract inherited from identical Bitmap method
                unsafe {
                    Self::from($crate::bitmap::Bitmap::from_owned_nonnull(bitmap))
                }
            }

            /// Wraps a borrowed hwloc_const_bitmap_t
            ///
            /// See [`Bitmap::borrow_from_raw`](crate::bitmap::Bitmap::borrow_from_raw).
            #[allow(unused)]
            pub(crate) unsafe fn borrow_from_raw<'target>(
                bitmap: *const $crate::bitmap::RawBitmap
            ) -> Option<$crate::bitmap::BitmapRef<'target, Self>> {
                // SAFETY: Safety contract inherited from identical Bitmap method
                unsafe {
                    $crate::bitmap::Bitmap::borrow_from_raw(bitmap)
                        .map(|bitmap_ref| bitmap_ref.cast())
                }
            }

            /// Wraps a borrowed `hwloc_bitmap_t`
            ///
            /// See [`Bitmap::borrow_from_raw_mut`](crate::bitmap::Bitmap::borrow_from_raw_mut).
            #[allow(unused)]
            pub(crate) unsafe fn borrow_from_raw_mut<'target>(
                bitmap: *mut $crate::bitmap::RawBitmap
            ) -> Option<$crate::bitmap::BitmapRef<'target, Self>> {
                // SAFETY: Safety contract inherited from identical Bitmap method
                unsafe {
                    $crate::bitmap::Bitmap::borrow_from_raw_mut(bitmap)
                        .map(|bitmap_ref| bitmap_ref.cast())
                }
            }

            /// Wraps a borrowed hwloc bitmap
            ///
            /// See [`Bitmap::borrow_from_nonnull`](crate::bitmap::Bitmap::borrow_from_nonnull).
            #[allow(unused)]
            pub(crate) unsafe fn borrow_from_nonnull<'target>(
                bitmap: std::ptr::NonNull<$crate::bitmap::RawBitmap>
            ) -> $crate::bitmap::BitmapRef<'target, Self> {
                // SAFETY: Safety contract inherited from identical Bitmap method
                unsafe {
                    $crate::bitmap::Bitmap::borrow_from_nonnull(bitmap).cast()
                }
            }

            /// Contained bitmap pointer (for interaction with hwloc)
            ///
            /// See [`Bitmap::as_ptr`](crate::bitmap::Bitmap::as_ptr).
            #[allow(unused)]
            pub(crate) fn as_ptr(&self) -> *const $crate::bitmap::RawBitmap {
                self.0.as_ptr()
            }

            /// Contained mutable bitmap pointer (for interaction with hwloc)
            ///
            /// See [`Bitmap::as_mut_ptr`](crate::bitmap::Bitmap::as_mut_ptr).
            #[allow(unused)]
            pub(crate) fn as_mut_ptr(&mut self) -> *mut $crate::bitmap::RawBitmap {
                self.0.as_mut_ptr()
            }

            /// Create an empty bitmap
            ///
            /// See [`Bitmap::new`](crate::bitmap::Bitmap::new).
            pub fn new() -> Self {
                Self::from($crate::bitmap::Bitmap::new())
            }

            /// Create a full bitmap
            ///
            /// See [`Bitmap::full`](crate::bitmap::Bitmap::full).
            pub fn full() -> Self {
                Self::from($crate::bitmap::Bitmap::full())
            }

            /// Creates a new bitmap with the given range of indices set
            ///
            /// See [`Bitmap::from_range`](crate::bitmap::Bitmap::from_range).
            pub fn from_range<Idx>(range: impl std::ops::RangeBounds<Idx>) -> Self
            where
                Idx: Copy + PartialEq + TryInto<$crate::bitmap::BitmapIndex>,
                <Idx as TryInto<$crate::bitmap::BitmapIndex>>::Error: std::fmt::Debug,
            {
                Self::from($crate::bitmap::Bitmap::from_range(range))
            }

            /// Turn this bitmap into a copy of another bitmap
            ///
            /// See [`Bitmap::copy_from`](crate::bitmap::Bitmap::copy_from).
            pub fn copy_from(&mut self, other: &Self) {
                self.0.copy_from(&other.0)
            }

            /// Clear all indices
            ///
            /// See [`Bitmap::clear`](crate::bitmap::Bitmap::clear).
            pub fn clear(&mut self) {
                self.0.clear()
            }

            /// Set all indices
            ///
            /// See [`Bitmap::fill`](crate::bitmap::Bitmap::fill).
            pub fn fill(&mut self) {
                self.0.fill()
            }

            /// Clear all indices except for `idx`, which is set
            ///
            /// See [`Bitmap::set_only`](crate::bitmap::Bitmap::set_only).
            pub fn set_only<Idx>(&mut self, idx: Idx)
            where
                Idx: TryInto<$crate::bitmap::BitmapIndex>,
                <Idx as TryInto<$crate::bitmap::BitmapIndex>>::Error: std::fmt::Debug,
            {
                self.0.set_only(idx)
            }

            /// Set all indices except for `idx`, which is cleared
            ///
            /// See [`Bitmap::set_all_but`](crate::bitmap::Bitmap::set_all_but).
            pub fn set_all_but<Idx>(&mut self, idx: Idx)
            where
                Idx: TryInto<$crate::bitmap::BitmapIndex>,
                <Idx as TryInto<$crate::bitmap::BitmapIndex>>::Error: std::fmt::Debug,
            {
                self.0.set_all_but(idx)
            }

            /// Set index `idx`
            ///
            /// See [`Bitmap::set`](crate::bitmap::Bitmap::set).
            pub fn set<Idx>(&mut self, idx: Idx)
            where
                Idx: TryInto<$crate::bitmap::BitmapIndex>,
                <Idx as TryInto<$crate::bitmap::BitmapIndex>>::Error: std::fmt::Debug,
            {
                self.0.set(idx)
            }

            /// Set indices covered by `range`
            ///
            /// See [`Bitmap::set_range`](crate::bitmap::Bitmap::set_range).
            pub fn set_range<Idx>(&mut self, range: impl std::ops::RangeBounds<Idx>)
            where
                Idx: Copy + PartialEq + TryInto<$crate::bitmap::BitmapIndex>,
                <Idx as TryInto<$crate::bitmap::BitmapIndex>>::Error: std::fmt::Debug,
            {
                self.0.set_range(range)
            }

            /// Clear index `idx`
            ///
            /// See [`Bitmap::unset`](crate::bitmap::Bitmap::unset).
            pub fn unset<Idx>(&mut self, idx: Idx)
            where
                Idx: TryInto<$crate::bitmap::BitmapIndex>,
                <Idx as TryInto<$crate::bitmap::BitmapIndex>>::Error: std::fmt::Debug,
            {
                self.0.unset(idx)
            }

            /// Clear indices covered by `range`
            ///
            /// See [`Bitmap::unset_range`](crate::bitmap::Bitmap::unset_range).
            pub fn unset_range<Idx>(&mut self, range: impl std::ops::RangeBounds<Idx>)
            where
                Idx: Copy + PartialEq + TryInto<$crate::bitmap::BitmapIndex>,
                <Idx as TryInto<$crate::bitmap::BitmapIndex>>::Error: std::fmt::Debug,
            {
                self.0.unset_range(range)
            }

            /// Keep a single index among those set in the bitmap
            ///
            /// See [`Bitmap::singlify`](crate::bitmap::Bitmap::singlify).
            pub fn singlify(&mut self) {
                self.0.singlify()
            }

            /// Check if index `idx` is set
            ///
            /// See [`Bitmap::is_set`](crate::bitmap::Bitmap::is_set).
            pub fn is_set<Idx>(&self, idx: Idx) -> bool
            where
                Idx: TryInto<$crate::bitmap::BitmapIndex>,
                <Idx as TryInto<$crate::bitmap::BitmapIndex>>::Error: std::fmt::Debug,
            {
                self.0.is_set(idx)
            }

            /// Check if all indices are unset
            ///
            /// See [`Bitmap::is_empty`](crate::bitmap::Bitmap::is_empty).
            pub fn is_empty(&self) -> bool {
                self.0.is_empty()
            }

            /// Check if all indices are set
            ///
            /// See [`Bitmap::is_full`](crate::bitmap::Bitmap::is_full).
            pub fn is_full(&self) -> bool {
                self.0.is_full()
            }

            /// Check the first set index, if any
            ///
            /// See [`Bitmap::first_set`](crate::bitmap::Bitmap::first_set).
            pub fn first_set(&self) -> Option<$crate::bitmap::BitmapIndex> {
                self.0.first_set()
            }

            /// Iterate over set indices
            ///
            /// See [`Bitmap::iter_set`](crate::bitmap::Bitmap::iter_set).
            pub fn iter_set(
                &self
            ) -> $crate::bitmap::Iter<&$crate::bitmap::Bitmap> {
                self.0.iter_set()
            }

            /// Check the last set index, if any
            ///
            /// See [`Bitmap::last_set`](crate::bitmap::Bitmap::last_set).
            pub fn last_set(&self) -> Option<$crate::bitmap::BitmapIndex> {
                self.0.last_set()
            }

            /// The number of indices that are set in the bitmap
            ///
            /// See [`Bitmap::weight`](crate::bitmap::Bitmap::weight).
            pub fn weight(&self) -> Option<usize> {
                self.0.weight()
            }

            /// Check the first unset index, if any
            ///
            /// See [`Bitmap::first_unset`](crate::bitmap::Bitmap::first_unset).
            pub fn first_unset(&self) -> Option<$crate::bitmap::BitmapIndex> {
                self.0.first_unset()
            }

            /// Iterate over unset indices
            ///
            /// See [`Bitmap::iter_unset`](crate::bitmap::Bitmap::iter_unset).
            pub fn iter_unset(
                &self
            ) -> $crate::bitmap::Iter<&$crate::bitmap::Bitmap> {
                self.0.iter_unset()
            }

            /// Check the last unset index, if any
            ///
            /// See [`Bitmap::last_unset`](crate::bitmap::Bitmap::last_unset).
            pub fn last_unset(&self) -> Option<$crate::bitmap::BitmapIndex> {
                self.0.last_unset()
            }

            /// Optimized version of `*self = !self`
            ///
            /// See [`Bitmap::invert`](crate::bitmap::Bitmap::invert).
            pub fn invert(&mut self) {
                self.0.invert()
            }

            /// Truth that `self` and `rhs` have some set indices in common
            ///
            /// See [`Bitmap::intersects`](crate::bitmap::Bitmap::intersects).
            pub fn intersects(&self, rhs: &Self) -> bool {
                self.0.intersects(&rhs.0)
            }

            /// Truth that the indices set in `inner` are a subset of those set in `self`
            ///
            /// See [`Bitmap::includes`](crate::bitmap::Bitmap::includes).
            pub fn includes(&self, inner: &Self) -> bool {
                self.0.includes(&inner.0)
            }
        }

        impl<'target> AsRef<$crate::bitmap::Bitmap> for $crate::bitmap::BitmapRef<'_, $newtype> {
            fn as_ref(&self) -> &$crate::bitmap::Bitmap {
                let newtype: &$newtype = self.as_ref();
                newtype.as_ref()
            }
        }

        impl<B: std::borrow::Borrow<$newtype>> std::ops::BitAnd<B> for &$newtype {
            type Output = $newtype;

            fn bitand(self, rhs: B) -> $newtype {
                $newtype((&self.0) & (&rhs.borrow().0))
            }
        }

        impl<B: std::borrow::Borrow<Self>> std::ops::BitAnd<B> for $newtype {
            type Output = Self;

            fn bitand(self, rhs: B) -> Self {
                $newtype(self.0 & (&rhs.borrow().0))
            }
        }

        impl<B: std::borrow::Borrow<Self>> std::ops::BitAndAssign<B> for $newtype {
            fn bitand_assign(&mut self, rhs: B) {
                self.0 &= (&rhs.borrow().0)
            }
        }

        impl<B: std::borrow::Borrow<$newtype>> std::ops::BitOr<B> for &$newtype {
            type Output = $newtype;

            fn bitor(self, rhs: B) -> $newtype {
                $newtype(&self.0 | &rhs.borrow().0)
            }
        }

        impl<B: std::borrow::Borrow<Self>> std::ops::BitOr<B> for $newtype {
            type Output = Self;

            fn bitor(self, rhs: B) -> Self {
                $newtype(self.0 | &rhs.borrow().0)
            }
        }

        impl<B: std::borrow::Borrow<Self>> std::ops::BitOrAssign<B> for $newtype {
            fn bitor_assign(&mut self, rhs: B) {
                self.0 |= &rhs.borrow().0
            }
        }

        impl<B: std::borrow::Borrow<$newtype>> std::ops::BitXor<B> for &$newtype {
            type Output = $newtype;

            fn bitxor(self, rhs: B) -> $newtype {
                $newtype(&self.0 ^ &rhs.borrow().0)
            }
        }

        impl<B: std::borrow::Borrow<Self>> std::ops::BitXor<B> for $newtype {
            type Output = Self;

            fn bitxor(self, rhs: B) -> Self {
                $newtype(self.0 ^ &rhs.borrow().0)
            }
        }

        impl<B: std::borrow::Borrow<Self>> std::ops::BitXorAssign<B> for $newtype {
            fn bitxor_assign(&mut self, rhs: B) {
                self.0 ^= &rhs.borrow().0
            }
        }

        impl<'target> std::borrow::Borrow<$crate::bitmap::Bitmap> for $newtype {
            fn borrow(&self) -> &$crate::bitmap::Bitmap {
                self.as_ref()
            }
        }

        impl<'target> std::borrow::Borrow<$crate::bitmap::Bitmap> for $crate::bitmap::BitmapRef<'_, $newtype> {
            fn borrow(&self) -> &$crate::bitmap::Bitmap {
                self.as_ref()
            }
        }

        impl<'target> std::borrow::BorrowMut<$crate::bitmap::Bitmap> for $newtype {
            fn borrow_mut(&mut self) -> &mut $crate::bitmap::Bitmap {
                self.as_mut()
            }
        }

        impl std::fmt::Debug for $newtype {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let text = format!("{}({:?})", stringify!($newtype), &self.0);
                f.pad(&text)
            }
        }

        impl std::fmt::Display for $newtype {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let text = format!("{}({})", stringify!($newtype), &self.0);
                f.pad(&text)
            }
        }

        impl<BI: std::borrow::Borrow<$crate::bitmap::BitmapIndex>> Extend<BI> for $newtype {
            fn extend<T: IntoIterator<Item = BI>>(&mut self, iter: T) {
                self.0.extend(iter)
            }
        }

        impl<BI: std::borrow::Borrow<$crate::bitmap::BitmapIndex>> From<BI> for $newtype {
            fn from(value: BI) -> Self {
                Self(value.into())
            }
        }

        impl<BI: std::borrow::Borrow<$crate::bitmap::BitmapIndex>> FromIterator<BI> for $newtype {
            fn from_iter<I: IntoIterator<Item = BI>>(iter: I) -> Self {
                Self($crate::bitmap::Bitmap::from_iter(iter))
            }
        }

        impl<'newtype> IntoIterator for &'newtype $newtype {
            type Item = $crate::bitmap::BitmapIndex;
            type IntoIter = $crate::bitmap::Iter<&'newtype $crate::bitmap::Bitmap>;

            fn into_iter(self) -> Self::IntoIter {
                (&self.0).into_iter()
            }
        }

        impl std::ops::Not for &$newtype {
            type Output = $newtype;

            fn not(self) -> $newtype {
                $newtype(!&self.0)
            }
        }

        // SAFETY: $newtype is a repr(transparent) newtype of Bitmap, which is
        //         itself a repr(transparent) newtype of RawBitmap.
        unsafe impl $crate::bitmap::OwnedBitmap for $newtype {
            unsafe fn as_raw(&self) -> std::ptr::NonNull<$crate::bitmap::RawBitmap> {
                self.0.as_raw()
            }
        }

        impl<B: std::borrow::Borrow<Self>> PartialEq<B> for $newtype {
            fn eq(&self, other: &B) -> bool {
                self.0 == other.borrow().0
            }
        }

        impl<B: std::borrow::Borrow<Self>> PartialOrd<B> for $newtype {
            fn partial_cmp(&self, other: &B) -> Option<std::cmp::Ordering> {
                self.0.partial_cmp(&other.borrow().0)
            }
        }

        impl $crate::Sealed for $newtype {}

        impl<B: std::borrow::Borrow<$newtype>> std::ops::Sub<B> for &$newtype {
            type Output = $newtype;

            fn sub(self, rhs: B) -> $newtype {
                $newtype(&self.0 - &rhs.borrow().0)
            }
        }

        impl<B: std::borrow::Borrow<Self>> std::ops::Sub<B> for $newtype {
            type Output = Self;

            fn sub(self, rhs: B) -> Self {
                $newtype(self.0 - &rhs.borrow().0)
            }
        }

        impl<B: std::borrow::Borrow<Self>> std::ops::SubAssign<B> for $newtype {
            fn sub_assign(&mut self, rhs: B) {
                self.0 -= &rhs.borrow().0
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck_macros::quickcheck;
    use std::{
        collections::HashSet,
        ffi::c_ulonglong,
        fmt::Write,
        ops::{Range, RangeFrom, RangeInclusive},
    };

    // We can't fully check the value of infinite iterators because that would
    // literally take forever, so we only check a small subrange of the final
    // all-set/unset region, large enough to catch off-by-one-longword issues.
    const INFINITE_EXPLORE_ITERS: usize = std::mem::size_of::<c_ulonglong>() * 8;

    // Unfortunately, ranges of BitmapIndex cannot do everything that ranges of
    // built-in integer types can do due to some unstable integer traits, so
    // it's sometimes good to go back to usize.
    fn range_inclusive_to_usize(range: &RangeInclusive<BitmapIndex>) -> RangeInclusive<usize> {
        usize::from(*range.start())..=usize::from(*range.end())
    }

    // Split a possibly infinite bitmap into a finite bitmap and an infinite
    // range of set indices, separated from the indices of the finite bitmap by
    // a range of unset indices. To get the original bitmap back, use `set_range`.
    fn split_infinite_bitmap(mut bitmap: Bitmap) -> (Bitmap, Option<RangeFrom<BitmapIndex>>) {
        // If this bitmap is infinite...
        if bitmap.weight().is_none() {
            // ...and it has a finite part...
            if let Some(last_unset) = bitmap.last_unset() {
                let infinite_part = last_unset.checked_add_signed(1).unwrap()..;
                bitmap.unset_range(infinite_part.clone());
                (bitmap, Some(infinite_part))
            } else {
                (Bitmap::new(), Some(BitmapIndex::MIN..))
            }
        } else {
            (bitmap, None)
        }
    }

    fn test_basic_inplace(initial: &Bitmap, inverse: &Bitmap) {
        let mut buf = initial.clone();
        buf.clear();
        assert!(buf.is_empty());

        buf.copy_from(initial);
        buf.fill();
        assert!(buf.is_full());

        buf.copy_from(initial);
        buf.invert();
        assert_eq!(buf, *inverse);

        if initial.weight().unwrap_or(usize::MAX) > 0 {
            buf.copy_from(initial);
            buf.singlify();
            assert_eq!(buf.weight(), Some(1));
        }
    }

    fn test_indexing(initial: &Bitmap, index: BitmapIndex, initially_set: bool) {
        let single = Bitmap::from(index);
        let single_hole = !&single;

        // Bitmaps are conceptually infinite so we must be careful with
        // iteration-based verification of full bitmap contents. Let's just
        // account for off-by-one-word errors.
        let max_iters = initial
            .weight()
            .unwrap_or(usize::from(index) + INFINITE_EXPLORE_ITERS);

        assert_eq!(initial.is_set(index), initially_set);

        let mut buf = initial.clone();
        buf.set(index);
        assert_eq!(
            buf.weight(),
            initial.weight().map(|w| w + !initially_set as usize)
        );
        for idx in std::iter::once(index).chain(initial.iter_set().take(max_iters)) {
            assert!(buf.is_set(idx));
        }

        buf.copy_from(initial);
        buf.set_only(index);
        assert_eq!(buf, single);

        buf.copy_from(initial);
        buf.set_all_but(index);
        assert_eq!(buf, single_hole);

        buf.copy_from(initial);
        buf.unset(index);
        assert_eq!(
            buf.weight(),
            initial.weight().map(|w| w - initially_set as usize)
        );
        for idx in initial.iter_set().take(max_iters) {
            assert_eq!(buf.is_set(idx), idx != index);
        }
    }

    fn test_and_sub(b1: &Bitmap, b2: &Bitmap, and: &Bitmap) {
        assert_eq!(b1 & b2, *and);
        let mut buf = b1.clone();
        buf &= b2;
        assert_eq!(buf, *and);

        let b1_andnot_b2 = b1 & !b2;
        assert_eq!(b1 - b2, b1_andnot_b2);
        buf.copy_from(b1);
        buf -= b2;
        assert_eq!(buf, b1_andnot_b2);

        let b2_andnot_b1 = b2 & !b1;
        assert_eq!(b2 - b1, b2_andnot_b1);
        buf.copy_from(b2);
        buf -= b1;
        assert_eq!(buf, b2_andnot_b1);
    }

    #[allow(clippy::redundant_clone)]
    #[test]
    fn empty() {
        let empty = Bitmap::new();
        let inverse = Bitmap::full();

        let test_empty = |empty: &Bitmap| {
            assert_eq!(empty.first_set(), None);
            assert_eq!(empty.first_unset().map(usize::from), Some(0));
            assert!(empty.is_empty());
            assert!(!empty.is_full());
            assert_eq!(empty.into_iter().count(), 0);
            assert_eq!(empty.iter_set().count(), 0);
            assert_eq!(empty.last_set(), None);
            assert_eq!(empty.last_unset(), None);
            assert_eq!(empty.weight(), Some(0));

            for (expected, idx) in empty.iter_unset().enumerate().take(INFINITE_EXPLORE_ITERS) {
                assert_eq!(expected, usize::from(idx));
            }

            assert_eq!(format!("{empty:?}"), "");
            assert_eq!(format!("{empty}"), "");
            assert_eq!(!empty, inverse);
        };
        test_empty(&empty);
        test_empty(&empty.clone());
        test_empty(&Bitmap::default());

        test_basic_inplace(&empty, &inverse);
    }

    #[quickcheck]
    fn empty_extend(extra: HashSet<BitmapIndex>) {
        let mut extended = Bitmap::new();
        extended.extend(extra.iter().copied());

        assert_eq!(extended.weight(), Some(extra.len()));
        for idx in extra {
            assert!(extended.is_set(idx));
        }
    }

    #[quickcheck]
    fn empty_op_index(index: BitmapIndex) {
        test_indexing(&Bitmap::new(), index, false);
    }

    #[quickcheck]
    fn empty_op_range(range: Range<BitmapIndex>) {
        let mut buf = Bitmap::new();
        buf.set_range(range.clone());
        assert_eq!(buf, Bitmap::from_range(range.clone()));
        buf.clear();

        buf.unset_range(range);
        assert!(buf.is_empty());
    }

    #[quickcheck]
    fn empty_op_bitmap(other: Bitmap) {
        let empty = Bitmap::new();

        assert_eq!(empty.includes(&other), other.is_empty());
        assert!(other.includes(&empty));
        assert!(!empty.intersects(&other));

        assert_eq!(empty == other, other.is_empty());
        if !other.is_empty() {
            assert!(empty < other);
        }

        test_and_sub(&empty, &other, &empty);

        assert_eq!(&empty | &other, other);
        let mut buf = Bitmap::new();
        buf |= &other;
        assert_eq!(buf, other);

        assert_eq!(&empty ^ &other, other);
        buf.clear();
        buf ^= &other;
        assert_eq!(buf, other);
    }

    #[allow(clippy::redundant_clone)]
    #[test]
    fn full() {
        let full = Bitmap::full();
        let inverse = Bitmap::new();

        let test_full = |full: &Bitmap| {
            assert_eq!(full.first_set().map(usize::from), Some(0));
            assert_eq!(full.first_unset(), None);
            assert!(!full.is_empty());
            assert!(full.is_full());
            assert_eq!(full.iter_unset().count(), 0);
            assert_eq!(full.last_set(), None);
            assert_eq!(full.last_unset(), None);
            assert_eq!(full.weight(), None);

            fn test_iter_set(iter: impl Iterator<Item = BitmapIndex>) {
                for (expected, idx) in iter.enumerate().take(INFINITE_EXPLORE_ITERS) {
                    assert_eq!(expected, usize::from(idx));
                }
            }
            test_iter_set(full.into_iter());
            test_iter_set(full.iter_set());

            assert_eq!(format!("{full:?}"), "0-");
            assert_eq!(format!("{full}"), "0-");
            assert_eq!(!full, inverse);
        };
        test_full(&full);
        test_full(&full.clone());

        test_basic_inplace(&full, &inverse);
    }

    #[quickcheck]
    fn full_extend(extra: HashSet<BitmapIndex>) {
        let mut extended = Bitmap::full();
        extended.extend(extra.iter().copied());
        assert!(extended.is_full());
    }

    #[quickcheck]
    fn full_op_index(index: BitmapIndex) {
        test_indexing(&Bitmap::full(), index, true);
    }

    #[quickcheck]
    fn full_op_range(range: Range<BitmapIndex>) {
        let mut ranged_hole = Bitmap::from_range(range.clone());
        ranged_hole.invert();

        let mut buf = Bitmap::full();
        buf.set_range(range.clone());
        assert!(buf.is_full());

        buf.fill();
        buf.unset_range(range);
        assert_eq!(buf, ranged_hole);
    }

    #[quickcheck]
    fn full_op_bitmap(other: Bitmap) {
        let full = Bitmap::full();
        let not_other = !&other;

        assert!(full.includes(&other));
        assert_eq!(other.includes(&full), other.is_full());
        assert_eq!(full.intersects(&other), !other.is_empty());

        assert_eq!(full == other, other.is_full());
        assert_eq!(
            full.cmp(&other),
            if other.is_full() {
                Ordering::Equal
            } else {
                Ordering::Greater
            }
        );

        test_and_sub(&full, &other, &other);

        assert!((&full | &other).is_full());
        let mut buf = Bitmap::full();
        buf |= &other;
        assert!(buf.is_full());

        assert_eq!(&full ^ &other, not_other);
        buf.fill();
        buf ^= &other;
        assert_eq!(buf, not_other);
    }

    #[allow(clippy::redundant_clone)]
    #[quickcheck]
    fn from_range(range: RangeInclusive<BitmapIndex>) {
        let ranged_bitmap = Bitmap::from_range(range.clone());

        let elems = (usize::from(*range.start())..=usize::from(*range.end()))
            .map(|idx| BitmapIndex::try_from(idx).unwrap())
            .collect::<Vec<_>>();
        let first_unset = if let Some(&BitmapIndex::MIN) = elems.first() {
            elems
                .last()
                .copied()
                .and_then(|item| item.checked_add_signed(1))
        } else {
            Some(BitmapIndex::MIN)
        };
        let unset_after_set = if let Some(last_set) = elems.last() {
            last_set.checked_add_signed(1)
        } else {
            Some(BitmapIndex::MIN)
        };
        let display = if let (Some(first), Some(last)) = (elems.first(), elems.last()) {
            if first != last {
                format!("{first}-{last}")
            } else {
                format!("{first}")
            }
        } else {
            String::new()
        };
        let inverse = if let (Some(&first), Some(last)) = (elems.first(), elems.last()) {
            let mut buf = Bitmap::from_range(..first);
            if let Some(after_last) = last.checked_add_signed(1) {
                buf.set_range(after_last..)
            }
            buf
        } else {
            Bitmap::full()
        };

        let test_ranged = |ranged_bitmap: &Bitmap| {
            assert_eq!(ranged_bitmap.first_set(), elems.first().copied());
            assert_eq!(ranged_bitmap.first_unset(), first_unset);
            assert_eq!(ranged_bitmap.is_empty(), elems.is_empty());
            assert!(!ranged_bitmap.is_full());
            assert_eq!(ranged_bitmap.into_iter().collect::<Vec<_>>(), elems);
            assert_eq!(ranged_bitmap.iter_set().collect::<Vec<_>>(), elems);
            assert_eq!(ranged_bitmap.last_set(), elems.last().copied());
            assert_eq!(ranged_bitmap.last_unset(), None);
            assert_eq!(ranged_bitmap.weight(), Some(elems.len()));

            let mut unset = ranged_bitmap.iter_unset();
            if let Some(first_set) = elems.first() {
                for expected_unset in 0..usize::from(*first_set) {
                    assert_eq!(unset.next().map(usize::from), Some(expected_unset));
                }
            }
            let mut expected_unset =
                std::iter::successors(unset_after_set, |unset| unset.checked_add_signed(1));
            for unset_index in unset.take(INFINITE_EXPLORE_ITERS) {
                assert_eq!(unset_index, expected_unset.next().unwrap())
            }

            assert_eq!(format!("{ranged_bitmap:?}"), display);
            assert_eq!(format!("{ranged_bitmap}"), display);
            assert_eq!(!ranged_bitmap, inverse);
        };
        test_ranged(&ranged_bitmap);
        test_ranged(&ranged_bitmap.clone());

        test_basic_inplace(&ranged_bitmap, &inverse);
    }

    #[quickcheck]
    fn from_range_extend(range: RangeInclusive<BitmapIndex>, extra: HashSet<BitmapIndex>) {
        let mut extended = Bitmap::from_range(range.clone());
        let mut indices = extra.clone();
        extended.extend(extra);

        for idx in usize::from(*range.start())..=usize::from(*range.end()) {
            indices.insert(idx.try_into().unwrap());
        }

        assert_eq!(extended.weight(), Some(indices.len()));
        for idx in indices {
            assert!(extended.is_set(idx));
        }
    }

    #[quickcheck]
    fn from_range_op_index(range: RangeInclusive<BitmapIndex>, index: BitmapIndex) {
        test_indexing(
            &Bitmap::from_range(range.clone()),
            index,
            range.contains(&index),
        );
    }

    #[quickcheck]
    fn from_range_op_range(
        range: RangeInclusive<BitmapIndex>,
        other_range: RangeInclusive<BitmapIndex>,
    ) {
        let usized = range_inclusive_to_usize(&range);
        let other_usized = range_inclusive_to_usize(&other_range);

        let num_indices = |range: &RangeInclusive<usize>| range.clone().count();
        let num_common_indices = if usized.is_empty() || other_usized.is_empty() {
            0
        } else {
            num_indices(
                &(*usized.start().max(other_usized.start())
                    ..=*usized.end().min(other_usized.end())),
            )
        };

        let ranged_bitmap = Bitmap::from_range(range);

        let mut buf = ranged_bitmap.clone();
        buf.set_range(other_range.clone());
        assert_eq!(
            buf.weight().unwrap(),
            num_indices(&usized) + num_indices(&other_usized) - num_common_indices
        );
        for idx in usized.clone().chain(other_usized.clone()) {
            assert!(buf.is_set(idx));
        }

        buf.copy_from(&ranged_bitmap);
        buf.unset_range(other_range);
        assert_eq!(
            buf.weight().unwrap(),
            num_indices(&usized) - num_common_indices
        );
        for idx in usized {
            assert_eq!(buf.is_set(idx), !other_usized.contains(&idx));
        }
    }

    #[allow(clippy::similar_names)]
    #[quickcheck]
    fn from_range_op_bitmap(range: RangeInclusive<BitmapIndex>, other: Bitmap) {
        let ranged_bitmap = Bitmap::from_range(range.clone());
        let usized = range_inclusive_to_usize(&range);

        assert_eq!(
            ranged_bitmap.includes(&other),
            other.is_empty()
                || (other.last_set().is_some() && other.iter_set().all(|idx| range.contains(&idx)))
        );
        assert_eq!(
            other.includes(&ranged_bitmap),
            usized.clone().all(|idx| other.is_set(idx))
        );
        assert_eq!(
            ranged_bitmap.intersects(&other),
            usized.clone().any(|idx| other.is_set(idx))
        );

        assert_eq!(
            ranged_bitmap == other,
            other.weight() == Some(usized.count()) && other.includes(&ranged_bitmap)
        );

        if ranged_bitmap.is_empty() {
            assert_eq!(
                ranged_bitmap.cmp(&other),
                if !other.is_empty() {
                    Ordering::Less
                } else {
                    Ordering::Equal
                }
            );
        } else {
            match ranged_bitmap.cmp(&other) {
                Ordering::Less => {
                    assert!(
                        other.last_set().unwrap_or(BitmapIndex::MAX) > *range.end()
                            || (other.includes(&ranged_bitmap)
                                && other.first_set().unwrap_or(BitmapIndex::MIN) < *range.start())
                    )
                }
                Ordering::Equal => assert_eq!(ranged_bitmap, other),
                Ordering::Greater => assert!(!other.includes(&ranged_bitmap)),
            }
        }

        let (other_finite, other_infinite) = split_infinite_bitmap(other.clone());

        let mut ranged_and_other = other_finite
            .iter_set()
            .filter(|idx| range.contains(idx))
            .collect::<Bitmap>();
        if let Some(infinite) = &other_infinite {
            if !ranged_bitmap.is_empty() {
                ranged_and_other.set_range(infinite.start.max(*range.start())..=*range.end());
            }
        }
        test_and_sub(&ranged_bitmap, &other, &ranged_and_other);

        let mut ranged_or_other = other.clone();
        ranged_or_other.set_range(range);
        assert_eq!(&ranged_bitmap | &other, ranged_or_other);
        let mut buf = ranged_bitmap.clone();
        buf |= &other;
        assert_eq!(buf, ranged_or_other);

        let ranged_xor_other = ranged_or_other - ranged_and_other;
        assert_eq!(&ranged_bitmap ^ &other, ranged_xor_other);
        let mut buf = ranged_bitmap;
        buf ^= &other;
        assert_eq!(buf, ranged_xor_other);
    }

    #[quickcheck]
    fn from_iterator(indices: HashSet<BitmapIndex>) {
        let bitmap = indices.iter().copied().collect::<Bitmap>();
        assert_eq!(bitmap.weight(), Some(indices.len()));
        for idx in indices {
            assert!(bitmap.is_set(idx));
        }
    }

    #[allow(clippy::redundant_clone)]
    #[quickcheck]
    fn arbitrary(bitmap: Bitmap) {
        // Test properties pertaining to first iterator output
        assert_eq!(bitmap.first_set(), bitmap.iter_set().next());
        assert_eq!(bitmap.first_unset(), bitmap.iter_unset().next());
        assert_eq!(bitmap.is_empty(), bitmap.first_set().is_none());
        assert_eq!(bitmap.is_full(), bitmap.first_unset().is_none());

        // Test iterator-wide properties
        fn test_iter(
            bitmap: &Bitmap,
            iter_set: impl Iterator<Item = BitmapIndex>,
        ) -> (Bitmap, String) {
            let mut iter_set = iter_set.peekable();
            let mut iter_unset = bitmap.iter_unset().peekable();

            // Iterate over BitmapIndex until the end ot either iterator is reached
            let mut next_index = BitmapIndex::MIN;
            let mut set_stripe_start = None;
            let mut observed_weight = 0;
            let mut observed_last_set = None;
            let mut observed_last_unset = None;
            let mut inverse = Bitmap::full();
            let mut display = String::new();
            //
            while let (Some(next_set), Some(next_unset)) =
                (iter_set.peek().copied(), iter_unset.peek().copied())
            {
                // Move least advanced iterator forward
                match next_set.cmp(&next_unset) {
                    Ordering::Less => {
                        // Next index should be set
                        iter_set.next();
                        assert_eq!(next_set, next_index);

                        // Acknowledge that a set index has been processed
                        observed_last_set = Some(next_set);
                        observed_weight += 1;
                        if set_stripe_start.is_none() {
                            set_stripe_start = Some(next_set);
                        }
                    }
                    // Next index should be unset
                    Ordering::Greater => {
                        // Next index should be unset
                        iter_unset.next();
                        assert_eq!(next_unset, next_index);
                        observed_last_unset = Some(next_unset);

                        // If we just went through a stripe of set indices,
                        // propagate that into the inverse & display predictions
                        if let Some(first_set) = set_stripe_start {
                            let last_set = observed_last_set.unwrap();
                            inverse.unset_range(first_set..=last_set);
                            if !display.is_empty() {
                                write!(display, ",").unwrap();
                            }
                            write!(display, "{first_set}").unwrap();
                            if last_set != first_set {
                                write!(display, "-{last_set}").unwrap();
                            }
                            set_stripe_start = None;
                        }
                    }
                    Ordering::Equal => unreachable!("Next index can't be both set and unset"),
                }

                // Update next_index
                next_index = next_index.checked_add_signed(1).expect(
                    "Shouldn't overflow if we had both a next set & unset index before iterating",
                );
            }

            // At this point, we reached the end of one of the iterators, and
            // the other iterator should just keep producing an infinite
            // sequence of consecutive indices. Reach some conclusions...
            let mut infinite_iter: Box<dyn Iterator<Item = BitmapIndex>> =
                match (iter_set.peek(), iter_unset.peek()) {
                    (Some(next_set), None) => {
                        // Check end-of-iterator properties
                        assert_eq!(bitmap.last_set(), None);
                        assert_eq!(bitmap.last_unset(), observed_last_unset);
                        assert_eq!(bitmap.weight(), None);

                        // Handle last (infinite) range of set elements
                        let stripe_start = set_stripe_start.unwrap_or(*next_set);
                        inverse.unset_range(stripe_start..);
                        if !display.is_empty() {
                            write!(display, ",").unwrap();
                        }
                        write!(display, "{stripe_start}-").unwrap();

                        // Expose infinite iterator of set elements
                        Box::new(iter_set)
                    }
                    (None, Some(_unset)) => {
                        // Check end-of-iterator properties
                        assert_eq!(bitmap.last_set(), observed_last_set);
                        assert_eq!(bitmap.last_unset(), None);
                        assert_eq!(bitmap.weight(), Some(observed_weight));

                        // Handle previous range of set elements, if any
                        if let Some(first_set) = set_stripe_start {
                            let last_set = observed_last_set.unwrap();
                            inverse.unset_range(first_set..=last_set);
                            if !display.is_empty() {
                                write!(display, ",").unwrap();
                            }
                            write!(display, "{first_set}").unwrap();
                            if last_set != first_set {
                                write!(display, "-{last_set}").unwrap();
                            }
                        }

                        Box::new(iter_unset)
                    }
                    _ => unreachable!("At least one iterator is finite, they can't both be"),
                };

            // ...and iterate the infinite iterator for a while to check it
            // does seem to meet expectations.
            for _ in 0..INFINITE_EXPLORE_ITERS {
                assert_eq!(infinite_iter.next(), Some(next_index));
                if let Some(index) = next_index.checked_add_signed(1) {
                    next_index = index;
                } else {
                    break;
                }
            }

            // Return predicted bitmap inverse and display
            (inverse, display)
        }
        let (inverse, display) = test_iter(&bitmap, (&bitmap).into_iter());
        let (inverse2, display2) = test_iter(&bitmap, bitmap.iter_set());
        //
        assert_eq!(inverse, inverse2);
        assert_eq!(display, display2);
        assert_eq!(!&bitmap, inverse);
        assert_eq!(format!("{bitmap:?}"), display);
        assert_eq!(format!("{bitmap}"), display);

        // Test in-place operations
        test_basic_inplace(&bitmap, &inverse);

        // Test that a clone is indistinguishable from the original bitmap
        let clone = bitmap.clone();
        assert_eq!(clone.first_set(), bitmap.first_set());
        assert_eq!(clone.first_unset(), bitmap.first_unset());
        assert_eq!(clone.is_empty(), bitmap.is_empty());
        assert_eq!(clone.is_full(), bitmap.is_full());
        assert_eq!(clone.last_set(), bitmap.last_set());
        assert_eq!(clone.last_unset(), bitmap.last_unset());
        assert_eq!(clone.weight(), bitmap.weight());
        //
        let (finite, infinite) = split_infinite_bitmap(bitmap);
        if let Some(infinite) = infinite {
            let test_iter = |mut iter_set: Box<dyn Iterator<Item = BitmapIndex>>| {
                let mut iter_unset = clone.iter_unset().fuse();
                let infinite_start = usize::from(infinite.start);
                for idx in 0..infinite_start {
                    let next = if finite.is_set(idx) {
                        iter_set.next()
                    } else {
                        iter_unset.next()
                    };
                    assert_eq!(next.map(usize::from), Some(idx));
                }
                assert_eq!(iter_unset.next(), None);
                for idx in (infinite_start..).take(INFINITE_EXPLORE_ITERS) {
                    assert_eq!(iter_set.next().map(usize::from), Some(idx));
                }
            };
            test_iter(Box::new((&clone).into_iter()));
            test_iter(Box::new(clone.iter_set()));
        } else {
            assert_eq!((&clone).into_iter().collect::<Bitmap>(), finite);
            assert_eq!(clone.iter_set().collect::<Bitmap>(), finite);

            let num_iters = usize::from(finite.last_set().unwrap_or(BitmapIndex::MIN)) + 1
                - finite.weight().unwrap()
                + INFINITE_EXPLORE_ITERS;
            let mut iterator = finite.iter_unset().zip(clone.iter_unset());
            for _ in 0..num_iters {
                let (expected, actual) = iterator.next().unwrap();
                assert_eq!(expected, actual);
            }
        }
        //
        assert_eq!(format!("{clone:?}"), display);
        assert_eq!(format!("{clone}"), display);
        assert_eq!(!clone, inverse);
    }

    #[quickcheck]
    fn arbitrary_extend(bitmap: Bitmap, extra: HashSet<BitmapIndex>) {
        let mut extended = bitmap.clone();
        extended.extend(extra.iter().copied());

        if let Some(bitmap_weight) = bitmap.weight() {
            let extra_weight = extended
                .weight()
                .unwrap()
                .checked_sub(bitmap_weight)
                .expect("Extending a bitmap shouldn't reduce the weight");
            assert!(extra_weight <= extra.len());
        }

        for idx in extra {
            assert!(extended.is_set(idx));
        }
    }

    #[quickcheck]
    fn arbitrary_op_index(bitmap: Bitmap, index: BitmapIndex) {
        test_indexing(&bitmap, index, bitmap.is_set(index))
    }

    #[quickcheck]
    fn arbitrary_op_range(bitmap: Bitmap, range: Range<BitmapIndex>) {
        let range_usize = usize::from(range.start)..usize::from(range.end);
        let range_len = range_usize.clone().count();

        let mut buf = bitmap.clone();
        buf.set_range(range.clone());
        if let Some(bitmap_weight) = bitmap.weight() {
            let extra_weight = buf
                .weight()
                .unwrap()
                .checked_sub(bitmap_weight)
                .expect("Setting indices shouldn't reduce the weight");
            assert!(extra_weight <= range_len);

            for idx in range_usize.clone() {
                assert!(buf.is_set(idx));
            }
        }

        buf.copy_from(&bitmap);
        buf.unset_range(range);
        if let Some(bitmap_weight) = bitmap.weight() {
            let lost_weight = bitmap_weight
                .checked_sub(buf.weight().unwrap())
                .expect("Clearing indices shouldn't increase the weight");
            assert!(lost_weight <= range_len);

            for idx in range_usize {
                assert!(!buf.is_set(idx));
            }
        }
    }

    #[allow(clippy::similar_names)]
    #[quickcheck]
    fn arbitrary_op_bitmap(bitmap: Bitmap, other: Bitmap) {
        let (finite, infinite) = split_infinite_bitmap(bitmap.clone());
        let (other_finite, other_infinite) = split_infinite_bitmap(other.clone());

        assert_eq!(
            bitmap.includes(&other),
            other_finite.iter_set().all(|idx| bitmap.is_set(idx))
                && match (&infinite, &other_infinite) {
                    (Some(infinite), Some(other_infinite)) => {
                        (usize::from(other_infinite.start)..usize::from(infinite.start))
                            .all(|idx| finite.is_set(idx))
                    }
                    (_, None) => true,
                    (None, Some(_)) => false,
                }
        );

        fn infinite_intersects_finite(infinite: &RangeFrom<BitmapIndex>, finite: &Bitmap) -> bool {
            finite
                .last_set()
                .map(|last_set| infinite.start <= last_set)
                .unwrap_or(false)
        }
        assert_eq!(
            bitmap.intersects(&other),
            finite.iter_set().any(|idx| other.is_set(idx))
                || match (&infinite, &other_infinite) {
                    (Some(_), Some(_)) => true,
                    (Some(infinite), None) => infinite_intersects_finite(infinite, &other_finite),
                    (None, Some(other_infinite)) =>
                        infinite_intersects_finite(other_infinite, &finite),
                    (None, None) => false,
                }
        );

        assert_eq!(
            bitmap == other,
            bitmap.includes(&other) && other.includes(&bitmap)
        );

        fn expected_cmp(bitmap: &Bitmap, reference: &Bitmap) -> Ordering {
            let (finite, infinite) = split_infinite_bitmap(bitmap.clone());
            let (ref_finite, ref_infinite) = split_infinite_bitmap(reference.clone());

            let finite_end = match (infinite, ref_infinite) {
                (Some(_), None) => return Ordering::Greater,
                (None, Some(_)) => return Ordering::Less,
                (Some(infinite), Some(ref_infinite)) => infinite.start.max(ref_infinite.start),
                (None, None) => finite
                    .last_set()
                    .unwrap_or(BitmapIndex::MIN)
                    .max(ref_finite.last_set().unwrap_or(BitmapIndex::MIN)),
            };

            for idx in (0..=usize::from(finite_end)).rev() {
                match (bitmap.is_set(idx), reference.is_set(idx)) {
                    (true, false) => return Ordering::Greater,
                    (false, true) => return Ordering::Less,
                    _ => continue,
                }
            }
            Ordering::Equal
        }
        assert_eq!(bitmap.cmp(&other), expected_cmp(&bitmap, &other));

        let mut bitmap_and_other = finite
            .iter_set()
            .filter(|idx| other.is_set(*idx))
            .collect::<Bitmap>();
        match (&infinite, &other_infinite) {
            (Some(infinite), Some(other_infinite)) => {
                bitmap_and_other.set_range(infinite.start.max(other_infinite.start)..);
                for idx in usize::from(infinite.start)..usize::from(other_infinite.start) {
                    if other.is_set(idx) {
                        bitmap_and_other.set(idx);
                    }
                }
            }
            (Some(infinite), None) => {
                let other_end = other_finite.last_set().unwrap_or(BitmapIndex::MIN);
                for idx in usize::from(infinite.start)..=usize::from(other_end) {
                    if other.is_set(idx) {
                        bitmap_and_other.set(idx)
                    }
                }
            }
            _ => {}
        }
        test_and_sub(&bitmap, &other, &bitmap_and_other);

        let mut bitmap_or_other = finite;
        for idx in &other_finite {
            bitmap_or_other.set(idx);
        }
        if let Some(infinite) = infinite {
            bitmap_or_other.set_range(infinite);
        }
        if let Some(other_infinite) = other_infinite {
            bitmap_or_other.set_range(other_infinite);
        }
        assert_eq!(&bitmap | &other, bitmap_or_other);
        let mut buf = bitmap.clone();
        buf |= &other;
        assert_eq!(buf, bitmap_or_other);

        let bitmap_xor_other = bitmap_or_other - bitmap_and_other;
        assert_eq!(&bitmap ^ &other, bitmap_xor_other);
        buf.copy_from(&bitmap);
        buf ^= &other;
        assert_eq!(buf, bitmap_xor_other);
    }
}