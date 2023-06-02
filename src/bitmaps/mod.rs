//! Bitmap API

// Main docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__bitmap.html

mod index;

#[cfg(doc)]
use crate::{
    cpu::cpusets::CpuSet,
    memory::nodesets::NodeSet,
    objects::TopologyObject,
    topology::{builder::BuildFlags, Topology},
};
use crate::{
    errors,
    ffi::{self, IncompleteType},
};
#[cfg(any(test, feature = "quickcheck"))]
use quickcheck::{Arbitrary, Gen};
use std::{
    borrow::Borrow,
    clone::Clone,
    cmp::Ordering,
    convert::TryFrom,
    ffi::{c_int, c_uint},
    fmt::{self, Debug, Display},
    iter::{FromIterator, FusedIterator},
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Bound, Not, RangeBounds,
        Sub, SubAssign,
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
#[repr(C)]
pub(crate) struct RawBitmap(IncompleteType);

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
/// #     cpu::{binding::CpuBindingFlags, cpusets::CpuSet},
/// #     objects::{types::ObjectType},
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
/// [`CpuSet`]: crate::cpu::cpusets::CpuSet
/// [`NodeSet`]: crate::memory::nodesets::NodeSet
#[doc(alias = "hwloc_bitmap_t")]
#[doc(alias = "hwloc_const_bitmap_t")]
#[repr(transparent)]
pub struct Bitmap(*mut RawBitmap);

// NOTE: Remember to keep the method signatures and first doc lines in
//       impl_newtype_ops in sync with what's going on below.
impl Bitmap {
    // === FFI interoperability ===

    /// Wraps an owned bitmap from hwloc
    ///
    /// # Safety
    ///
    /// If non-null, the pointer must target a valid bitmap that we will acquire
    /// ownership of and automatically free on Drop.
    pub(crate) unsafe fn from_raw(bitmap: *mut RawBitmap) -> Option<Self> {
        NonNull::new(bitmap).map(|ptr| unsafe { Self::from_non_null(ptr) })
    }

    /// Wraps an owned bitmap from hwloc
    ///
    /// # Safety
    ///
    /// The pointer must target a valid bitmap that we will acquire ownership of
    /// and automatically free on Drop.
    pub(crate) unsafe fn from_non_null(bitmap: NonNull<RawBitmap>) -> Self {
        Self(bitmap.as_ptr())
    }

    /// Wraps an hwloc-originated borrowed bitmap pointer into the `Bitmap` representation.
    ///
    /// # Safety
    ///
    /// If non-null, the pointer must target a valid bitmap, but unlike with
    /// from_raw, it will not be automatically freed on Drop.
    pub(crate) unsafe fn borrow_from_raw(bitmap: &*const RawBitmap) -> Option<&Self> {
        (!bitmap.is_null()).then_some(std::mem::transmute::<&*const RawBitmap, &Self>(bitmap))
    }

    /// Wraps an hwloc-originated borrowed bitmap pointer into the `Bitmap` representation.
    ///
    /// # Safety
    ///
    /// If non-null, the pointer must target a valid bitmap, but unlike with
    /// from_raw, it will not be automatically freed on Drop.
    pub(crate) unsafe fn borrow_from_raw_mut(bitmap: &*mut RawBitmap) -> Option<&Self> {
        (!bitmap.is_null()).then_some(std::mem::transmute::<&*mut RawBitmap, &Self>(bitmap))
    }

    /// Wraps an hwloc-originated borrowed bitmap pointer into the `Bitmap` representation.
    ///
    /// # Safety
    ///
    /// If non-null, the pointer must target a valid bitmap, but unlike with
    /// from_raw, it will not be automatically freed on Drop.
    pub(crate) unsafe fn borrow_from_non_null(bitmap: &NonNull<RawBitmap>) -> &Self {
        std::mem::transmute::<&NonNull<RawBitmap>, &Self>(bitmap)
    }

    // NOTE: There is no borrow_mut_from_raw because it would not be safe as if
    //       you expose an &mut Bitmap, the user can trigger Drop.

    /// Contained bitmap pointer (for interaction with hwloc)
    pub(crate) fn as_ptr(&self) -> *const RawBitmap {
        self.0
    }

    /// Contained mutable bitmap pointer (for interaction with hwloc)
    pub(crate) fn as_mut_ptr(&mut self) -> *mut RawBitmap {
        self.0
    }

    // === Constructors ===

    /// Creates an empty `Bitmap`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let empty = Bitmap::new();
    /// assert!(empty.is_empty());
    /// ```
    #[doc(alias = "hwloc_bitmap_alloc")]
    pub fn new() -> Self {
        unsafe {
            let ptr =
                errors::call_hwloc_ptr_mut("hwloc_bitmap_alloc", || ffi::hwloc_bitmap_alloc())
                    .expect("Bitmap operation failures are handled via panics");
            Self::from_non_null(ptr)
        }
    }

    /// Creates a full `Bitmap`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let full = Bitmap::full();
    /// assert!(full.is_full());
    /// ```
    #[doc(alias = "hwloc_bitmap_alloc_full")]
    pub fn full() -> Self {
        unsafe {
            let ptr = errors::call_hwloc_ptr_mut("hwloc_bitmap_alloc_full", || {
                ffi::hwloc_bitmap_alloc_full()
            })
            .expect("Bitmap operation failures are handled via panics");
            Self::from_non_null(ptr)
        }
    }

    /// Creates a new `Bitmap` with the given range of indices set
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(12..=34);
    /// let mut bitmap2 = Bitmap::new();
    /// bitmap2.copy_from(&bitmap);
    /// assert_eq!(format!("{bitmap2}"), "12-34");
    /// ```
    #[doc(alias = "hwloc_bitmap_copy")]
    pub fn copy_from(&mut self, other: &Self) {
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(12..=34);
    /// bitmap.clear();
    /// assert!(bitmap.is_empty());
    /// ```
    #[doc(alias = "hwloc_bitmap_zero")]
    pub fn clear(&mut self) {
        unsafe { ffi::hwloc_bitmap_zero(self.as_mut_ptr()) }
    }

    /// Set all indices
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(12..=34);
    /// bitmap.fill();
    /// assert!(bitmap.is_full());
    /// ```
    #[doc(alias = "hwloc_bitmap_fill")]
    pub fn fill(&mut self) {
        unsafe { ffi::hwloc_bitmap_fill(self.as_mut_ptr()) }
    }

    /// Clear all indices except for `idx`, which is set
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
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
    /// use hwlocality::bitmaps::Bitmap;
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
    /// use hwlocality::bitmaps::Bitmap;
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
    /// use hwlocality::bitmaps::Bitmap;
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
    /// use hwlocality::bitmaps::Bitmap;
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
    /// use hwlocality::bitmaps::Bitmap;
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(12..=34);
    /// bitmap.singlify();
    /// assert_eq!(bitmap.weight(), Some(1));
    /// ```
    #[doc(alias = "hwloc_bitmap_singlify")]
    pub fn singlify(&mut self) {
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
    /// use hwlocality::bitmaps::Bitmap;
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// assert!(Bitmap::new().is_empty());
    /// assert!(!Bitmap::from_range(12..=34).is_empty());
    /// assert!(!Bitmap::full().is_empty());
    /// ```
    #[doc(alias = "hwloc_bitmap_iszero")]
    pub fn is_empty(&self) -> bool {
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// assert!(!Bitmap::new().is_full());
    /// assert!(!Bitmap::from_range(12..=34).is_full());
    /// assert!(Bitmap::full().is_full());
    /// ```
    #[doc(alias = "hwloc_bitmap_isfull")]
    pub fn is_full(&self) -> bool {
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let first_set_usize = |b: Bitmap| b.first_set().map(usize::from);
    /// assert_eq!(Bitmap::new().first_set(), None);
    /// assert_eq!(first_set_usize(Bitmap::from_range(12..=34)), Some(12));
    /// assert_eq!(first_set_usize(Bitmap::full()), Some(0));
    /// ```
    #[doc(alias = "hwloc_bitmap_first")]
    pub fn first_set(&self) -> Option<BitmapIndex> {
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(12..=21);
    /// let indices = bitmap.iter_set().map(usize::from).collect::<Vec<_>>();
    /// assert_eq!(indices, &[12, 13, 14, 15, 16, 17, 18, 19, 20, 21]);
    /// ```
    #[doc(alias = "hwloc_bitmap_foreach_begin")]
    #[doc(alias = "hwloc_bitmap_foreach_end")]
    #[doc(alias = "hwloc_bitmap_next")]
    pub fn iter_set(&self) -> BitmapIterator<&Bitmap> {
        BitmapIterator::new(self, Bitmap::next_set)
    }

    /// Check the last set index, if any
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let last_set_usize = |b: Bitmap| b.last_set().map(usize::from);
    /// assert_eq!(Bitmap::new().last_set(), None);
    /// assert_eq!(last_set_usize(Bitmap::from_range(12..=34)), Some(34));
    /// assert_eq!(Bitmap::full().last_set(), None);
    /// ```
    #[doc(alias = "hwloc_bitmap_last")]
    pub fn last_set(&self) -> Option<BitmapIndex> {
        let result = unsafe { ffi::hwloc_bitmap_last(self.as_ptr()) };
        assert!(
            result >= -1,
            "hwloc_bitmap_last returned error code {result}"
        );
        BitmapIndex::try_from_c_int(result).ok()
    }

    /// The number of indices that are set in the bitmap.
    ///
    /// None means that an infinite number of indices are set.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// assert_eq!(Bitmap::new().weight(), Some(0));
    /// assert_eq!(Bitmap::from_range(12..34).weight(), Some(34-12));
    /// assert_eq!(Bitmap::full().weight(), None);
    /// ```
    #[doc(alias = "hwloc_bitmap_weight")]
    pub fn weight(&self) -> Option<usize> {
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let first_unset_usize = |b: Bitmap| b.first_unset().map(usize::from);
    /// assert_eq!(first_unset_usize(Bitmap::new()), Some(0));
    /// assert_eq!(first_unset_usize(Bitmap::from_range(..12)), Some(12));
    /// assert_eq!(Bitmap::full().first_unset(), None);
    /// ```
    #[doc(alias = "hwloc_bitmap_first_unset")]
    pub fn first_unset(&self) -> Option<BitmapIndex> {
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(12..);
    /// let indices = bitmap.iter_unset().map(usize::from).collect::<Vec<_>>();
    /// assert_eq!(indices, &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]);
    /// ```
    #[doc(alias = "hwloc_bitmap_next_unset")]
    pub fn iter_unset(&self) -> BitmapIterator<&Bitmap> {
        BitmapIterator::new(self, Bitmap::next_unset)
    }

    /// Check the last unset index, if any
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let last_unset_usize = |b: Bitmap| b.last_unset().map(usize::from);
    /// assert_eq!(Bitmap::new().last_unset(), None);
    /// assert_eq!(last_unset_usize(Bitmap::from_range(12..)), Some(11));
    /// assert_eq!(Bitmap::full().last_unset(), None);
    /// ```
    #[doc(alias = "hwloc_bitmap_last_unset")]
    pub fn last_unset(&self) -> Option<BitmapIndex> {
        let result = unsafe { ffi::hwloc_bitmap_last_unset(self.as_ptr()) };
        assert!(
            result >= -1,
            "hwloc_bitmap_last_unset returned error code {result}"
        );
        BitmapIndex::try_from_c_int(result).ok()
    }

    /// Inverts the current `Bitmap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(12..=34);
    /// bitmap.invert();
    /// assert_eq!(format!("{bitmap}"), "0-11,35-");
    /// ```
    pub fn invert(&mut self) {
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
    /// use hwlocality::bitmaps::Bitmap;
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
        errors::call_hwloc_bool("hwloc_bitmap_intersects", || unsafe {
            ffi::hwloc_bitmap_intersects(self.as_ptr(), rhs.as_ptr())
        })
        .expect("Should not involve faillible syscalls")
    }

    /// Truth that the indices set in `inner` are a subset of those set in `self`.
    ///
    /// The empty bitmap is considered included in any other bitmap.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let bitmap1 = Bitmap::from_range(12..=78);
    /// let bitmap2 = Bitmap::from_range(34..=56);
    /// assert!(bitmap1.includes(&bitmap2));
    /// assert!(!bitmap2.includes(&bitmap1));
    /// ```
    #[doc(alias = "hwloc_bitmap_isincluded")]
    pub fn includes(&self, inner: &Self) -> bool {
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
                Bound::Excluded(i) => start_idx(*i).checked_succ()?,
            };
            let end_idx = |idx| convert_idx(idx).expect("Range end is too high for hwloc");
            let end = match range.end_bound() {
                Bound::Unbounded => -1,
                Bound::Included(i) => end_idx(*i).into_c_int(),
                Bound::Excluded(i) => end_idx(*i).checked_pred()?.into_c_int(),
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
        let result = next_fn(
            self.as_ptr(),
            index.map(BitmapIndex::into_c_int).unwrap_or(-1),
        );
        assert!(
            result >= -1,
            "hwloc bitmap iterator returned error code {result}"
        );
        BitmapIndex::try_from_c_int(result).ok()
    }

    /// Set index iterator building block
    fn next_set(&self, index: Option<BitmapIndex>) -> Option<BitmapIndex> {
        self.next(index, |bitmap, prev| unsafe {
            ffi::hwloc_bitmap_next(bitmap, prev)
        })
    }

    /// Unset index iterator building block
    fn next_unset(&self, index: Option<BitmapIndex>) -> Option<BitmapIndex> {
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

impl BitAnd<&Bitmap> for &Bitmap {
    type Output = Bitmap;

    #[doc(alias = "hwloc_bitmap_and")]
    fn bitand(self, rhs: &Bitmap) -> Bitmap {
        let mut result = Bitmap::new();
        errors::call_hwloc_int_normal("hwloc_bitmap_and", || unsafe {
            ffi::hwloc_bitmap_and(result.as_mut_ptr(), self.as_ptr(), rhs.as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
        result
    }
}

impl BitAnd<Bitmap> for &Bitmap {
    type Output = Bitmap;

    fn bitand(self, mut rhs: Bitmap) -> Bitmap {
        rhs &= self;
        rhs
    }
}

impl BitAnd<&Bitmap> for Bitmap {
    type Output = Bitmap;

    fn bitand(mut self, rhs: &Bitmap) -> Bitmap {
        self &= rhs;
        self
    }
}

impl BitAnd<Bitmap> for Bitmap {
    type Output = Bitmap;

    fn bitand(self, rhs: Bitmap) -> Bitmap {
        self & &rhs
    }
}

impl BitAndAssign<&Bitmap> for Bitmap {
    fn bitand_assign(&mut self, rhs: &Bitmap) {
        errors::call_hwloc_int_normal("hwloc_bitmap_and", || unsafe {
            ffi::hwloc_bitmap_and(self.as_mut_ptr(), self.as_ptr(), rhs.as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
    }
}

impl BitAndAssign<Bitmap> for Bitmap {
    fn bitand_assign(&mut self, rhs: Bitmap) {
        *self &= &rhs
    }
}

impl BitOr<&Bitmap> for &Bitmap {
    type Output = Bitmap;

    #[doc(alias = "hwloc_bitmap_or")]
    fn bitor(self, rhs: &Bitmap) -> Bitmap {
        let mut result = Bitmap::new();
        errors::call_hwloc_int_normal("hwloc_bitmap_or", || unsafe {
            ffi::hwloc_bitmap_or(result.as_mut_ptr(), self.as_ptr(), rhs.as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
        result
    }
}

impl BitOr<Bitmap> for &Bitmap {
    type Output = Bitmap;

    fn bitor(self, mut rhs: Bitmap) -> Bitmap {
        rhs |= self;
        rhs
    }
}

impl BitOr<&Bitmap> for Bitmap {
    type Output = Bitmap;

    fn bitor(mut self, rhs: &Bitmap) -> Bitmap {
        self |= rhs;
        self
    }
}

impl BitOr<Bitmap> for Bitmap {
    type Output = Bitmap;

    fn bitor(self, rhs: Bitmap) -> Bitmap {
        self | &rhs
    }
}

impl BitOrAssign<&Bitmap> for Bitmap {
    fn bitor_assign(&mut self, rhs: &Bitmap) {
        errors::call_hwloc_int_normal("hwloc_bitmap_or", || unsafe {
            ffi::hwloc_bitmap_or(self.as_mut_ptr(), self.as_ptr(), rhs.as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
    }
}

impl BitOrAssign<Bitmap> for Bitmap {
    fn bitor_assign(&mut self, rhs: Bitmap) {
        *self |= &rhs
    }
}

impl BitXor<&Bitmap> for &Bitmap {
    type Output = Bitmap;

    #[doc(alias = "hwloc_bitmap_xor")]
    fn bitxor(self, rhs: &Bitmap) -> Bitmap {
        let mut result = Bitmap::new();
        errors::call_hwloc_int_normal("hwloc_bitmap_xor", || unsafe {
            ffi::hwloc_bitmap_xor(result.as_mut_ptr(), self.as_ptr(), rhs.as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
        result
    }
}

impl BitXor<Bitmap> for &Bitmap {
    type Output = Bitmap;

    fn bitxor(self, mut rhs: Bitmap) -> Bitmap {
        rhs ^= self;
        rhs
    }
}

impl BitXor<&Bitmap> for Bitmap {
    type Output = Bitmap;

    fn bitxor(mut self, rhs: &Bitmap) -> Bitmap {
        self ^= rhs;
        self
    }
}

impl BitXor<Bitmap> for Bitmap {
    type Output = Bitmap;

    fn bitxor(self, rhs: Bitmap) -> Bitmap {
        self ^ &rhs
    }
}

impl BitXorAssign<&Bitmap> for Bitmap {
    fn bitxor_assign(&mut self, rhs: &Bitmap) {
        errors::call_hwloc_int_normal("hwloc_bitmap_xor", || unsafe {
            ffi::hwloc_bitmap_xor(self.as_mut_ptr(), self.as_ptr(), rhs.as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
    }
}

impl BitXorAssign<Bitmap> for Bitmap {
    fn bitxor_assign(&mut self, rhs: Bitmap) {
        *self ^= &rhs
    }
}

impl Clone for Bitmap {
    #[doc(alias = "hwloc_bitmap_dup")]
    fn clone(&self) -> Bitmap {
        unsafe {
            let ptr = errors::call_hwloc_ptr_mut("hwloc_bitmap_dup", || {
                ffi::hwloc_bitmap_dup(self.as_ptr())
            })
            .expect("Bitmap operation failures are handled via panics");
            Self::from_non_null(ptr)
        }
    }
}

impl Debug for Bitmap {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        ffi::write_snprintf(f, |buf, len| unsafe {
            ffi::hwloc_bitmap_list_snprintf(buf, len, self.as_ptr())
        })
    }
}

impl Drop for Bitmap {
    #[doc(alias = "hwloc_bitmap_free")]
    fn drop(&mut self) {
        unsafe { ffi::hwloc_bitmap_free(self.as_mut_ptr()) }
    }
}

impl Eq for Bitmap {}

impl Extend<BitmapIndex> for Bitmap {
    fn extend<T: IntoIterator<Item = BitmapIndex>>(&mut self, iter: T) {
        for i in iter {
            self.set(i);
        }
    }
}

impl<'a> Extend<&'a BitmapIndex> for Bitmap {
    fn extend<T: IntoIterator<Item = &'a BitmapIndex>>(&mut self, iter: T) {
        self.extend(iter.into_iter().copied())
    }
}

impl From<BitmapIndex> for Bitmap {
    fn from(value: BitmapIndex) -> Self {
        let mut bitmap = Self::new();
        bitmap.set(value);
        bitmap
    }
}

impl From<&BitmapIndex> for Bitmap {
    fn from(value: &BitmapIndex) -> Self {
        Self::from(*value)
    }
}

impl FromIterator<BitmapIndex> for Bitmap {
    fn from_iter<I: IntoIterator<Item = BitmapIndex>>(iter: I) -> Self {
        let mut bitmap = Self::new();
        bitmap.extend(iter);
        bitmap
    }
}

impl<'a> FromIterator<&'a BitmapIndex> for Bitmap {
    fn from_iter<I: IntoIterator<Item = &'a BitmapIndex>>(iter: I) -> Self {
        Self::from_iter(iter.into_iter().copied())
    }
}

/// Iterator over set or unset [`Bitmap`] indices
#[derive(Copy, Clone)]
pub struct BitmapIterator<B> {
    /// Bitmap over which we're iterating
    bitmap: B,

    /// Last explored index
    prev: Option<BitmapIndex>,

    /// Mapping from last index to next index
    next: fn(&Bitmap, Option<BitmapIndex>) -> Option<BitmapIndex>,
}
//
impl<B: Borrow<Bitmap>> BitmapIterator<B> {
    fn new(bitmap: B, next: fn(&Bitmap, Option<BitmapIndex>) -> Option<BitmapIndex>) -> Self {
        Self {
            bitmap,
            prev: None,
            next,
        }
    }
}
//
impl<B: Borrow<Bitmap>> Iterator for BitmapIterator<B> {
    type Item = BitmapIndex;

    fn next(&mut self) -> Option<BitmapIndex> {
        self.prev = (self.next)(self.bitmap.borrow(), self.prev);
        self.prev
    }
}
//
impl<B: Borrow<Bitmap>> FusedIterator for BitmapIterator<B> {}
//
impl<'bitmap> IntoIterator for &'bitmap Bitmap {
    type Item = BitmapIndex;
    type IntoIter = BitmapIterator<&'bitmap Bitmap>;

    fn into_iter(self) -> Self::IntoIter {
        BitmapIterator::new(self, Bitmap::next_set)
    }
}
//
impl IntoIterator for Bitmap {
    type Item = BitmapIndex;
    type IntoIter = BitmapIterator<Bitmap>;

    fn into_iter(self) -> Self::IntoIter {
        BitmapIterator::new(self, Bitmap::next_set)
    }
}

impl Not for &Bitmap {
    type Output = Bitmap;

    #[doc(alias = "hwloc_bitmap_not")]
    fn not(self) -> Bitmap {
        let mut result = Bitmap::new();
        errors::call_hwloc_int_normal("hwloc_bitmap_not", || unsafe {
            ffi::hwloc_bitmap_not(result.as_mut_ptr(), self.as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
        result
    }
}

impl Not for Bitmap {
    type Output = Bitmap;

    fn not(mut self) -> Self {
        self.invert();
        self
    }
}

impl Ord for Bitmap {
    #[doc(alias = "hwloc_bitmap_compare")]
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
    #[doc(alias = "hwloc_bitmap_isequal")]
    fn eq(&self, other: &Self) -> bool {
        errors::call_hwloc_bool("hwloc_bitmap_isequal", || unsafe {
            ffi::hwloc_bitmap_isequal(self.as_ptr(), other.as_ptr())
        })
        .expect("Should not involve faillible syscalls")
    }
}

impl PartialOrd for Bitmap {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Sub<&Bitmap> for &Bitmap {
    type Output = Bitmap;

    #[doc(alias = "hwloc_bitmap_andnot")]
    fn sub(self, rhs: &Bitmap) -> Bitmap {
        let mut result = Bitmap::new();
        errors::call_hwloc_int_normal("hwloc_bitmap_andnot", || unsafe {
            ffi::hwloc_bitmap_andnot(result.as_mut_ptr(), self.as_ptr(), rhs.as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
        result
    }
}

impl Sub<Bitmap> for &Bitmap {
    type Output = Bitmap;

    fn sub(self, mut rhs: Bitmap) -> Bitmap {
        rhs -= self;
        rhs
    }
}

impl Sub<&Bitmap> for Bitmap {
    type Output = Bitmap;

    fn sub(mut self, rhs: &Bitmap) -> Bitmap {
        self -= rhs;
        self
    }
}

impl Sub<Bitmap> for Bitmap {
    type Output = Bitmap;

    fn sub(self, rhs: Bitmap) -> Bitmap {
        self - &rhs
    }
}

impl SubAssign<&Bitmap> for Bitmap {
    fn sub_assign(&mut self, rhs: &Bitmap) {
        errors::call_hwloc_int_normal("hwloc_bitmap_andnot", || unsafe {
            ffi::hwloc_bitmap_andnot(self.as_mut_ptr(), self.as_ptr(), rhs.as_ptr())
        })
        .expect("Bitmap operation failures are handled via panics");
    }
}

impl SubAssign<Bitmap> for Bitmap {
    fn sub_assign(&mut self, rhs: Bitmap) {
        *self -= &rhs
    }
}

unsafe impl Send for Bitmap {}
unsafe impl Sync for Bitmap {}

/// Trait for manipulating specialized bitmaps (CpuSet, NodeSet) in a homogeneous way
pub trait SpecializedBitmap:
    AsRef<Bitmap> + AsMut<Bitmap> + Clone + Debug + Display + From<Bitmap> + Into<Bitmap> + 'static
{
    /// What kind of bitmap is this?
    const BITMAP_KIND: BitmapKind;

    /// Convert a reference to bitmap to a reference to this
    //
    // FIXME: Adding a `where Bitmap: AsRef<Self>` bound on the trait should
    //        suffice, but for some unknown reason rustc v1.67.1 rejects this
    //        claiming the trait isn't implemented.
    #[doc(hidden)]
    fn from_bitmap_ref(bitmap: &Bitmap) -> &Self;
}

/// Kind of specialized bitmap
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum BitmapKind {
    /// [`CpuSet`]
    CpuSet,

    /// [`NodeSet`]
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
            derive_more::BitAnd,
            derive_more::BitAndAssign,
            derive_more::BitOr,
            derive_more::BitOrAssign,
            derive_more::BitXor,
            derive_more::BitXorAssign,
            Clone,
            Default,
            Eq,
            derive_more::From,
            derive_more::Into,
            derive_more::IntoIterator,
            derive_more::Not,
            Ord,
            PartialEq,
            PartialOrd,
            derive_more::Sub,
            derive_more::SubAssign,
        )]
        #[repr(transparent)]
        pub struct $newtype($crate::bitmaps::Bitmap);

        impl AsRef<$newtype> for $crate::bitmaps::Bitmap {
            fn as_ref(&self) -> &$newtype {
                // Safe because $newtype is repr(transparent)
                unsafe { std::mem::transmute(self) }
            }
        }

        impl $crate::bitmaps::SpecializedBitmap for $newtype {
            const BITMAP_KIND: $crate::bitmaps::BitmapKind =
                $crate::bitmaps::BitmapKind::$newtype;

            fn from_bitmap_ref(bitmap: &$crate::bitmaps::Bitmap) -> &Self {
                bitmap.as_ref()
            }
        }

        /// # Re-export of the Bitmap API
        ///
        /// Only documentation headers are repeated here, you will find most of
        /// the documentation attached to identically named `Bitmap` methods.
        impl $newtype {
            /// Wraps an owned bitmap from hwloc
            ///
            /// See [`Bitmap::from_raw`](crate::bitmaps::Bitmap::from_raw).
            #[allow(unused)]
            pub(crate) unsafe fn from_raw(
                bitmap: *mut $crate::bitmaps::RawBitmap
            ) -> Option<Self> {
                $crate::bitmaps::Bitmap::from_raw(bitmap).map(Self::from)
            }

            /// Wraps an owned bitmap from hwloc
            ///
            /// See [`Bitmap::from_non_null`](crate::bitmaps::Bitmap::from_non_null).
            #[allow(unused)]
            pub(crate) unsafe fn from_non_null(
                bitmap: std::ptr::NonNull<$crate::bitmaps::RawBitmap>
            ) -> Self {
                Self::from($crate::bitmaps::Bitmap::from_non_null(bitmap))
            }

            /// Wraps an hwloc-originated borrowed bitmap pointer into the bitmap representation.
            ///
            /// See [`Bitmap::borrow_from_raw`](crate::bitmaps::Bitmap::borrow_from_raw).
            #[allow(unused)]
            pub(crate) unsafe fn borrow_from_raw(
                bitmap: &*const $crate::bitmaps::RawBitmap
            ) -> Option<&Self> {
                $crate::bitmaps::Bitmap::borrow_from_raw(bitmap)
                    .map($crate::bitmaps::Bitmap::as_ref)
            }

            /// Wraps an hwloc-originated borrowed bitmap pointer into the bitmap representation.
            ///
            /// See [`Bitmap::borrow_from_raw_mut`](crate::bitmaps::Bitmap::borrow_from_raw_mut).
            #[allow(unused)]
            pub(crate) unsafe fn borrow_from_raw_mut(
                bitmap: &*mut $crate::bitmaps::RawBitmap
            ) -> Option<&Self> {
                $crate::bitmaps::Bitmap::borrow_from_raw_mut(bitmap)
                    .map($crate::bitmaps::Bitmap::as_ref)
            }

            /// Wraps an hwloc-originated borrowed bitmap pointer into the bitmap representation.
            ///
            /// See [`Bitmap::borrow_from_non_null`](crate::bitmaps::Bitmap::borrow_from_non_null).
            #[allow(unused)]
            pub(crate) unsafe fn borrow_from_non_null(
                bitmap: &std::ptr::NonNull<$crate::bitmaps::RawBitmap>
            ) -> &Self {
                <$crate::bitmaps::Bitmap as AsRef<Self>>::as_ref(
                    $crate::bitmaps::Bitmap::borrow_from_non_null(bitmap)
                )
            }

            /// Contained bitmap pointer (for interaction with hwloc)
            ///
            /// See [`Bitmap::as_ptr`](crate::bitmaps::Bitmap::as_ptr).
            #[allow(unused)]
            pub(crate) fn as_ptr(&self) -> *const $crate::bitmaps::RawBitmap {
                self.0.as_ptr()
            }

            /// Contained mutable bitmap pointer (for interaction with hwloc)
            ///
            /// See [`Bitmap::as_mut_ptr`](crate::bitmaps::Bitmap::as_mut_ptr).
            #[allow(unused)]
            pub(crate) fn as_mut_ptr(&mut self) -> *mut $crate::bitmaps::RawBitmap {
                self.0.as_mut_ptr()
            }

            /// Create an empty bitmap
            ///
            /// See [`Bitmap::new`](crate::bitmaps::Bitmap::new).
            pub fn new() -> Self {
                Self::from($crate::bitmaps::Bitmap::new())
            }

            /// Create a full bitmap
            ///
            /// See [`Bitmap::full`](crate::bitmaps::Bitmap::full).
            pub fn full() -> Self {
                Self::from($crate::bitmaps::Bitmap::full())
            }

            /// Creates a new bitmap with the given range of indices set
            ///
            /// See [`Bitmap::from_range`](crate::bitmaps::Bitmap::from_range).
            pub fn from_range<Idx>(range: impl std::ops::RangeBounds<Idx>) -> Self
            where
                Idx: Copy + PartialEq + TryInto<$crate::bitmaps::BitmapIndex>,
                <Idx as TryInto<$crate::bitmaps::BitmapIndex>>::Error: std::fmt::Debug,
            {
                Self::from($crate::bitmaps::Bitmap::from_range(range))
            }

            /// Turn this bitmap into a copy of another bitmap
            ///
            /// See [`Bitmap::copy_from`](crate::bitmaps::Bitmap::copy_from).
            pub fn copy_from(&mut self, other: &Self) {
                self.0.copy_from(&other.0)
            }

            /// Clear all indices
            ///
            /// See [`Bitmap::clear`](crate::bitmaps::Bitmap::clear).
            pub fn clear(&mut self) {
                self.0.clear()
            }

            /// Set all indices
            ///
            /// See [`Bitmap::fill`](crate::bitmaps::Bitmap::fill).
            pub fn fill(&mut self) {
                self.0.fill()
            }

            /// Clear all indices except for `idx`, which is set
            ///
            /// See [`Bitmap::set_only`](crate::bitmaps::Bitmap::set_only).
            pub fn set_only<Idx>(&mut self, idx: Idx)
            where
                Idx: TryInto<$crate::bitmaps::BitmapIndex>,
                <Idx as TryInto<$crate::bitmaps::BitmapIndex>>::Error: std::fmt::Debug,
            {
                self.0.set_only(idx)
            }

            /// Set all indices except for `idx`, which is cleared
            ///
            /// See [`Bitmap::set_all_but`](crate::bitmaps::Bitmap::set_all_but).
            pub fn set_all_but<Idx>(&mut self, idx: Idx)
            where
                Idx: TryInto<$crate::bitmaps::BitmapIndex>,
                <Idx as TryInto<$crate::bitmaps::BitmapIndex>>::Error: std::fmt::Debug,
            {
                self.0.set_all_but(idx)
            }

            /// Set index `idx`
            ///
            /// See [`Bitmap::set`](crate::bitmaps::Bitmap::set).
            pub fn set<Idx>(&mut self, idx: Idx)
            where
                Idx: TryInto<$crate::bitmaps::BitmapIndex>,
                <Idx as TryInto<$crate::bitmaps::BitmapIndex>>::Error: std::fmt::Debug,
            {
                self.0.set(idx)
            }

            /// Set indices covered by `range`
            ///
            /// See [`Bitmap::set_range`](crate::bitmaps::Bitmap::set_range).
            pub fn set_range<Idx>(&mut self, range: impl std::ops::RangeBounds<Idx>)
            where
                Idx: Copy + PartialEq + TryInto<$crate::bitmaps::BitmapIndex>,
                <Idx as TryInto<$crate::bitmaps::BitmapIndex>>::Error: std::fmt::Debug,
            {
                self.0.set_range(range)
            }

            /// Clear index `idx`
            ///
            /// See [`Bitmap::unset`](crate::bitmaps::Bitmap::unset).
            pub fn unset<Idx>(&mut self, idx: Idx)
            where
                Idx: TryInto<$crate::bitmaps::BitmapIndex>,
                <Idx as TryInto<$crate::bitmaps::BitmapIndex>>::Error: std::fmt::Debug,
            {
                self.0.unset(idx)
            }

            /// Clear indices covered by `range`
            ///
            /// See [`Bitmap::unset_range`](crate::bitmaps::Bitmap::unset_range).
            pub fn unset_range<Idx>(&mut self, range: impl std::ops::RangeBounds<Idx>)
            where
                Idx: Copy + PartialEq + TryInto<$crate::bitmaps::BitmapIndex>,
                <Idx as TryInto<$crate::bitmaps::BitmapIndex>>::Error: std::fmt::Debug,
            {
                self.0.unset_range(range)
            }

            /// Keep a single index among those set in the bitmap
            ///
            /// See [`Bitmap::singlify`](crate::bitmaps::Bitmap::singlify).
            pub fn singlify(&mut self) {
                self.0.singlify()
            }

            /// Check if index `idx` is set
            ///
            /// See [`Bitmap::is_set`](crate::bitmaps::Bitmap::is_set).
            pub fn is_set<Idx>(&self, idx: Idx) -> bool
            where
                Idx: TryInto<$crate::bitmaps::BitmapIndex>,
                <Idx as TryInto<$crate::bitmaps::BitmapIndex>>::Error: std::fmt::Debug,
            {
                self.0.is_set(idx)
            }

            /// Check if all indices are unset
            ///
            /// See [`Bitmap::is_empty`](crate::bitmaps::Bitmap::is_empty).
            pub fn is_empty(&self) -> bool {
                self.0.is_empty()
            }

            /// Check if all indices are set
            ///
            /// See [`Bitmap::is_full`](crate::bitmaps::Bitmap::is_full).
            pub fn is_full(&self) -> bool {
                self.0.is_full()
            }

            /// Check the first set index, if any
            ///
            /// See [`Bitmap::first_set`](crate::bitmaps::Bitmap::first_set).
            pub fn first_set(&self) -> Option<$crate::bitmaps::BitmapIndex> {
                self.0.first_set()
            }

            /// Iterate over set indices
            ///
            /// See [`Bitmap::iter_set`](crate::bitmaps::Bitmap::iter_set).
            pub fn iter_set(
                &self
            ) -> $crate::bitmaps::BitmapIterator<&$crate::bitmaps::Bitmap> {
                self.0.iter_set()
            }

            /// Check the last set index, if any
            ///
            /// See [`Bitmap::last_set`](crate::bitmaps::Bitmap::last_set).
            pub fn last_set(&self) -> Option<$crate::bitmaps::BitmapIndex> {
                self.0.last_set()
            }

            /// The number of indices that are set in the bitmap.
            ///
            /// See [`Bitmap::weight`](crate::bitmaps::Bitmap::weight).
            pub fn weight(&self) -> Option<usize> {
                self.0.weight()
            }

            /// Check the first unset index, if any
            ///
            /// See [`Bitmap::first_unset`](crate::bitmaps::Bitmap::first_unset).
            pub fn first_unset(&self) -> Option<$crate::bitmaps::BitmapIndex> {
                self.0.first_unset()
            }

            /// Iterate over unset indices
            ///
            /// See [`Bitmap::iter_unset`](crate::bitmaps::Bitmap::iter_unset).
            pub fn iter_unset(
                &self
            ) -> $crate::bitmaps::BitmapIterator<&$crate::bitmaps::Bitmap> {
                self.0.iter_unset()
            }

            /// Check the last unset index, if any
            ///
            /// See [`Bitmap::last_unset`](crate::bitmaps::Bitmap::last_unset).
            pub fn last_unset(&self) -> Option<$crate::bitmaps::BitmapIndex> {
                self.0.last_unset()
            }

            /// Inverts the current `Bitmap`.
            ///
            /// See [`Bitmap::invert`](crate::bitmaps::Bitmap::invert).
            pub fn invert(&mut self) {
                self.0.invert()
            }

            /// Truth that `self` and `rhs` have some set indices in common
            ///
            /// See [`Bitmap::intersects`](crate::bitmaps::Bitmap::intersects).
            pub fn intersects(&self, rhs: &Self) -> bool {
                self.0.intersects(&rhs.0)
            }

            /// Truth that the indices set in `inner` are a subset of those set in `self`
            ///
            /// See [`Bitmap::includes`](crate::bitmaps::Bitmap::includes).
            pub fn includes(&self, inner: &Self) -> bool {
                self.0.includes(&inner.0)
            }
        }

        impl std::ops::BitAnd<&$newtype> for &$newtype {
            type Output = $newtype;

            fn bitand(self, rhs: &$newtype) -> $newtype {
                $newtype((&self.0) & (&rhs.0))
            }
        }

        impl std::ops::BitAnd<$newtype> for &$newtype {
            type Output = $newtype;

            fn bitand(self, rhs: $newtype) -> $newtype {
                $newtype((&self.0) & rhs.0)
            }
        }

        impl std::ops::BitAnd<&$newtype> for $newtype {
            type Output = $newtype;

            fn bitand(self, rhs: &$newtype) -> $newtype {
                $newtype(self.0 & (&rhs.0))
            }
        }

        impl std::ops::BitAndAssign<&$newtype> for $newtype {
            fn bitand_assign(&mut self, rhs: &$newtype) {
                self.0 &= (&rhs.0)
            }
        }

        impl std::ops::BitOr<&$newtype> for &$newtype {
            type Output = $newtype;

            fn bitor(self, rhs: &$newtype) -> $newtype {
                $newtype(&self.0 | &rhs.0)
            }
        }

        impl std::ops::BitOr<$newtype> for &$newtype {
            type Output = $newtype;

            fn bitor(self, rhs: $newtype) -> $newtype {
                $newtype(&self.0 | rhs.0)
            }
        }

        impl std::ops::BitOr<&$newtype> for $newtype {
            type Output = $newtype;

            fn bitor(self, rhs: &$newtype) -> $newtype {
                $newtype(self.0 | &rhs.0)
            }
        }

        impl std::ops::BitOrAssign<&$newtype> for $newtype {
            fn bitor_assign(&mut self, rhs: &$newtype) {
                self.0 |= &rhs.0
            }
        }

        impl std::ops::BitXor<&$newtype> for &$newtype {
            type Output = $newtype;

            fn bitxor(self, rhs: &$newtype) -> $newtype {
                $newtype(&self.0 ^ &rhs.0)
            }
        }

        impl std::ops::BitXor<$newtype> for &$newtype {
            type Output = $newtype;

            fn bitxor(self, rhs: $newtype) -> $newtype {
                $newtype(&self.0 ^ rhs.0)
            }
        }

        impl std::ops::BitXor<&$newtype> for $newtype {
            type Output = $newtype;

            fn bitxor(self, rhs: &$newtype) -> $newtype {
                $newtype(self.0 ^ &rhs.0)
            }
        }

        impl std::ops::BitXorAssign<&$newtype> for $newtype {
            fn bitxor_assign(&mut self, rhs: &$newtype) {
                self.0 ^= &rhs.0
            }
        }

        impl std::fmt::Debug for $newtype {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "{}({:?})", stringify!($newtype), &self.0)
            }
        }

        impl std::fmt::Display for $newtype {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "{}({})", stringify!($newtype), &self.0)
            }
        }

        impl Extend<$crate::bitmaps::BitmapIndex> for $newtype {
            fn extend<T: IntoIterator<Item = $crate::bitmaps::BitmapIndex>>(&mut self, iter: T) {
                self.0.extend(iter)
            }
        }

        impl<'a> Extend<&'a $crate::bitmaps::BitmapIndex> for $newtype {
            fn extend<T: IntoIterator<Item = &'a $crate::bitmaps::BitmapIndex>>(&mut self, iter: T) {
                self.0.extend(iter)
            }
        }

        impl From<$crate::bitmaps::BitmapIndex> for $newtype {
            fn from(value: $crate::bitmaps::BitmapIndex) -> Self {
                Self(value.into())
            }
        }

        impl From<&$crate::bitmaps::BitmapIndex> for $newtype {
            fn from(value: &$crate::bitmaps::BitmapIndex) -> Self {
                Self(value.into())
            }
        }

        impl FromIterator<$crate::bitmaps::BitmapIndex> for $newtype {
            fn from_iter<I: IntoIterator<Item = $crate::bitmaps::BitmapIndex>>(iter: I) -> Self {
                Self($crate::bitmaps::Bitmap::from_iter(iter))
            }
        }

        impl<'a> FromIterator<&'a $crate::bitmaps::BitmapIndex> for $newtype {
            fn from_iter<I: IntoIterator<Item = &'a $crate::bitmaps::BitmapIndex>>(iter: I) -> Self {
                Self($crate::bitmaps::Bitmap::from_iter(iter))
            }
        }

        impl<'newtype> IntoIterator for &'newtype $newtype {
            type Item = $crate::bitmaps::BitmapIndex;
            type IntoIter = $crate::bitmaps::BitmapIterator<&'newtype $crate::bitmaps::Bitmap>;

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

        impl std::ops::Sub<&$newtype> for &$newtype {
            type Output = $newtype;

            fn sub(self, rhs: &$newtype) -> $newtype {
                $newtype(&self.0 - &rhs.0)
            }
        }

        impl std::ops::Sub<$newtype> for &$newtype {
            type Output = $newtype;

            fn sub(self, rhs: $newtype) -> $newtype {
                $newtype(&self.0 - rhs.0)
            }
        }

        impl std::ops::Sub<&$newtype> for $newtype {
            type Output = $newtype;

            fn sub(self, rhs: &$newtype) -> $newtype {
                $newtype(self.0 - &rhs.0)
            }
        }

        impl std::ops::SubAssign<&$newtype> for $newtype {
            fn sub_assign(&mut self, rhs: &$newtype) {
                self.0 -= &rhs.0
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
        ops::{Range, RangeFrom, RangeInclusive},
    };

    // Unfortunately, ranges of BitmapIndex cannot do everything that ranges of
    // built-in integer types can do due to some unstable integer traits, so
    // it's sometimes good to go back to usize.
    fn range_inclusive_to_usize(range: &RangeInclusive<BitmapIndex>) -> RangeInclusive<usize> {
        usize::from(*range.start())..=usize::from(*range.end())
    }

    // Split a possibly infinite bitmap into a finite bitmap and an infinite
    // range of set indices. To get the original bitmap back, use `set_range`.
    fn split_infinite_bitmap(mut bitmap: Bitmap) -> (Bitmap, Option<RangeFrom<BitmapIndex>>) {
        // If this bitmap is infinite...
        if bitmap.weight().is_none() {
            // ...and it has a finite part...
            if let Some(last_unset) = bitmap.last_unset() {
                let infinite_part = last_unset.checked_succ().unwrap()..;
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

    fn test_indexing(initial: &Bitmap, index: BitmapIndex, set: bool) {
        let single = Bitmap::from(index);
        let single_hole = !&single;

        // Bitmaps are conceptually infinite so we must be careful with
        // iteration-based verification of full bitmap contents. Let's just
        // account for off-by-one-word errors.
        let max_iters = initial
            .weight()
            .unwrap_or(usize::from(index) + std::mem::size_of::<c_ulonglong>() * 8);

        assert_eq!(initial.is_set(index), set);

        let mut buf = initial.clone();
        buf.set(index);
        assert_eq!(buf.weight(), initial.weight().map(|w| w + !set as usize));
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
        assert_eq!(buf.weight(), initial.weight().map(|w| w - set as usize));
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
            assert_eq!(empty.iter_unset().next(), empty.first_unset());
            assert_eq!(empty.last_set(), None);
            assert_eq!(empty.last_unset(), None);
            assert_eq!(empty.weight(), Some(0));

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
            assert_eq!(full.into_iter().next(), full.first_set());
            assert_eq!(full.iter_set().next(), full.first_set());
            assert_eq!(full.iter_unset().count(), 0);
            assert_eq!(full.last_set(), None);
            assert_eq!(full.last_unset(), None);
            assert_eq!(full.weight(), None);

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
            elems.last().copied().and_then(BitmapIndex::checked_succ)
        } else {
            Some(BitmapIndex::MIN)
        };
        let unset_after_set = if let Some(last_set) = elems.last() {
            last_set.checked_succ()
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
            if let Some(after_last) = last.checked_succ() {
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
            assert_eq!(unset.next(), unset_after_set);

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
                    assert!(other.last_set().unwrap_or(BitmapIndex::MAX) > *range.end())
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
        ranged_or_other.set_range(range.clone());
        assert_eq!(&ranged_bitmap | &other, ranged_or_other);
        let mut buf = ranged_bitmap.clone();
        buf |= &other;
        assert_eq!(buf, ranged_or_other);

        let mut ranged_xor_other = ranged_bitmap.clone();
        for idx in other_finite {
            if ranged_xor_other.is_set(idx) {
                ranged_xor_other.unset(idx);
            } else {
                ranged_xor_other.set(idx);
            }
        }
        if let Some(infinite) = other_infinite {
            ranged_xor_other.set_range(infinite.start..);
            if !ranged_bitmap.is_empty() {
                ranged_xor_other.unset_range(infinite.start.max(*range.start())..=*range.end());
            }
        }
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

    // TODO: Add tests that check properties that should be true of any bitmap,
    //       based on the above but sticking to generalities (e.g. we cannot
    //       tell anything about is_set() for an arbitrary bitmap, but we can
    //       relate first_set() to iter_set(), and we know that if we unset()
    //       an index then it should not be set afterwards and vice versa if we
    //       set() an index)
}
