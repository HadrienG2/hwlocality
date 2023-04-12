//! Bitmap API

// Main docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__bitmap.html

#[cfg(doc)]
use crate::{builder::BuildFlags, support::DiscoverySupport};
use crate::{
    depth::Depth,
    errors::{self, RawHwlocError},
    ffi::{self, IncompleteType},
    objects::{types::ObjectType, TopologyObject},
    RawTopology, Topology,
};
use derive_more::*;
use std::{
    borrow::Borrow,
    clone::Clone,
    cmp::Ordering,
    convert::TryFrom,
    ffi::c_int,
    fmt::{self, Debug, Display},
    iter::{FromIterator, FusedIterator},
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Bound, Not, RangeBounds,
    },
    ptr::{self, NonNull},
};

/// # Finding objects inside a CPU set
//
// This is inspired by the upstream functionality described at
// https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__find__inside.html
// but the code had to be ported to Rust as most C code is inline and thus
// cannot be called from Rust, and the only function that's not inline does not
// fit Rust's design (assumes caller has allocated large enough storage with no
// way to tell what is large enough)
impl Topology {
    /// Enumerate the largest objects included in the given cpuset `set`
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set).
    ///
    /// In the common case where `set` is a subset of the root cpuset, this
    /// operation can be more efficiently performed by using
    /// `coarsest_cpuset_partition()`.
    #[doc(alias = "hwloc_get_first_largest_obj_inside_cpuset")]
    pub fn largest_objects_inside_cpuset(
        &self,
        set: CpuSet,
    ) -> impl Iterator<Item = &TopologyObject> + FusedIterator {
        LargestObjectsInsideCpuSet {
            topology: self,
            set,
        }
    }

    /// Get the largest objects exactly covering the given cpuset `set`
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set).
    ///
    /// # Panics
    ///
    /// If the requested cpuset is not a subset of the root cpuset, we can't
    /// find children covering the indices outside of the root cpuset
    #[doc(alias = "hwloc_get_largest_objs_inside_cpuset")]
    pub fn coarsest_cpuset_partition(&self, set: &CpuSet) -> Vec<&TopologyObject> {
        // Make sure each set index actually maps into a hardware PU
        let root = self.root_object();
        assert!(
            set.includes(root.cpuset().expect("Root should have a CPU set")),
            "Requested set has indices outside the root cpuset"
        );

        // Start recursion
        let mut result = Vec::new();
        let mut cpusets = Vec::new();
        fn process_object<'a>(
            parent: &'a TopologyObject,
            set: &CpuSet,
            result: &mut Vec<&'a TopologyObject>,
            cpusets: &mut Vec<CpuSet>,
        ) {
            // If the current object does not have a cpuset, ignore it
            let Some(parent_cpuset) = parent.cpuset() else { return };

            // If it exactly covers the target cpuset, we're done
            if parent_cpuset == set {
                result.push(parent);
                return;
            }

            // Otherwise, look for children that cover the target cpuset
            let mut subset = cpusets.pop().unwrap_or_default();
            for child in parent.normal_children() {
                // Ignore children without a cpuset, or with a cpuset that
                // doesn't intersect the target cpuset
                let Some(child_cpuset) = child.cpuset() else { continue };
                if !child_cpuset.intersects(set) {
                    continue;
                }

                // Split out the cpuset part corresponding to this child and recurse
                subset.copy_from(set);
                subset &= child_cpuset;
                process_object(child, &subset, result, cpusets);
            }
            cpusets.push(subset);
        }
        process_object(root, set, &mut result, &mut cpusets);
        result
    }

    /// Enumerate objects included in the given cpuset `set` at a certain depth
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set). Therefore, an empty iterator will
    /// always be returned for I/O or Misc depths as those objects have no cpusets.
    #[doc(alias = "hwloc_get_obj_inside_cpuset_by_depth")]
    #[doc(alias = "hwloc_get_next_obj_inside_cpuset_by_depth")]
    #[doc(alias = "hwloc_get_nbobjs_inside_cpuset_by_depth")]
    pub fn objects_inside_cpuset_at_depth<'result>(
        &'result self,
        set: &'result CpuSet,
        depth: impl Into<Depth>,
    ) -> impl Iterator<Item = &TopologyObject> + Clone + DoubleEndedIterator + FusedIterator + 'result
    {
        let depth = depth.into();
        self.objects_at_depth(depth)
            .filter(|object| object.is_inside_cpuset(set))
    }

    /// Get objects included in the given cpuset `set` with a certain type
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set). Therefore, an empty Vec will
    /// always be returned for I/O or Misc objects as they don't have cpusets.
    #[doc(alias = "hwloc_get_obj_inside_cpuset_by_type")]
    #[doc(alias = "hwloc_get_next_obj_inside_cpuset_by_type")]
    #[doc(alias = "hwloc_get_nbobjs_inside_cpuset_by_type")]
    pub fn objects_inside_cpuset_with_type<'result>(
        &'result self,
        set: &'result CpuSet,
        object_type: ObjectType,
    ) -> impl Iterator<Item = &TopologyObject> + Clone + DoubleEndedIterator + FusedIterator + 'result
    {
        self.objects_with_type(object_type)
            .filter(|object| object.is_inside_cpuset(set))
    }

    /// Get the first largest object included in the given cpuset `set`
    ///
    /// Returns the first object that is included in `set` and whose parent is
    /// not, in descending depth and children iteration order.
    ///
    /// This is convenient for iterating over all largest objects within a CPU
    /// set by doing a loop getting the first largest object and clearing its
    /// CPU set from the remaining CPU set. This very pattern is exposed by
    /// the `largest_objects_inside_cpuset` method, which is why this method is
    /// not publicly exposed.
    ///
    /// That being said, if the cpuset is a strict subset of the root cpuset of
    /// this `Topology`, the work may be more efficiently done by
    /// `largest_cpuset_partition()`, which only needs to walk the topology
    /// tree once.
    ///
    /// Objects with empty CPU sets are ignored (otherwise they would be
    /// considered included in any given set).
    fn first_largest_object_inside_cpuset(&self, set: &CpuSet) -> Option<&TopologyObject> {
        // If root object doesn't intersect this CPU set then no child will
        let root = self.root_object();
        let root_cpuset = root.cpuset().expect("Root should have a CPU set");
        if !root_cpuset.intersects(set) {
            return None;
        }

        // Walk the topology tree until we find an object included into set
        let mut parent = root;
        let mut parent_cpuset = root_cpuset;
        while !set.includes(parent_cpuset) {
            // While the object intersects without being included, look at children
            let old_parent = parent;
            for child in parent.normal_children() {
                if let Some(child_cpuset) = child.cpuset() {
                    // This child intersects, make it the new parent and recurse
                    if set.intersects(child_cpuset) {
                        parent = child;
                        parent_cpuset = child_cpuset;
                    }
                }
            }
            assert!(
                !ptr::eq(parent, old_parent),
                "This should not happen because...\n\
                - The root intersects, so it has at least one index from the set\n\
                - The lowest-level children are PUs, which have only one index set,\
                  so one of them should pass the includes() test"
            );
        }
        Some(parent)
    }
}

/// Iterator over largest objects inside a cpuset
#[derive(Clone, Debug)]
struct LargestObjectsInsideCpuSet<'topology> {
    topology: &'topology Topology,
    set: CpuSet,
}
//
impl<'topology> Iterator for LargestObjectsInsideCpuSet<'topology> {
    type Item = &'topology TopologyObject;

    fn next(&mut self) -> Option<Self::Item> {
        let object = self
            .topology
            .first_largest_object_inside_cpuset(&self.set)?;
        let object_cpuset = object
            .cpuset()
            .expect("Output of first_largest_object_inside_cpuset should have a cpuset");
        self.set.and_not_assign(object_cpuset);
        Some(object)
    }
}
//
impl FusedIterator for LargestObjectsInsideCpuSet<'_> {}

/// # Finding objects covering at least a CPU set
//
// This is inspired by the upstream functionality described at
// https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__find__covering.html
// but the code had to be ported to Rust because it's inline
impl Topology {
    /// Get the lowest object covering at least the given cpuset `set`
    ///
    /// No object is considered to cover the empty cpuset, therefore such a
    /// request will always return None, as if a set going outside of the root
    /// cpuset were passed as input.
    #[doc(alias = "hwloc_get_obj_covering_cpuset")]
    pub fn smallest_object_covering_cpuset(&self, set: &CpuSet) -> Option<&TopologyObject> {
        let root = self.root_object();
        if !root.covers_cpuset(set) || set.is_empty() {
            return None;
        }
        let mut parent = root;
        while let Some(child) = parent.normal_child_covering_cpuset(set) {
            parent = child;
        }
        Some(parent)
    }

    /// Get the first data (or unified) cache covering the given cpuset
    #[doc(alias = "hwloc_get_cache_covering_cpuset")]
    pub fn first_cache_covering_cpuset(&self, set: &CpuSet) -> Option<&TopologyObject> {
        let first_obj = self.smallest_object_covering_cpuset(set)?;
        std::iter::once(first_obj)
            .chain(first_obj.ancestors())
            .find(|obj| obj.object_type().is_cpu_data_cache())
    }

    /// Enumerate objects covering the given cpuset `set` at a certain depth
    ///
    /// Objects are not considered to cover the empty CPU set (otherwise a list
    /// of all objects would be returned). Therefore, an empty iterator will
    /// always be returned for I/O or Misc depths as those objects have no cpusets.
    #[doc(alias = "hwloc_get_next_obj_covering_cpuset_by_depth")]
    pub fn objects_covering_cpuset_at_depth<'result>(
        &'result self,
        set: &'result CpuSet,
        depth: impl Into<Depth>,
    ) -> impl Iterator<Item = &TopologyObject> + Clone + DoubleEndedIterator + FusedIterator + 'result
    {
        let depth = depth.into();
        self.objects_at_depth(depth)
            .filter(|object| object.covers_cpuset(set))
    }

    /// Get objects covering the given cpuset `set` with a certain type
    ///
    /// Objects are not considered to cover the empty CPU set (otherwise a list
    /// of all objects would be returned). Therefore, an empty iterator will
    /// always be returned for I/O or Misc depths as those objects have no cpusets.
    #[doc(alias = "hwloc_get_next_obj_covering_cpuset_by_type")]
    pub fn objects_covering_cpuset_with_type<'result>(
        &'result self,
        set: &'result CpuSet,
        object_type: ObjectType,
    ) -> impl Iterator<Item = &TopologyObject> + Clone + DoubleEndedIterator + FusedIterator + 'result
    {
        self.objects_with_type(object_type)
            .filter(|object| object.covers_cpuset(set))
    }
}

/// # CPU and node sets of entire topologies
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__helper__topology__sets.html
impl Topology {
    /// Topology CPU set
    ///
    /// This is equivalent to calling [`TopologyObject::cpuset()`] on
    /// the topology's root object.
    #[doc(alias = "hwloc_topology_get_topology_cpuset")]
    pub fn cpuset(&self) -> Result<&CpuSet, RawHwlocError> {
        unsafe {
            self.topology_set(
                "hwloc_topology_get_topology_cpuset",
                ffi::hwloc_topology_get_topology_cpuset,
            )
        }
    }

    /// Complete CPU set
    ///
    /// This is equivalent to calling [`TopologyObject::complete_cpuset()`] on
    /// the topology's root object.
    #[doc(alias = "hwloc_topology_get_complete_cpuset")]
    pub fn complete_cpuset(&self) -> Result<&CpuSet, RawHwlocError> {
        unsafe {
            self.topology_set(
                "hwloc_topology_get_complete_cpuset",
                ffi::hwloc_topology_get_complete_cpuset,
            )
        }
    }

    /// Allowed CPU set
    ///
    /// If [`BuildFlags::INCLUDE_DISALLOWED`] was not set, this is identical to
    /// [`Topology::cpuset()`]: all visible PUs are allowed.
    ///
    /// Otherwise, you can check whether a particular cpuset contains allowed
    /// PUs by calling `cpuset.intersects(topology.allowed_cpuset())`, and if so
    /// you can get the set of allowed PUs with
    /// `cpuset & topology.allowed_cpuset()`.
    #[doc(alias = "hwloc_topology_get_allowed_cpuset")]
    pub fn allowed_cpuset(&self) -> Result<&CpuSet, RawHwlocError> {
        unsafe {
            self.topology_set(
                "hwloc_topology_get_allowed_cpuset",
                ffi::hwloc_topology_get_allowed_cpuset,
            )
        }
    }

    /// Topology node set
    ///
    /// This is equivalent to calling [`TopologyObject::nodeset()`] on
    /// the topology's root object.
    #[doc(alias = "hwloc_topology_get_topology_nodeset")]
    pub fn nodeset(&self) -> Result<&NodeSet, RawHwlocError> {
        unsafe {
            self.topology_set(
                "hwloc_topology_get_topology_nodeset",
                ffi::hwloc_topology_get_topology_nodeset,
            )
        }
    }

    /// Complete node set
    ///
    /// This is equivalent to calling [`TopologyObject::complete_nodeset()`] on
    /// the topology's root object.
    #[doc(alias = "hwloc_topology_get_complete_nodeset")]
    pub fn complete_nodeset(&self) -> Result<&NodeSet, RawHwlocError> {
        unsafe {
            self.topology_set(
                "hwloc_topology_get_complete_nodeset",
                ffi::hwloc_topology_get_complete_nodeset,
            )
        }
    }

    /// Allowed node set
    ///
    /// If [`BuildFlags::INCLUDE_DISALLOWED`] was not set, this is identical to
    /// [`Topology::nodeset()`]: all visible NUMA nodes are allowed.
    ///
    /// Otherwise, you can check whether a particular nodeset contains allowed
    /// NUMA nodes by calling `nodeset.intersects(topology.allowed_nodeset())`,
    /// and if so you can get the set of allowed NUMA nodes with
    /// `nodeset & topology.allowed_nodeset()`.
    #[doc(alias = "hwloc_topology_get_allowed_nodeset")]
    pub fn allowed_nodeset(&self) -> Result<&NodeSet, RawHwlocError> {
        unsafe {
            self.topology_set(
                "hwloc_topology_get_allowed_nodeset",
                ffi::hwloc_topology_get_allowed_nodeset,
            )
        }
    }

    /// Query a topology-wide `CpuSet` or `NodeSet`
    ///
    /// # Safety
    ///
    /// The `*const RawBitmap` returned by `getter` must originate from `self`.
    unsafe fn topology_set<'topology, Set: SpecializedBitmap>(
        &'topology self,
        getter_name: &'static str,
        getter: unsafe extern "C" fn(*const RawTopology) -> *const RawBitmap,
    ) -> Result<&Set, RawHwlocError> {
        Ok(Set::from_bitmap_ref(unsafe {
            let bitmap_ptr = errors::call_hwloc_ptr(getter_name, || getter(self.as_ptr()))?;
            let bitmap_ref = std::mem::transmute::<
                &NonNull<RawBitmap>,
                &'topology NonNull<RawBitmap>,
            >(&bitmap_ptr);
            Bitmap::borrow_from_non_null(bitmap_ref)
        }))
    }
}

/// Trait for manipulating specialized bitmaps in a homogeneous way
pub trait SpecializedBitmap:
    AsRef<Bitmap> + AsMut<Bitmap> + Clone + Display + From<Bitmap> + Into<Bitmap> + 'static
{
    /// What kind of bitmap is this?
    const BITMAP_KIND: BitmapKind;

    /// Convert a reference to bitmap to a reference to this
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
macro_rules! impl_bitmap_newtype {
    (
        $(#[$attr:meta])*
        $newtype:ident
    ) => {
        $(#[$attr])*
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
        pub struct $newtype(Bitmap);

        impl SpecializedBitmap for $newtype {
            const BITMAP_KIND: BitmapKind = BitmapKind::$newtype;

            fn from_bitmap_ref(bitmap: &Bitmap) -> &Self {
                bitmap.as_ref()
            }
        }

        impl Display for $newtype {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}({})", stringify!($newtype), &self.0)
            }
        }

        impl AsRef<$newtype> for Bitmap {
            fn as_ref(&self) -> &$newtype {
                // Safe because $newtype is repr(transparent)
                unsafe { std::mem::transmute(self) }
            }
        }

        /// # Re-export of the Bitmap API
        ///
        /// Only documentation headers are repeated here, you will find most of
        /// the documentation attached to identically named `Bitmap` methods.
        impl $newtype {
            /// Wrap an owned bitmap from hwloc
            ///
            /// See [`Bitmap::from_raw`].
            #[allow(unused)]
            pub(crate) unsafe fn from_raw(bitmap: *mut RawBitmap) -> Option<Self> {
                Bitmap::from_raw(bitmap).map(Self::from)
            }

            /// Wrap an owned bitmap from hwloc
            ///
            /// See [`Bitmap::from_non_null`].
            #[allow(unused)]
            pub(crate) unsafe fn from_non_null(bitmap: NonNull<RawBitmap>) -> Self {
                Self::from(Bitmap::from_non_null(bitmap))
            }

            /// Wrap an hwloc-originated borrowed bitmap pointer
            ///
            /// See [`Bitmap::borrow_from_raw`].
            #[allow(unused)]
            pub(crate) unsafe fn borrow_from_raw(bitmap: &*const RawBitmap) -> Option<&Self> {
                Bitmap::borrow_from_raw(bitmap).map(Bitmap::as_ref)
            }

            /// Wrap an hwloc-originated borrowed bitmap pointer
            ///
            /// See [`Bitmap::borrow_from_raw_mut`].
            #[allow(unused)]
            pub(crate) unsafe fn borrow_from_raw_mut(bitmap: &*mut RawBitmap) -> Option<&Self> {
                Bitmap::borrow_from_raw_mut(bitmap).map(Bitmap::as_ref)
            }

            /// Wrap an hwloc-originated borrowed bitmap pointer
            ///
            /// See [`Bitmap::borrow_from_non_null`].
            #[allow(unused)]
            pub(crate) unsafe fn borrow_from_non_null(bitmap: &NonNull<RawBitmap>) -> &Self {
                <Bitmap as AsRef<Self>>::as_ref(Bitmap::borrow_from_non_null(bitmap))
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

/// # CpuSet-specific API
//
// NOTE: This goes before the main impl_bitmap_newtype macro so that it appears
//       before the bitmap API reexport in rustdoc.
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
    #[doc(alias = "hwloc_bitmap_singlify_per_core")]
    pub fn singlify_per_core(&mut self, topology: &Topology, which: u32) {
        let result = unsafe {
            ffi::hwloc_bitmap_singlify_per_core(topology.as_ptr(), self.as_mut_ptr(), which)
        };
        assert!(
            result >= 0,
            "Unexpected result from hwloc_bitmap_singlify_per_core"
        )
    }

    /// Convert a NUMA node set into a CPU set
    ///
    /// For each NUMA node included in the input `nodeset`, set the
    /// corresponding local PUs in the output cpuset.
    ///
    /// If some CPUs have no local NUMA nodes, this function never sets their
    /// indexes in the output CPU set, even if a full node set is given in input.
    ///
    /// Hence the entire topology node set, that one can query via
    /// [`Topology::nodeset()`], would be converted by this function into the
    /// set of all CPUs that have some local NUMA nodes.
    ///
    /// Requires [`DiscoverySupport::numa_count()`].
    pub fn from_nodeset(topology: &Topology, nodeset: &NodeSet) -> CpuSet {
        let mut cpuset = CpuSet::new();
        for obj in topology.objects_at_depth(Depth::NUMANode) {
            if nodeset.is_set(obj.os_index().expect("NUMA nodes should have OS indices")) {
                cpuset |= obj.cpuset().expect("NUMA nodes should have cpusets");
            }
        }
        cpuset
    }
}

impl_bitmap_newtype!(
    /// A `CpuSet` is a [`Bitmap`] whose bits are set according to CPU physical OS indexes.
    CpuSet
);

/// # NodeSet-specific API
//
// NOTE: This goes before the main impl_bitmap_newtype macro so that it appears
//       before the bitmap API reexport in rustdoc.
impl NodeSet {
    /// Convert a CPU set into a NUMA node set
    ///
    /// For each PU included in the input `cpuset`, set the corresponding local
    /// NUMA node(s) in the output nodeset.
    ///
    /// If some NUMA nodes have no CPUs at all, this function never sets their
    /// indices in the output node set, even if a full CPU set is given in input.
    ///
    /// Hence the entire topology CPU set, that one can query via
    /// [`Topology::cpuset()`], would be converted by this functino into the
    /// set of all nodes that have some local CPUs.
    ///
    /// Requires [`DiscoverySupport::numa_count()`].
    pub fn from_cpuset(topology: &Topology, cpuset: &CpuSet) -> NodeSet {
        let mut nodeset = NodeSet::new();
        for obj in topology.objects_covering_cpuset_at_depth(cpuset, Depth::NUMANode) {
            nodeset.set(obj.os_index().expect("NUMA nodes should have OS indices"));
        }
        nodeset
    }
}

impl_bitmap_newtype!(
    /// A `NodeSet` is a [`Bitmap`] whose bits are set according to NUMA memory node
    /// physical OS indexes.
    NodeSet
);

/// Opaque bitmap struct
///
/// Represents the private `hwloc_bitmap_s` type that `hwloc_bitmap_t` API
/// pointers map to.
#[repr(C)]
#[doc(alias = "hwloc_bitmap_s")]
pub(crate) struct RawBitmap(IncompleteType);

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
#[doc(alias = "hwloc_bitmap_t")]
#[doc(alias = "hwloc_const_bitmap_t")]
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let bitmap = Bitmap::new();
    /// assert_eq!("", format!("{}", bitmap));
    /// assert_eq!(true, bitmap.is_empty());
    // ```
    #[doc(alias = "hwloc_bitmap_alloc")]
    pub fn new() -> Self {
        unsafe {
            let ptr =
                errors::call_hwloc_ptr_mut("hwloc_bitmap_alloc", || ffi::hwloc_bitmap_alloc())
                    .expect("hwloc_bitmap_alloc failed");
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
    /// let bitmap = Bitmap::full();
    /// assert_eq!("0-", format!("{}", bitmap));
    /// assert_eq!(false, bitmap.is_empty());
    // ```
    #[doc(alias = "hwloc_bitmap_alloc_full")]
    pub fn full() -> Self {
        unsafe {
            let ptr = errors::call_hwloc_ptr_mut("hwloc_bitmap_alloc_full", || {
                ffi::hwloc_bitmap_alloc_full()
            })
            .expect("hwloc_bitmap_alloc_full failed");
            Self::from_non_null(ptr)
        }
    }

    /// Creates a new `Bitmap` with the given range
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(0..=5);
    /// let mut bitmap2 = Bitmap::new();
    /// bitmap2.copy_from(&bitmap);
    /// assert_eq!("0-5", format!("{}", bitmap2));
    // ```
    #[doc(alias = "hwloc_bitmap_copy")]
    pub fn copy_from(&mut self, other: &Self) {
        errors::call_hwloc_int_normal("hwloc_bitmap_copy", || unsafe {
            ffi::hwloc_bitmap_copy(self.as_mut_ptr(), other.as_ptr())
        })
        .expect("hwloc_bitmap_copy failed");
    }

    /// Clear all indices
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(1..=5);
    /// assert_eq!(Some(5), bitmap.weight());
    /// assert_eq!(false, bitmap.is_empty());
    ///
    /// bitmap.clear();
    /// assert_eq!(Some(0), bitmap.weight());
    /// assert_eq!(true, bitmap.is_empty());
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
    /// let mut bitmap = Bitmap::from_range(1..=5);
    /// assert_eq!(Some(5), bitmap.weight());
    ///
    /// bitmap.fill();
    /// assert_eq!(None, bitmap.weight());
    /// ```
    #[doc(alias = "hwloc_bitmap_fill")]
    pub fn fill(&mut self) {
        unsafe { ffi::hwloc_bitmap_fill(self.as_mut_ptr()) }
    }

    /// Clear all indices except for the `id`, which is set
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(1..=5);
    /// assert_eq!(Some(5), bitmap.weight());
    ///
    /// bitmap.set_only(0);
    /// assert_eq!(Some(1), bitmap.weight());
    /// ```
    #[doc(alias = "hwloc_bitmap_only")]
    pub fn set_only(&mut self, id: u32) {
        errors::call_hwloc_int_normal("hwloc_bitmap_only", || unsafe {
            ffi::hwloc_bitmap_only(self.as_mut_ptr(), id)
        })
        .expect("hwloc_bitmap_only failed");
    }

    /// Set all indices except for `id`, which is cleared
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(1..=5);
    /// assert_eq!(Some(5), bitmap.weight());
    ///
    /// bitmap.set_all_but(42);
    /// assert_eq!(None, bitmap.weight());
    /// assert!(!bitmap.is_set(42));
    /// assert!(bitmap.is_set(43));
    /// ```
    #[doc(alias = "hwloc_bitmap_allbut")]
    pub fn set_all_but(&mut self, id: u32) {
        errors::call_hwloc_int_normal("hwloc_bitmap_allbut", || unsafe {
            ffi::hwloc_bitmap_allbut(self.as_mut_ptr(), id)
        })
        .expect("hwloc_bitmap_allbut failed");
    }

    /// Set index `id`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let mut bitmap = Bitmap::new();
    /// bitmap.set(4);
    /// assert_eq!("4", format!("{}", bitmap));
    // ```
    #[doc(alias = "hwloc_bitmap_set")]
    pub fn set(&mut self, id: u32) {
        errors::call_hwloc_int_normal("hwloc_bitmap_set", || unsafe {
            ffi::hwloc_bitmap_set(self.as_mut_ptr(), id)
        })
        .expect("hwloc_bitmap_set failed");
    }

    /// Set indexes covered by `range`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let mut bitmap = Bitmap::new();
    /// bitmap.set_range(3..=5);
    /// assert_eq!("3-5", format!("{}", bitmap));
    ///
    /// bitmap.set_range(2..);
    /// assert_eq!("2-", format!("{}", bitmap));
    // ```
    #[doc(alias = "hwloc_bitmap_set_range")]
    pub fn set_range(&mut self, range: impl RangeBounds<u32>) {
        if (range.start_bound(), range.end_bound()) == (Bound::Unbounded, Bound::Unbounded) {
            self.fill();
            return;
        }

        let (begin, end) = Self::hwloc_range(range);
        errors::call_hwloc_int_normal("hwloc_bitmap_set_range", || unsafe {
            ffi::hwloc_bitmap_set_range(self.as_mut_ptr(), begin, end)
        })
        .expect("hwloc_bitmap_set_range failed");
    }

    /// Clear index `id`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(1..=3);
    /// bitmap.unset(1);
    /// assert_eq!("2-3", format!("{}", bitmap));
    // ```
    #[doc(alias = "hwloc_bitmap_clr")]
    pub fn unset(&mut self, id: u32) {
        errors::call_hwloc_int_normal("hwloc_bitmap_clr", || unsafe {
            ffi::hwloc_bitmap_clr(self.as_mut_ptr(), id)
        })
        .expect("hwloc_bitmap_clr failed");
    }

    /// Clear indexes covered by `range`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(1..=5);
    /// bitmap.unset_range(4..6);
    /// assert_eq!("1-3", format!("{}", bitmap));
    ///
    /// bitmap.unset_range(2..);
    /// assert_eq!("1", format!("{}", bitmap));
    // ```
    #[doc(alias = "hwloc_bitmap_clr_range")]
    pub fn unset_range(&mut self, range: impl RangeBounds<u32>) {
        if (range.start_bound(), range.end_bound()) == (Bound::Unbounded, Bound::Unbounded) {
            self.clear();
            return;
        }

        let (begin, end) = Self::hwloc_range(range);
        errors::call_hwloc_int_normal("hwloc_bitmap_clr_range", || unsafe {
            ffi::hwloc_bitmap_clr_range(self.as_mut_ptr(), begin, end)
        })
        .expect("hwloc_bitmap_clr_range failed");
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
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
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
    #[doc(alias = "hwloc_bitmap_singlify")]
    pub fn singlify(&mut self) {
        errors::call_hwloc_int_normal("hwloc_bitmap_singlify", || unsafe {
            ffi::hwloc_bitmap_singlify(self.as_mut_ptr())
        })
        .expect("hwloc_bitmap_singlify failed");
    }

    /// Check if index `id` is set
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let mut bitmap = Bitmap::new();
    /// assert_eq!(false, bitmap.is_set(2));
    ///
    /// bitmap.set(2);
    /// assert_eq!(true, bitmap.is_set(2));
    /// ```
    #[doc(alias = "hwloc_bitmap_isset")]
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
    /// use hwlocality::bitmaps::Bitmap;
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
    #[doc(alias = "hwloc_bitmap_iszero")]
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let empty_bitmap = Bitmap::new();
    /// assert_eq!(false, empty_bitmap.is_full());
    ///
    /// let full_bitmap = Bitmap::full();
    /// assert_eq!(true, full_bitmap.is_full());
    /// ```
    #[doc(alias = "hwloc_bitmap_isfull")]
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(4..=10);
    /// assert_eq!(Some(4), bitmap.first_set());
    /// ```
    #[doc(alias = "hwloc_bitmap_first")]
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(4..=10);
    /// let indices = bitmap.iter_set().collect::<Vec<_>>();
    /// assert_eq!(indices, &[4, 5, 6, 7, 8, 9, 10]);
    /// ```
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
    /// let bitmap = Bitmap::from_range(4..=10);
    /// assert_eq!(Some(10), bitmap.last_set());
    /// ```
    #[doc(alias = "hwloc_bitmap_last")]
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let mut bitmap = Bitmap::from_range(1..=5);
    /// assert_eq!(Some(5), bitmap.weight());
    /// bitmap.unset(3);
    /// assert_eq!(Some(4), bitmap.weight());
    /// ```
    #[doc(alias = "hwloc_bitmap_weight")]
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(..10);
    /// assert_eq!(Some(10), bitmap.first_unset());
    /// ```
    #[doc(alias = "hwloc_bitmap_first_unset")]
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(4..);
    /// let indices = bitmap.iter_unset().collect::<Vec<_>>();
    /// assert_eq!(indices, &[0, 1, 2, 3]);
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
    /// let bitmap = Bitmap::from_range(4..);
    /// assert_eq!(Some(3), bitmap.last_unset());
    /// ```
    #[doc(alias = "hwloc_bitmap_last_unset")]
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(4..=10);
    /// let bitmap2 = Bitmap::from_range(5..=6);
    /// let result = bitmap.and_not(&bitmap2);
    /// assert_eq!(bitmap.and_not(&bitmap2), bitmap & !bitmap2);
    /// ```
    #[doc(alias = "hwloc_bitmap_andnot")]
    pub fn and_not(&self, rhs: &Self) -> Self {
        let mut result = Self::new();
        unsafe {
            Self::and_not_impl(result.as_mut_ptr(), self.as_ptr(), rhs);
        }
        result
    }

    /// Optimized `*self &= !rhs`
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let bitmap = Bitmap::from_range(4..=10);
    /// let mut bitmap2 = bitmap.clone();
    /// let rhs = Bitmap::from_range(5..=6);
    /// bitmap2.and_not_assign(&rhs);
    /// assert_eq!(bitmap2, bitmap.and_not(&rhs));
    /// ```
    pub fn and_not_assign(&mut self, rhs: &Self) {
        unsafe {
            Self::and_not_impl(self.as_mut_ptr(), self.as_ptr(), rhs);
        }
    }

    /// General `*target = (lhs & !rhs)`
    ///
    /// # Safety
    ///
    /// `target` and `lhs` must be valid bitmap pointers.
    unsafe fn and_not_impl(target: *mut RawBitmap, lhs: *const RawBitmap, rhs: &Bitmap) {
        errors::call_hwloc_int_normal("hwloc_bitmap_andnot", || unsafe {
            ffi::hwloc_bitmap_andnot(target, lhs, rhs.as_ptr())
        })
        .expect("hwloc_bitmap_andnot failed");
    }

    /// Inverts the current `Bitmap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let mut bitmap = Bitmap::new();
    /// bitmap.set(3);
    ///
    /// assert_eq!("3", format!("{}", bitmap));
    /// assert_eq!("0-2,4-", format!("{}", !bitmap));
    /// ```
    #[doc(alias = "hwloc_bitmap_not")]
    pub fn invert(&mut self) {
        errors::call_hwloc_int_normal("hwloc_bitmap_not", || unsafe {
            ffi::hwloc_bitmap_not(self.as_mut_ptr(), self.as_ptr())
        })
        .expect("hwloc_bitmap_not failed");
    }

    /// Truth that `self` and `rhs` have some set indices in common
    ///
    /// # Examples
    ///
    /// ```
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let bitmap1 = Bitmap::from_range(1..3);
    /// let bitmap2 = Bitmap::from_range(3..6);
    /// assert!(!bitmap1.intersects(&bitmap2));
    ///
    /// let bitmap3 = Bitmap::from_range(2..4);
    /// assert!(bitmap1.intersects(&bitmap3));
    /// assert!(bitmap2.intersects(&bitmap3));
    /// ```
    #[doc(alias = "hwloc_bitmap_intersects")]
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
    /// use hwlocality::bitmaps::Bitmap;
    ///
    /// let bitmap1 = Bitmap::from_range(3..8);
    /// let bitmap2 = Bitmap::from_range(5..9);
    /// assert!(!bitmap1.includes(&bitmap2));
    ///
    /// let bitmap3 = Bitmap::from_range(4..8);
    /// assert!(bitmap1.includes(&bitmap3));
    /// assert!(!bitmap2.includes(&bitmap3));
    /// ```
    #[doc(alias = "hwloc_bitmap_isincluded")]
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

impl BitAnd<&Bitmap> for &Bitmap {
    type Output = Bitmap;

    #[doc(alias = "hwloc_bitmap_and")]
    fn bitand(self, rhs: &Bitmap) -> Bitmap {
        let mut result = Bitmap::new();
        errors::call_hwloc_int_normal("hwloc_bitmap_and", || unsafe {
            ffi::hwloc_bitmap_and(result.as_mut_ptr(), self.as_ptr(), rhs.as_ptr())
        })
        .expect("hwloc_bitmap_and failed");
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
        errors::call_hwloc_int_normal("hwloc_bitmap_and", || unsafe {
            ffi::hwloc_bitmap_and(self.as_mut_ptr(), self.as_ptr(), rhs.as_ptr())
        })
        .expect("hwloc_bitmap_and failed");
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
        .expect("hwloc_bitmap_or failed");
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
        errors::call_hwloc_int_normal("hwloc_bitmap_or", || unsafe {
            ffi::hwloc_bitmap_or(self.as_mut_ptr(), self.as_ptr(), rhs.as_ptr())
        })
        .expect("hwloc_bitmap_or failed");
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
        .expect("hwloc_bitmap_xor failed");
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
        errors::call_hwloc_int_normal("hwloc_bitmap_xor", || unsafe {
            ffi::hwloc_bitmap_xor(self.as_mut_ptr(), self.as_ptr(), rhs.as_ptr())
        })
        .expect("hwloc_bitmap_xor failed");
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
            .expect("hwloc_bitmap_dup failed");
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

    #[doc(alias = "hwloc_bitmap_not")]
    fn not(self) -> Bitmap {
        let mut result = Bitmap::new();
        errors::call_hwloc_int_normal("hwloc_bitmap_not", || unsafe {
            ffi::hwloc_bitmap_not(result.as_mut_ptr(), self.as_ptr())
        })
        .expect("hwloc_bitmap_not failed");
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

unsafe impl Send for Bitmap {}
unsafe impl Sync for Bitmap {}

#[cfg(test)]
mod tests {
    use super::*;

    // TODO: Migrate to doctests, use hidden quickcheck in doctests for
    //       properties that should be true of any bitmap.

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
