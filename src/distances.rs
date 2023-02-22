//! Object distances

// Upstream docs:
// - https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__get.html
// - https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__consult.html
// - https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__add.html
// - https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__remove.html

use crate::{ffi, objects::TopologyObject, Topology};
use bitflags::bitflags;
use derive_more::Display;
use errno::{errno, Errno};
use num_enum::{IntoPrimitive, TryFromPrimitive};
use std::{
    ffi::{c_uint, c_ulong, CStr},
    fmt::{self, Debug},
    iter::FusedIterator,
    ops::{Index, IndexMut},
    ptr::NonNull,
};

/// Direct mapping of `hwloc_distances_s`. Cannot be exposed to safe code as it
/// needs a special liberation procedure.
#[repr(C)]
pub(crate) struct RawDistances {
    // Pointers objs and values should not be replaced, reallocated, freed, etc
    // and thus nbobj should not be changed either.
    nbobj: c_uint,
    objs: *mut *const TopologyObject,
    kind: c_ulong,
    values: *mut u64,
}
//
impl RawDistances {
    /// Check that the inner raw distance matrix upholds this crate's invariants
    fn check(&self) {
        assert!(
            !self.objs.is_null(),
            "Got unexpected null object list in distances"
        );
        DistancesKind::from_bits(self.kind).expect("Got unexpected distance kind");
        assert!(
            !self.values.is_null(),
            "Got unexpected null matrix in distances"
        );
    }
}

/// Matrix of distances between a set of objects
///
/// This matrix often contains latencies between NUMA nodes (as reported in the
/// System Locality Distance Information Table (SLIT) in the ACPI
/// specification), which may or may not be physically accurate. It corresponds
/// to the latency for accessing the memory of one node from a core in another
/// node. The corresponding kind is [`DistancesKind::FROM_OS`] |
/// [`DistancesKind::FROM_USER`]. The name of this distances structure is
/// "NUMALatency". Others common distance structures include "XGMIBandwidth",
/// "XGMIHops", "XeLinkBandwidth" and "NVLinkBandwidth".
///
/// The matrix may also contain bandwidths between random sets of objects,
/// possibly provided by the user, as specified in the `kind` attribute provided
/// to [`Topology::distances()`].
///
/// Resizing a distance matrix is not allowed, however users may freely change
/// their kind and contents. For instance, if there is a single NUMA node per
/// Package, [`Topology::object_with_same_locality()`] may be used to convert
/// between them and replace NUMA nodes in the objs array with the corresponding
/// Packages. See also [`Distances::transform()`] for applying some
/// transformations to the structure.
#[doc(alias = "hwloc_distances_s")]
pub struct Distances<'topology> {
    inner: NonNull<RawDistances>,
    topology: &'topology Topology,
}
//
impl<'topology> Distances<'topology> {
    /// Wrap a distance matrix from hwloc
    pub(crate) unsafe fn wrap(topology: &'topology Topology, inner: *mut RawDistances) -> Self {
        let inner = NonNull::new(inner).expect("Got null distance matrix pointer from hwloc");
        inner.as_ref().check();
        Self { inner, topology }
    }

    /// Access the inner `RawDistances` (& version)
    fn inner(&self) -> &RawDistances {
        unsafe { self.inner.as_ref() }
    }

    /// Get  the inner `RawDistances` (&mut version)
    fn inner_mut(&mut self) -> &mut RawDistances {
        unsafe { self.inner.as_mut() }
    }

    /// Description of what a distances structure contains
    ///
    /// For instance "NUMALatency" for hardware-provided NUMA distances (ACPI
    /// SLIT), or None if unknown.
    #[doc(alias = "hwloc_distances_get_name")]
    pub fn name(&self) -> Option<&str> {
        unsafe {
            let name = ffi::hwloc_distances_get_name(self.topology.as_ptr(), self.inner());
            (!name.is_null()).then(|| {
                CStr::from_ptr(name)
                    .to_str()
                    .expect("Got non UTF-8 string from hwloc_distances_get_name")
            })
        }
    }

    /// Kind of distance matrix
    pub fn kind(&self) -> DistancesKind {
        unsafe { DistancesKind::from_bits_unchecked(self.inner().kind) }
    }

    /// Number of objects described by the distance matrix
    pub fn num_objects(&self) -> usize {
        usize::try_from(self.inner().nbobj).expect("Impossible number of objects")
    }

    /// Objects described by the distance matrix
    ///
    /// These objects are not in any particular order, see methods below for
    /// easy ways to find objects and corresponding distance values.
    pub fn objects(
        &self,
    ) -> impl Iterator<Item = Option<&TopologyObject>>
           + Clone
           + DoubleEndedIterator
           + ExactSizeIterator
           + FusedIterator {
        unsafe {
            let objs = std::slice::from_raw_parts(self.inner().objs, self.num_objects());
            objs.iter().map(|ptr| ffi::deref_ptr(ptr))
        }
    }

    /// Find the row/column index of an object in the distance matrix
    ///
    /// Beware that calling this in a loop will result in a lot of duplicate work.
    /// It is a good idea to instead build a cache of indices for the objects
    /// that you are interested in, or to use the
    /// [`Distances::object_distances()`] iterator if your algorithm allows for it.
    #[doc(alias = "hwloc_distances_obj_index")]
    pub fn object_idx(&self, obj: &TopologyObject) -> Option<usize> {
        self.objects()
            .enumerate()
            .find_map(|(idx, candidate)| std::ptr::eq(candidate?, obj).then_some(idx))
    }

    /// Access the raw array of object pointers
    fn objects_mut(&mut self) -> &mut [*const TopologyObject] {
        unsafe { std::slice::from_raw_parts_mut(self.inner_mut().objs, self.num_objects()) }
    }

    /// Convert Option<&'topology TopologyObject> to a *const TopologyObject for
    /// storage in objects_mut().
    fn obj_to_ptr(obj: Option<&'topology TopologyObject>) -> *const TopologyObject {
        if let Some(obj) = obj {
            obj
        } else {
            std::ptr::null()
        }
    }

    /// Replace the object at index `idx` with another
    ///
    /// If the new object is unrelated to the original one, you may want to
    /// adjust the distance matrix after doing this, which you can using one
    /// of the [`distances_mut()`](Distances::distances_mut()),
    /// [`enumerate_distances_mut()`](Distances::enumerate_distances_mut())
    /// and [`object_distances_mut()`](Distances::object_distances_mut()) methods.
    pub fn replace_object(&mut self, idx: usize, new_object: Option<&'topology TopologyObject>) {
        self.objects_mut()[idx] = Self::obj_to_ptr(new_object);
    }

    /// Replace all objects using the provided (index, object) -> object mapping
    ///
    /// This is more efficient than calling [`Distances::replace_object()`] in
    /// a loop and allows you to know what object you are replacing.
    pub fn replace_objects(
        &mut self,
        mut mapping: impl FnMut(usize, Option<&TopologyObject>) -> Option<&'topology TopologyObject>,
    ) {
        for (idx, obj) in self.objects_mut().iter_mut().enumerate() {
            let old_obj = unsafe { ffi::deref_ptr(obj) };
            let new_obj = mapping(idx, old_obj);
            *obj = Self::obj_to_ptr(new_obj);
        }
    }

    /// Number of distances
    fn num_distances(&self) -> usize {
        self.num_objects().pow(2)
    }

    /// Distances in sender-major order
    ///
    /// This will first report the distance from the first object to the
    /// second object, then to the second object, and so on for all other
    /// objects. Then the distance from the second object to the first object
    /// will be reported, and so on.
    ///
    /// The meaning of the distance value depends on [`Distances::kind()`].
    ///
    /// If you do not know the indices of the objects that you are looking for,
    /// you may want to use [`Distances::object_distances()`] instead.
    pub fn distances(&self) -> &[u64] {
        unsafe { std::slice::from_raw_parts(self.inner().values, self.num_distances()) }
    }

    /// Distances in sender-major order (mutable access)
    ///
    /// See also [`Distances::distances()`].
    pub fn distances_mut(&mut self) -> &mut [u64] {
        unsafe { std::slice::from_raw_parts_mut(self.inner_mut().values, self.num_distances()) }
    }

    /// Iteration over ((sender index, receiver index), distance) tuples
    ///
    /// See also [`Distances::distances()`].
    pub fn enumerate_distances(
        &self,
    ) -> impl Iterator<Item = ((usize, usize), u64)>
           + Clone
           + DoubleEndedIterator
           + ExactSizeIterator
           + FusedIterator
           + '_ {
        let num_objects = self.num_objects();
        self.distances()
            .iter()
            .copied()
            .enumerate()
            .map(move |(idx, distance)| ((idx / num_objects, idx % num_objects), distance))
    }

    /// Iteration over ((sender index, receiver index), &mut distance) tuples
    ///
    /// See also [`Distances::distances()`].
    pub fn enumerate_distances_mut(
        &mut self,
    ) -> impl Iterator<Item = ((usize, usize), &mut u64)>
           + DoubleEndedIterator
           + ExactSizeIterator
           + FusedIterator
           + '_ {
        let num_objects = self.num_objects();
        self.distances_mut()
            .iter_mut()
            .enumerate()
            .map(move |(idx, distance)| ((idx / num_objects, idx % num_objects), distance))
    }

    /// Iteration over ((sender, receiver), distance) tuples
    ///
    /// See also [`Distances::distances()`].
    pub fn object_distances(
        &self,
    ) -> impl Iterator<Item = ((Option<&TopologyObject>, Option<&TopologyObject>), u64)>
           + Clone
           + FusedIterator
           + '_ {
        self.objects()
            .flat_map(|obj1| self.objects().map(move |obj2| (obj1, obj2)))
            .zip(self.distances().iter().copied())
    }

    /// Iteration over ((sender, receiver), &mut distance) tuples
    ///
    /// See also [`Distances::distances()`].
    pub fn object_distances_mut(
        &mut self,
    ) -> impl Iterator<Item = ((Option<&TopologyObject>, Option<&TopologyObject>), &mut u64)>
           + FusedIterator
           + '_ {
        let objects = unsafe { std::slice::from_raw_parts(self.inner().objs, self.num_objects()) };
        self.enumerate_distances_mut()
            .map(move |((sender_idx, receiver_idx), distance)| {
                let obj = |idx| unsafe {
                    let obj_ptr: *const TopologyObject = *objects.get_unchecked(idx);
                    (!obj_ptr.is_null()).then(|| &*obj_ptr)
                };
                ((obj(sender_idx), obj(receiver_idx)), distance)
            })
    }

    /// Distance between a pair of objects
    ///
    /// Will return the distance from the first to the second input object and
    /// the distance from the second to the first input object.
    ///
    /// This is a rather expensive operation. If you find yourself needing to
    /// do it in a loop, consider rearchitecturing your workflow around object
    /// indices or [`Distances::object_distances()`].
    #[doc(alias = "hwloc_distances_obj_pair_values")]
    pub fn object_pair_distance(
        &self,
        (obj1, obj2): (&TopologyObject, &TopologyObject),
    ) -> Option<(u64, u64)> {
        let idx1 = self.object_idx(obj1)?;
        let idx2 = self.object_idx(obj2)?;
        let num_objects = self.num_objects();
        let distances = self.distances();
        unsafe {
            let dist1to2 = *distances.get_unchecked(idx1 * num_objects + idx2);
            let dist2to1 = *distances.get_unchecked(idx2 * num_objects + idx1);
            Some((dist1to2, dist2to1))
        }
    }

    /// Checked distance matrix indexing
    fn checked_idx(&self, (sender, receiver): (usize, usize)) -> usize {
        assert!(sender < self.num_objects(), "Invalid sender index");
        assert!(receiver < self.num_objects(), "Invalid receiver index");
        sender * self.num_objects() + receiver
    }

    /// Apply a transformation to this distance matrix
    ///
    /// This modifies the local copy of the distances structures but does not
    /// modify the distances information stored inside the topology (retrieved
    /// by another call to [`Topology::distances()`] or exported to XML). To do
    /// so, one should add a new distances structure with same name, kind,
    /// objects and values (see "Add distances between objects" TODO wrap and
    /// link) and then remove this old one with hwloc_distances_release_remove()
    /// (TODO wrap and link).
    ///
    /// Objects may also be directly replaced in place using
    /// [`Distances::replace_objects()`]. One may use e.g.
    /// [`Topology::object_with_same_locality()`] to easily convert between
    /// similar objects of different types.
    pub fn transform(&mut self, transform: DistancesTransform) -> Result<(), Errno> {
        let result = unsafe {
            ffi::hwloc_distances_transform(
                self.topology.as_ptr(),
                self.inner_mut(),
                transform.into(),
                std::ptr::null_mut(),
                0,
            )
        };
        match result {
            -1 => Err(errno()),
            0 => Ok(()),
            other => panic!("Unexpected result from hwloc_distances_transform: {other}"),
        }
    }
}
//
impl Debug for Distances<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Distances")
            .field("name", &self.name())
            .field("kind", &self.kind())
            .finish_non_exhaustive()
    }
}
//
impl Drop for Distances<'_> {
    fn drop(&mut self) {
        unsafe { ffi::hwloc_distances_release(self.topology.as_ptr(), self.inner.as_ptr()) }
    }
}
//
impl Eq for Distances<'_> {}
//
impl Index<(usize, usize)> for Distances<'_> {
    type Output = u64;

    fn index(&self, idx: (usize, usize)) -> &u64 {
        unsafe { self.distances().get_unchecked(self.checked_idx(idx)) }
    }
}
//
impl IndexMut<(usize, usize)> for Distances<'_> {
    fn index_mut(&mut self, idx: (usize, usize)) -> &mut u64 {
        let idx = self.checked_idx(idx);
        unsafe { self.distances_mut().get_unchecked_mut(idx) }
    }
}
//
impl PartialEq for Distances<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.name() == other.name()
            && self.kind() == other.kind()
            && self
                .objects()
                .zip(other.objects())
                .all(|obj_pair| match obj_pair {
                    (Some(obj1), Some(obj2)) => std::ptr::eq(obj1, obj2),
                    (None, None) => true,
                    _ => false,
                })
            && self.distances() == other.distances()
    }
}
// TODO: Impl more traits, check out slice and ndarray::ArrayBase for ideas

bitflags! {
    /// Kinds of distance matrices
    ///
    /// A kind with a name starting with "FROM_" specifies where the distance
    /// information comes from, if known.
    ///
    /// A kind with a name starting with "MEANS_" specifies whether values are
    /// latencies or bandwidths, if applicable.
    #[repr(C)]
    #[doc(alias = "hwloc_distances_kind_e")]
    pub struct DistancesKind: c_ulong {
        /// These distances were obtained from the operating system or hardware
        #[doc(alias = "HWLOC_DISTANCES_KIND_FROM_OS")]
        const FROM_OS = (1<<0);

        /// These distances were provided by the user
        #[doc(alias = "HWLOC_DISTANCES_KIND_FROM_USER")]
        const FROM_USER = (1<<1);

        /// Distance values are similar to latencies between objects
        ///
        /// Values are smaller for closer objects, hence minimal on the diagonal
        /// of the matrix (distance between an object and itself).
        ///
        /// It could also be the number of network hops between objects, etc.
        #[doc(alias = "HWLOC_DISTANCES_KIND_MEANS_LATENCY")]
        const MEANS_LATENCY = (1<<2);

        /// Distance values are similar to bandwidths between objects
        ///
        /// Values are higher for closer objects, hence maximal on the diagonal
        /// of the matrix (distance between an object and itself).
        ///
        /// Such values are currently ignored for distance-based grouping.
        #[doc(alias = "HWLOC_DISTANCES_KIND_MEANS_BANDWIDTH")]
        const MEANS_BANDWIDTH = (1<<3);

        /// This distances structure covers objects of different types
        ///
        /// This may apply to the "NVLinkBandwidth" structure in presence of a
        /// NVSwitch or POWER processor NVLink port.
        #[doc(alias = "HWLOC_DISTANCES_KIND_HETEROGENEOUS_TYPES")]
        const HETEROGENEOUS_TYPES = (1<<4);
    }
}

/// Rust mapping of the hwloc_distances_transform_e enum
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
///
pub(crate) type RawDistancesTransform = c_uint;

/// Transformations of distances structures
#[repr(u32)]
#[derive(Copy, Clone, Debug, Display, Eq, Hash, IntoPrimitive, TryFromPrimitive, PartialEq)]
#[doc(alias = "hwloc_distances_transform_e")]
pub enum DistancesTransform {
    /// Remove `None` objects from the distances structure.
    ///
    /// Every object that was replaced with `None` in [`Distances::objects()`]
    /// is removed and the matric is updated accordingly.
    ///
    /// At least 2 objects must remain, otherwise [`Distances::transform()`]
    /// will fail.
    ///
    /// [`Distances::kind()`] will be updated with or without
    /// [`HETEROGENEOUS_TYPES`](DistancesKind::HETEROGENEOUS_TYPES) according to
    /// the remaining objects.
    #[doc(alias = "HWLOC_DISTANCES_TRANSFORM_REMOVE_NULL")]
    RemoveNone = 0,

    /// Replace bandwidth values with a number of links
    ///
    /// Usually all values will be either 0 (no link) or 1 (one link).
    /// However some matrices could get larger values if some pairs of
    /// peers are connected by different numbers of links.
    ///
    /// Values on the diagonal are set to 0.
    ///
    /// This transformation only applies to bandwidth matrices.
    #[doc(alias = "HWLOC_DISTANCES_TRANSFORM_LINKS")]
    BandwidthToLinkCount = 1,

    /// Merge switches with multiple ports into a single object
    ///
    /// This currently only applies to NVSwitches where GPUs seem connected to
    /// different separate switch ports in the NVLinkBandwidth matrix.
    ///
    /// This transformation will replace all switch ports with the same port
    /// connected to all GPUs.
    ///
    /// Other ports are removed by applying the `RemoveNone` transformation
    /// internally.
    #[doc(alias = "HWLOC_DISTANCES_TRANSFORM_MERGE_SWITCH_PORTS")]
    MergeSwitchPorts = 2,

    /// Apply a transitive closure to the matrix to connect objects across
    /// switches.
    ///
    /// This currently only applies to GPUs and NVSwitches in the
    /// NVLinkBandwidth matrix.
    ///
    /// All pairs of GPUs will be reported as directly connected.
    #[doc(alias = "HWLOC_DISTANCES_TRANSFORM_TRANSITIVE_CLOSURE")]
    TransitiveSwitchClosure = 3,
}
