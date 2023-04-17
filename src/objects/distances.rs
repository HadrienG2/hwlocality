//! Object distances

// Upstream docs:
// - https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__get.html
// - https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__consult.html

#[cfg(feature = "hwloc-2_5_0")]
use crate::errors::HybridError;
#[cfg(feature = "hwloc-2_1_0")]
use crate::{errors::NulError, ffi::LibcString};
#[cfg(feature = "hwloc-2_3_0")]
use crate::{
    errors::{self, RawHwlocError},
    topology::editor::TopologyEditor,
};
use crate::{
    ffi,
    objects::{depth::Depth, types::ObjectType, TopologyObject},
    topology::{RawTopology, Topology},
};
use bitflags::bitflags;
use std::{
    ffi::{c_int, c_uint, c_ulong},
    fmt::{self, Debug},
    iter::FusedIterator,
    ops::{Index, IndexMut},
    ptr::{self, NonNull},
};
#[cfg(feature = "hwloc-2_5_0")]
use thiserror::Error;

/// # Retrieve distances between objects
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__get.html
impl Topology {
    /// Retrieve distance matrices from the topology
    ///
    /// By default, all available distance matrices are returned. Some filtering
    /// may be applied using the `kind` parameter: if it contains some
    /// [`DistancesKind`]`::FROM_xyz` options, only distance matrices matching
    /// one of them is returned. The same applies for `MEANS_xyz` options.
    #[doc(alias = "hwloc_distances_get")]
    pub fn distances(&self, kind: DistancesKind) -> Vec<Distances> {
        unsafe {
            self.get_distances(|topology, nr, distances, flags| {
                ffi::hwloc_distances_get(topology, nr, distances, kind.bits(), flags)
            })
        }
    }

    /// Retrieve distance matrices for object at a specific depth in the topology
    ///
    /// Identical to `distances()` with the additional `depth` filter.
    #[doc(alias = "hwloc_distances_get_by_depth")]
    pub fn distances_at_depth(
        &self,
        kind: DistancesKind,
        depth: impl Into<Depth>,
    ) -> Vec<Distances> {
        let depth = depth.into();
        unsafe {
            self.get_distances(|topology, nr, distances, flags| {
                ffi::hwloc_distances_get_by_depth(
                    topology,
                    depth.into(),
                    nr,
                    distances,
                    kind.bits(),
                    flags,
                )
            })
        }
    }

    /// Retrieve distance matrices for object with a specific type
    ///
    /// Identical to `distances()` with the additional `ty` filter.
    #[doc(alias = "hwloc_distances_get_by_type")]
    pub fn distances_with_type(&self, kind: DistancesKind, ty: ObjectType) -> Vec<Distances> {
        unsafe {
            self.get_distances(|topology, nr, distances, flags| {
                ffi::hwloc_distances_get_by_type(
                    topology,
                    ty.into(),
                    nr,
                    distances,
                    kind.bits(),
                    flags,
                )
            })
        }
    }

    /// Retrieve a distance matrix with the given name
    ///
    /// Usually only one distances matrix may match a given name.
    ///
    /// Names of distances matrices currently created by hwloc may be found
    /// [in the hwloc documentation](https://hwloc.readthedocs.io/en/v2.9/topoattrs.html#topoattrs_distances).
    ///
    /// # Errors
    ///
    /// - [`NulError`] if `name` contains NUL chars.
    #[cfg(feature = "hwloc-2_1_0")]
    #[doc(alias = "hwloc_distances_get_by_name")]
    pub fn distances_with_name(&self, name: &str) -> Result<Vec<Distances>, NulError> {
        let name = LibcString::new(name)?;
        unsafe {
            Ok(self.get_distances(|topology, nr, distances, flags| {
                ffi::hwloc_distances_get_by_name(topology, name.borrow(), nr, distances, flags)
            }))
        }
    }

    /// Call one of the hwloc_distances_get(_by)? APIs
    ///
    /// Takes care of all parameters except for `kind`, which is not universal
    /// to these APIs. So the last c_ulong is the flags parameter.
    ///
    /// # Safety
    ///
    /// `getter` must perform a correct call to a `hwloc_distances_get` API
    unsafe fn get_distances(
        &self,
        mut getter: impl FnMut(
            *const RawTopology,
            *mut c_uint,
            *mut *mut RawDistances,
            c_ulong,
        ) -> c_int,
    ) -> Vec<Distances> {
        // Common setup to all getter calls
        let mut nr = 0;
        let flags = 0;
        let check_result = |result: c_int| {
            assert!(result >= 0, "Unexpected result from hwloc distances getter");
        };

        // Allocate array of distances pointers
        check_result(getter(self.as_ptr(), &mut nr, ptr::null_mut(), flags));
        let mut distances_ptrs = vec![
            ptr::null_mut();
            usize::try_from(nr)
                .expect("Impossibly large amount of distance matrices")
        ];

        // Let hwloc fill the distance pointers
        let old_nr = nr;
        check_result(getter(
            self.as_ptr(),
            &mut nr,
            distances_ptrs.as_mut_ptr(),
            flags,
        ));
        assert_eq!(
            nr, old_nr,
            "Inconsistent reported number of distance matrices"
        );

        // Wrap them into a safe interface
        distances_ptrs
            .into_iter()
            .map(|raw| unsafe { Distances::wrap(self, raw) })
            .collect()
    }
}

/// # Add distances between objects
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__add.html
#[cfg(feature = "hwloc-2_5_0")]
impl TopologyEditor<'_> {
    /// Create a new object distances matrix
    ///
    /// `kind` specifies the kind of distance.
    ///
    /// `flags` can be used to request the grouping of existing objects based on
    /// distance.
    ///
    /// The `collect_objects_and_distances` callback should query the geometry
    /// to collect references to the objects of interest, and produce the
    /// corresponding distance matrix. If there are N output objects, then there
    /// should be N.pow(2) output distances.
    ///
    /// Distances must be provided in sender-major order: the distance from
    /// object 0 to object 1, then object 0 to object 2, ... all the way to
    /// object N, and then from object 1 to object 0, and so on.
    ///
    /// # Errors
    ///
    /// - [`NameContainsNul`](AddDistancesError::NameContainsNul) if the
    ///   provided `name` contains NUL chars
    /// - [`BadKind`](AddDistancesError::BadKind) if the provided `kind`
    ///   contains [`HETEROGENEOUS_TYPES`](DistancesKind::HETEROGENEOUS_TYPES).
    /// - [`BadObjectsCount`](AddDistancesError::BadObjectsCount) if less
    ///   than 2 or more than `u32::MAX` objects are returned by the callback
    ///   (hwloc does not support such configurations).
    /// - [`BadDistancesCount`](AddDistancesError::BadDistancesCount) if
    ///   the number of distances returned by the callback is not compatible
    ///   with the number of objects (it should be the square of it).
    #[doc(alias = "hwloc_distances_add_create")]
    #[doc(alias = "hwloc_distances_add_values")]
    #[doc(alias = "hwloc_distances_add_commit")]
    pub fn add_distances(
        &mut self,
        name: Option<&str>,
        kind: DistancesKind,
        flags: AddDistancesFlags,
        collect_objects_and_distances: impl FnOnce(
            &Topology,
        ) -> (Vec<Option<&TopologyObject>>, Vec<u64>),
    ) -> Result<(), HybridError<AddDistancesError>> {
        // Prepare arguments for C consumption and validate them
        let name = match name.map(LibcString::new).transpose() {
            Ok(name) => name,
            Err(NulError) => return Err(AddDistancesError::NameContainsNul.into()),
        };
        let name = name.map(|lcs| lcs.borrow()).unwrap_or(ptr::null());
        //
        if kind.contains(DistancesKind::HETEROGENEOUS_TYPES) {
            return Err(AddDistancesError::BadKind.into());
        }
        let kind = kind.bits();
        //
        let create_add_flags = 0;
        let commit_flags = flags.bits();
        //
        let (objects, distances) = collect_objects_and_distances(self.topology());
        if objects.len() < 2 {
            return Err(AddDistancesError::BadObjectsCount(objects.len()).into());
        }
        let Ok(nbobjs) = c_uint::try_from(objects.len()) else {
            return Err(AddDistancesError::BadObjectsCount(objects.len()).into())
        };
        let expected_distances_len = objects.len().pow(2);
        if distances.len() != expected_distances_len {
            return Err(AddDistancesError::BadDistancesCount {
                expected_distances_len,
                actual_distances_len: distances.len(),
            }
            .into());
        }
        let objs = objects.as_ptr() as *const *const TopologyObject;
        let values = distances.as_ptr() as *const u64;

        // Create new empty distances structure
        let handle = errors::call_hwloc_ptr_mut("hwloc_distances_add_create", || unsafe {
            ffi::hwloc_distances_add_create(self.topology_mut_ptr(), name, kind, create_add_flags)
        })
        .map_err(HybridError::Hwloc)?;

        // Add objects to the distance structure
        errors::call_hwloc_int_normal("hwloc_distances_add_values", || unsafe {
            ffi::hwloc_distances_add_values(
                self.topology_mut_ptr(),
                handle.as_ptr(),
                nbobjs,
                objs,
                values,
                create_add_flags,
            )
        })
        .map_err(HybridError::Hwloc)?;

        // Finalize the distance structure and insert it into the topology
        errors::call_hwloc_int_normal("hwloc_distances_add_commit", || unsafe {
            ffi::hwloc_distances_add_commit(self.topology_mut_ptr(), handle.as_ptr(), commit_flags)
        })
        .map_err(HybridError::Hwloc)?;
        Ok(())
    }
}

#[cfg(feature = "hwloc-2_5_0")]
bitflags! {
    /// Flags to be given to [`TopologyEditor::add_distances()`]
    #[repr(C)]
    pub struct AddDistancesFlags: c_ulong {
        /// Try to group objects based on the newly provided distance information
        ///
        /// This is ignored for distances between objects of different types.
        #[doc(alias = "HWLOC_DISTANCES_ADD_FLAG_GROUP")]
        const GROUP = (1<<0);

        /// Like Group, but consider the distance values as inaccurate and relax
        /// the comparisons during the grouping algorithms. The actual accuracy
        /// may be modified through the HWLOC_GROUPING_ACCURACY environment
        /// variable (see
        /// [Environment Variables](https://hwloc.readthedocs.io/en/v2.9/envvar.html)).
        #[doc(alias = "HWLOC_DISTANCES_ADD_FLAG_GROUP_INACCURATE")]
        const GROUP_INACCURATE = (1<<0) | (1<<1);
    }
}

#[cfg(feature = "hwloc-2_5_0")]
impl Default for AddDistancesFlags {
    fn default() -> Self {
        Self::empty()
    }
}

/// Failed to add a new distance matrix to the topology
#[cfg(feature = "hwloc-2_5_0")]
#[derive(Copy, Clone, Debug, Eq, Error, Hash, PartialEq)]
pub enum AddDistancesError {
    /// Provided `name` contains NUL chars
    #[error("provided name contains NUL chars")]
    NameContainsNul,

    /// Provided `kind` contains [`DistancesKind::HETEROGENEOUS_TYPES`]
    ///
    /// You should not set this kind yourself, it will be automatically set by
    /// hwloc through scanning of the provided object list.
    #[cfg(feature = "hwloc-2_1_0")]
    #[error("provided kind contains HETEROGENEOUS_TYPES")]
    BadKind,

    /// Provided callback returned too many or too few objects
    ///
    /// hwloc only supports distances matrices with 2 to `u32::MAX` objects.
    #[error("callback emitted <2 or >u32::MAX objects: {0}")]
    BadObjectsCount(usize),

    /// Provided callback returned incompatible objects and distances arrays
    ///
    /// If we denote N the length of the objects array, the distances array
    /// should contain N.pow(2) elements.
    #[error("callback emitted an invalid amount of distances (expected {expected_distances_len}, got {actual_distances_len})")]
    BadDistancesCount {
        expected_distances_len: usize,
        actual_distances_len: usize,
    },
}
//
#[cfg(feature = "hwloc-2_5_0")]
impl From<NulError> for AddDistancesError {
    fn from(_: NulError) -> Self {
        Self::NameContainsNul
    }
}

/// Handle to a new distances structure during its addition to the topology
#[cfg(feature = "hwloc-2_5_0")]
pub(crate) type DistancesAddHandle = *mut std::ffi::c_void;

/// # Remove distances between objects
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__remove.html
#[cfg(feature = "hwloc-2_3_0")]
impl TopologyEditor<'_> {
    /// Remove a single distances matrix from the topology
    ///
    /// The distances matrix to be removed can be selected using the
    /// `find_distances` callback.
    #[doc(alias = "hwloc_distances_release_remove")]
    pub fn remove_distances(
        &mut self,
        find_distances: impl FnOnce(&Topology) -> Distances,
    ) -> Result<(), RawHwlocError> {
        let distances = find_distances(self.topology()).into_inner();
        errors::call_hwloc_int_normal("hwloc_distances_release_remove", || unsafe {
            ffi::hwloc_distances_release_remove(self.topology_mut_ptr(), distances)
        })
        .map(|_| ())
    }

    /// Remove all distance matrices from a topology
    ///
    /// If these distances were used to group objects, these additional Group
    /// objects are not removed from the topology.
    #[doc(alias = "hwloc_distances_remove")]
    pub fn remove_all_distances(&mut self) -> Result<(), RawHwlocError> {
        errors::call_hwloc_int_normal("hwloc_distances_remove", || unsafe {
            ffi::hwloc_distances_remove(self.topology_mut_ptr())
        })
        .map(|_| ())
    }

    /// Remove distance matrices for objects at a specific depth in the topology
    ///
    /// See also [`TopologyEditor::remove_all_distances()`].
    #[doc(alias = "hwloc_distances_remove_by_depth")]
    pub fn remove_distances_at_depth(
        &mut self,
        depth: impl Into<Depth>,
    ) -> Result<(), RawHwlocError> {
        errors::call_hwloc_int_normal("hwloc_distances_remove_by_depth", || unsafe {
            ffi::hwloc_distances_remove_by_depth(self.topology_mut_ptr(), depth.into().into())
        })
        .map(|_| ())
    }

    /// Remove distance matrices for objects of a specific type in the topology
    ///
    /// See also [`TopologyEditor::remove_all_distances()`].
    #[doc(alias = "hwloc_distances_remove_by_type")]
    pub fn remove_distances_with_type(&mut self, ty: ObjectType) -> Result<(), RawHwlocError> {
        let topology = self.topology();
        if let Ok(depth) = topology.depth_for_type(ty) {
            self.remove_distances_at_depth(depth)?;
        } else {
            let depths = (0..topology.depth())
                .map(Depth::from)
                .filter_map(|depth| {
                    let depth_ty = topology
                        .type_at_depth(depth)
                        .expect("A type should be present at this depth");
                    (depth_ty == ty).then_some(depth)
                })
                .collect::<Vec<_>>();
            for depth in depths {
                self.remove_distances_at_depth(depth)?;
            }
        }
        Ok(())
    }
}

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
/// "NUMALatency".
///
/// The names and semantics of other distances matrices currently created by
/// hwloc may be found
/// [in the hwloc documentation](https://hwloc.readthedocs.io/en/v2.9/topoattrs.html#topoattrs_distances).
///
/// The matrix may also contain bandwidths between random sets of objects,
/// possibly provided by the user, as specified in the `kind` attribute provided
/// to [`Topology::distances()`].
///
/// Resizing a distance matrix is not allowed, however users may freely change
/// their kind and contents.
///
#[cfg_attr(
    feature = "hwloc-2_5_0",
    doc = "For instance, on hwloc 2.5+, if there is a single NUMA node per Package,"
)]
#[cfg_attr(
    feature = "hwloc-2_5_0",
    doc = "[`Topology::object_with_same_locality()`] may be used to convert"
)]
#[cfg_attr(
    feature = "hwloc-2_5_0",
    doc = "between them and replace NUMA nodes in the objs array with the corresponding"
)]
#[cfg_attr(feature = "hwloc-2_5_0", doc = "Packages.")]
#[cfg_attr(feature = "hwloc-2_5_0", doc = "")]
#[cfg_attr(
    feature = "hwloc-2_5_0",
    doc = "See also [`Distances::transform()`] for applying some"
)]
#[cfg_attr(feature = "hwloc-2_5_0", doc = "transformations to the structure.")]
#[doc(alias = "hwloc_distances_s")]
pub struct Distances<'topology> {
    inner: NonNull<RawDistances>,
    topology: &'topology Topology,
}
//
impl<'topology> Distances<'topology> {
    /// Wrap a distance matrix from hwloc
    ///
    /// # Safety
    ///
    /// `inner` must originate from `topology`
    pub(crate) unsafe fn wrap(topology: &'topology Topology, inner: *mut RawDistances) -> Self {
        let inner = NonNull::new(inner).expect("Got null distance matrix pointer from hwloc");
        inner.as_ref().check();
        Self { inner, topology }
    }

    /// Access the inner `RawDistances` (& version)
    fn inner(&self) -> &RawDistances {
        unsafe { self.inner.as_ref() }
    }

    /// Get the inner `RawDistances` (&mut version)
    fn inner_mut(&mut self) -> &mut RawDistances {
        unsafe { self.inner.as_mut() }
    }

    /// Release the inner `RawDistances` pointer
    ///
    /// This will result in a resource leak unless the pointer is subsequently
    /// liberated through `hwloc_distances_release` or
    /// `hwloc_distances_release_remove`.
    #[allow(unused)]
    pub(crate) fn into_inner(self) -> *mut RawDistances {
        let inner = self.inner.as_ptr();
        std::mem::forget(self);
        inner
    }

    /// Description of what a distances structure contains
    ///
    /// For instance "NUMALatency" for hardware-provided NUMA distances (ACPI
    /// SLIT), or None if unknown.
    #[cfg(feature = "hwloc-2_1_0")]
    #[doc(alias = "hwloc_distances_get_name")]
    pub fn name(&self) -> Option<&std::ffi::CStr> {
        unsafe {
            let name = ffi::hwloc_distances_get_name(self.topology.as_ptr(), self.inner());
            (!name.is_null()).then(|| std::ffi::CStr::from_ptr(name))
        }
    }

    /// Kind of distance matrix
    pub fn kind(&self) -> DistancesKind {
        DistancesKind::from_bits_truncate(self.inner().kind)
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
           + FusedIterator {
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
           + FusedIterator {
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
           + FusedIterator {
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
    /// by another call to [`Topology::distances()`] or exported to XML).
    ///
    /// To do so, one should add a new distances structure with same name, kind,
    /// objects and values (see [`TopologyEditor::add_distances()`]) and then
    /// remove this old one using one of the `TopologyEditor` APIs for removing
    /// distances.
    ///
    /// Objects may also be directly replaced in place using
    /// [`Distances::replace_objects()`]. One may use e.g.
    /// [`Topology::object_with_same_locality()`] to easily convert between
    /// similar objects of different types.
    #[cfg(feature = "hwloc-2_5_0")]
    #[doc(alias = "hwloc_distances_transform")]
    pub fn transform(&mut self, transform: DistancesTransform) -> Result<(), RawHwlocError> {
        errors::call_hwloc_int_normal("hwloc_distances_transform", || unsafe {
            ffi::hwloc_distances_transform(
                self.topology.as_ptr(),
                self.inner_mut(),
                transform.into(),
                std::ptr::null_mut(),
                0,
            )
        })
        .map(|_| ())
    }
}
//
impl Debug for Distances<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug = f.debug_struct("Distances");
        #[cfg(feature = "hwloc-2_1_0")]
        debug.field("name", &self.name());
        debug.field("kind", &self.kind()).finish_non_exhaustive()
    }
}
//
impl Drop for Distances<'_> {
    fn drop(&mut self) {
        unsafe { ffi::hwloc_distances_release(self.topology.as_ptr(), self.inner.as_ptr()) }
    }
}
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
        #[cfg(feature = "hwloc-2_1_0")]
        #[doc(alias = "HWLOC_DISTANCES_KIND_HETEROGENEOUS_TYPES")]
        const HETEROGENEOUS_TYPES = (1<<4);
    }
}

/// Rust mapping of the hwloc_distances_transform_e enum
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
///
#[cfg(feature = "hwloc-2_5_0")]
pub(crate) type RawDistancesTransform = c_uint;

/// Transformations of distances structures
#[cfg(feature = "hwloc-2_5_0")]
#[derive(
    Copy,
    Clone,
    Debug,
    derive_more::Display,
    Eq,
    Hash,
    num_enum::IntoPrimitive,
    num_enum::TryFromPrimitive,
    PartialEq,
)]
#[doc(alias = "hwloc_distances_transform_e")]
#[repr(u32)]
pub enum DistancesTransform {
    /// Remove `None` objects from the distances structure.
    ///
    /// Every object that was replaced with `None` in [`Distances::objects()`]
    /// is removed and the matric is updated accordingly.
    ///
    /// At least 2 objects must remain, otherwise [`Distances::transform()`]
    /// will fail.
    ///
    #[cfg_attr(
        feature = "hwloc-2_1_0",
        doc = "On hwloc 2.1+, [`Distances::kind()`] will be updated with or without"
    )]
    #[cfg_attr(
        feature = "hwloc-2_1_0",
        doc = "[`HETEROGENEOUS_TYPES`](DistancesKind::HETEROGENEOUS_TYPES) according to"
    )]
    #[cfg_attr(feature = "hwloc-2_1_0", doc = "the remaining objects.")]
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
