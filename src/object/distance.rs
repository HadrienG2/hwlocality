//! Object distances
//!
//! Modern computer components are not usually connected via all-to-all
//! networks. Instead, more scalable network topologies like rings or meshes
//! are preferred. As a result, some components can communicate more quickly
//! with each other than others, and the hwloc object distance API is meant to
//! expose this information.
//!
//! At the time of writing, hwloc can only measure distances between NUMA nodes
//! and between GPUs.
//!
//! Most of this module's functionality is exposed via [methods of the Topology
//! struct](../../topology/struct.Topology.html#retrieve-distances-between-objects).
//! The module itself only hosts type definitions that are related to this
//! functionality.

#[cfg(feature = "hwloc-2_5_0")]
use crate::errors::FlagsError;
#[cfg(any(doc, feature = "hwloc-2_3_0"))]
use crate::object::depth::NormalDepth;
#[cfg(feature = "hwloc-2_3_0")]
use crate::topology::editor::TopologyEditor;
use crate::{
    errors::{self, ForeignObjectError, RawHwlocError},
    ffi::{self, int, transparent::TransparentNewtype},
    object::{depth::Depth, types::ObjectType, TopologyObject},
    topology::Topology,
};
#[cfg(feature = "hwloc-2_1_0")]
use crate::{
    errors::{HybridError, NulError},
    ffi::string::LibcString,
};
use bitflags::bitflags;
#[cfg(feature = "hwloc-2_5_0")]
use enum_iterator::Sequence;
#[cfg(feature = "hwloc-2_1_0")]
use hwlocality_sys::HWLOC_DISTANCES_KIND_HETEROGENEOUS_TYPES;
use hwlocality_sys::{
    hwloc_const_topology_t, hwloc_distances_kind_e, hwloc_distances_s, hwloc_obj, hwloc_topology,
    HWLOC_DISTANCES_KIND_FROM_OS, HWLOC_DISTANCES_KIND_FROM_USER,
    HWLOC_DISTANCES_KIND_MEANS_BANDWIDTH, HWLOC_DISTANCES_KIND_MEANS_LATENCY,
};
#[cfg(feature = "hwloc-2_5_0")]
use hwlocality_sys::{
    hwloc_distances_add_flag_e, HWLOC_DISTANCES_ADD_FLAG_GROUP,
    HWLOC_DISTANCES_ADD_FLAG_GROUP_INACCURATE, HWLOC_DISTANCES_TRANSFORM_LINKS,
    HWLOC_DISTANCES_TRANSFORM_MERGE_SWITCH_PORTS, HWLOC_DISTANCES_TRANSFORM_REMOVE_NULL,
    HWLOC_DISTANCES_TRANSFORM_TRANSITIVE_CLOSURE,
};
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
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
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__get.html
impl Topology {
    /// Retrieve distance matrices from the topology
    ///
    /// By default, all available distance matrices are returned. Some filtering
    /// may be applied using the `kind` parameter: if it contains some
    /// [`DistancesKind`]`::FROM_xyz` options, only distance matrices matching
    /// one of them is returned. The same applies for `MEANS_xyz` options.
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_distances_get")]
    pub fn distances(
        &self,
        kind: Option<DistancesKind>,
    ) -> Result<Vec<Distances<'_>>, RawHwlocError> {
        // SAFETY: - By definition, it's valid to pass hwloc_distances_get
        //         - Parameters are guaranteed valid per get_distances_with_kind
        //           contract
        unsafe {
            self.get_distances(
                kind,
                "hwloc_distances_get",
                |topology, nr, distances, kind, flags| {
                    hwlocality_sys::hwloc_distances_get(topology, nr, distances, kind, flags)
                },
            )
        }
    }

    /// Retrieve distance matrices for objects at a specific depth in the
    /// topology (if any)
    ///
    /// Identical to [`distances()`] with the additional `depth` filter.
    ///
    /// `depth` can be a [`Depth`], a [`NormalDepth`] or an [`usize`].
    ///
    /// [`distances()`]: Topology::distances()
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_distances_get_by_depth")]
    pub fn distances_at_depth<DepthLike>(
        &self,
        kind: Option<DistancesKind>,
        depth: DepthLike,
    ) -> Result<Vec<Distances<'_>>, RawHwlocError>
    where
        DepthLike: TryInto<Depth>,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized(
            self_: &Topology,
            kind: Option<DistancesKind>,
            depth: Depth,
        ) -> Result<Vec<Distances<'_>>, RawHwlocError> {
            // SAFETY: - hwloc_distances_get_by_depth with the depth parameter
            //           curried away behaves indeed like hwloc_distances_get
            //         - Depth only allows valid depth values to exist
            //         - Other parameters are guaranteed valid per
            //           get_distances_with_kind contract
            unsafe {
                self_.get_distances(
                    kind,
                    "hwloc_distances_get_by_depth",
                    |topology, nr, distances, kind, flags| {
                        hwlocality_sys::hwloc_distances_get_by_depth(
                            topology,
                            depth.to_raw(),
                            nr,
                            distances,
                            kind,
                            flags,
                        )
                    },
                )
            }
        }

        // There cannot be any object at a depth below the hwloc-supported max
        depth
            .try_into()
            .map_or_else(|_| Ok(Vec::new()), |depth| polymorphized(self, kind, depth))
    }

    /// Retrieve distance matrices for object with a specific type
    ///
    /// Identical to [`distances()`] with the additional `ty` filter.
    ///
    /// [`distances()`]: Topology::distances()
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_distances_get_by_type")]
    pub fn distances_with_type(
        &self,
        kind: Option<DistancesKind>,
        ty: ObjectType,
    ) -> Result<Vec<Distances<'_>>, RawHwlocError> {
        // SAFETY: - hwloc_distances_get_by_type with the type parameter curried
        //           away behaves indeed like hwloc_distances_get
        //         - No invalid ObjectType value should be exposed by this
        //           binding (to enable values from newer releases of hwloc, you
        //           must configure the build to require newer hwloc DLLs)
        //         - Other parameters are guaranteed valid per
        //           get_distances_with_kind contract
        unsafe {
            self.get_distances(
                kind,
                "hwloc_distances_get_by_type",
                |topology, nr, distances, kind, flags| {
                    hwlocality_sys::hwloc_distances_get_by_type(
                        topology,
                        ty.into(),
                        nr,
                        distances,
                        kind,
                        flags,
                    )
                },
            )
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
    pub fn distances_with_name(
        &self,
        name: &str,
    ) -> Result<Vec<Distances<'_>>, HybridError<NulError>> {
        let name = LibcString::new(name)?;
        // SAFETY: - hwloc_distances_get_by_name with the name parameter curried
        //           away behaves indeed like hwloc_distances_get
        //         - `name` is a valid c string by construction of LibcString
        //         - Other parameters are guaranteed valid per get_distances contract
        unsafe {
            self.get_distances_without_kind(
                "hwloc_distances_get_by_name",
                |topology, nr, distances, flags| {
                    hwlocality_sys::hwloc_distances_get_by_name(
                        topology,
                        name.borrow(),
                        nr,
                        distances,
                        flags,
                    )
                },
            )
            .map_err(HybridError::Hwloc)
        }
    }

    /// Call one of the `hwloc_distances_get(_by)?` APIs
    ///
    /// # Safety
    ///
    /// - `getter` must be an hwloc API with `hwloc_distances_get`-like
    ///   semantics
    /// - This API is guaranteed to be passed valid (Topology, distances buffer
    ///   length, distance out-buffer pointer, kind, flags) tuples
    #[allow(clippy::missing_errors_doc)]
    unsafe fn get_distances(
        &self,
        kind: Option<DistancesKind>,
        getter_name: &'static str,
        mut getter: impl FnMut(
            *const hwloc_topology,
            *mut c_uint,
            *mut *mut hwloc_distances_s,
            hwloc_distances_kind_e,
            c_ulong,
        ) -> c_int,
    ) -> Result<Vec<Distances<'_>>, RawHwlocError> {
        let kind = kind.unwrap_or(DistancesKind::empty());
        // SAFETY: - getter with the kind parameters curried away behaves as
        //           get_distances would expect
        //         - There are no invalid kind values for these search APIs
        //           since the kind flags only serves as a "one of" filter and
        //           DistancesKind exposes no invalid flags through proper
        //           version-gating
        //         - Other parameters are guaranteed valid per get_distances contract
        unsafe {
            self.get_distances_without_kind(getter_name, |topology, nr, distances, flags| {
                getter(topology, nr, distances, kind.bits(), flags)
            })
        }
    }

    /// Call one of the `hwloc_distances_get(_by)?` APIs, without the `kind`
    /// parameter
    ///
    /// Takes care of all parameters except for `kind`, which is not universal
    /// to these APIs and taken care of by [`get_distances()`]. So the last
    /// `c_ulong` here is the flags parameter.
    ///
    /// # Safety
    ///
    /// - `getter` must be an hwloc API with `hwloc_distances_get`-like
    ///   semantics, save for the absence of a kind parameter
    /// - This API is guaranteed to be passed valid (Topology, distances buffer
    ///   length, distance out-buffer pointer, flags) tuples
    ///
    /// [`get_distances()`]: Self::get_distances()
    #[allow(clippy::missing_errors_doc)]
    unsafe fn get_distances_without_kind(
        &self,
        getter_name: &'static str,
        mut getter: impl FnMut(
            hwloc_const_topology_t,
            *mut c_uint,
            *mut *mut hwloc_distances_s,
            c_ulong,
        ) -> c_int,
    ) -> Result<Vec<Distances<'_>>, RawHwlocError> {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized<'self_>(
            self_: &'self_ Topology,
            getter_name: &'static str,
            getter: &mut dyn FnMut(
                hwloc_const_topology_t,
                *mut c_uint,
                *mut *mut hwloc_distances_s,
                c_ulong,
            ) -> c_int,
        ) -> Result<Vec<Distances<'self_>>, RawHwlocError> {
            // Prepare to call hwloc
            let mut nr = 0;
            let mut call_ffi = |nr_mut, distances_out| {
                errors::call_hwloc_int_normal(getter_name, || {
                    // SAFETY: - Topology is trusted to contain a valid ptr
                    //           (type invariant)
                    //         - hwloc ops are trusted not to modify *const
                    //           parameters
                    //         - Per documentation, flags must be 0
                    //         - Correctness of nr_mut and distances_out is call
                    //           site dependent, see below
                    getter(self_.as_ptr(), nr_mut, distances_out, 0)
                })
            };

            // Allocate array of distances pointers
            // SAFETY: 0 elements + null buffer pointers is the correct way to
            //         request the buffer size to be allocated from hwloc
            call_ffi(&mut nr, ptr::null_mut())?;
            let mut distances_ptrs = vec![ptr::null_mut(); int::expect_usize(nr)];

            // Let hwloc fill the distances array
            let old_nr = nr;
            // SAFETY: - distances_ptrs is indeed an array of nr elements
            //         - Input array contents don't matter as this is an
            //           out-parameter
            call_ffi(&mut nr, distances_ptrs.as_mut_ptr())?;
            assert_eq!(nr, old_nr, "Inconsistent distances count from hwloc");

            // Wrap them into a safe interface
            Ok(distances_ptrs
                .into_iter()
                // SAFETY: If hwloc distance queries succeed, they are trusted
                //         to emit valid distances pointers
                .map(|raw| unsafe { Distances::wrap(self_, raw) })
                .collect())
        }
        polymorphized(self, getter_name, &mut getter)
    }
}

/// # Add distances between objects
//
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__add.html
#[cfg(feature = "hwloc-2_5_0")]
impl TopologyEditor<'_> {
    /// Create a new object distances matrix
    ///
    /// `kind` specifies the kind of distance. You should not use the
    /// [`HETEROGENEOUS_TYPES`] kind here, it will be set automatically.
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
    /// - [`InconsistentData`] if the number of distances returned by the
    ///   callback is not compatible with the number of objects (it should be
    ///   the square of it)
    /// - [`BadKind`] if the provided `kind` contains [`HETEROGENEOUS_TYPES`] or
    ///   several of the "FROM_" and "MEANS_" kinds
    /// - [`BadObjectsCount`] if less than 2 or more than `c_uint::MAX` objects
    ///   are returned by the callback(hwloc does not support such
    ///   configurations)
    /// - [`ForeignEndpoint`] if the callback returned objects that do not
    ///   belong to this topology
    /// - [`NameContainsNul`] if the provided `name` contains NUL chars
    ///
    /// [`InconsistentData`]: AddDistancesError::InconsistentData
    /// [`BadKind`]: AddDistancesError::BadKind
    /// [`BadObjectsCount`]: AddDistancesError::BadObjectsCount
    /// [`ForeignEndpoint`]: AddDistancesError::ForeignEndpoint
    /// [`HETEROGENEOUS_TYPES`]: DistancesKind::HETEROGENEOUS_TYPES
    /// [`NameContainsNul`]: AddDistancesError::NameContainsNul
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
        /// Polymorphized subset of this function (avoids generics code bloat)
        ///
        /// # Safety
        ///
        /// `objects` must contain pointers that are either null or point to
        /// valid objects within this topology.
        unsafe fn polymorphized(
            self_: &mut TopologyEditor<'_>,
            name: Option<&str>,
            kind: DistancesKind,
            flags: AddDistancesFlags,
            object_ptrs: &[*const hwloc_obj],
            distances: Vec<u64>,
        ) -> Result<(), HybridError<AddDistancesError>> {
            // Prepare arguments for C consumption and validate them
            let name = match name.map(LibcString::new).transpose() {
                Ok(name) => name,
                Err(NulError) => return Err(AddDistancesError::NameContainsNul.into()),
            };
            let name = name.map_or(ptr::null(), |lcs| lcs.borrow());
            //
            if !kind.is_valid(true) {
                return Err(AddDistancesError::BadKind(kind.into()).into());
            }
            let kind = kind.bits();
            //
            let create_add_flags = 0;
            let commit_flags = flags.bits();
            //
            if object_ptrs.len() < 2 {
                return Err(AddDistancesError::BadObjectsCount(object_ptrs.len()).into());
            }
            let Ok(nbobjs) = c_uint::try_from(object_ptrs.len()) else {
                return Err(AddDistancesError::BadObjectsCount(object_ptrs.len()).into());
            };
            let expected_distances_len = object_ptrs.len().pow(2);
            if distances.len() != expected_distances_len {
                return Err(AddDistancesError::InconsistentData.into());
            }
            let values = distances.as_ptr();

            // Create new empty distances structure
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - name is trusted to be a valid C string (type invariant)
            //         - hwloc ops are trusted not to modify *const parameters
            //         - hwloc ops are trusted to keep *mut parameters in a
            //           valid state unless stated otherwise
            //         - kind was validated to be correct
            //         - Per documentation, flags should be zero
            let handle = errors::call_hwloc_ptr_mut("hwloc_distances_add_create", || unsafe {
                hwlocality_sys::hwloc_distances_add_create(
                    self_.topology_mut_ptr(),
                    name,
                    kind,
                    create_add_flags,
                )
            })
            .map_err(HybridError::Hwloc)?;

            // Add objects to the distance structure
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - handle comes from a successful hwloc_distances_add_create run
            //         - hwloc ops are trusted not to modify *const parameters
            //         - hwloc ops are trusted to keep *mut parameters in a
            //           valid state unless stated otherwise
            //         - (nbobjs, objs) come from a single objects vec, which is
            //           still in scope and thus not liberated, and only contains
            //           objects from the active topology
            //         - values comes from a distances that's still in scope and
            //           whose length has been checked
            errors::call_hwloc_int_normal("hwloc_distances_add_values", || unsafe {
                hwlocality_sys::hwloc_distances_add_values(
                    self_.topology_mut_ptr(),
                    handle.as_ptr(),
                    nbobjs,
                    object_ptrs.as_ptr(),
                    values,
                    create_add_flags,
                )
            })
            .map_err(HybridError::Hwloc)?;

            // Finalize the distance structure and insert it into the topology
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - handle comes from a successful hwloc_distances_add_create run
            //         - hwloc ops are trusted to keep *mut parameters in a
            //           valid state unless stated otherwise
            //         - commit_flags only allows values supported by hwloc
            errors::call_hwloc_int_normal("hwloc_distances_add_commit", || unsafe {
                hwlocality_sys::hwloc_distances_add_commit(
                    self_.topology_mut_ptr(),
                    handle.as_ptr(),
                    commit_flags,
                )
            })
            .map_err(HybridError::Hwloc)?;
            Ok(())
        }

        // Run user callback, validate results, and translate them into
        // something that hwloc and the borrow checker will accept
        let topology = self.topology();
        let (objects, distances) = collect_objects_and_distances(topology);
        for obj in objects.iter().flatten().copied() {
            if !topology.contains(obj) {
                return Err(AddDistancesError::ForeignEndpoint(obj.into()).into());
            }
        }
        let object_ptrs =
            // SAFETY: TopologyObject is a repr(transparent) newtype of
            //         hwloc_obj, and the (ptr, len) tuple is consistent
            unsafe {
                std::slice::from_raw_parts(
                    objects.as_ptr().cast::<*const hwloc_obj>(),
                    objects.len()
                )
            };

        // Call the polymorphized version of this function
        // SAFETY: objects do belong to this topology
        unsafe { polymorphized(self, name, kind, flags, object_ptrs, distances) }
    }
}

#[cfg(feature = "hwloc-2_5_0")]
bitflags! {
    /// Flags to be given to [`TopologyEditor::add_distances()`]
    #[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
    #[doc(alias = "hwloc_distances_add_flag_e")]
    pub struct AddDistancesFlags: hwloc_distances_add_flag_e {
        /// Try to group objects based on the newly provided distance information
        ///
        /// This is ignored for distances between objects of different types.
        #[doc(alias = "HWLOC_DISTANCES_ADD_FLAG_GROUP")]
        const GROUP = HWLOC_DISTANCES_ADD_FLAG_GROUP;

        /// Like `GROUP`, but consider the distance values as inaccurate and
        /// relax the comparisons during the grouping algorithms. The actual
        /// accuracy may be modified through the HWLOC_GROUPING_ACCURACY
        /// environment variable (see [Environment
        /// Variables](https://hwloc.readthedocs.io/en/v2.9/envvar.html)).
        #[doc(alias = "HWLOC_DISTANCES_ADD_FLAG_GROUP_INACCURATE")]
        const GROUP_INACCURATE = HWLOC_DISTANCES_ADD_FLAG_GROUP | HWLOC_DISTANCES_ADD_FLAG_GROUP_INACCURATE;
    }
}
//
#[cfg(feature = "hwloc-2_5_0")]
crate::impl_arbitrary_for_bitflags!(AddDistancesFlags, hwloc_distances_add_flag_e);

/// Failed to add a new distance matrix to the topology
#[cfg(feature = "hwloc-2_5_0")]
#[derive(Clone, Debug, Eq, Error, Hash, PartialEq)]
pub enum AddDistancesError {
    /// Provided `kind` is invalid
    ///
    /// Either it contains [`DistancesKind::HETEROGENEOUS_TYPES`], which should
    /// not be set by you (it will be automatically set by hwloc through
    /// scanning of the provided object list), or it contains several of the
    /// "FROM_" and "MEANS_" kinds, which are mutually exclusive.
    #[cfg(feature = "hwloc-2_1_0")]
    #[error(transparent)]
    BadKind(#[from] FlagsError<DistancesKind>),

    /// Provided callback returned too many or too few objects
    ///
    /// hwloc only supports distances matrices involving 2 to [`c_uint::MAX`]
    /// objects.
    #[error("can't add distances between {0} objects")]
    BadObjectsCount(usize),

    /// Provided callback returned one or more enpoint objects that do not
    /// belong to this [`Topology`]
    #[error("distance endpoint {0}")]
    ForeignEndpoint(#[from] ForeignObjectError),

    /// Provided callback returned incompatible objects and distances arrays
    ///
    /// If we denote N the length of the objects array, the distances array
    /// should contain N.pow(2) elements.
    #[error("number of specified objects and distances isn't consistent")]
    InconsistentData,

    /// Provided `name` contains NUL chars
    #[error("distances name can't contain NUL chars")]
    NameContainsNul,
}
//
#[cfg(feature = "hwloc-2_5_0")]
impl From<DistancesKind> for AddDistancesError {
    fn from(value: DistancesKind) -> Self {
        Self::BadKind(value.into())
    }
}
//
#[cfg(feature = "hwloc-2_5_0")]
impl From<NulError> for AddDistancesError {
    fn from(_: NulError) -> Self {
        Self::NameContainsNul
    }
}
//
#[cfg(feature = "hwloc-2_5_0")]
impl<'topology> From<&'topology TopologyObject> for AddDistancesError {
    fn from(object: &'topology TopologyObject) -> Self {
        Self::ForeignEndpoint(object.into())
    }
}

/// # Remove distances between objects
//
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__remove.html
#[cfg(feature = "hwloc-2_3_0")]
impl TopologyEditor<'_> {
    /// Remove a single distances matrix from the topology
    ///
    /// The distances matrix to be removed can be selected using the
    /// `find_distances` callback.
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_distances_release_remove")]
    pub fn remove_distances(
        &mut self,
        find_distances: impl FnOnce(&Topology) -> Distances<'_>,
    ) -> Result<(), RawHwlocError> {
        /// Polymorphized subset of this function (avoids generics code bloat)
        ///
        /// # Safety
        ///
        /// `distances` must point to a valid set of distances from this
        /// topology, with no residual high-level wrapper remaining
        unsafe fn polymorphized(
            self_: &mut TopologyEditor<'_>,
            distances: NonNull<hwloc_distances_s>,
        ) -> Result<(), RawHwlocError> {
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - hwloc ops are trusted to keep *mut parameters in a valid
            //           state unless stated otherwise
            //         - distances is trusted per function contract
            errors::call_hwloc_int_normal("hwloc_distances_release_remove", || unsafe {
                hwlocality_sys::hwloc_distances_release_remove(
                    self_.topology_mut_ptr(),
                    distances.as_ptr(),
                )
            })
            .map(std::mem::drop)
        }

        // Run user callback and call polymorphized subset with result
        let distances = find_distances(self.topology()).into_inner();
        // SAFETY: distances is indeed a valid distances pointer with no
        //         remaining high level wrapper to bother us, since the
        //         Distances struct that we just discarded with into_inner
        //         assumed full ownership.
        unsafe { polymorphized(self, distances) }
    }

    /// Remove all distance matrices from a topology
    ///
    /// If these distances were used to group objects, these additional Group
    /// objects are not removed from the topology.
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_distances_remove")]
    pub fn remove_all_distances(&mut self) -> Result<(), RawHwlocError> {
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - Distances lifetime is bound by the host topology, so this
        //           will invalidate all Distances struct in existence and thus
        //           use-after-free cannot happen
        errors::call_hwloc_int_normal("hwloc_distances_remove", || unsafe {
            hwlocality_sys::hwloc_distances_remove(self.topology_mut_ptr())
        })
        .map(std::mem::drop)
    }

    /// Remove distance matrices for objects at a specific depth in the topology
    /// (if any)
    ///
    /// Identical to [`remove_all_distances()`], but only applies to one level
    /// of the topology.
    ///
    /// `depth` can be a [`Depth`], a [`NormalDepth`] or an [`usize`].
    ///
    /// [`remove_all_distances()`]: [`TopologyEditor::remove_all_distances()`]
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_distances_remove_by_depth")]
    pub fn remove_distances_at_depth<DepthLike>(
        &mut self,
        depth: DepthLike,
    ) -> Result<(), RawHwlocError>
    where
        DepthLike: TryInto<Depth>,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        /// Polymorphized subset of this function (avoids generics code bloat)
        fn polymorphized(
            self_: &mut TopologyEditor<'_>,
            depth: Depth,
        ) -> Result<(), RawHwlocError> {
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - Distances lifetime is bound by the host topology, so this
            //           will invalidate all Distances struct in existence and thus
            //           use-after-free cannot happen
            //         - hwloc should be able to handle any valid depth value
            errors::call_hwloc_int_normal("hwloc_distances_remove_by_depth", || unsafe {
                hwlocality_sys::hwloc_distances_remove_by_depth(
                    self_.topology_mut_ptr(),
                    depth.to_raw(),
                )
            })
            .map(std::mem::drop)
        }

        // There cannot be any object at a depth below the hwloc-supported max
        depth
            .try_into()
            .map_or_else(|_| Ok(()), |depth| polymorphized(self, depth))
    }

    /// Remove distance matrices for objects of a specific type in the topology
    ///
    /// Identical to [`remove_all_distances()`], but only applies to one level
    /// of the topology.
    ///
    /// [`remove_all_distances()`]: [`TopologyEditor::remove_all_distances()`]
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_distances_remove_by_type")]
    pub fn remove_distances_with_type(&mut self, ty: ObjectType) -> Result<(), RawHwlocError> {
        let topology = self.topology();
        if let Ok(depth) = topology.depth_for_type(ty) {
            self.remove_distances_at_depth(depth)?;
        } else {
            let depths = NormalDepth::iter_range(NormalDepth::MIN, topology.depth())
                .map(Depth::from)
                .filter(|&depth| {
                    let depth_ty = topology
                        .type_at_depth(depth)
                        .expect("A type should be present at this depth");
                    depth_ty == ty
                })
                .collect::<Vec<_>>();
            for depth in depths {
                self.remove_distances_at_depth(depth)?;
            }
        }
        Ok(())
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
/// hwloc may be found [in the hwloc
/// documentation](https://hwloc.readthedocs.io/en/v2.9/topoattrs.html#topoattrs_distances).
///
/// The matrix may also contain bandwidths between random sets of objects,
/// possibly provided by the user, as specified in the [`kind()`] attribute.
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
///
/// You cannot create an owned object of this type, it belongs to the topology.
///
/// [`kind()`]: Self::kind()
//
// --- Implementation details
//
// Upstream inspiration: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__distances__consult.html
//
// # Safety
//
// As a type invariant, the inner pointer is assumed to always point to a valid,
// owned, unaliased hwloc_distances_s struct. This means that...
//
// - The kind flags must be valid
// - objs array should contain nbobj hwloc_obj pointers, each of which should
//   point to a valid object belonging to "topology" or be null
// - values array should contain nbobj*nbobj values
#[doc(alias = "hwloc_distances_s")]
pub struct Distances<'topology> {
    /// Pointer to a valid hwloc_distances_s struct that originates from `topology`
    ///
    /// # Safety
    ///
    /// - The pointers objs and values should not be replaced, reallocated,
    ///   freed, etc and thus nbobj should not be changed either
    /// - Target topology objects should not be mutated, since this would
    ///   violate Rust aliasing rules as they come from &Topology
    /// - As a type invariant, target topology objects are assumed to be
    ///   valid and devoid of (mutable) aliases.
    inner: NonNull<hwloc_distances_s>,

    /// Topology from which `inner` was extracted
    topology: &'topology Topology,
}
//
impl<'topology> Distances<'topology> {
    /// Wrap a distance matrix from hwloc
    ///
    /// # Safety
    ///
    /// `inner` must be a valid and non-aliased `hwloc_distances_s` pointer
    /// originating from a query against `topology`
    pub(crate) unsafe fn wrap(
        topology: &'topology Topology,
        inner: *mut hwloc_distances_s,
    ) -> Self {
        let inner = NonNull::new(inner).expect("Got null distance matrix pointer from hwloc");
        // SAFETY: inner is assumed valid & unaliased per precondition
        let inner_ref = unsafe { inner.as_ref() };
        assert!(
            !inner_ref.objs.is_null(),
            "Got unexpected null object list in distances"
        );
        assert!(
            !inner_ref.values.is_null(),
            "Got unexpected null matrix in distances"
        );
        // SAFETY: inner is assumed to originate from topology per precondition
        Self { inner, topology }
    }

    /// Access the inner `hwloc_distances_s` (& version)
    ///
    /// # Safety
    ///
    /// - The pointers objs and values should not be reallocated, freed, etc
    /// - Target topology objects should not be mutated, since this would
    ///   violate Rust aliasing rules as they come from &Topology
    unsafe fn inner(&self) -> &hwloc_distances_s {
        // SAFETY: - inner is assumed valid and unaliased as a type invariant,
        //         - Its lifetime is assumed to be bound to self.topology and
        //           thus to self
        unsafe { self.inner.as_ref() }
    }

    /// Get the inner `hwloc_distances_s` (&mut version)
    ///
    /// # Safety
    ///
    /// - The pointers objs and values should not be replaced, reallocated,
    ///   freed, etc and thus nbobj should not be changed either
    /// - Target topology objects should not be mutated, since this would
    ///   violate Rust aliasing rules as they come from &Topology
    unsafe fn inner_mut(&mut self) -> &mut hwloc_distances_s {
        // SAFETY: - inner is assumed valid and unaliased as a type invariant,
        //         - Its lifetime is assumed to be bound to self.topology and
        //           thus to self
        unsafe { self.inner.as_mut() }
    }

    /// Release the inner `hwloc_distances_s` pointer
    ///
    /// This will result in a resource leak unless the pointer is subsequently
    /// liberated through `hwloc_distances_release` or
    /// `hwloc_distances_release_remove`.
    #[allow(unused)]
    pub(crate) fn into_inner(self) -> NonNull<hwloc_distances_s> {
        let inner = self.inner;
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
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - inner distances validity is assumed as a type invariant
        //         - inner is assumed to belong to topology as a type invariant
        //         - hwloc ops are trusted not to modify *const parameters
        //         - Successful output is assumed to be a valid C string, whose
        //           lifetime/mutability is bound to self.topology and thus to
        //           self
        //         - Topology has no internal mutability so holding an &-ref to
        //           it is enough to prevent mutation and invalidation
        unsafe {
            let name =
                hwlocality_sys::hwloc_distances_get_name(self.topology.as_ptr(), self.inner());
            (!name.is_null()).then(|| std::ffi::CStr::from_ptr(name))
        }
    }

    /// Kind of distance matrix
    #[doc(alias = "hwloc_distances_s::kind")]
    pub fn kind(&self) -> DistancesKind {
        // SAFETY: No invalid mutation of inner state occurs
        let result = DistancesKind::from_bits_truncate(unsafe { self.inner().kind });
        assert!(
            result.is_valid(false),
            "hwloc should not emit invalid kinds"
        );
        result
    }

    /// Number of objects described by the distance matrix
    ///
    /// # Safety
    ///
    /// Output can be trusted by unsafe code
    #[doc(alias = "hwloc_distances_s::nbobjs")]
    pub fn num_objects(&self) -> usize {
        // SAFETY: No invalid mutation of inner state occurs
        int::expect_usize(unsafe { self.inner().nbobj })
    }

    /// Object list pointer
    ///
    /// # Safety
    ///
    /// - Users must only overwrite this pointer with object pointers
    ///   originating from the same topology or null pointers
    /// - The objects should not be modified, only replaced.
    /// - Unsafe code can trust the fact that the initial topology pointers are
    ///   either null or valid and bound to self.topology
    unsafe fn raw_objects(&self) -> *mut *const TopologyObject
    // This is always true, I just made it a where clause so it's machine-checked
    where
        TopologyObject: TransparentNewtype<Inner = hwloc_obj>,
    {
        // SAFETY: - inner is assumed valid as a type invariant
        //         - cast is legal per TransparentNewtype contract
        //         - Mutation concerns are offloaded to caller via precondition
        unsafe { self.inner().objs.cast::<*const TopologyObject>() }
    }

    /// Objects described by the distance matrix
    ///
    /// These objects are not in any particular order, see methods below for
    /// easy ways to find objects and corresponding distance values.
    #[doc(alias = "hwloc_distances_s::objs")]
    pub fn objects(
        &self,
    ) -> impl DoubleEndedIterator<Item = Option<&TopologyObject>>
           + Clone
           + ExactSizeIterator
           + FusedIterator {
        // SAFETY: - inner is assumed valid as a type invariant, thus objs &
        //           num_objects() are trusted to be consistent, objs is assumed
        //           unaliased and bound to the lifetime of self.topology,
        //           and inner obj pointers are assumed to be valid and bound
        //           to the lifetime of self.topology and thus to self
        //         - No invalid mutation of inner state is possible in safe code
        //           using this API
        unsafe {
            let objs = self.raw_objects();
            let objs = std::slice::from_raw_parts(objs.cast_const(), self.num_objects());
            objs.iter().map(|ptr| ffi::deref_ptr(ptr))
        }
    }

    /// Find the row/column index of an object in the distance matrix
    ///
    /// This will return `None` if called with an object that does not belong
    /// to the active topology.
    ///
    /// Beware that calling this in a loop will result in a lot of duplicate
    /// work. It is a good idea to instead build a cache of indices for the
    /// objects that you are interested in, or to use the
    /// [`object_distances()`] iterator if your algorithm allows for it.
    ///
    /// [`object_distances()`]: Distances::object_distances()
    #[doc(alias = "hwloc_distances_obj_index")]
    pub fn object_idx(&self, obj: &TopologyObject) -> Option<usize> {
        self.objects()
            .enumerate()
            .find_map(|(idx, candidate)| std::ptr::eq(candidate?, obj).then_some(idx))
    }

    /// Access the raw array of object pointers
    ///
    /// # Safety
    ///
    /// - Users must only overwrite this pointer with object pointers
    ///   originating from the same topology or null pointers
    /// - The objects should not be modified, only replaced.
    /// - Unsafe code can trust the fact that the initial topology pointers are
    ///   either null or valid and bound to self.topology
    unsafe fn objects_mut(&mut self) -> &mut [*const TopologyObject] {
        // SAFETY: Allowed mutations are covered by the function's safety contract
        let objs = unsafe { self.raw_objects() };
        // SAFETY: inner is assumed valid as a type invariant, thus objs &
        //         num_objects() are trusted to be consistent, objs is assumed
        //         unaliased and bound to the lifetime of self.topology
        unsafe { std::slice::from_raw_parts_mut(objs, self.num_objects()) }
    }

    /// Convert `Option<&'topology TopologyObject>` to a `*const TopologyObject`
    /// for storage in [`objects_mut()`], validating that it does belong to the
    /// target [`Topology`] along the way.
    ///
    /// # Errors
    ///
    /// [`ForeignObject`] if the input object does not belong to the [`Topology`]
    ///
    /// # Safety
    ///
    /// Correctness can be trusted by unsafe code
    #[allow(clippy::option_if_let_else)]
    fn obj_to_checked_ptr(
        topology: &'topology Topology,
        obj: Option<&'topology TopologyObject>,
    ) -> Result<*const TopologyObject, ForeignObjectError> {
        if let Some(obj) = obj {
            if topology.contains(obj) {
                Ok(obj)
            } else {
                Err(obj.into())
            }
        } else {
            Ok(std::ptr::null())
        }
    }

    /// Replace the object at index `idx` with another
    ///
    /// If the new object is unrelated to the original one, you may want to
    /// adjust the distance matrix after doing this, which you can using one
    /// of the [`distances_mut()`], [`enumerate_distances_mut()`] and
    /// [`object_distances_mut()`] methods.
    ///
    /// # Errors
    ///
    /// [`ForeignObjectError`] if `new_object` does not belong to the same
    /// [`Topology`] as this distances matrix.
    ///
    /// [`distances_mut()`]: Distances::distances_mut()
    /// [`enumerate_distances_mut()`]: Distances::enumerate_distances_mut()
    /// [`object_distances_mut()`]: Distances::object_distances_mut()
    pub fn replace_object(
        &mut self,
        idx: usize,
        new_object: Option<&'topology TopologyObject>,
    ) -> Result<(), ForeignObjectError> {
        let topology = self.topology;
        // SAFETY: Overwriting with a valid topology object pointer from
        //         topology, as checked by obj_to_checked_ptr
        unsafe { self.objects_mut()[idx] = Self::obj_to_checked_ptr(topology, new_object)? };
        Ok(())
    }

    /// Replace all objects using the provided (index, object) -> object mapping
    ///
    /// This is more efficient than calling [`Distances::replace_object()`] in
    /// a loop and allows you to know what object you are replacing.
    ///
    /// # Errors
    ///
    /// [`ForeignObjectError`] if any of the [`TopologyObject`]s returned by
    /// `mapping` does not belong to the same [`Topology`] as this distances
    /// matrix.
    pub fn replace_objects(
        &mut self,
        mut mapping: impl FnMut(usize, Option<&TopologyObject>) -> Option<&'topology TopologyObject>,
    ) -> Result<(), ForeignObjectError> {
        let topology = self.topology;
        // SAFETY: Overwriting these with a valid topology object pointers from topology
        for (idx, obj) in unsafe { self.objects_mut().iter_mut().enumerate() } {
            // SAFETY: inner is assumed valid as a type invariant, thus inner
            //         obj pointers are assumed to be valid and bound to the
            //         lifetime of self.topology and thus to self
            let old_obj = unsafe { ffi::deref_ptr(obj) };
            let new_obj = mapping(idx, old_obj);
            // SAFETY: Overwriting with a valid topology object pointer from
            //         topology, as checked by obj_to_checked_ptr
            *obj = Self::obj_to_checked_ptr(topology, new_obj)?;
        }
        Ok(())
    }

    /// Number of distances
    ///
    /// # Safety
    ///
    /// Output can be trusted by unsafe code
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
    #[doc(alias = "hwloc_distances_s::values")]
    pub fn distances(&self) -> &[u64] {
        // SAFETY: - inner is assumed valid as a type invariant, thus values &
        //           num_distances() are trusted to be consistent. values is
        //           assumed to be  unaliased and bound to the lifetime of
        //           self.topology, and thus to that of self
        //         - No invalid mutation of inner state is possible in safe code
        //           using this API
        unsafe { std::slice::from_raw_parts(self.inner().values, self.num_distances()) }
    }

    /// Distances in sender-major order (mutable access)
    ///
    /// See also [`Distances::distances()`].
    pub fn distances_mut(&mut self) -> &mut [u64] {
        // SAFETY: - inner is assumed valid as a type invariant, thus values &
        //           num_distances() are trusted to be consistent. values is
        //           assumed to be  unaliased and bound to the lifetime of
        //           self.topology, and thus to that of self
        //         - No invalid mutation of inner state is possible in safe code
        //           using this API
        unsafe { std::slice::from_raw_parts_mut(self.inner_mut().values, self.num_distances()) }
    }

    /// Iteration over ((sender index, receiver index), distance) tuples
    ///
    /// See also [`Distances::distances()`].
    pub fn enumerate_distances(
        &self,
    ) -> impl DoubleEndedIterator<Item = ((usize, usize), u64)>
           + Clone
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
    ///
    /// # Safety
    ///
    /// Output can be trusted by unsafe code
    pub fn enumerate_distances_mut(
        &mut self,
    ) -> impl DoubleEndedIterator<Item = ((usize, usize), &mut u64)> + ExactSizeIterator + FusedIterator
    {
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
    ) -> impl FusedIterator<Item = ((Option<&TopologyObject>, Option<&TopologyObject>), u64)> + Clone
    {
        self.objects()
            .flat_map(|obj1| self.objects().map(move |obj2| (obj1, obj2)))
            .zip(self.distances().iter().copied())
    }

    /// Iteration over ((sender, receiver), &mut distance) tuples
    ///
    /// See also [`Distances::distances()`].
    pub fn object_distances_mut(
        &mut self,
    ) -> impl FusedIterator<Item = ((Option<&TopologyObject>, Option<&TopologyObject>), &mut u64)>
    {
        // SAFETY: This function does not mutate the objects in any way
        let objs = unsafe { self.raw_objects() };
        // SAFETY: - inner is assumed valid as a type invariant, thus objs &
        //           num_objects() are trusted to be consistent, objs is assumed
        //           unaliased and bound to the lifetime of self.topology
        let objects = unsafe { std::slice::from_raw_parts(objs, self.num_objects()) };
        self.enumerate_distances_mut()
            .map(move |((sender_idx, receiver_idx), distance)| {
                // SAFETY: - enumerate_distances_mut will only produces valid
                //           object indices in the 0..num_objects range
                //         - inner is assumed valid, so inner.objs are assumed
                //           to be either null or valid, unaliased and bound to
                //           the self.topology lifetime
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
    /// the distance from the second to the first input object, if known.
    ///
    /// Will return `None` if one of the objects doesn't belong to the host
    /// topology.
    ///
    /// This is a rather expensive operation. If you find yourself needing to
    /// do it in a loop, consider rearchitecturing your workflow around object
    /// indices or [`object_distances()`].
    ///
    /// [`object_distances()`]: Distances::object_distances()
    #[doc(alias = "hwloc_distances_obj_pair_values")]
    pub fn object_pair_distance(
        &self,
        (obj1, obj2): (&TopologyObject, &TopologyObject),
    ) -> Option<(u64, u64)> {
        let idx1 = self.object_idx(obj1)?;
        let idx2 = self.object_idx(obj2)?;
        let num_objects = self.num_objects();
        let distances = self.distances();
        // SAFETY: Will produce indices smaller than the square of the number of
        //         objects in the distances matrix, which is the number of
        //         distances in the matrix
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
    ///
    /// # Errors
    ///
    /// [`TransformError`] if one attempts to use
    /// [`DistancesTransform::RemoveNone`] to reduce the number of objects to
    /// <2, which is forbidden.
    #[cfg(feature = "hwloc-2_5_0")]
    #[doc(alias = "hwloc_distances_transform")]
    pub fn transform(
        &mut self,
        transform: DistancesTransform,
    ) -> Result<(), HybridError<TransformError>> {
        use errno::Errno;
        use libc::EINVAL;
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - inner pointer validity is assumed as a type invariant
        //         - inner is assumed to belong to topology as a type invariant
        //         - hwloc ops are trusted not to modify *const parameters
        //         - hwloc ops are trusted to keep *mut parameters in a
        //           valid state unless stated otherwise
        //         - Any supported transform value is accepted by hwloc
        //         - Per documentation, transform attr/flags must be NULL/0
        errors::call_hwloc_int_normal("hwloc_distances_transform", || unsafe {
            hwlocality_sys::hwloc_distances_transform(
                self.topology.as_ptr(),
                self.inner_mut(),
                transform.into(),
                std::ptr::null_mut(),
                0,
            )
        })
        .map(std::mem::drop)
        .map_err(|e| match e {
            RawHwlocError {
                errno: Some(Errno(EINVAL)),
                ..
            } if transform == DistancesTransform::RemoveNone => HybridError::Rust(TransformError),
            other => HybridError::Hwloc(other),
        })
    }
}
//
impl Debug for Distances<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;

        let mut debug = f.debug_struct("Distances");
        #[cfg(feature = "hwloc-2_1_0")]
        debug.field("name", &self.name());
        debug
            .field("kind", &self.kind())
            .field("objects", &self.objects().collect::<Vec<_>>());

        let mut distances_display = String::new();
        let mut last_row = usize::MAX;
        for ((row, _col), distance) in self.enumerate_distances() {
            if row == last_row {
                distances_display.push('\t');
            } else {
                distances_display.push_str("\n\t");
                last_row = row;
            }
            write!(distances_display, "{distance}").unwrap();
        }
        debug.field("distances", &distances_display).finish()
    }
}
//
impl Drop for Distances<'_> {
    #[doc(alias = "hwloc_distances_release")]
    fn drop(&mut self) {
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - inner pointer validity is assumed as a type invariant
        //         - inner is assumed to belong to topology as a type invariant
        //         - hwloc ops are trusted not to modify *const parameters
        //         - Distances will not be usable again after Drop
        unsafe {
            hwlocality_sys::hwloc_distances_release(self.topology.as_ptr(), self.inner.as_ptr())
        }
    }
}
//
impl Index<(usize, usize)> for Distances<'_> {
    type Output = u64;

    fn index(&self, idx: (usize, usize)) -> &u64 {
        // SAFETY: index validity is checked by checked_idx
        unsafe { self.distances().get_unchecked(self.checked_idx(idx)) }
    }
}
//
impl IndexMut<(usize, usize)> for Distances<'_> {
    fn index_mut(&mut self, idx: (usize, usize)) -> &mut u64 {
        let idx = self.checked_idx(idx);
        // SAFETY: index validity is checked by checked_idx
        unsafe { self.distances_mut().get_unchecked_mut(idx) }
    }
}
//
// SAFETY: No internal mutability
unsafe impl Send for Distances<'_> {}
//
// SAFETY: No internal mutability
unsafe impl Sync for Distances<'_> {}

bitflags! {
    /// Kinds of distance matrices
    ///
    /// A kind with a name starting with "FROM_" specifies where the distance
    /// information comes from, if known.
    ///
    /// A kind with a name starting with "MEANS_" specifies whether values are
    /// latencies or bandwidths, if applicable.
    ///
    /// Only one of the "FROM_" and "MEANS_" kinds should be present.
    #[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
    #[doc(alias = "hwloc_distances_kind_e")]
    pub struct DistancesKind: hwloc_distances_kind_e {
        /// These distances were obtained from the operating system or hardware
        #[doc(alias = "HWLOC_DISTANCES_KIND_FROM_OS")]
        const FROM_OS = HWLOC_DISTANCES_KIND_FROM_OS;

        /// These distances were provided by the user
        #[doc(alias = "HWLOC_DISTANCES_KIND_FROM_USER")]
        const FROM_USER = HWLOC_DISTANCES_KIND_FROM_USER;

        /// Distance values are similar to latencies between objects
        ///
        /// Values are smaller for closer objects, hence minimal on the diagonal
        /// of the matrix (distance between an object and itself).
        ///
        /// It could also be the number of network hops between objects, etc.
        #[doc(alias = "HWLOC_DISTANCES_KIND_MEANS_LATENCY")]
        const MEANS_LATENCY = HWLOC_DISTANCES_KIND_MEANS_LATENCY;

        /// Distance values are similar to bandwidths between objects
        ///
        /// Values are higher for closer objects, hence maximal on the diagonal
        /// of the matrix (distance between an object and itself).
        ///
        /// Such values are currently ignored for distance-based grouping.
        #[doc(alias = "HWLOC_DISTANCES_KIND_MEANS_BANDWIDTH")]
        const MEANS_BANDWIDTH = HWLOC_DISTANCES_KIND_MEANS_BANDWIDTH;

        /// This distances structure covers objects of different types
        ///
        /// This may apply to the "NVLinkBandwidth" structure in presence of a
        /// NVSwitch or POWER processor NVLink port.
        #[cfg(feature = "hwloc-2_1_0")]
        #[doc(alias = "HWLOC_DISTANCES_KIND_HETEROGENEOUS_TYPES")]
        const HETEROGENEOUS_TYPES = HWLOC_DISTANCES_KIND_HETEROGENEOUS_TYPES;
    }
}
//
impl DistancesKind {
    /// Truth that this kind is in a valid state
    #[allow(unused_mut, clippy::let_and_return, unused_variables)]
    pub(crate) fn is_valid(self, writing: bool) -> bool {
        let mut result = !((self.contains(Self::FROM_OS) && self.contains(Self::FROM_USER))
            || (self.contains(Self::MEANS_LATENCY) && self.contains(Self::MEANS_BANDWIDTH)));

        #[cfg(feature = "hwloc-2_1_0")]
        {
            result &= !(writing && self.contains(Self::HETEROGENEOUS_TYPES));
        }

        result
    }
}
//
#[cfg(any(test, feature = "proptest"))]
crate::impl_arbitrary_for_bitflags!(DistancesKind, hwloc_distances_kind_e);

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
    Sequence,
)]
#[doc(alias = "hwloc_distances_transform_e")]
#[repr(u32)]
pub enum DistancesTransform {
    /// Remove `None` objects from the distances structure.
    ///
    /// Every object that was replaced with `None` in [`Distances::objects()`]
    /// is removed and the matrix is updated accordingly.
    ///
    /// At least 2 objects must remain, otherwise [`Distances::transform()`]
    /// will fail.
    ///
    /// [`Distances::kind()`] will be updated with or without
    /// [`HETEROGENEOUS_TYPES`] according to the remaining objects.
    ///
    /// [`HETEROGENEOUS_TYPES`]: DistancesKind::HETEROGENEOUS_TYPES
    #[doc(alias = "HWLOC_DISTANCES_TRANSFORM_REMOVE_NULL")]
    RemoveNone = HWLOC_DISTANCES_TRANSFORM_REMOVE_NULL,

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
    BandwidthToLinkCount = HWLOC_DISTANCES_TRANSFORM_LINKS,

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
    MergeSwitchPorts = HWLOC_DISTANCES_TRANSFORM_MERGE_SWITCH_PORTS,

    /// Apply a transitive closure to the matrix to connect objects across
    /// switches.
    ///
    /// This currently only applies to GPUs and NVSwitches in the
    /// NVLinkBandwidth matrix.
    ///
    /// All pairs of GPUs will be reported as directly connected.
    #[doc(alias = "HWLOC_DISTANCES_TRANSFORM_TRANSITIVE_CLOSURE")]
    TransitiveSwitchClosure = HWLOC_DISTANCES_TRANSFORM_TRANSITIVE_CLOSURE,
}
//
#[cfg(feature = "hwloc-2_5_0")]
crate::impl_arbitrary_for_sequence!(DistancesTransform);

/// Error returned when attempting to remove all distances using
/// [`DistancesTransform::RemoveNone`].
#[cfg(feature = "hwloc-2_5_0")]
#[derive(Copy, Clone, Debug, Default, Eq, Error, Hash, PartialEq)]
#[error("can't empty a distance matrix using DistancesTransform::RemoveNone")]
pub struct TransformError;
