//! Object distance matrices
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

#[cfg(doc)]
use crate::object::depth::NormalDepth;
#[cfg(feature = "hwloc-2_3_0")]
use crate::topology::editor::TopologyEditor;
#[cfg(feature = "hwloc-2_1_0")]
use crate::{errors::NulError, ffi::string::LibcString};
use crate::{
    errors::{self, FlagsError, ForeignObjectError, HybridError, RawHwlocError},
    ffi::{self, int, transparent::TransparentNewtype},
    object::{depth::Depth, types::ObjectType, TopologyObject, TopologyObjectID},
    topology::Topology,
};
use bitflags::bitflags;
#[cfg(feature = "hwloc-2_1_0")]
use hwlocality_sys::HWLOC_DISTANCES_KIND_HETEROGENEOUS_TYPES;
use hwlocality_sys::{
    hwloc_const_topology_t, hwloc_distances_kind_e, hwloc_distances_s, hwloc_obj, hwloc_topology,
    HWLOC_DISTANCES_KIND_FROM_OS, HWLOC_DISTANCES_KIND_FROM_USER,
    HWLOC_DISTANCES_KIND_MEANS_BANDWIDTH, HWLOC_DISTANCES_KIND_MEANS_LATENCY,
};
#[cfg(feature = "hwloc-2_5_0")]
use hwlocality_sys::{
    hwloc_distances_add_flag_e, hwloc_distances_transform_e, HWLOC_DISTANCES_TRANSFORM_LINKS,
    HWLOC_DISTANCES_TRANSFORM_MERGE_SWITCH_PORTS, HWLOC_DISTANCES_TRANSFORM_REMOVE_NULL,
    HWLOC_DISTANCES_TRANSFORM_TRANSITIVE_CLOSURE,
};
#[cfg(feature = "hwloc-3_0_0")]
use hwlocality_sys::{HWLOC_DISTANCES_ADD_FLAG_GROUP, HWLOC_DISTANCES_ADD_FLAG_GROUP_INACCURATE};
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
use strum::{EnumCount, EnumIter, FromRepr};
#[cfg(feature = "hwloc-2_5_0")]
use thiserror::Error;

/// # Retrieve distances between objects
//
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/stable/group__hwlocality__distances__get.html
impl Topology {
    /// Retrieve distance matrices from the topology
    ///
    /// Filtering may be applied using the `kind` parameter: if it contains some
    /// [`DistanceKind`]`::FROM_xyz` options, only distance matrices matching
    /// one of them is returned. The same applies for `MEANS_xyz` options. If
    /// `kind` is left as `DistanceKind::empty()`, all distance matrices are
    /// returned.
    #[cfg_attr(feature = "hwloc-2_1_0", doc = "")]
    #[cfg_attr(
        feature = "hwloc-2_1_0",
        doc = "[`HETEROGENEOUS_TYPES`](DistanceKind::HETEROGENEOUS_TYPES) cannot be used as a filter here."
    )]
    ///
    ///
    /// # Errors
    ///
    /// [`FlagsError`] if the specified `kind` contains an invalid pattern, such
    /// as multiple `FROM_xyz` or `MEANS_xyz` options.
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_distances_get")]
    pub fn distances(
        &self,
        kind: DistanceKind,
    ) -> Result<Vec<DistanceMatrix<'_>>, HybridError<FlagsError<DistanceKind>>> {
        // SAFETY: - By definition, it's valid to pass hwloc_distances_get
        //         - Parameters are guaranteed valid per get_distances
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

    /// Retrieve distance matrices that only contain objects at a specific depth
    /// in the topology
    ///
    /// Similar to [`distances()`](Topology::distances()) with an additional
    /// `depth` filter.
    ///
    /// `depth` can be a [`Depth`], a [`NormalDepth`] or an [`usize`].
    ///
    /// As of hwloc v2.12.1, querying distances at the depth of
    /// [`Group`](ObjectType::Group) objects is unfortunately not fully
    /// supported by hwloc. It may error out if such objects exist at multiple
    /// depths in the topology.
    ///
    /// # Errors
    ///
    /// [`FlagsError`] if the specified `kind` contains multiple `FROM_xyz` or
    /// `MEANS_xyz` options.
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_distances_get_by_depth")]
    pub fn distances_at_depth<DepthLike>(
        &self,
        kind: DistanceKind,
        depth: DepthLike,
    ) -> Result<Vec<DistanceMatrix<'_>>, HybridError<FlagsError<DistanceKind>>>
    where
        DepthLike: TryInto<Depth>,
        <DepthLike as TryInto<Depth>>::Error: Debug,
    {
        /// Polymorphized version of this function (avoids generics code bloat)
        fn polymorphized(
            self_: &Topology,
            kind: DistanceKind,
            depth: Depth,
        ) -> Result<Vec<DistanceMatrix<'_>>, HybridError<FlagsError<DistanceKind>>> {
            // There cannot be any object at a depth below the topology depth
            if matches!(depth, Depth::Normal(depth) if depth >= self_.depth()) {
                return Ok(Vec::new());
            }

            // SAFETY: - hwloc_distances_get_by_depth with the depth parameter
            //           curried away behaves indeed like hwloc_distances_get
            //         - Depth only allows valid depth values to exist
            //         - Other parameters are guaranteed valid per
            //           get_distances contract
            unsafe {
                self_.get_distances(
                    kind,
                    "hwloc_distances_get_by_depth",
                    |topology, nr, distances, kind, flags| {
                        hwlocality_sys::hwloc_distances_get_by_depth(
                            topology,
                            depth.to_hwloc(),
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

    /// Retrieve distance matrices that only contain objects with type `ty`
    ///
    /// Similar to [`distances()`](Topology::distances()) with an additional
    /// type filter.
    ///
    /// # Errors
    ///
    /// [`FlagsError`] if the specified `kind` contains multiple `FROM_xyz` or
    /// `MEANS_xyz` options.
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_distances_get_by_type")]
    pub fn distances_with_type(
        &self,
        kind: DistanceKind,
        ty: ObjectType,
    ) -> Result<Vec<DistanceMatrix<'_>>, HybridError<FlagsError<DistanceKind>>> {
        // SAFETY: - hwloc_distances_get_by_type with the type parameter curried
        //           away behaves indeed like hwloc_distances_get
        //         - No invalid ObjectType value should be exposed by this
        //           binding (to enable values from newer releases of hwloc, you
        //           must configure the build to require newer hwloc DLLs)
        //         - Other parameters are guaranteed valid per
        //           get_distances contract
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

    /// Retrieve distance matrices with the given name
    ///
    /// Usually only one distance matrix will match a given name.
    ///
    /// Names of distance matrices currently created by hwloc may be found [in
    /// the hwloc
    /// documentation](https://hwloc.readthedocs.io/en/stable/topoattrs.html#topoattrs_distances).
    ///
    /// # Errors
    ///
    /// - [`NulError`] if `name` contains NUL chars.
    #[cfg(feature = "hwloc-2_1_0")]
    #[doc(alias = "hwloc_distances_get_by_name")]
    pub fn distances_with_name(
        &self,
        name: &str,
    ) -> Result<Vec<DistanceMatrix<'_>>, HybridError<NulError>> {
        let name = LibcString::new(name)?;
        // SAFETY: - hwloc_distances_get_by_name with the name parameter curried
        //           away behaves indeed like hwloc_distances_get
        //         - `name` is a valid c string by construction of LibcString
        //         - Other parameters are guaranteed valid per
        //           get_distances_without_kind contract
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
    ///
    /// # Errors
    ///
    /// [`FlagsError`] if the specified `kind` contains an invalid pattern, such
    /// as multiple `FROM_xyz` or `MEANS_xyz` options.
    #[allow(clippy::missing_errors_doc)]
    unsafe fn get_distances(
        &self,
        kind: DistanceKind,
        getter_name: &'static str,
        mut getter: impl FnMut(
            *const hwloc_topology,
            *mut c_uint,
            *mut *mut hwloc_distances_s,
            hwloc_distances_kind_e,
            c_ulong,
        ) -> c_int,
    ) -> Result<Vec<DistanceMatrix<'_>>, HybridError<FlagsError<DistanceKind>>> {
        if !kind.is_valid(DistanceKindUsage::Query) {
            return Err(FlagsError::from(kind).into());
        }
        // SAFETY: - getter with the kind parameters curried away behaves as
        //           get_distances would expect
        //         - There are no invalid kind values for these search APIs
        //           since the kind flags only serves as a "one of" filter and
        //           DistanceKind exposes no invalid flags through proper
        //           version-gating
        //         - Other parameters are guaranteed valid per
        //           get_distances_without_kind contract
        unsafe {
            self.get_distances_without_kind(getter_name, |topology, nr, distances, flags| {
                getter(topology, nr, distances, kind.bits(), flags)
            })
            .map_err(HybridError::Hwloc)
        }
    }

    /// Call one of the `hwloc_distances_get(_by)?` APIs, without the `kind`
    /// parameter
    ///
    /// Takes care of all parameters except for `kind`, which is not universal
    /// to these APIs and taken care of by
    /// [`get_distances()`](Self::get_distances()). So the last
    /// `c_ulong` here is the flags parameter.
    ///
    /// # Safety
    ///
    /// - `getter` must be an hwloc API with `hwloc_distances_get`-like
    ///   semantics, save for the absence of a kind parameter
    /// - This API is guaranteed to be passed valid (Topology, distances buffer
    ///   length, distance out-buffer pointer, flags) tuples
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
    ) -> Result<Vec<DistanceMatrix<'_>>, RawHwlocError> {
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
        ) -> Result<Vec<DistanceMatrix<'self_>>, RawHwlocError> {
            // Prepare to call hwloc
            let mut nr = 0;
            let mut call_ffi = |nr_mut, distances_out| {
                errors::call_hwloc_zero_or_minus1(getter_name, || {
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
                .map(|raw| unsafe { DistanceMatrix::wrap(self_, raw) })
                .collect())
        }
        polymorphized(self, getter_name, &mut getter)
    }
}

/// # Add distances between objects
//
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/stable/group__hwlocality__distances__add.html
#[cfg(feature = "hwloc-2_5_0")]
impl TopologyEditor<'_> {
    /// Create a new object distance matrix
    ///
    /// `name` is optional and can be used to clarify what the distances mean.
    ///
    /// `kind` specifies the kind of distance you are specifying. You should not
    /// use the [`HETEROGENEOUS_TYPES`] kind here, it will be set automatically.
    ///
    /// `flags` can be used to request the grouping of existing objects based on
    /// distance.
    ///
    /// The `collect_endpoints_and_values` callback should query the topology to
    /// collect references to the objects of interest, and produce the
    /// corresponding distance values. If there are N endpoint objects, then
    /// there should be N.pow(2) distance values.
    ///
    /// It is legal for some topology objects to appear multiple times as
    /// endpoints of the distance matrix. This is how one can describe the
    /// existence of multiple links between two objects.
    ///
    /// Distance values must follow the following requirements:
    ///
    /// - They are provided in sender-major order: the distance from object 0 to
    ///   object 1, then object 0 to object 2, ... all the way to object N, and
    ///   then from object 1 to object 0, and so on.
    /// - They must be consistent with the `_MEANS` kind, if specified: diagonal
    ///   values (from an object to itself) must be minimal for latency-like
    ///   distances, and maximal for bandwidh-like distances.
    ///
    /// # Errors
    ///
    /// - [`NameContainsNul`] if the provided `name` contains NUL chars
    /// - [`BadKind`] if the provided `kind` contains [`HETEROGENEOUS_TYPES`] or
    ///   several of the "FROM_" and "MEANS_" kinds
    /// - [`BadEndpointCount`] if less than 2 or more than `c_uint::MAX` objects
    ///   are returned by the callback (hwloc does not support such
    ///   configurations)
    /// - [`ForeignEndpoint`] if the callback returned objects that do not
    ///   belong to this topology
    /// - [`InconsistentDiagonal`] if a `MEANS_` kind is specified and the
    ///   diagonal values are not consistent with it (minimal for
    ///   [`MEANS_LATENCY`], maximal for [`MEANS_BANDWIDTH`])
    /// - [`InconsistentLen`] if the number of distance values returned by the
    ///   callback is not compatible with the number of objects (it should be
    ///   the square of it)
    ///
    /// [`BadEndpointCount`]: AddDistanceMatrixError::BadEndpointCount
    /// [`BadKind`]: AddDistanceMatrixError::BadKind
    /// [`ForeignEndpoint`]: AddDistanceMatrixError::ForeignEndpoint
    /// [`HETEROGENEOUS_TYPES`]: DistanceKind::HETEROGENEOUS_TYPES
    /// [`InconsistentDiagonal`]: AddDistanceMatrixError::InconsistentDiagonal
    /// [`InconsistentLen`]: AddDistanceMatrixError::InconsistentLen
    /// [`MEANS_BANDWIDTH`]: DistanceKind::MEANS_BANDWIDTH
    /// [`MEANS_LATENCY`]: DistanceKind::MEANS_LATENCY
    /// [`NameContainsNul`]: AddDistanceMatrixError::NameContainsNul
    #[doc(alias = "hwloc_distances_add_create")]
    #[doc(alias = "hwloc_distances_add_values")]
    #[doc(alias = "hwloc_distances_add_commit")]
    pub fn add_distance_matrix(
        &mut self,
        name: Option<&str>,
        kind: DistanceKind,
        flags: AddDistanceMatrixFlags,
        collect_endpoints_and_values: impl FnOnce(&Topology) -> (Vec<&TopologyObject>, Vec<u64>),
    ) -> Result<(), HybridError<AddDistanceMatrixError>> {
        /// Polymorphized subset of this function (avoids generics code bloat)
        ///
        /// # Safety
        ///
        /// `objects` must contain pointers that are either null or point to
        /// valid objects within this topology.
        unsafe fn polymorphized(
            self_: &mut TopologyEditor<'_>,
            name: Option<&str>,
            kind: DistanceKind,
            flags: AddDistanceMatrixFlags,
            objs: &[*const hwloc_obj],
            values: Vec<u64>,
        ) -> Result<(), HybridError<AddDistanceMatrixError>> {
            // Prepare arguments for C consumption and validate them
            let name = match name.map(LibcString::new).transpose() {
                Ok(name) => name,
                Err(NulError) => return Err(AddDistanceMatrixError::NameContainsNul.into()),
            };
            let name = name.as_ref().map_or(ptr::null(), LibcString::borrow);
            //
            if !kind.is_valid(DistanceKindUsage::AddEdit) {
                return Err(AddDistanceMatrixError::BadKind(kind.into()).into());
            }
            //
            let create_add_flags = 0;
            let commit_flags = flags.bits();
            //
            if objs.len() < 2 {
                return Err(AddDistanceMatrixError::BadEndpointCount(objs.len()).into());
            }
            let Ok(nbobjs) = c_uint::try_from(objs.len()) else {
                return Err(AddDistanceMatrixError::BadEndpointCount(objs.len()).into());
            };
            let expected_values_len = objs.len().pow(2);
            if values.len() != expected_values_len {
                return Err(AddDistanceMatrixError::InconsistentLen.into());
            }
            //
            type ExtremalValue = for<'a> fn(std::slice::Iter<'a, u64>) -> Option<&'a u64>;
            let check_value_kind_consistency =
                |means_kind: DistanceKind, diagonal_value: ExtremalValue| {
                    if kind.contains(means_kind) {
                        for (origin_idx, values) in values.chunks(objs.len()).enumerate() {
                            let expected = *diagonal_value(values.iter())
                                .expect("There are distance values if control reaches this point");
                            if values[origin_idx] != expected {
                                return Err(
                                    AddDistanceMatrixError::InconsistentDiagonal(kind).into()
                                );
                            }
                        }
                    }
                    Ok::<_, HybridError<AddDistanceMatrixError>>(())
                };
            check_value_kind_consistency(DistanceKind::MEANS_LATENCY, |iter| iter.min())?;
            check_value_kind_consistency(DistanceKind::MEANS_BANDWIDTH, |iter| iter.max())?;
            //
            let kind = kind.bits();
            let values = values.as_ptr();

            // Create a new empty distances structure
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

            // Add objects to the distances structure
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
            errors::call_hwloc_zero_or_minus1("hwloc_distances_add_values", || unsafe {
                hwlocality_sys::hwloc_distances_add_values(
                    self_.topology_mut_ptr(),
                    handle.as_ptr(),
                    nbobjs,
                    objs.as_ptr(),
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
            errors::call_hwloc_zero_or_minus1("hwloc_distances_add_commit", || unsafe {
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
        let (endpoints, values) = collect_endpoints_and_values(topology);
        for obj in endpoints.iter().copied() {
            if !topology.contains(obj) {
                return Err(AddDistanceMatrixError::ForeignEndpoint(obj.into()).into());
            }
        }
        let endpoint_ptrs =
            // SAFETY: - TopologyObject is a repr(transparent) newtype of
            //           hwloc_obj so &TopologyObject matches *const hwloc_obj
            //           in layout and semantics.
            //         - The output slice covers the same memory span as the
            //           original objects vec, so if the length was right for
            //           the former, it is right for the latter too.
            unsafe {
                std::slice::from_raw_parts(
                    endpoints.as_ptr().cast::<*const hwloc_obj>(),
                    endpoints.len()
                )
            };

        // Call the polymorphized version of this function
        // SAFETY: endpoints do belong to this topology
        unsafe { polymorphized(self, name, kind, flags, endpoint_ptrs, values) }
    }
}

#[cfg(feature = "hwloc-2_5_0")]
bitflags! {
    /// Flags to be given to [`TopologyEditor::add_distance_matrix()`]
    #[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
    #[doc(alias = "hwloc_distances_add_flag_e")]
    pub struct AddDistanceMatrixFlags: hwloc_distances_add_flag_e {
        /// Try to group objects based on the newly provided distance information
        ///
        /// Grouping is only performed when the distance matrix contains
        /// latencies, and when all objects are of the same type.
        ///
        /// Disabled for older versions of hwloc as a workaround for [upstream
        /// bug #728](https://github.com/open-mpi/hwloc/issues/728).
        #[cfg(feature = "hwloc-3_0_0")]
        #[doc(alias = "HWLOC_DISTANCES_ADD_FLAG_GROUP")]
        const GROUP = HWLOC_DISTANCES_ADD_FLAG_GROUP;

        /// Like `GROUP`, but consider the distance values as inaccurate and
        /// relax the comparisons during the grouping algorithms. The actual
        /// accuracy may be modified through the HWLOC_GROUPING_ACCURACY
        /// environment variable (see [Environment
        /// Variables](https://hwloc.readthedocs.io/en/stable/envvar.html)).
        ///
        /// Disabled for older versions of hwloc as a workaround for [upstream
        /// bug #728](https://github.com/open-mpi/hwloc/issues/728).
        #[cfg(feature = "hwloc-3_0_0")]
        #[doc(alias = "HWLOC_DISTANCES_ADD_FLAG_GROUP_INACCURATE")]
        const GROUP_INACCURATE = HWLOC_DISTANCES_ADD_FLAG_GROUP | HWLOC_DISTANCES_ADD_FLAG_GROUP_INACCURATE;
    }
}
//
#[cfg(feature = "hwloc-2_5_0")]
crate::impl_arbitrary_for_bitflags!(AddDistanceMatrixFlags, hwloc_distances_add_flag_e);

/// Failed to add a new distance matrix to the topology
#[cfg(feature = "hwloc-2_5_0")]
#[derive(Clone, Debug, Eq, Error, Hash, PartialEq)]
pub enum AddDistanceMatrixError {
    /// Provided `name` contains NUL chars
    #[error("distance matrix name can't contain NUL chars")]
    NameContainsNul,

    /// Provided `kind` is invalid
    ///
    /// Either it contains [`DistanceKind::HETEROGENEOUS_TYPES`], which should
    /// not be set by you (it will be automatically set by hwloc through
    /// scanning of the provided object list), or it contains several of the
    /// "FROM_" and "MEANS_" kinds, which are mutually exclusive.
    #[error(transparent)]
    BadKind(#[from] FlagsError<DistanceKind>),

    /// Provided callback returned too many or too few objects
    ///
    /// hwloc only supports distance matrices involving 2 to [`c_uint::MAX`]
    /// objects.
    #[error("can't add distances between {0} objects")]
    BadEndpointCount(usize),

    /// Provided callback returned one or more enpoint objects that do not
    /// belong to this [`Topology`]
    #[error("distance endpoint {0}")]
    ForeignEndpoint(#[from] ForeignObjectError),

    /// Provided callback returned distance values that are not specified with
    /// the specified distance kind
    ///
    /// If `kind` contains [`MEANS_LATENCY`](DistanceKind::MEANS_LATENCY),
    /// diagonal distance values (from an object to itself) should be lower than
    /// other distances from the same origin.
    ///
    /// If `kind` contains [`MEANS_BANDWIDTH`](DistanceKind::MEANS_BANDWIDTH),
    /// diagonal distance values should be higher than other distances from the
    /// same origin.
    #[error("diagonal distance values are not compatible with kind {0:?}")]
    InconsistentDiagonal(DistanceKind),

    /// Provided callback returned incompatible endpoint and value arrays
    ///
    /// If we denote `N` the length of the endpoint array, the value array
    /// should contain `N.pow(2)` elements.
    #[error("number of specified endpoints and values isn't consistent")]
    InconsistentLen,
}
//
#[cfg(feature = "hwloc-2_5_0")]
impl From<DistanceKind> for AddDistanceMatrixError {
    fn from(value: DistanceKind) -> Self {
        Self::BadKind(value.into())
    }
}
//
#[cfg(feature = "hwloc-2_5_0")]
impl From<NulError> for AddDistanceMatrixError {
    fn from(_: NulError) -> Self {
        Self::NameContainsNul
    }
}
//
#[cfg(feature = "hwloc-2_5_0")]
impl<'topology> From<&'topology TopologyObject> for AddDistanceMatrixError {
    fn from(object: &'topology TopologyObject) -> Self {
        Self::ForeignEndpoint(object.into())
    }
}

/// # Remove distances between objects
//
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/stable/group__hwlocality__distances__remove.html
#[cfg(feature = "hwloc-2_3_0")]
impl TopologyEditor<'_> {
    /// Remove a single distance matrix from the topology
    ///
    /// The distance matrix to be removed can be selected using the
    /// `find_matrix` callback.
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_distances_release_remove")]
    pub fn remove_distance_matrix(
        &mut self,
        find_matrix: impl FnOnce(&Topology) -> DistanceMatrix<'_>,
    ) -> Result<(), RawHwlocError> {
        /// Polymorphized subset of this function (avoids generics code bloat)
        ///
        /// # Safety
        ///
        /// `distance` must point to a valid distance matrix from this
        /// topology, with no residual high-level wrapper remaining
        unsafe fn polymorphized(
            self_: &mut TopologyEditor<'_>,
            distances: NonNull<hwloc_distances_s>,
        ) -> Result<(), RawHwlocError> {
            // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
            //         - hwloc ops are trusted to keep *mut parameters in a valid
            //           state unless stated otherwise
            //         - distances is trusted per function contract
            errors::call_hwloc_zero_or_minus1("hwloc_distances_release_remove", || unsafe {
                hwlocality_sys::hwloc_distances_release_remove(
                    self_.topology_mut_ptr(),
                    distances.as_ptr(),
                )
            })
        }

        // Run user callback and call polymorphized subset with result
        let distances = find_matrix(self.topology()).into_inner();
        // SAFETY: distances is indeed a valid distances pointer with no
        //         remaining high level wrapper to bother us, since the
        //         DistanceMatrix struct that we just discarded with into_inner
        //         assumed full ownership.
        unsafe { polymorphized(self, distances) }
    }

    /// Remove all distance matrices from a topology
    ///
    /// If these distances were used to group objects, the associated
    /// [`Group`](ObjectType::Group) objects are not removed from the topology.
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_distances_remove")]
    pub fn remove_all_distances(&mut self) -> Result<(), RawHwlocError> {
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - DistanceMatrix lifetime is bound by the host topology, so
        //           this will invalidate all DistanceMatrix struct in existence
        //           and thus use-after-free cannot happen
        errors::call_hwloc_zero_or_minus1("hwloc_distances_remove", || unsafe {
            hwlocality_sys::hwloc_distances_remove(self.topology_mut_ptr())
        })
    }

    /// Remove distance matrices for objects at a specific depth in the topology
    /// (if any)
    ///
    /// Similar to
    /// [`remove_all_distances()`](TopologyEditor::remove_all_distances()), but
    /// only applies to distance matrices where all endpoint objects reside at
    /// the specified depth.
    ///
    /// `depth` can be a [`Depth`], a [`NormalDepth`] or an [`usize`].
    ///
    /// As of hwloc v2.12.1, removing distances at the depth of
    /// [`Group`](ObjectType::Group) objects is unfortunately not fully
    /// supported by hwloc. It may error out if such objects exist at multiple
    /// depths in the topology.
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
            //         - DistanceMatrix lifetime is bound by the host topology,
            //           so this will invalidate all DistanceMatrix struct in
            //           existence and thus use-after-free cannot happen
            //         - hwloc should be able to handle any valid depth value
            errors::call_hwloc_zero_or_minus1("hwloc_distances_remove_by_depth", || unsafe {
                hwlocality_sys::hwloc_distances_remove_by_depth(
                    self_.topology_mut_ptr(),
                    depth.to_hwloc(),
                )
            })
        }

        // There cannot be any object at a depth below the hwloc-supported max
        depth
            .try_into()
            .map_or_else(|_| Ok(()), |depth| polymorphized(self, depth))
    }

    /// Remove distance matrices for objects of a specific type in the topology
    ///
    /// Similar to
    /// [`remove_all_distances()`](TopologyEditor::remove_all_distances()), but
    /// only applies to distance matrices where all endpoint objects have the
    /// specified type.
    ///
    /// As of hwloc v2.12.1, removing distances between
    /// [`Group`](ObjectType::Group) objects is unfortunately not fully
    /// supported by hwloc. It may error out if such objects exist at multiple
    /// depths in the topology.
    #[allow(clippy::missing_errors_doc)]
    #[doc(alias = "hwloc_distances_remove_by_type")]
    pub fn remove_distances_with_type(&mut self, ty: ObjectType) -> Result<(), RawHwlocError> {
        let topology = self.topology();
        if let Ok(depth) = topology.depth_for_type(ty) {
            self.remove_distances_at_depth(depth)?;
        } else {
            let depths = topology
                .possible_depths()
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
/// The names and semantics of distance matrices currently created by
/// hwloc may be found [in the hwloc
/// documentation](https://hwloc.readthedocs.io/en/stable/topoattrs.html#topoattrs_distances).
#[cfg_attr(feature = "hwloc-2_5_0", doc = "")]
#[cfg_attr(
    feature = "hwloc-2_5_0",
    doc = "More matrices may be added by the user using the"
)]
#[cfg_attr(
    feature = "hwloc-2_5_0",
    doc = "[`TopologyEditor::add_distance_matrix()`] API."
)]
///
/// The ownership/lifetime semantics of this object are subtle:
///
/// - Its internal allocations are managed by an hwloc topology, and it contains
///   references to objects from a topology. As a result, its lifetime is tied
///   to that of a topology, the number of objects cannot grow, and there is no
///   easy way to clone a `DistanceMatrix`...
/// - ...but inner objects and values are not themselves part of the "home"
///   topology, and can therefore be modified without affecting it. Which is why
///   you only need an `&Topology` to retrieve modifiable distance matrices.
#[cfg_attr(feature = "hwloc-2_5_0", doc = "")]
#[cfg_attr(
    feature = "hwloc-2_5_0",
    doc = "Let's give an example of a possible distance matrix modification."
)]
#[cfg_attr(
    feature = "hwloc-2_5_0",
    doc = "On hwloc 2.5+, if there is a single NUMA node per Package,"
)]
#[cfg_attr(
    feature = "hwloc-2_5_0",
    doc = "[`Topology::object_with_same_locality()`] may be used to convert"
)]
#[cfg_attr(
    feature = "hwloc-2_5_0",
    doc = "between them and replace NUMA nodes in the objects array with the"
)]
#[cfg_attr(feature = "hwloc-2_5_0", doc = "corresponding Packages.")]
#[cfg_attr(feature = "hwloc-2_5_0", doc = "")]
#[cfg_attr(
    feature = "hwloc-2_5_0",
    doc = "See also [`DistanceMatrix::transform()`] for applying some"
)]
#[cfg_attr(feature = "hwloc-2_5_0", doc = "transformations to the structure.")]
///
///
// --- Implementation details
//
// Upstream inspiration: https://hwloc.readthedocs.io/en/stable/group__hwlocality__distances__consult.html
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
// - The objs and values pointers should not be replaced (but contents can be
//   freely modified)
#[doc(alias = "hwloc_distances_s")]
pub struct DistanceMatrix<'topology> {
    /// Pointer to a valid [`hwloc_distances_s`] struct that originates from
    /// `topology`
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
impl<'topology> DistanceMatrix<'topology> {
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
        let num_objects = int::expect_usize(inner_ref.nbobj);
        int::assert_slice_len::<*const TopologyObject>(num_objects);
        int::assert_slice_len::<u64>(
            num_objects
                .checked_mul(num_objects)
                .expect("distance count should fit usize"),
        );
        // SAFETY: inner is assumed to originate from topology per precondition
        Self { inner, topology }
    }

    /// Access the inner `hwloc_distances_s` (`&` version)
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

    /// Get the inner `hwloc_distances_s` (`&mut` version)
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

    /// Description of this distance matrix
    ///
    /// For instance "NUMALatency" for hardware-provided NUMA distances (ACPI
    /// SLIT), or `None` if unknown.
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
    pub fn kind(&self) -> DistanceKind {
        // SAFETY: No invalid mutation of inner state occurs
        let result = DistanceKind::from_bits_retain(unsafe { self.inner().kind });
        assert!(
            result.is_valid(DistanceKindUsage::FromHwloc),
            "hwloc should not emit invalid kinds"
        );
        result
    }

    /// Change the distance matrix kind
    ///
    #[cfg_attr(
        feature = "hwloc-2_1_0",
        doc = "You should not attempt to set or clear the"
    )]
    #[cfg_attr(
        feature = "hwloc-2_1_0",
        doc = "`DistanceKind::HETEROGENEOUS_TYPES` flag, it will be set or cleared"
    )]
    #[cfg_attr(feature = "hwloc-2_1_0", doc = "automatically.")]
    ///
    /// # Errors
    ///
    /// It is illegal to attempt to set both `FROM_` or `MEANS_` kind flags at
    /// the same time. However clearing them is fine.
    pub fn set_kind(
        &mut self,
        #[allow(unused_mut)] mut kind: DistanceKind,
    ) -> Result<(), FlagsError<DistanceKind>> {
        if !kind.is_valid(DistanceKindUsage::AddEdit) {
            return Err(kind.into());
        }
        #[cfg(feature = "hwloc-2_1_0")]
        {
            kind |= self.kind() & DistanceKind::HETEROGENEOUS_TYPES;
        }
        // SAFETY: objs and values array are not touched
        unsafe {
            self.inner_mut().kind = kind.bits();
        }
        Ok(())
    }

    /// Make sure the `HETEROGENEOUS_TYPES` flag is set according to the current
    /// set of objects covered by the distance matrix.
    #[cfg(feature = "hwloc-2_1_0")]
    fn update_heterogeneous_flag(&mut self) {
        let mut ty_so_far = None;
        let mut inner = self.inner;
        for ty in self.objects().flatten().map(TopologyObject::object_type) {
            if let Some(ty_so_far) = ty_so_far {
                if ty != ty_so_far {
                    // SAFETY: It is safe to change the kind as the
                    //         self.objects() iterator never accesses it.
                    unsafe {
                        inner.as_mut().kind |= HWLOC_DISTANCES_KIND_HETEROGENEOUS_TYPES;
                    }
                    return;
                }
            } else {
                ty_so_far = Some(ty);
            }
        }
        // SAFETY: It is safe to change the kind as the
        //         self.objects() iterator never accesses it.
        unsafe {
            inner.as_mut().kind &= !HWLOC_DISTANCES_KIND_HETEROGENEOUS_TYPES;
        }
    }

    /// Number of objects described by the distance matrix
    ///
    /// # Safety
    ///
    /// Output can be trusted by unsafe code to be the actual number of elements
    /// in the target allocation, and this number can be trusted to fit within
    /// Rust's limit of `isize::MAX` slice length limit.
    fn num_objects(&self) -> usize {
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
    #[doc(alias = "hwloc_distances_s::nbobjs")]
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
        //         - num_objects guarantees a target smaller than isize::MAX
        unsafe {
            let objs = self.raw_objects();
            let objs = std::slice::from_raw_parts(objs.cast_const(), self.num_objects());
            objs.iter().map(|ptr| ffi::deref_ptr(ptr))
        }
    }

    /// Find the row/column indices of an object in the distance matrix
    ///
    /// An object is allowed to appear multiple times in the distance matrix in
    /// order to model multiple network links between the same objects.
    ///
    /// This will return an empty iterator if `obj` does not belong to the
    /// active topology or doesn't have distances associated with it.
    ///
    /// Beware that calling this in a loop for each object you are interested in
    /// will result in a lot of duplicate work. It is better to instead build a
    /// cache of indices for the objects that you are interested in, or to use
    /// the [`object_distances()`](DistanceMatrix::object_distances()) iterator
    /// if your algorithm allows for it.
    #[doc(alias = "hwloc_distances_obj_index")]
    pub fn object_indices<'result>(
        &'result self,
        obj: &'result TopologyObject,
    ) -> impl DoubleEndedIterator<Item = usize> + Clone + FusedIterator + 'result {
        self.objects()
            .enumerate()
            .filter_map(move |(idx, candidate)| std::ptr::eq(candidate?, obj).then_some(idx))
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
        // SAFETY: - inner is assumed valid as a type invariant, thus objs &
        //           num_objects() are trusted to be consistent
        //         - objs is assumed unaliased and bound to the lifetime of
        //           self.topology
        //         - num_objects guarantees a target smaller than isize::MAX
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
    /// adjust the distance matrix after doing this, which you can do using one
    /// of the [`distances_mut()`], [`enumerate_distances_mut()`] and
    /// [`object_distances_mut()`] methods.
    ///
    /// # Errors
    ///
    /// [`ForeignObjectError`] if `new_object` does not belong to the same
    /// [`Topology`] as this distance matrix.
    ///
    /// [`distances_mut()`]: DistanceMatrix::distances_mut()
    /// [`enumerate_distances_mut()`]: DistanceMatrix::enumerate_distances_mut()
    /// [`object_distances_mut()`]: DistanceMatrix::object_distances_mut()
    pub fn replace_object(
        &mut self,
        idx: usize,
        new_object: Option<&'topology TopologyObject>,
    ) -> Result<(), ForeignObjectError> {
        let topology = self.topology;
        // SAFETY: Overwriting with a valid topology object pointer from
        //         topology, as checked by obj_to_checked_ptr
        unsafe { self.objects_mut()[idx] = Self::obj_to_checked_ptr(topology, new_object)? };
        #[cfg(feature = "hwloc-2_1_0")]
        self.update_heterogeneous_flag();
        Ok(())
    }

    /// Replace all objects using the provided `(index, current object) -> new
    /// object` mapping
    ///
    /// This is more efficient than calling
    /// [`replace_object()`](DistanceMatrix::replace_object()) in a loop and
    /// allows you to know what object you are replacing.
    ///
    /// # Errors
    ///
    /// [`ForeignObjectError`] if any of the [`TopologyObject`]s returned by
    /// `mapping` does not belong to the same [`Topology`] as this distance
    /// matrix.
    pub fn replace_all_objects(
        &mut self,
        mut mapping: impl FnMut(usize, Option<&TopologyObject>) -> Option<&'topology TopologyObject>,
    ) -> Result<(), ForeignObjectError> {
        let topology = self.topology;
        // SAFETY: Overwriting these with valid object pointers from topology
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
        #[cfg(feature = "hwloc-2_1_0")]
        self.update_heterogeneous_flag();
        Ok(())
    }

    /// Number of distances
    ///
    /// # Safety
    ///
    /// Output can be trusted by unsafe code to be the actual number of elements
    /// in the target allocation, and this number can be trusted to fit within
    /// Rust's limit of `isize::MAX` slice length limit.
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
    /// The meaning of the distance value depends on [`DistanceMatrix::kind()`].
    ///
    /// If you do not know the indices of the objects that you are looking for,
    /// you may want to use [`DistanceMatrix::object_distances()`] instead.
    #[doc(alias = "hwloc_distances_s::values")]
    pub fn distances(&self) -> &[u64] {
        // SAFETY: - inner is assumed valid as a type invariant, thus values &
        //           num_distances() are trusted to be consistent. values is
        //           assumed to be  unaliased and bound to the lifetime of
        //           self.topology, and thus to that of self
        //         - No invalid mutation of inner state is possible in safe code
        //           using this API
        //         - num_distances guarantees a target smaller than isize::MAX
        unsafe { std::slice::from_raw_parts(self.inner().values, self.num_distances()) }
    }

    /// Distances in sender-major order (mutable access)
    ///
    /// See also [`distances()`](DistanceMatrix::distances()).
    pub fn distances_mut(&mut self) -> &mut [u64] {
        // SAFETY: - inner is assumed valid as a type invariant, thus values &
        //           num_distances() are trusted to be consistent. values is
        //           assumed to be  unaliased and bound to the lifetime of
        //           self.topology, and thus to that of self
        //         - No invalid mutation of inner state is possible in safe code
        //           using this API
        //         - num_distances guarantees a target smaller than isize::MAX
        unsafe { std::slice::from_raw_parts_mut(self.inner_mut().values, self.num_distances()) }
    }

    /// Iteration over `((sender index, receiver index), distance)` tuples
    ///
    /// See also [`distances()`](DistanceMatrix::distances()).
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

    /// Iteration over `((sender index, receiver index), &mut distance)` tuples
    ///
    /// See also [`distances()`](DistanceMatrix::distances()).
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

    /// Iteration over `((sender, receiver), distance)` tuples
    ///
    /// See also [`distances()`](DistanceMatrix::distances()).
    pub fn object_distances(
        &self,
    ) -> impl FusedIterator<Item = ((Option<&TopologyObject>, Option<&TopologyObject>), u64)> + Clone
    {
        self.objects()
            .flat_map(|obj1| self.objects().map(move |obj2| (obj1, obj2)))
            .zip(self.distances().iter().copied())
    }

    /// Iteration over `((sender, receiver), &mut distance)` tuples
    ///
    /// See also [`distances()`](DistanceMatrix::distances()).
    pub fn object_distances_mut(
        &mut self,
    ) -> impl FusedIterator<Item = ((Option<&TopologyObject>, Option<&TopologyObject>), &mut u64)>
    {
        // SAFETY: This function does not mutate the objects in any way
        let objs = unsafe { self.raw_objects() };
        // SAFETY: - inner is assumed valid as a type invariant, thus objs &
        //           num_objects() are trusted to be consistent, objs is assumed
        //           unaliased and bound to the lifetime of self.topology
        //         - num_objects guarantees a target smaller than isize::MAX
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

    /// Distances between a pair of objects
    ///
    /// For each occurence of the first and second object in the distance
    /// matrix, this will yield the distance from this occurence of the first
    /// object to that occurence of the second object and back.
    ///
    /// An object is allowed to appear multiple times in the distance matrix in
    /// order to model multiple network links between the same objects.
    ///
    /// This will yield an empty iterator if one of the input objects doesn't
    /// belong to the host topology or doesn't have distances associated with it.
    ///
    /// This is a rather expensive operation. If you find yourself needing to
    /// do it in a loop, consider rearchitecturing your workflow around object
    /// indices or [`object_distances()`](DistanceMatrix::object_distances()).
    #[doc(alias = "hwloc_distances_obj_pair_values")]
    pub fn object_pair_distances<'result>(
        &'result self,
        (obj1, obj2): (&'result TopologyObject, &'result TopologyObject),
    ) -> impl DoubleEndedIterator<Item = ObjectPairDistances> + Clone + FusedIterator + 'result
    {
        let num_objects = self.num_objects();
        let distances = self.distances();
        self.object_indices(obj1).flat_map(move |index1| {
            // Ideally this would be computed once and the output would be
            // stored in a Vec and reused, but alas that would create a
            // self-referential iterator, which is currently unsupported.
            self.object_indices(obj2).map(move |index2| {
                // SAFETY: Will produce indices smaller than the square of the number of
                //         objects in the distances matrix, which is the number of
                //         distances in the matrix
                unsafe {
                    let distance12 = *distances.get_unchecked(index1 * num_objects + index2);
                    let distance21 = *distances.get_unchecked(index2 * num_objects + index1);
                    ObjectPairDistances {
                        index1,
                        index2,
                        distance12,
                        distance21,
                    }
                }
            })
        })
    }

    /// Checked distance matrix indexing
    fn checked_idx(&self, (sender, receiver): (usize, usize)) -> usize {
        assert!(sender < self.num_objects(), "Invalid sender index");
        assert!(receiver < self.num_objects(), "Invalid receiver index");
        sender * self.num_objects() + receiver
    }

    /// Truth that this distance matrix is the same as another distance matrix,
    /// assuming both dumps originate from related topologies.
    ///
    /// By related, we mean that `other` should either originate from the same
    /// [`Topology`] as `self`, or from a (possibly modified) clone of that
    /// topology, which allows us to use object global persistent indices as
    /// object identifiers.
    ///
    /// Comparing dumps from unrelated topologies will yield an unpredictable
    /// boolean value.
    pub(crate) fn eq_modulo_topology(&self, other: &Self) -> bool {
        #[cfg(feature = "hwloc-2_1_0")]
        if self.name() != other.name() {
            return false;
        }
        if self.kind() != other.kind() {
            return false;
        }
        /// Translate the objects iterator into a GP index iterator
        fn object_indices<'out>(
            matrix: &'out DistanceMatrix<'out>,
        ) -> impl Iterator<Item = Option<TopologyObjectID>> + 'out {
            matrix
                .objects()
                .map(|obj| obj.map(TopologyObject::global_persistent_index))
        }
        if object_indices(self).ne(object_indices(other)) {
            return false;
        }
        self.distances().eq(other.distances())
    }

    /// Apply a transformation to this distance matrix
    ///
    /// This modifies the local copy of the distance matrix but does not modify
    /// the distance information stored inside the topology (retrieved by
    /// another call to [`Topology::distances()`] or exported to XML).
    ///
    /// To do so, one should add a new distance matrix with same name, kind,
    /// objects and values (see [`TopologyEditor::add_distance_matrix()`]) and
    /// then remove this old one using one of the `TopologyEditor` APIs for
    /// removing distance matrices.
    ///
    /// Objects may also be directly replaced in place using
    /// [`replace_all_objects()`](DistanceMatrix::replace_all_objects()). One
    /// may use e.g. [`Topology::object_with_same_locality()`] to easily convert
    /// between similar objects of different types.
    ///
    /// # Errors
    ///
    /// [`TransformError`] if one attempts to use
    /// [`DistanceTransform::RemoveNone`] to reduce the number of objects to
    /// <2, which is forbidden.
    #[cfg(feature = "hwloc-2_5_0")]
    #[doc(alias = "hwloc_distances_transform")]
    pub fn transform(
        &mut self,
        transform: DistanceTransform,
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
        errors::call_hwloc_zero_or_minus1("hwloc_distances_transform", || unsafe {
            hwlocality_sys::hwloc_distances_transform(
                self.topology.as_ptr(),
                self.inner_mut(),
                transform.into(),
                std::ptr::null_mut(),
                0,
            )
        })
        .map_err(|e| match e {
            RawHwlocError {
                errno: Some(Errno(EINVAL)),
                ..
            } if transform == DistanceTransform::RemoveNone => HybridError::Rust(TransformError),
            other => HybridError::Hwloc(other),
        })?;
        #[cfg(feature = "hwloc-2_1_0")]
        self.update_heterogeneous_flag();
        Ok(())
    }
}
//
/// Distance information yielded by the output iterator of
/// [`DistanceMatrix::object_pair_distances()`]
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub struct ObjectPairDistances {
    /// Index of the selected occurence of the first object specified as a
    /// parameter to `object_pair_distances()`
    pub index1: usize,

    /// Index of the selected occurence of the second object specified as a
    /// parameter to `object_pair_distances()`
    pub index2: usize,

    /// Distance from the occurence of the first object designated by `index1`
    /// to that of the second object designated by `index2`.
    pub distance12: u64,

    /// Distance from the occurence of the second object designated by `index2`
    /// to that of the first object designated by `index1`.
    pub distance21: u64,
}
//
impl Debug for DistanceMatrix<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug = f.debug_struct("DistanceMatrix");
        #[cfg(feature = "hwloc-2_1_0")]
        debug.field("name", &self.name());
        debug
            .field("kind", &self.kind())
            .field("objects", &self.objects().collect::<Vec<_>>());

        let mut distance_table = Vec::new();
        let mut current_row = 0;
        let mut row_values = Vec::new();
        for ((row, _col), distance) in self.enumerate_distances() {
            if row != current_row {
                distance_table.push(std::mem::take(&mut row_values));
                current_row = row;
            }
            row_values.push(distance);
        }
        distance_table.push(row_values);
        debug.field("distances", &distance_table).finish()
    }
}
//
impl Drop for DistanceMatrix<'_> {
    #[doc(alias = "hwloc_distances_release")]
    fn drop(&mut self) {
        // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
        //         - inner pointer validity is assumed as a type invariant
        //         - inner is assumed to belong to topology as a type invariant
        //         - hwloc ops are trusted not to modify *const parameters
        //         - DistanceMatrix will not be usable again after Drop
        unsafe {
            hwlocality_sys::hwloc_distances_release(self.topology.as_ptr(), self.inner.as_ptr())
        }
    }
}
//
impl Index<(usize, usize)> for DistanceMatrix<'_> {
    type Output = u64;

    fn index(&self, idx: (usize, usize)) -> &u64 {
        // SAFETY: index validity is checked by checked_idx
        unsafe { self.distances().get_unchecked(self.checked_idx(idx)) }
    }
}
//
impl IndexMut<(usize, usize)> for DistanceMatrix<'_> {
    fn index_mut(&mut self, idx: (usize, usize)) -> &mut u64 {
        let idx = self.checked_idx(idx);
        // SAFETY: index validity is checked by checked_idx
        unsafe { self.distances_mut().get_unchecked_mut(idx) }
    }
}
//
// SAFETY: No internal mutability
unsafe impl Send for DistanceMatrix<'_> {}
//
// SAFETY: No internal mutability
unsafe impl Sync for DistanceMatrix<'_> {}

bitflags! {
    /// Kinds of distance matrices
    ///
    /// A kind with a name starting with "FROM_" specifies where the distance
    /// information comes from, if known.
    ///
    /// A kind with a name starting with "MEANS_" specifies whether values are
    /// latencies or bandwidths, if applicable.
    ///
    /// At most one of the "FROM_" and "MEANS_" kinds should be present.
    #[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
    #[doc(alias = "hwloc_distances_kind_e")]
    pub struct DistanceKind: hwloc_distances_kind_e {
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
        //
        // TODO: Adjust is_valid when adding new kinds
    }
}
//
impl DistanceKind {
    /// Truth that this kind is in a valid state
    fn is_valid(self, #[allow(unused)] usage: DistanceKindUsage) -> bool {
        // FROM and MEANS kinds are mutually exclusive
        if self.contains(Self::FROM_OS | Self::FROM_USER)
            || self.contains(Self::MEANS_LATENCY | Self::MEANS_BANDWIDTH)
        {
            return false;
        }

        // What about HETEROGENEOUS_TYPES, if supported?
        #[cfg(feature = "hwloc-2_1_0")]
        {
            match usage {
                // It's normal for hwloc to return it
                DistanceKindUsage::FromHwloc => {},

                // It shouldn't be used in queries because it's ignored...
                DistanceKindUsage::Query
                // ...and it shouldn't be used when adding or modifying
                // distances because it's added and removed automatically
                | DistanceKindUsage::AddEdit => {
                    if self.contains(Self::HETEROGENEOUS_TYPES) {
                        return false;
                    }
                }
            }
        }
        true
    }
}
//
/// Context in which a [`DistanceKind`] can be used
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DistanceKindUsage {
    /// Translation of raw hwloc flags
    FromHwloc,

    /// Input to a query that selects distances matrices that have certain kinds
    Query,

    /// Input to an operation that creates or modifies a topology
    AddEdit,
}
//
#[cfg(any(test, feature = "proptest"))]
crate::impl_arbitrary_for_bitflags!(DistanceKind, hwloc_distances_kind_e);

/// Transformations of distances structures
#[cfg(feature = "hwloc-2_5_0")]
#[derive(
    Copy, Clone, Debug, derive_more::Display, EnumCount, EnumIter, Eq, FromRepr, Hash, PartialEq,
)]
#[doc(alias = "hwloc_distances_transform_e")]
#[repr(u32)]
pub enum DistanceTransform {
    /// Remove `None` objects from the distances structure.
    ///
    /// Every object that was replaced with `None` in
    /// [`DistanceMatrix::objects()`] is removed and the matrix is updated
    /// accordingly. This is a way to shrink a distance matrix.
    ///
    /// At least 2 objects must remain, otherwise
    /// [`DistanceMatrix::transform()`] will fail.
    ///
    /// [`DistanceMatrix::kind()`] will be updated with or without
    /// [`HETEROGENEOUS_TYPES`] according to the remaining objects.
    ///
    /// [`HETEROGENEOUS_TYPES`]: DistanceKind::HETEROGENEOUS_TYPES
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
    /// This currently only applies to NVSwitches where GPUs seem connected
    /// to different switch ports. Switch ports must be objects with subtype
    /// "NVSwitch" as in the NVLinkBandwidth matrix.
    ///
    /// This transformation will replace all ports with only the first one, now
    /// connected to all GPUs. Other ports are removed by applying the
    /// `RemoveNone` transformation internally.
    #[doc(alias = "HWLOC_DISTANCES_TRANSFORM_MERGE_SWITCH_PORTS")]
    MergeSwitchPorts = HWLOC_DISTANCES_TRANSFORM_MERGE_SWITCH_PORTS,

    /// Apply a transitive closure to the matrix to connect objects across
    /// switches.
    ///
    /// All pairs of GPUs will be reported as directly connected instead GPUs
    /// being only connected to switches.
    ///
    /// Switch ports must be objects with subtype "NVSwitch" as in the
    /// NVLinkBandwidth matrix.
    #[doc(alias = "HWLOC_DISTANCES_TRANSFORM_TRANSITIVE_CLOSURE")]
    TransitiveSwitchClosure = HWLOC_DISTANCES_TRANSFORM_TRANSITIVE_CLOSURE,
}
//
#[cfg(feature = "hwloc-2_5_0")]
crate::impl_arbitrary_for_sequence!(DistanceTransform);
//
#[cfg(feature = "hwloc-2_5_0")]
impl From<DistanceTransform> for hwloc_distances_transform_e {
    fn from(value: DistanceTransform) -> Self {
        match value {
            DistanceTransform::RemoveNone => HWLOC_DISTANCES_TRANSFORM_REMOVE_NULL,
            DistanceTransform::BandwidthToLinkCount => HWLOC_DISTANCES_TRANSFORM_LINKS,
            DistanceTransform::MergeSwitchPorts => HWLOC_DISTANCES_TRANSFORM_MERGE_SWITCH_PORTS,
            DistanceTransform::TransitiveSwitchClosure => {
                HWLOC_DISTANCES_TRANSFORM_TRANSITIVE_CLOSURE
            }
        }
    }
}

/// Error returned when attempting to remove all distances using
/// [`DistanceTransform::RemoveNone`].
#[cfg(feature = "hwloc-2_5_0")]
#[derive(Copy, Clone, Debug, Default, Eq, Error, Hash, PartialEq)]
#[error("can't empty a distance matrix using DistanceTransform::RemoveNone")]
pub struct TransformError;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{errors::ParameterError, object::hierarchy::tests::any_hwloc_depth};
    use proptest::prelude::*;
    #[allow(unused)]
    use similar_asserts::assert_eq;
    use std::{
        collections::{HashMap, HashSet},
        error::Error,
    };

    /// Check all distance matrices in a topology
    fn check_topology_distances(topology: &Topology) -> Result<(), TestCaseError> {
        // Enumerate and check all distances
        for mut matrix in topology.distances(DistanceKind::empty())? {
            check_distance_matrix(&mut matrix)?;
        }
        Ok(())
    }

    /// Test properties that any distance matrix should follow
    fn check_distance_matrix(matrix: &mut DistanceMatrix<'_>) -> Result<(), TestCaseError> {
        // Distance names should be valid Unicode on well-behaved systems, and
        // is guaranteed to be for matrices that we add ourselves.
        #[cfg(feature = "hwloc-2_1_0")]
        prop_assert!(matrix.name().map_or(true, |cstr| cstr.to_str().is_ok()));

        // Possible kinds are governed by some rules
        let kind = matrix.kind();
        prop_assert!(!kind.contains(DistanceKind::FROM_OS | DistanceKind::FROM_USER));
        prop_assert!(!kind.contains(DistanceKind::MEANS_LATENCY | DistanceKind::MEANS_BANDWIDTH));
        #[cfg(feature = "hwloc-2_1_0")]
        {
            let distinct_types = matrix
                .objects()
                .flatten()
                .map(TopologyObject::object_type)
                .collect::<HashSet<_>>();
            prop_assert_eq!(
                kind.contains(DistanceKind::HETEROGENEOUS_TYPES),
                distinct_types.len() > 1
            );
        }

        // TODO: Add a proptest for set_kind()

        // object_indices() is just a convenience around objects() queries
        let mut objects_to_indices = HashMap::new();
        for (idx, obj) in matrix.objects().flatten().enumerate() {
            objects_to_indices
                .entry(obj.global_persistent_index())
                .or_insert_with(|| (obj, HashSet::new()))
                .1
                .insert(idx);
        }
        for (obj, expected_indices) in objects_to_indices.into_values() {
            let actual_indices = matrix.object_indices(obj).collect::<HashSet<_>>();
            prop_assert_eq!(actual_indices, expected_indices);
        }
        // TODO: Add proptest that calls object_indices for arbitrary objects,
        //       integrating the above to get higher odds of hitting a correct
        //       object + know how to interprete the result?
        // TODO: Add proptests for replace_object() and replace_all_objects()

        // Distance count should match object count
        let num_objects = matrix.num_objects();
        prop_assert_eq!(matrix.distances().len(), num_objects.pow(2));
        let distances_from_mut = matrix.distances_mut().to_owned();
        prop_assert!(matrix.distances().iter().eq(&distances_from_mut));

        // Check index generation from enumerate_distances
        let expected_enum_distances = matrix
            .distances()
            .iter()
            .enumerate()
            .map(|(idx, &dist)| ((idx / num_objects, idx % num_objects), dist));
        prop_assert!(matrix.enumerate_distances().eq(expected_enum_distances));
        let enumerate_from_mut = matrix
            .enumerate_distances_mut()
            .map(|(indices, dist)| (indices, *dist))
            .collect::<Vec<_>>();
        prop_assert!(matrix.enumerate_distances().eq(enumerate_from_mut));

        // Check index-to-object translation from object_distances
        let expected_obj_distances = matrix.enumerate_distances().map(|((idx1, idx2), dist)| {
            let obj = |idx| matrix.objects().nth(idx).unwrap();
            ((obj(idx1), obj(idx2)), dist)
        });
        fn option_to_ptr(opt: Option<&TopologyObject>) -> *const TopologyObject {
            opt.map_or(ptr::null(), |obj_ref| obj_ref)
        }
        fn obj_to_ptr<'a>(
            iter: impl Iterator<
                    Item = (
                        (Option<&'a TopologyObject>, Option<&'a TopologyObject>),
                        u64,
                    ),
                > + 'a,
        ) -> impl Iterator<Item = ((*const TopologyObject, *const TopologyObject), u64)> + 'a
        {
            iter.map(move |((obj1, obj2), value)| {
                ((option_to_ptr(obj1), option_to_ptr(obj2)), value)
            })
        }
        prop_assert!(obj_to_ptr(matrix.object_distances()).eq(obj_to_ptr(expected_obj_distances)));
        #[allow(clippy::needless_collect)]
        let object_distances_from_mut = matrix
            .object_distances_mut()
            .map(|((obj1, obj2), dist)| ((option_to_ptr(obj1), option_to_ptr(obj2)), *dist))
            .collect::<Vec<_>>();
        prop_assert!(object_distances_from_mut
            .into_iter()
            .eq(obj_to_ptr(matrix.object_distances())));

        // TODO: Add proptest for object_pair_distances()
        // TODO: Add proptest for transform() on v2.5+

        // Test indexing against enumerate_distances
        for ((idx1, idx2), dist) in matrix.enumerate_distances() {
            prop_assert_eq!(matrix[(idx1, idx2)], dist);
        }

        // Test that debug doesn't crash
        let _debug = format!("{matrix:?}");
        Ok(())
    }

    /// Check all distance matrices from the default topology
    ///
    /// Note that a hwloc will not expose any distance matrix on a typical
    /// developer workstation, as those are normally reserved for communication
    /// between sockets, NUMA nodes, GPUs, etc. For good test coverage on such
    /// systems, you will therefore need to enable at least the `hwloc-2_5_0`
    /// feature, which lets us add arbitrary distance matrices to the topology.
    #[test]
    fn default_distances() {
        check_topology_distances(Topology::test_instance()).unwrap();
    }

    /// Pick a valid distance kind for a certain application
    ///
    /// Set `WRITING` to `true` when creating or modifying distances, set it
    /// to `false` when querying distances.
    #[allow(unused)]
    fn valid_distance_kind(usage: DistanceKindUsage) -> impl Strategy<Value = DistanceKind> {
        (
            prop::array::uniform2(prop::option::of(any::<bool>())),
            any::<bool>(),
        )
            .prop_map(move |([source, meaning], heterogeneous)| {
                let source_flags = source.map_or(DistanceKind::empty(), |source_bool| {
                    if source_bool {
                        DistanceKind::FROM_OS
                    } else {
                        DistanceKind::FROM_USER
                    }
                });
                let meaning_flags = meaning.map_or(DistanceKind::empty(), |meaning_bool| {
                    if meaning_bool {
                        DistanceKind::MEANS_LATENCY
                    } else {
                        DistanceKind::MEANS_BANDWIDTH
                    }
                });
                #[allow(unused_mut)]
                let mut heterogeneous_flags = DistanceKind::empty();
                #[cfg(feature = "hwloc-2_1_0")]
                {
                    match usage {
                        DistanceKindUsage::FromHwloc => {
                            unreachable!("Not used as input to hwloc APIs")
                        }
                        // HETEROGENEOUS_TYPES cannot be used for querying (it's
                        // ignored) or for add/edit (it's auto-filled)
                        DistanceKindUsage::Query | DistanceKindUsage::AddEdit => {}
                    }
                    // TODO: Set heterogeneous_flags according to heterogeneous
                    //       boolean if any situation allows it
                }
                source_flags | meaning_flags | heterogeneous_flags
            })
    }
    //
    /// Pick a distance kind that is likely to be correct, but may be wrong
    fn distance_kind(usage: DistanceKindUsage) -> impl Strategy<Value = DistanceKind> {
        prop_oneof![
            4 => valid_distance_kind(usage),
            1 => any::<DistanceKind>()
        ]
    }

    /// Check a distance matrix query that has a kind filter
    fn check_matrix_query_with_kind(
        topology: &Topology,
        kind: DistanceKind,
        query: impl Fn(
            &Topology,
        )
            -> Result<Vec<DistanceMatrix<'_>>, HybridError<FlagsError<DistanceKind>>>,
        extra_filter: impl Fn(&DistanceMatrix<'_>) -> bool,
        allow_hwloc_error: bool,
        allow_empty_return_with_bad_kind: bool,
    ) -> Result<(), TestCaseError> {
        // Predict filtering validity
        let kind_valid = kind.is_valid(DistanceKindUsage::Query);

        // Perform filtering, check errors
        let filtered = match query(topology) {
            Ok(filtered) => {
                prop_assert!(
                    kind_valid || (filtered.is_empty() && allow_empty_return_with_bad_kind)
                );
                filtered
            }
            Err(HybridError::Rust(ParameterError(k))) => {
                prop_assert!(!kind_valid);
                prop_assert_eq!(k, kind);
                return Ok(());
            }
            Err(HybridError::Hwloc(h)) => {
                prop_assert!(allow_hwloc_error, "Unexpected hwloc error {h}");
                return Ok(());
            }
        };

        // Check result
        let expected = topology
            .distances(Default::default())?
            .into_iter()
            .filter(|dist| dist.kind().contains(kind) && extra_filter(dist))
            .collect::<Vec<_>>();
        prop_assert_eq!(filtered.len(), expected.len());
        prop_assert!(filtered
            .into_iter()
            .zip(&expected)
            .all(|(dist1, dist2)| dist1.eq_modulo_topology(dist2)));
        Ok(())
    }
    //
    /// Test the `distances()` query on some topology
    fn check_distances(topology: &Topology, kind: DistanceKind) -> Result<(), TestCaseError> {
        check_matrix_query_with_kind(
            topology,
            kind,
            |topology| topology.distances(kind),
            |_distance| true,
            false,
            false,
        )
    }
    //
    /// Test the `distances_at_depth()` query on some topology
    fn check_distances_at_depth(
        topology: &Topology,
        kind: DistanceKind,
        depth: Depth,
    ) -> Result<(), TestCaseError> {
        check_matrix_query_with_kind(
            topology,
            kind,
            |topology| topology.distances_at_depth(kind, depth),
            |distance| {
                distance
                    .objects()
                    .all(|obj| obj.map_or(true, |obj| obj.depth() == depth))
            },
            topology.type_at_depth(depth) == Some(ObjectType::Group),
            matches!(depth, Depth::Normal(depth) if depth >= topology.depth()),
        )
    }
    //
    /// Test the `distances_with_type()` query on some topology
    fn check_distances_with_type(
        topology: &Topology,
        kind: DistanceKind,
        ty: ObjectType,
    ) -> Result<(), TestCaseError> {
        check_matrix_query_with_kind(
            topology,
            kind,
            |topology| topology.distances_with_type(kind, ty),
            |distance| {
                distance
                    .objects()
                    .all(|obj| obj.map_or(true, |obj| obj.object_type() == ty))
            },
            false,
            false,
        )
    }

    proptest! {
        /// Check distance filtering by kind on default topology
        #[test]
        fn distances(kind in distance_kind(DistanceKindUsage::Query)) {
            check_distances(Topology::test_instance(), kind)?;
        }

        /// Check distance filtering by kind and depth on default topology
        #[test]
        fn distances_at_depth(
            kind in distance_kind(DistanceKindUsage::Query),
            depth in any_hwloc_depth(),
        ) {
            check_distances_at_depth(Topology::test_instance(), kind, depth)?;
        }

        /// Check distance filtering by kind and type on default topology
        #[test]
        fn distances_with_type(
            kind in distance_kind(DistanceKindUsage::Query),
            ty in any::<ObjectType>(),
        ) {
            check_distances_with_type(Topology::test_instance(), kind, ty)?;
        }
    }

    // TODO: Proptests of &self distance matrix methods that don't require use
    //       of a DistanceMatrixPicker, see TODOs above + add copies to hwloc25.

    /// Distance matrix picker
    ///
    /// A picker is designed to operate on a certain topology and provides a
    /// `pick()` method that can be targeted as many times as needed on the same
    /// (unmodified) topology, consistently returning the same distance matrix.
    ///
    /// Use cases include working around lack of a `Clone` implementation for
    /// `DistanceMatrix` when testing editing functions, as well as testing of
    /// [`TopologyEditor::remove_distance_matrix()`].
    #[derive(Clone, Debug, Eq, PartialEq)]
    struct DistanceMatrixPicker {
        /// Index of the selected matrix within the output of the un-filtered
        /// `topology.distances(Default::default())` list.
        global_idx: usize,

        /// Strategy used to retrieve the matrix whenever needed, fetching as
        /// few other distance matrices as possible.
        strategy: PickStrategy,

        /// Index of the selected matrix within the reduced list from `strategy`
        local_idx: usize,
    }
    //
    impl DistanceMatrixPicker {
        /// Generate random distance matrix pickers for a certain topology
        ///
        /// Given a topology that contains at least one distance matrix, this
        /// returns a proptest strategy for generating distance pickers that
        /// consistently return one of these distance matrices.
        ///
        /// If the topology contains no distance matrix, `None` will be returned
        /// instead, as matrix can be picked so no picker can be returned.
        fn any(topology: &Topology) -> Option<impl Strategy<Value = Self>> {
            // Get distances, return None if they are none
            let distances = topology.distances(Default::default()).unwrap();
            if distances.is_empty() {
                return None;
            }

            // For each distance matrix, determine the optimal strategy for
            // retrieving it from the topology
            let num_distances = distances.len();
            let strategy_and_local_idx = distances
                .into_iter()
                .enumerate()
                .map(|(global_idx, matrix)| {
                    // Common logic for finding the index of a matrix in the
                    // output of a certain topology query
                    fn find_local_idx(
                        matrix: &DistanceMatrix<'_>,
                        query_output: Result<Vec<DistanceMatrix<'_>>, impl Error>,
                    ) -> usize {
                        query_output
                            .expect("Query by known matrix characteristic should succeed")
                            .into_iter()
                            .position(|candidate| candidate.eq_modulo_topology(matrix))
                            .expect("Matrix should be present in query output")
                    }
                    let from_filter = DistanceKind::FROM_OS | DistanceKind::FROM_USER;
                    let means_filter = DistanceKind::MEANS_LATENCY | DistanceKind::MEANS_BANDWIDTH;

                    // Does the matrix have a Rust-intelligible name?
                    #[cfg(feature = "hwloc-2_1_0")]
                    if let Some(name) = matrix.name() {
                        if let Ok(name) = name.to_str() {
                            // Does this hwloc version support querying it by name?
                            if cfg!(feature = "hwloc-3_0_0")
                                || (matrix.kind().intersects(from_filter)
                                    && matrix.kind().intersects(means_filter))
                            {
                                // If so, querying by name will likely be most
                                // efficient (normally only yields a single result)
                                let local_idx =
                                    find_local_idx(&matrix, topology.distances_with_name(name));
                                return (
                                    global_idx,
                                    (PickStrategy::ByName(name.to_owned()), local_idx),
                                );
                            }
                        }
                    }

                    // If the matrix does not have a usable name, or if names
                    // are not supported, query by kind instead.
                    let kind_filter = matrix.kind() & (from_filter | means_filter);
                    let local_idx = find_local_idx(&matrix, topology.distances(kind_filter));
                    (global_idx, (PickStrategy::ByKind(kind_filter), local_idx))
                })
                .collect::<HashMap<_, _>>();

            // From this info, we can trivially build a matrix-picking strategy
            let picker = (0..num_distances).prop_map(move |global_idx| {
                let (strategy, local_idx) = strategy_and_local_idx[&global_idx].clone();
                Self {
                    global_idx,
                    strategy,
                    local_idx,
                }
            });
            Some(picker)
        }

        // Pick the desired distance matrix
        fn pick<'topology>(&self, topology: &'topology Topology) -> DistanceMatrix<'topology> {
            match &self.strategy {
                #[cfg(feature = "hwloc-2_1_0")]
                PickStrategy::ByName(name) => topology
                    .distances_with_name(name)
                    .expect("Query should succeed on same topology")
                    .into_iter()
                    .nth(self.local_idx),
                PickStrategy::ByKind(kind) => topology
                    .distances(*kind)
                    .expect("Query should succeed on same topology")
                    .into_iter()
                    .nth(self.local_idx),
            }
            .expect("Local index should exist on same topology")
        }
    }
    //
    /// Strategy for extracting the distance matrix from the topology
    #[derive(Clone, Debug, Eq, PartialEq)]
    enum PickStrategy {
        /// Start from the name-filtered distance list
        ///
        /// Normally there is only one matrix with a given name, so this is the
        /// preferred option for all matrices that have names.
        #[cfg(feature = "hwloc-2_1_0")]
        ByName(String),

        /// Start from the kind-filtered distance list
        ///
        /// All distance matrices have kinds, so this option is always
        /// applicable. But it may be inefficient when there are lots of other
        /// distance matrices with the same kind. The worst case being matrices
        /// with no `FROM` and `MEANS` kind, where the query returns everything.
        ByKind(DistanceKind),
    }

    // TODO: Proptests of &mut DistanceMatrix functions that do require use of
    //       DistanceMatrixPicker, see TODOs above + add copies to hwloc25.

    /// Features that require hwloc v2.1 (i.e. naming distance matrices)
    #[cfg(feature = "hwloc-2_1_0")]
    mod hwloc21 {
        use super::*;
        use crate::strategies::any_string;

        /// Generate a string that has a good chance of being a matrix name,
        /// but may not be one
        pub(super) fn matrix_name(topology: &Topology) -> impl Strategy<Value = String> {
            let matrix_names = topology
                .distances(Default::default())
                .unwrap()
                .into_iter()
                .filter_map(|matrix| {
                    let name = matrix.name()?;
                    let name = name.to_str().ok()?;
                    Some(name.to_owned())
                })
                .collect::<Vec<_>>();
            if matrix_names.is_empty() {
                any_string().boxed()
            } else {
                prop_oneof![
                    3 => prop::sample::select(matrix_names),
                    2 => any_string(),
                ]
                .boxed()
            }
        }

        /// Check querying distances by name
        pub(super) fn check_distances_with_name(
            topology: &Topology,
            name: String,
        ) -> Result<(), TestCaseError> {
            // Predict filtering validity
            let name_valid = name.chars().all(|c| c != '\0');

            // Perform filtering, check errors
            let filtered = match topology.distances_with_name(&name) {
                Ok(filtered) => {
                    prop_assert!(name_valid);
                    filtered
                }
                Err(HybridError::Rust(NulError)) => {
                    prop_assert!(!name_valid);
                    return Ok(());
                }
                Err(HybridError::Hwloc(h)) => unreachable!("Unexpected hwloc error {h}"),
            };

            // Work around upstream issue
            // https://github.com/open-mpi/hwloc/issues/730 for older hwloc
            // releases where get_by_name() is buggy.
            let matrices = topology.distances(Default::default())?;
            if cfg!(not(feature = "hwloc-3_0_0"))
                && matrices.iter().any(|matrix| {
                    let kind = matrix.kind();
                    !kind.intersects(DistanceKind::FROM_OS | DistanceKind::FROM_USER)
                        || !kind
                            .intersects(DistanceKind::MEANS_LATENCY | DistanceKind::MEANS_BANDWIDTH)
                })
            {
                return Ok(());
            }

            // Check result
            let expected = matrices
                .into_iter()
                .filter(|matrix| matches!(matrix.name(), Some(matname) if matname.to_str() == Ok(&name)))
                .collect::<Vec<_>>();
            prop_assert_eq!(filtered.len(), expected.len());
            prop_assert!(filtered
                .into_iter()
                .zip(&expected)
                .all(|(dist1, dist2)| dist1.eq_modulo_topology(dist2)));
            Ok(())
        }

        proptest! {
            /// Check distance filtering by name on default topology
            #[test]
            fn distances_with_name(name in matrix_name(Topology::test_instance())) {
                check_distances_with_name(Topology::test_instance(), name)?;
            }
        }
    }
    #[cfg(feature = "hwloc-2_5_0")]
    use hwloc21::{check_distances_with_name, matrix_name};

    /// Features that require hwloc v2.3 (i.e. editing topologies)
    #[cfg(feature = "hwloc-2_3_0")]
    mod hwloc23 {
        use super::*;

        /// Check that removing all distance matrices work
        pub(super) fn check_remove_all_distances(
            topology: &mut Topology,
        ) -> Result<(), TestCaseError> {
            #[allow(clippy::redundant_closure_for_method_calls)]
            topology.edit(|editor| editor.remove_all_distances())?;
            prop_assert!(topology.distances(Default::default())?.is_empty());
            Ok(())
        }

        /// Check removing all distances from the default topology
        #[test]
        fn remove_all_distances() {
            let mut topology = Topology::test_instance().clone();
            check_remove_all_distances(&mut topology).unwrap();
        }

        /// Check that removing a single distance matrices works
        pub(super) fn check_remove_distance_matrix(
            topology: &mut Topology,
            picker: DistanceMatrixPicker,
        ) -> Result<(), TestCaseError> {
            let initial_topology = topology.clone();
            let mut expected_matrices = initial_topology.distances(Default::default())?;
            expected_matrices.remove(picker.global_idx);

            topology
                .edit(|editor| editor.remove_distance_matrix(|topology| picker.pick(topology)))?;
            let actual_matrices = topology.distances(Default::default())?;

            prop_assert_eq!(actual_matrices.len(), expected_matrices.len());
            prop_assert!(actual_matrices
                .into_iter()
                .zip(expected_matrices)
                .all(|(actual, expected)| actual.eq_modulo_topology(&expected)));
            Ok(())
        }
        //
        /// Check removing a distance matrix from the default topology
        #[test]
        fn remove_distance_matrix() {
            let Some(any_picker) = DistanceMatrixPicker::any(Topology::test_instance()) else {
                return;
            };
            proptest!(|(picker in any_picker)| {
                let mut topology = Topology::test_instance().clone();
                check_remove_distance_matrix(&mut topology, picker)?;
            })
        }

        // TODO: Check other removal methods + add copies to hwloc25 module
    }
    #[cfg(feature = "hwloc-2_5_0")]
    use hwloc23::{check_remove_all_distances, check_remove_distance_matrix};

    /// Features that require hwloc v2.5 (i.e. adding distances between objects)
    #[cfg(feature = "hwloc-2_5_0")]
    mod hwloc25 {
        use super::*;
        use crate::{
            errors::{NulError, ParameterError},
            strategies::{any_c_string, any_object, any_size, any_string, test_object},
        };
        use proptest::collection::SizeRange;
        #[allow(unused)]
        use similar_asserts::assert_eq;
        use std::collections::{HashMap, HashSet};

        /// Maximum number of distance matrices from [`topology_with_distance()`]
        ///
        /// Can be tuned higher at the expense of slower tests
        const MAX_DISTANCE_MATRICES: usize = 10;

        /// Topology test instance variation with some distances added
        fn topology_with_distances() -> impl Strategy<Value = Topology> {
            topology_with_distances_inputs().prop_map(make_topology_with_distances)
        }

        /// Building blocks for repeated calls to
        /// [`add_distance_matrix()`](TopologyEditor::add_distance_matrix)
        ///
        /// Used when building a topology with some pre-filled distances
        fn topology_with_distances_inputs() -> impl Strategy<Value = Vec<MatrixBuildingBlocks>> {
            prop::collection::vec(MatrixBuildingBlocks::valid(), 1..=MAX_DISTANCE_MATRICES)
        }

        /// Process for turning the output of
        /// [`topology_with_distances_inputs()`] into a topology
        fn make_topology_with_distances(inputs: Vec<MatrixBuildingBlocks>) -> Topology {
            let mut topology = Topology::test_instance().clone();
            topology.edit(move |editor| {
                for building_blocks in inputs {
                    let MatrixBuildingBlocks {
                        name,
                        kind,
                        flags,
                        endpoints,
                        values,
                    } = building_blocks;
                    editor
                        .add_distance_matrix(name.as_deref(), kind, flags, |topology| {
                            let id_to_object = topology
                                .objects()
                                .map(|obj| (obj.global_persistent_index(), obj))
                                .collect::<HashMap<_, _>>();
                            let endpoints = endpoints
                                .iter()
                                .map(|obj| id_to_object[&obj.global_persistent_index()])
                                .collect::<Vec<_>>();
                            (endpoints, values)
                        })
                        .unwrap();
                }
            });
            topology
        }

        /// Building blocks for a single call to `add_distance_matrix()`
        ///
        /// Generated endpoints come from `Topology::test_instance()` and must
        /// be fixed up for the actual target topology.
        #[derive(Clone, Debug)]
        struct MatrixBuildingBlocks {
            name: Option<String>,
            kind: DistanceKind,
            flags: AddDistanceMatrixFlags,
            endpoints: Vec<&'static TopologyObject>,
            values: Vec<u64>,
        }
        //
        impl MatrixBuildingBlocks {
            /// Always-valid building blocks
            ///
            /// Use this strategy when you are not exercising the
            /// `add_distance_matrix()` method in isolation, but rather want to build
            /// a topology with some distances inserted ahead of time for the
            /// purpose of exercising distances functionality later on.
            ///
            /// In this situation, bad building blocks reduce the odds of
            /// successful topology building, and thus the efficiency of the
            /// subsequent tests.
            fn valid() -> impl Strategy<Value = Self> {
                let name = prop::option::of(any_c_string());
                let kind = valid_distance_kind(DistanceKindUsage::AddEdit);
                let flags = any::<AddDistanceMatrixFlags>();
                // FIXME: Use isqrt() after bumping MSRV to 1.84+
                #[allow(
                    clippy::cast_possible_truncation,
                    clippy::cast_sign_loss,
                    clippy::cast_precision_loss
                )]
                let max_endpoints = (SizeRange::default().end_incl() as f64).sqrt() as usize;
                let num_endpoints = 2..=max_endpoints.min(c_uint::MAX as usize);
                let endpoints = prop::collection::vec(test_object(), num_endpoints);
                (name, kind, flags, endpoints).prop_flat_map(|(name, kind, flags, endpoints)| {
                    let num_endpoints = endpoints.len();
                    let values = prop::collection::vec(any::<u64>(), num_endpoints.pow(2))
                        .prop_map(move |mut values| {
                            fixup_values(kind, &mut values);
                            values
                        });
                    (Just(name), Just(kind), Just(flags), Just(endpoints), values).prop_map(
                        |(name, kind, flags, endpoints, values)| Self {
                            name,
                            kind,
                            flags,
                            endpoints,
                            values,
                        },
                    )
                })
            }

            /// Likely-valid building blocks
            ///
            /// Use this strategy when exercising the `add_distance_matrix()` method
            /// in isolation. In this situation, all aspects of the method
            /// should be stressed, including error handling.
            fn any() -> impl Strategy<Value = Self> {
                let name = prop::option::of(any_string());
                let kind = distance_kind(DistanceKindUsage::AddEdit);
                let flags = any::<AddDistanceMatrixFlags>();
                let endpoints = any_size().prop_flat_map(|size| {
                    // FIXME: Use isqrt() after bumping MSRV to 1.84+
                    #[allow(
                        clippy::cast_possible_truncation,
                        clippy::cast_sign_loss,
                        clippy::cast_precision_loss
                    )]
                    prop::collection::vec(any_object(size), (size as f64).sqrt() as usize)
                });
                (name, kind, flags, endpoints).prop_flat_map(|(name, kind, flags, endpoints)| {
                    let num_endpoints = endpoints.len();
                    let correct_values_count =
                        prop::collection::vec(any::<u64>(), num_endpoints.pow(2));
                    let values = prop_oneof![
                        // Correct number of values
                        4 => correct_values_count.prop_flat_map(move |values| {
                            prop_oneof![
                                // Correct diagonal values
                                4 => {
                                    let mut values = values.clone();
                                    fixup_values(kind, &mut values);
                                    Just(values)
                                },
                                // Likely-incorrect diagonal values
                                1 => Just(values)
                            ]
                        }),
                        // Likely-incorrect number of values
                        1 => prop::collection::vec(any::<u64>(), SizeRange::default()),
                    ];
                    (Just(name), Just(kind), Just(flags), Just(endpoints), values).prop_map(
                        |(name, kind, flags, endpoints, values)| Self {
                            name,
                            kind,
                            flags,
                            endpoints,
                            values,
                        },
                    )
                })
            }
        }

        /// Fix up random distance values to match the `MEANS_xyz` expectations
        /// about diagonal values being smaller/bigger.
        ///
        /// Assumes that the value matrix is otherwise valid (number of values
        /// is the square of the number of endpoints)
        fn fixup_values(kind: DistanceKind, values: &mut [u64]) {
            if !values.is_empty()
                && kind.intersects(DistanceKind::MEANS_LATENCY | DistanceKind::MEANS_BANDWIDTH)
            {
                // If so, fix up diagonal values
                let num_values = values.len();
                // FIXME: Use isqrt() after bumping MSRV to 1.84+
                #[allow(
                    clippy::cast_possible_truncation,
                    clippy::cast_sign_loss,
                    clippy::cast_precision_loss
                )]
                let num_endpoints = (num_values as f64).sqrt() as usize;
                assert_eq!(num_values % num_endpoints, 0);
                for (endpoint_idx, values_from_endpoint) in
                    values.chunks_mut(num_endpoints).enumerate()
                {
                    let diagonal_value = if kind.contains(DistanceKind::MEANS_LATENCY) {
                        *values_from_endpoint.iter().min().unwrap()
                    } else {
                        assert!(kind.contains(DistanceKind::MEANS_BANDWIDTH));
                        *values_from_endpoint.iter().max().unwrap()
                    };
                    let diagonal_value_idx = values_from_endpoint
                        .iter()
                        .position(|&v| v == diagonal_value)
                        .unwrap();
                    values_from_endpoint.swap(endpoint_idx, diagonal_value_idx);
                }
            }
        }

        proptest! {
            /// Check the process of building a topology with pre-filled
            /// distance matrices from building blocks
            ///
            /// This process can fail if
            /// [`add_distance_matrix()`](TopologyEditor::add_distance_matrix)
            /// has a bug, and having one proptest where the failure occurs
            /// inside of the proptest body makes it possible to use normal
            /// proptest failure analysis like `PROPTEST_FORK`.
            ///
            /// Of course, any other test that uses
            /// [`topology_with_distances()`] will also fail in this case,
            /// during test case generation (which results in much less ideal
            /// failure modes like the test brutally segfaulting without any
            /// failure reduction). These failures should be filtered out using
            /// cargo test's regex filter until the
            /// [`make_topology_with_distances()`] failure is fixed.
            #[test]
            fn test_topology_with_distances(inputs in topology_with_distances_inputs()) {
                let topology = make_topology_with_distances(inputs);
                check_topology_distances(&topology)?;
            }

            /// Check distance filtering by kind on random topology
            #[test]
            fn distances(
                topology in topology_with_distances(),
                kind in distance_kind(DistanceKindUsage::Query),
            ) {
                check_distances(&topology, kind)?;
            }

            /// Check distance filtering by kind and depth on random topology
            #[test]
            fn distances_at_depth(
                topology in topology_with_distances(),
                kind in distance_kind(DistanceKindUsage::Query),
                depth in any_hwloc_depth(),
            ) {
                check_distances_at_depth(&topology, kind, depth)?;
            }

            /// Check distance filtering by kind and type on random topology
            #[test]
            fn distances_with_type(
                topology in topology_with_distances(),
                kind in distance_kind(DistanceKindUsage::Query),
                ty in any::<ObjectType>(),
            ) {
                check_distances_with_type(&topology, kind, ty)?;
            }

            /// Check distance filtering by name on random topology
            #[test]
            fn distances_with_name(
                (topology, name) in topology_with_distances()
                    .prop_flat_map(|topology| {
                        let name = matrix_name(&topology);
                        (Just(topology), name)
                    })
            ) {
                check_distances_with_name(&topology, name)?;
            }

            /// Check removing all distances from a random topology
            #[test]
            fn remove_all_distances(
                mut topology in topology_with_distances(),
            ) {
                check_remove_all_distances(&mut topology)?;
            }

            /// Check removing a distance matrix from a random topology
            #[test]
            fn remove_distance_matrix(
                (mut topology, picker) in topology_with_distances()
                    .prop_flat_map(|topology| {
                        let picker = DistanceMatrixPicker::any(&topology).expect(
                            "topology_with_distances() always produces a \
                            topology that has distances in it"
                        );
                        (Just(topology), picker)
                    })
            ) {
                check_remove_distance_matrix(&mut topology, picker)?;
            }

            // TODO: Run same tests on initial topology above
        }

        /// Test conversion of bad distance kinds to [`AddDistanceMatrixError`]
        #[test]
        fn kind_to_add_error() {
            for bad_kind in [
                DistanceKind::FROM_OS | DistanceKind::FROM_USER,
                DistanceKind::MEANS_LATENCY | DistanceKind::MEANS_BANDWIDTH,
                DistanceKind::HETEROGENEOUS_TYPES,
            ] {
                assert_eq!(
                    AddDistanceMatrixError::from(bad_kind),
                    AddDistanceMatrixError::BadKind(ParameterError(bad_kind)),
                );
            }
        }

        /// Test conversion of [`NulError`] to [`AddDistanceMatrixError`]
        #[test]
        fn nul_to_add_error() {
            assert_eq!(
                AddDistanceMatrixError::from(NulError),
                AddDistanceMatrixError::NameContainsNul,
            );
        }

        proptest! {
            /// Test conversion of foreign object to [`AddDistanceMatrixError`]
            #[test]
            fn foreign_to_add_error(foreign in prop::sample::select(Topology::foreign_objects())) {
                assert_eq!(
                    AddDistanceMatrixError::from(foreign),
                    AddDistanceMatrixError::ForeignEndpoint(ForeignObjectError::from(foreign)),
                );
            }

            /// Test [`TopologyEditor::add_distance_matrix()`]
            #[test]
            fn add_distance_matrix(
                initial_topology in topology_with_distances(),
                building_blocks in MatrixBuildingBlocks::any(),
            ) {
                // Access the reference topology and unpack building blocks
                let test_topology = Topology::test_instance();
                let MatrixBuildingBlocks {
                    name,
                    kind,
                    flags,
                    endpoints,
                    values,
                } = building_blocks;

                // Predict errors
                let name_contains_nul =
                    name.as_ref().is_some_and(|name| name.chars().any(|c| c == '\0'));
                type Kind = DistanceKind;
                let bad_kind =
                    kind.contains(Kind::HETEROGENEOUS_TYPES)
                    || kind.contains(Kind::FROM_OS | Kind::FROM_USER)
                    || kind.contains(Kind::MEANS_LATENCY | Kind::MEANS_BANDWIDTH);
                let bad_endpoint_count = endpoints.len() < 2 || endpoints.len() > c_uint::MAX as usize;
                let foreign_endpoint = endpoints.iter().any(|obj| !test_topology.contains(obj));
                let inconsistent_len = values.len() != endpoints.len().pow(2);
                let inconsistent_diagonal = {
                    let preconditions = !bad_endpoint_count && !inconsistent_len;
                    let has_inconsistent_diagonal = |
                        means_kind,
                        reduction: fn(std::slice::Iter<'_, u64>) -> Option<&u64>,
                    | {
                        kind.contains(means_kind)
                        && values
                            .chunks(endpoints.len())
                            .enumerate()
                            .any(|(endpoint_idx, values_from_endpoint)| {
                                let expected_diagonal = *reduction(values_from_endpoint.iter()).unwrap();
                                values_from_endpoint[endpoint_idx] != expected_diagonal
                            })
                    };
                    preconditions && (
                        has_inconsistent_diagonal(Kind::MEANS_LATENCY, |iter| iter.min())
                        || has_inconsistent_diagonal(Kind::MEANS_BANDWIDTH, |iter| iter.max())
                    )
                };
                let expecting_error =
                    name_contains_nul
                    || bad_kind
                    || bad_endpoint_count
                    || foreign_endpoint
                    || inconsistent_diagonal
                    || inconsistent_len;

                // Now try adding the distances
                let mut topology = initial_topology.clone();
                topology.edit(|editor| {
                    let res = editor.add_distance_matrix(name.as_deref(), kind, flags, |topology| {
                        let id_to_object = topology
                            .objects()
                            .map(|obj| (obj.global_persistent_index(), obj))
                            .collect::<HashMap<_, _>>();
                        let endpoints = endpoints
                            .iter()
                            .map(|obj| {
                                if test_topology.contains(obj) {
                                    id_to_object[&obj.global_persistent_index()]
                                } else {
                                    obj
                                }
                            })
                            .collect::<Vec<_>>();
                        (endpoints, values.clone())
                    });

                    // Check the result against expectations
                    match res {
                        Ok(()) => prop_assert!(!expecting_error),
                        Err(HybridError::Rust(r)) => {
                            match r {
                                AddDistanceMatrixError::NameContainsNul => prop_assert!(name_contains_nul),
                                AddDistanceMatrixError::BadKind(_) => prop_assert!(bad_kind),
                                AddDistanceMatrixError::BadEndpointCount(_) => prop_assert!(bad_endpoint_count),
                                AddDistanceMatrixError::ForeignEndpoint(_) => prop_assert!(foreign_endpoint),
                                AddDistanceMatrixError::InconsistentDiagonal(_) => prop_assert!(inconsistent_diagonal),
                                AddDistanceMatrixError::InconsistentLen => prop_assert!(inconsistent_len),
                            }
                            prop_assert_eq!(editor.topology(), &initial_topology);
                            return Ok(());
                        },
                        Err(HybridError::Hwloc(h)) => unreachable!("unexpected hwloc error {h:?}"),
                    };

                    // If control reached this point, the distances should
                    // have been added. Let's check that.
                    //
                    // First, we should see one more distance matrix
                    let topology = editor.topology();
                    let initial_matrices = initial_topology.distances(DistanceKind::empty()).unwrap();
                    let mut matrices = topology.distances(DistanceKind::empty()).unwrap();
                    prop_assert_eq!(matrices.len(), initial_matrices.len() + 1);

                    // The first distances should be the same as before, the last
                    // one should be newly added.
                    let last_matrix = matrices.pop().unwrap();
                    let first_matrices = matrices;
                    for (initial, current) in initial_matrices.iter().zip(first_matrices) {
                        prop_assert!(initial.eq_modulo_topology(&current));
                    }

                    // If a name was specified, hwloc should preserve it
                    if let Some(name) = name.as_deref() {
                        prop_assert!(last_matrix.name().is_some());
                        let last_name = last_matrix.name().unwrap();
                        prop_assert_eq!(last_name.to_str(), Ok(name));
                    } else {
                        prop_assert_eq!(last_matrix.name(), None);
                    }

                    // HETEROGENEOUS_TYPES is automatically added
                    let mut expected_kind = kind;
                    if endpoints.iter().map(|obj| obj.object_type()).collect::<HashSet<_>>().len() != 1 {
                        expected_kind |= DistanceKind::HETEROGENEOUS_TYPES;
                    }
                    prop_assert_eq!(last_matrix.kind(), expected_kind);

                    // Number and IDs of endpoint objects should match
                    prop_assert_eq!(
                        last_matrix.num_objects(),
                        endpoints.len(),
                    );
                    prop_assert!(last_matrix.objects().all(|opt| opt.is_some()));
                    prop_assert!(
                        last_matrix
                            .objects()
                            .map(|obj_opt| obj_opt.unwrap().global_persistent_index())
                            .eq(endpoints.iter().copied().map(TopologyObject::global_persistent_index))
                    );

                    // Distance values should match
                    prop_assert_eq!(last_matrix.distances(), values);

                    // Distance matrix should otherwise be valid
                    let mut last_matrix = last_matrix;
                    check_distance_matrix(&mut last_matrix)?;

                    // Topology distances should generally be valid
                    check_topology_distances(topology)
                })?;
            }
        }
    }
}
