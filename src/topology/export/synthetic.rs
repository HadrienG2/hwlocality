//! Exporting topologies to Synthetic
//!
//! Synthetic topologies are a very simple textual representation that may only
//! model certain topologies (they must be symmetric among other things, i.e.
//! all CPU cores should be equal), and only some aspects of them (e.g. no I/O
//! devices), but does so extremely concisely.

#[cfg(doc)]
use crate::topology::builder::TopologyBuilder;
use crate::{
    errors::{self, RawHwlocError},
    ffi::int,
    topology::Topology,
};
use bitflags::bitflags;
use hwlocality_sys::{
    hwloc_topology_export_synthetic_flags_e, HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_IGNORE_MEMORY,
    HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_NO_ATTRS,
    HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_NO_EXTENDED_TYPES,
    HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_V1,
};
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::ffi::{c_char, CString};

/// # Exporting Topologies to Synthetic
//
// --- Implementation details ---
//
// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__syntheticexport.html
impl Topology {
    /// Export the topology as a synthetic string
    ///
    /// This string may be loaded later using
    /// [`TopologyBuilder::from_synthetic()`].
    ///
    /// I/O and Misc children are ignored, the synthetic string only describes
    /// normal children.
    ///
    /// By default, the exported topology is only meant to be compatible with
    /// the latest hwloc version. You may want to set some of the `flags` to be
    /// compatible with older hwloc releases, at the cost of dropping support
    /// for newer features.
    ///
    /// # Errors
    ///
    /// Synthetic topologies cannot express the full range of hardware
    /// topologies supported by hwloc, for example they don't support asymmetric
    /// topologies. An error will be returned if the current topology cannot be
    /// expressed as a synthetic topology.
    #[allow(clippy::missing_errors_doc, clippy::needless_continue)]
    #[doc(alias = "hwloc_topology_export_synthetic")]
    pub fn export_synthetic(&self, flags: SyntheticExportFlags) -> Result<String, RawHwlocError> {
        let mut buf = vec![0u8; 1024]; // Size chosen per hwloc docs advice
        loop {
            let len =
                // SAFETY: - Topology is trusted to contain a valid ptr (type invariant)
                //         - hwloc ops are trusted not to modify *const parameters
                //         - buffer and buflen are in sync (same vector)
                //         - flags only allows values supported by the active
                //           hwloc version
                errors::call_hwloc_positive_or_minus1("hwloc_topology_export_synthetic", || unsafe {
                    hwlocality_sys::hwloc_topology_export_synthetic(
                        self.as_ptr(),
                        buf.as_mut_ptr().cast::<c_char>(),
                        buf.len(),
                        flags.bits(),
                    )
                })?;
            if int::expect_usize(len) == buf.len() - 1 {
                // hwloc exactly filled the buffer, which suggests the output
                // was truncated. Try a larger buffer.
                buf.resize(2 * buf.len(), 0);
                continue;
            } else {
                // Buffer seems alright, return it
                buf.truncate(len as usize + 1);
                return Ok(CString::from_vec_with_nul(buf)
                    .expect("Missing NUL from hwloc")
                    .into_string()
                    .expect("Synthetic export should yield an ASCII string"));
            }
        }
    }
}

bitflags! {
    /// Flags to be given to [`Topology::export_synthetic()`]
    #[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
    #[doc(alias = "hwloc_topology_export_synthetic_flags_e")]
    pub struct SyntheticExportFlags: hwloc_topology_export_synthetic_flags_e {
        /// Export extended types such as L2dcache as basic types such as Cache
        ///
        /// This is required if loading the synthetic description with hwloc
        /// < 1.9.
        #[doc(alias = "HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_NO_EXTENDED_TYPES")]
        const NO_EXTENDED_TYPES = HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_NO_EXTENDED_TYPES;

        /// Do not export level attributes
        ///
        /// Ignore level attributes such as memory/cache sizes or PU indices.
        ///
        /// This is required if loading the synthetic description with hwloc
        /// < 1.10.
        #[doc(alias = "HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_NO_ATTRS")]
        const NO_ATTRIBUTES = HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_NO_ATTRS;

        /// Export the memory hierarchy as expected in hwloc 1.x
        ///
        /// Instead of attaching memory children to levels, export single NUMA
        /// node children as normal intermediate levels, when possible.
        ///
        /// This is required if loading the synthetic description with hwloc
        /// 1.x. However this may fail if some objects have multiple local NUMA
        /// nodes.
        #[doc(alias = "HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_V1")]
        const V1 = HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_V1;

        /// Do not export memory information
        ///
        /// Only export the actual hierarchy of normal CPU-side objects and
        /// ignore where memory is attached.
        ///
        /// This is useful for when the hierarchy of CPUs is what really matters,
        /// but it behaves as if there was a single machine-wide NUMA node.
        #[doc(alias = "HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_IGNORE_MEMORY")]
        const IGNORE_MEMORY = HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_IGNORE_MEMORY;
    }
}
//
crate::impl_arbitrary_for_bitflags!(
    SyntheticExportFlags,
    hwloc_topology_export_synthetic_flags_e
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        object::types::ObjectType,
        topology::{builder::TypeFilter, TopologyObject},
    };
    use proptest::prelude::*;
    #[allow(unused)]
    use similar_asserts::assert_eq;
    use strum::IntoEnumIterator;

    proptest! {
        #[test]
        fn export_synthetic(flags: SyntheticExportFlags) {
            let topology = Topology::test_instance();
            let result = topology.export_synthetic(flags);

            // Per hwloc docs, exporting should always fail on asymmetric
            // topologies, and may fail for unspecified other reasons.
            if !topology.root_object().is_symmetric_subtree() {
                prop_assert!(result.is_err());
            }
            let Ok(synthetic) = result else { return Ok(()); };

            // Try to import back the topology
            let imported = Topology::builder().from_synthetic(&synthetic);
            if imported.is_err() {
                // Hwloc may not manage to load topologies exported with some
                // v1.x compatibility flags
                prop_assert!(flags.contains(SyntheticExportFlags::NO_EXTENDED_TYPES));
                return Ok(());
            }
            let imported = imported
                    .expect("Synthetic strings from hwloc should be valid")
                    .with_common_type_filter(TypeFilter::KeepAll)
                    .unwrap()
                    .build()
                    .expect("Building a topology from an hwloc synthetic string should be valid");

            // Check basic properties of the imported topology
            prop_assert_eq!(imported.cpuset().weight(), topology.cpuset().weight());
            //
            if !flags.contains(SyntheticExportFlags::NO_EXTENDED_TYPES) {
                let flags_affecting_memobjs = SyntheticExportFlags::IGNORE_MEMORY | SyntheticExportFlags::V1;
                for ty in ObjectType::iter() {
                    if ty.is_normal()
                       || (ty.is_memory() && !flags.intersects(flags_affecting_memobjs))
                    {
                        prop_assert_eq!(
                            imported.objects_with_type(ty).count(),
                            topology.objects_with_type(ty).count(),
                            "count of objects of type {} doesn't match", ty
                        );
                    }
                    if ty.is_memory() && flags.contains(SyntheticExportFlags::IGNORE_MEMORY) {
                        let expected_count = usize::from(ty == ObjectType::NUMANode);
                        prop_assert_eq!(
                            imported.objects_with_type(ty).count(),
                            expected_count
                        );
                    }
                }
            }
            //
            let total_memory = |topology: &Topology| topology.objects().map(TopologyObject::total_memory).sum::<u64>();
            if !flags.intersects(SyntheticExportFlags::NO_ATTRIBUTES | SyntheticExportFlags::IGNORE_MEMORY) {
                prop_assert_eq!(total_memory(&imported), total_memory(topology));
            };
        }
    }
}
