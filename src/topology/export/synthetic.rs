//! Exporting topologies to Synthetic

#[cfg(doc)]
use crate::topology::builder::TopologyBuilder;
use crate::{
    errors::{self, RawHwlocError},
    ffi,
    topology::Topology,
};
use bitflags::bitflags;
use std::ffi::{c_char, c_ulong, CString};

/// # Exporting Topologies to Synthetic
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
    #[doc(alias = "hwloc_topology_export_synthetic")]
    pub fn export_synthetic(&self, flags: SyntheticExportFlags) -> Result<String, RawHwlocError> {
        let mut buf = vec![0u8; 1024];
        loop {
            let len =
                errors::call_hwloc_int_normal("hwloc_topology_export_synthetic", || unsafe {
                    ffi::hwloc_topology_export_synthetic(
                        self.as_ptr(),
                        buf.as_mut_ptr().cast::<c_char>(),
                        buf.len(),
                        flags.bits(),
                    )
                })?;
            if usize::try_from(len).expect("Should fit if I can build the vec") == buf.len() - 1 {
                // hwloc exactly filled the buffer, which suggests the
                // output was truncated. Try a larget buffer.
                buf.resize(2 * buf.len(), 0);
                continue;
            } else {
                // Buffer seems alright, return it
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
    #[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
    #[doc(alias = "hwloc_topology_export_synthetic_flags_e")]
    #[repr(C)]
    pub struct SyntheticExportFlags: c_ulong {
        /// Export extended types such as L2dcache as basic types such as Cache
        ///
        /// This is required if loading the synthetic description with hwloc
        /// < 1.9.
        #[doc(alias = "HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_NO_EXTENDED_TYPES")]
        const NO_EXTENDED_TYPES = (1<<0);

        /// Do not export level attributes
        ///
        /// Ignore level attributes such as memory/cache sizes or PU indices.
        ///
        /// This is required if loading the synthetic description with hwloc
        /// < 1.10.
        #[doc(alias = "HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_NO_ATTRS")]
        const NO_ATTRIBUTES = (1<<1);

        /// Export the memory hierarchy as expected in hwloc 1.x
        ///
        /// Instead of attaching memory children to levels, export single NUMA
        /// node children as normal intermediate levels, when possible.
        ///
        /// This is required if loading the synthetic description with hwloc
        /// 1.x. However this may fail if some objects have multiple local NUMA
        /// nodes.
        #[doc(alias = "HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_V1")]
        const V1 = (1<<2);

        /// Do not export memory information
        ///
        /// Only export the actual hierarchy of normal CPU-side objects and
        /// ignore where memory is attached.
        ///
        /// This is useful for when the hierarchy of CPUs is what really matters,
        /// but it behaves as if there was a single machine-wide NUMA node.
        #[doc(alias = "HWLOC_TOPOLOGY_EXPORT_SYNTHETIC_FLAG_IGNORE_MEMORY")]
        const IGNORE_MEMORY = (1<<3);
    }
}

impl Default for SyntheticExportFlags {
    fn default() -> Self {
        Self::empty()
    }
}
