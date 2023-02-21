//! Exporting topologies to XML

// Upstream docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__xmlexport.html

use bitflags::bitflags;
use std::ffi::c_ulong;

bitflags! {
    /// Flags to be given to [`Topology::export_xml()`]
    #[repr(C)]
    pub struct XMLExportFlags: c_ulong {
        /// Export XML that is loadable by hwloc v1.x
        ///
        /// The export may miss some details about the topology.
        const V1 = (1<<0);
    }
}

impl Default for XMLExportFlags {
    fn default() -> Self {
        Self::empty()
    }
}
