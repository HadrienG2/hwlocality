use crate::{
    bitmap::{CpuSet, IntHwlocBitmap, NodeSet},
    ffi::{self, ObjectType},
};
use libc::{c_char, c_float, c_int, c_uchar, c_uint, c_ulonglong, c_ushort, c_void};
use std::{ffi::CStr, fmt};

#[repr(C)]
pub struct TopologyObject {
    object_type: ObjectType,
    subtype: *mut c_char,
    os_index: c_uint,
    name: *mut c_char,
    total_memory: u64,
    attr: *mut TopologyObjectAttributes,
    depth: c_uint,
    logical_index: c_uint,
    next_cousin: *mut TopologyObject,
    prev_cousin: *mut TopologyObject,
    parent: *mut TopologyObject,
    sibling_rank: c_uint,
    next_sibling: *mut TopologyObject,
    prev_sibling: *mut TopologyObject,
    arity: c_uint,
    children: *mut *mut TopologyObject,
    first_child: *mut TopologyObject,
    last_child: *mut TopologyObject,
    symmetric_subtree: c_int,
    memory_arity: c_uint,
    memory_first_child: *mut TopologyObject,
    io_arity: c_uint,
    io_first_child: *mut TopologyObject,
    misc_arity: c_int,
    misc_first_child: *mut TopologyObject,
    cpuset: *mut IntHwlocBitmap,
    complete_cpuset: *mut IntHwlocBitmap,
    nodeset: *mut IntHwlocBitmap,
    complete_nodeset: *mut IntHwlocBitmap,
    infos: *mut TopologyObjectInfo,
    infos_count: c_uint,
    userdata: *mut c_void,
    gp_index: u64,
}

impl TopologyObject {
    /// The type of the object.
    pub fn object_type(&self) -> ObjectType {
        self.object_type.clone()
    }

    /// Total memory (in bytes) in NUMA nodes below this object
    pub fn total_memory(&self) -> u64 {
        self.total_memory
    }

    /// The OS-provided physical index number.
    ///
    /// It is not guaranteed unique across the entire machine,
    /// except for PUs and NUMA nodes.
    pub fn os_index(&self) -> u32 {
        self.os_index
    }

    /// The name of the object, if set.
    pub fn name(&self) -> String {
        let c_str = unsafe { CStr::from_ptr(self.name) };
        c_str.to_str().unwrap().to_string()
    }

    /// Vertical index in the hierarchy.
    ///
    /// If the topology is symmetric, this is equal to the parent
    /// depth plus one, and also equal to the number of parent/child
    /// links from the root object to here.
    pub fn depth(&self) -> u32 {
        self.depth
    }

    /// Horizontal index in the whole list of similar objects, hence guaranteed
    /// unique across the entire machine.
    ///
    /// Could be a "cousin_rank" since it's the rank within the "cousin" list below.
    pub fn logical_index(&self) -> u32 {
        self.logical_index
    }

    /// This objects index in the parents children list.
    pub fn sibling_rank(&self) -> u32 {
        self.sibling_rank
    }

    /// The number of normal direct children.
    ///
    /// Memory, Misc and I/O children are not listed here but rather in their
    /// dedicated children list.
    pub fn arity(&self) -> u32 {
        self.arity
    }

    /// Truth that this object is symmetric, which means all normal children and
    /// their children have identical subtrees.
    ///
    /// Memory, I/O and Misc children are ignored.
    pub fn symmetric_subtree(&self) -> bool {
        self.symmetric_subtree != 0
    }

    /// All direct children of this object.
    pub fn children(&self) -> impl Iterator<Item = &TopologyObject> {
        let len = if self.children.is_null() {
            0
        } else {
            self.arity()
        };
        (0..len).map(move |i| unsafe { &**self.children.offset(i as isize) })
    }

    /// The number of memory children.
    pub fn memory_arity(&self) -> u32 {
        self.memory_arity
    }

    /// All memory children of this object.
    pub fn memory_children(&self) -> impl Iterator<Item = &TopologyObject> {
        let len = if self.memory_first_child.is_null() {
            0
        } else {
            self.memory_arity()
        };
        (0..len).map(move |i| unsafe { &*self.memory_first_child.offset(i as isize) })
    }

    /// Next object of same type and depth.
    pub fn next_cousin(&self) -> Option<&TopologyObject> {
        self.deref_topology(&self.next_cousin)
    }

    /// Previous object of same type and depth.
    pub fn prev_cousin(&self) -> Option<&TopologyObject> {
        self.deref_topology(&self.prev_cousin)
    }

    /// First child of the next depth.
    pub fn first_child(&self) -> Option<&TopologyObject> {
        self.deref_topology(&self.first_child)
    }

    /// Last child of the next depth.
    pub fn last_child(&self) -> Option<&TopologyObject> {
        self.deref_topology(&self.last_child)
    }

    /// Last child of the next depth.
    pub fn parent(&self) -> Option<&TopologyObject> {
        self.deref_topology(&self.parent)
    }

    /// Previous object below the same parent.
    pub fn prev_sibling(&self) -> Option<&TopologyObject> {
        self.deref_topology(&self.prev_sibling)
    }

    /// Next object below the same parent.
    pub fn next_sibling(&self) -> Option<&TopologyObject> {
        self.deref_topology(&self.next_sibling)
    }

    /// CPUs covered by this object.
    ///
    /// This is the set of CPUs for which there are PU objects in the
    /// topology under this object, i.e. which are known to be physically
    /// contained in this object and known how (the children path between this
    /// object and the PU objects).
    pub fn cpuset(&self) -> Option<CpuSet> {
        self.deref_cpuset(self.cpuset)
    }

    /// The complete CPU set of logical processors of this object.
    ///
    /// This includes not only the same as the cpuset field, but also the
    /// CPUs for which topology information is unknown or incomplete, and the
    /// CPUs that are ignored when the HWLOC_TOPOLOGY_FLAG_WHOLE_SYSTEM flag is
    /// not set. Thus no corresponding PU object may be found in the topology,
    /// because the precise position is undefined. It is however known that it
    /// would be somewhere under this object.
    pub fn complete_cpuset(&self) -> Option<CpuSet> {
        self.deref_cpuset(self.complete_cpuset)
    }

    /// NUMA nodes covered by this object or containing this object.
    ///
    /// This is the set of NUMA nodes for which there are NODE objects in the topology under or
    // above this object, i.e. which are known to be physically contained in this object or
    /// containing it and known how (the children path between this object and the NODE objects).
    ///
    /// In the end, these nodes are those that are close to the current object.
    /// If the HWLOC_TOPOLOGY_FLAG_WHOLE_SYSTEM configuration flag is set, some of these nodes may
    /// not be allowed for allocation, see allowed_nodeset.
    ///
    /// If there are no NUMA nodes in the machine, all the memory is close to this object, so the
    /// nodeset is full.
    pub fn nodeset(&self) -> Option<NodeSet> {
        self.deref_nodeset(self.nodeset)
    }

    /// The complete NUMA node set of this object,.
    ///
    /// This includes not only the same as the nodeset field, but also the NUMA nodes for which
    /// topology information is unknown or incomplete, and the nodes that are ignored when the
    /// HWLOC_TOPOLOGY_FLAG_WHOLE_SYSTEM flag is not set. Thus no corresponding NODE object may
    /// be found in the topology, because the precise position is undefined. It is however known
    /// that it would be somewhere under this object.
    ///
    /// If there are no NUMA nodes in the machine, all the memory is close to this object, so
    /// complete_nodeset is full.
    pub fn complete_nodeset(&self) -> Option<NodeSet> {
        self.deref_nodeset(self.complete_nodeset)
    }

    fn deref_topology(&self, p: &*mut TopologyObject) -> Option<&TopologyObject> {
        unsafe {
            if p.is_null() {
                None
            } else {
                Some(&**p)
            }
        }
    }

    // FIXME: This allows the user to modify the CPUSet, which is undesirable,
    //        introduce a view type to prevent this
    fn deref_cpuset(&self, p: *mut IntHwlocBitmap) -> Option<CpuSet> {
        if p.is_null() {
            None
        } else {
            Some(CpuSet::from_raw(p, false))
        }
    }

    // FIXME: This allows the user to modify the NodeSet, which is undesirable,
    //        introduce a view type to prevent this
    fn deref_nodeset(&self, p: *mut IntHwlocBitmap) -> Option<NodeSet> {
        if p.is_null() {
            None
        } else {
            Some(NodeSet::from_raw(p, false))
        }
    }

    // FIXME: This assumes that the hwloc_obj_attr_u union is always a cache.
    //        Must check that it is indeed a cache first!
    fn cache_attributes(&self) -> Option<&TopologyObjectCacheAttributes> {
        let cache_ptr = unsafe { (*self.attr).cache() };
        if cache_ptr.is_null() {
            None
        } else {
            unsafe { Some(&*cache_ptr) }
        }
    }

    /// Get TopologyObject infos
    pub fn infos(&self) -> &[TopologyObjectInfo] {
        let len = if self.infos.is_null() {
            0
        } else {
            self.infos_count as usize
        };
        unsafe { std::slice::from_raw_parts(self.infos, len) }
    }
}

impl fmt::Display for TopologyObject {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut buf_type = [0; 64];
        let mut buf_attr = [0; 2048];
        let separator_ptr = b"  \0".as_ptr() as *const c_char;

        unsafe {
            ffi::hwloc_obj_type_snprintf(
                buf_type.as_mut_ptr(),
                64,
                self as *const TopologyObject,
                0,
            );
            ffi::hwloc_obj_attr_snprintf(
                buf_attr.as_mut_ptr(),
                2048,
                self as *const TopologyObject,
                separator_ptr,
                0,
            );

            write!(
                f,
                "{} ({})",
                CStr::from_ptr(buf_type.as_ptr()).to_str().unwrap(),
                CStr::from_ptr(buf_attr.as_ptr()).to_str().unwrap()
            )
        }
    }
}

impl fmt::Debug for TopologyObject {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

#[repr(C)]
pub struct TopologyObjectMemory {
    total_memory: c_ulonglong,
    local_memory: c_ulonglong,
    page_types_len: c_uint,                        // todo: getter
    page_types: *mut TopologyObjectMemoryPageType, // todo: getter
}

impl TopologyObjectMemory {
    /// The total memory (in bytes) in this object and its children.
    pub fn total_memory(&self) -> u64 {
        self.total_memory
    }

    /// The local memory (in bytes) in this object.
    pub fn local_memory(&self) -> u64 {
        self.local_memory
    }
}

#[repr(C)]
pub struct TopologyObjectMemoryPageType {
    size: c_ulonglong,
    count: c_ulonglong,
}

#[repr(C)]
pub struct TopologyObjectInfo {
    name: *mut c_char,
    value: *mut c_char,
}

impl TopologyObjectInfo {
    pub const NAME_OF_CPU_VENDOR: &'static str = "CPUVendor";
    pub const NAME_OF_CPU_MODEL: &'static str = "CPUModel";
    pub const NAME_OF_CPU_FAMILY_NUMBER: &'static str = "CPUFamilyNumber";
    pub const NAME_OF_CPU_MODEL_NUMBER: &'static str = "CPUModelNumber";
    pub const NAME_OF_CPU_STEPPING: &'static str = "CPUStepping";
    pub const NAME_OF_BACKEND: &'static str = "Backend";
    pub const NAME_OF_OS_NAME: &'static str = "OSName";
    pub const NAME_OF_OS_RELEASE: &'static str = "OSRelease";
    pub const NAME_OF_OS_VERSION: &'static str = "OSVersion";
    pub const NAME_OF_OS_HOST_NAME: &'static str = "HostName";
    pub const NAME_OF_OS_ARCHITECTURE: &'static str = "Architecture";
    pub const NAME_OF_OS_HWLOC_VERSION: &'static str = "hwlocVersion";
    pub const NAME_OF_OS_PROCESS_NAME: &'static str = "ProcessName";

    /// The name of the ObjectInfo
    pub fn name(&self) -> &CStr {
        unsafe { CStr::from_ptr(self.name) }
    }

    /// The value of the ObjectInfo
    pub fn value(&self) -> &CStr {
        unsafe { CStr::from_ptr(self.value) }
    }
}

#[repr(C)]
pub struct TopologyObjectDistances {
    relative_depth: c_uint,
    nbobjs: c_uint,
    latency: *mut c_float, // TODO: getter (expose properly)
    latency_max: c_float,
    latency_base: c_float,
}

impl TopologyObjectDistances {
    /// Relative depth of the considered objects below the
    /// object containing this distance information.
    pub fn relative_depth(&self) -> u32 {
        self.relative_depth
    }

    /// Number of objects considered in the matrix.
    ///
    /// It is the number of descendant objects at relative_depth below
    /// the containing object.
    pub fn number_of_objects(&self) -> u32 {
        self.nbobjs
    }

    /// The maximal value in the latency matrix.
    pub fn max_latency(&self) -> f32 {
        self.latency_max
    }

    /// The multiplier that should be applied to latency matrix to
    /// retrieve the original OS-provided latencies.
    ///
    /// Usually 10 on Linux since ACPI SLIT uses 10 for local latency.
    pub fn base_latency(&self) -> f32 {
        self.latency_base
    }
}

#[cfg(not(feature = "32bits_pci_domain"))]
const TOPOLOGY_OBJECT_ATTRIBUTES_SIZE: usize = 5;
#[cfg(feature = "32bits_pci_domain")]
const TOPOLOGY_OBJECT_ATTRIBUTES_SIZE: usize = 6;

#[repr(C)]
pub struct TopologyObjectAttributes {
    _bindgen_data_: [u64; TOPOLOGY_OBJECT_ATTRIBUTES_SIZE],
}

impl TopologyObjectAttributes {
    pub unsafe fn numa(&mut self) -> *mut TopologyObjectNUMANodeAttributes {
        let raw: *mut u8 =
            &self._bindgen_data_ as *const [u64; TOPOLOGY_OBJECT_ATTRIBUTES_SIZE] as *mut u8;
        ::std::mem::transmute(raw.offset(0))
    }
    pub unsafe fn cache(&mut self) -> *mut TopologyObjectCacheAttributes {
        let raw: *mut u8 =
            &self._bindgen_data_ as *const [u64; TOPOLOGY_OBJECT_ATTRIBUTES_SIZE] as *mut u8;
        ::std::mem::transmute(raw.offset(0))
    }
    pub unsafe fn group(&mut self) -> *mut TopologyObjectGroupAttributes {
        let raw: *mut u8 =
            &self._bindgen_data_ as *const [u64; TOPOLOGY_OBJECT_ATTRIBUTES_SIZE] as *mut u8;
        ::std::mem::transmute(raw.offset(0))
    }
    pub unsafe fn pcidev(&mut self) -> *mut TopologyObjectPCIDevAttributes {
        let raw: *mut u8 =
            &self._bindgen_data_ as *const [u64; TOPOLOGY_OBJECT_ATTRIBUTES_SIZE] as *mut u8;
        ::std::mem::transmute(raw.offset(0))
    }
    pub unsafe fn bridge(&mut self) -> *mut TopologyObjectBridgeAttributes {
        let raw: *mut u8 =
            &self._bindgen_data_ as *const [u64; TOPOLOGY_OBJECT_ATTRIBUTES_SIZE] as *mut u8;
        ::std::mem::transmute(raw.offset(0))
    }
    pub unsafe fn osdev(&mut self) -> *mut TopologyObjectOSDevAttributes {
        let raw: *mut u8 =
            &self._bindgen_data_ as *const [u64; TOPOLOGY_OBJECT_ATTRIBUTES_SIZE] as *mut u8;
        ::std::mem::transmute(raw.offset(0))
    }
}

#[repr(C)]
pub struct TopologyObjectNUMANodePageTypeAttributes {
    pub size: u64,
    pub count: u64,
}

#[repr(C)]
pub struct TopologyObjectNUMANodeAttributes {
    pub local_memory: u64,
    pub page_types_len: c_uint,
    pub page_types: *mut TopologyObjectNUMANodePageTypeAttributes,
}

#[repr(C)]
pub struct TopologyObjectCacheAttributes {
    pub size: c_ulonglong,
    pub depth: c_uint,
    pub linesize: c_uint,
    pub associativity: c_int,
    pub _type: TopologyObjectCacheType,
}

impl TopologyObjectCacheAttributes {
    pub fn size(&self) -> u64 {
        self.size
    }

    pub fn depth(&self) -> u32 {
        self.depth
    }
}

#[repr(C)]
pub enum TopologyObjectCacheType {
    Unified = 0,
    Data = 1,
    Instruction = 2,
}

#[repr(C)]
pub struct TopologyObjectGroupAttributes {
    depth: c_uint,
    kind: c_uint,
    subkind: c_uint,
    dont_merge: c_uchar,
}

#[repr(C)]
pub struct TopologyObjectPCIDevAttributes {
    #[cfg(not(feature = "32bits_pci_domain"))]
    domain: c_ushort,
    #[cfg(feature = "32bits_pci_domain")]
    domain: c_uint,
    bus: c_uchar,
    dev: c_uchar,
    func: c_uchar,
    class_id: c_ushort,
    vendor_id: c_ushort,
    device_id: c_ushort,
    subvendor_id: c_ushort,
    subdevice_id: c_ushort,
    revision: c_uchar,
    linkspeed: c_float,
}

#[repr(C)]
pub struct TopologyObjectBridgeDownstreamPCIAttributes {
    #[cfg(not(feature = "32bits_pci_domain"))]
    domain: c_ushort,
    #[cfg(feature = "32bits_pci_domain")]
    domain: c_uint,
    secondary_bus: c_uchar,
    subordinate_bus: c_uchar,
}

#[repr(C)]
pub struct TopologyObjectBridgeAttributes {
    upstream: TopologyObjectPCIDevAttributes,
    upstream_type: TopologyObjectBridgeType,
    downstream: TopologyObjectBridgeDownstreamPCIAttributes,
    downstream_type: TopologyObjectBridgeType,
    depth: c_uint,
}

#[repr(C)]
pub enum TopologyObjectBridgeType {
    Host = 0,
    PCI = 1,
}

#[repr(C)]
pub struct TopologyObjectOSDevAttributes {
    _type: TopologyObjectOSDevType,
}

#[repr(C)]
pub enum TopologyObjectOSDevType {
    Block = 0,
    GPU = 1,
    Network = 2,
    OpenFabrics = 3,
    DMA = 4,
    COPROC = 5,
}
