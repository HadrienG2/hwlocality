//! Topology objects

// - Top-level doc: https://hwloc.readthedocs.io/en/v2.9/structhwloc__obj.html
// - Attributes: https://hwloc.readthedocs.io/en/v2.9/attributes.html

pub mod attributes;
pub mod types;

use self::{
    attributes::{ObjectAttributes, ObjectInfo, RawObjectAttributes},
    types::{ObjectType, RawObjectType},
};
#[cfg(doc)]
use crate::builder::BuildFlags;
use crate::{
    bitmap::{CpuSet, NodeSet, RawBitmap},
    depth::{Depth, RawDepth},
    ffi::{self, LibcString},
};
use libc::{c_char, c_int, c_uint, c_void};
use std::{ffi::CStr, fmt};

/// Hardware topology object
//
// See the matching method names for more details on field semantics
#[repr(C)]
pub struct TopologyObject {
    object_type: RawObjectType,
    subtype: *mut c_char,
    os_index: c_uint,
    name: *mut c_char,
    total_memory: u64,
    attr: *mut RawObjectAttributes,
    depth: RawDepth,
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
    misc_arity: c_uint,
    misc_first_child: *mut TopologyObject,
    cpuset: *mut RawBitmap,
    complete_cpuset: *mut RawBitmap,
    nodeset: *mut RawBitmap,
    complete_nodeset: *mut RawBitmap,
    infos: *mut ObjectInfo,
    infos_count: c_uint,
    __userdata: *mut c_void, // BEWARE: Topology duplication blindly duplicates this!
    gp_index: u64,
}

impl TopologyObject {
    /// Type of object.
    pub fn object_type(&self) -> ObjectType {
        self.object_type
            .try_into()
            .expect("Got unexpected object type")
    }

    /// Subtype string to better describe the type field
    ///
    /// See <https://hwloc.readthedocs.io/en/v2.9/attributes.html#attributes_normal>
    /// for a list of subtype strings that hwloc can emit.
    pub fn subtype(&self) -> Option<&str> {
        unsafe { ffi::deref_string(&self.subtype) }
    }

    /// Set the subtype string
    ///
    /// This is something you'll often want to do when creating Group or Misc
    /// objects in order to make them more descriptive.
    ///
    /// # Panics
    ///
    /// This function will panic if the requested string contains NUL bytes, as
    /// hwloc, like all C libraries, doesn't handle that well.
    pub fn set_subtype(&mut self, subtype: &str) {
        self.subtype = LibcString::new(subtype)
            .expect("Can't have NUL bytes in subtype string")
            .into_raw()
    }

    /// The OS-provided physical index number.
    ///
    /// It is not guaranteed unique across the entire machine,
    /// except for PUs and NUMA nodes.
    ///
    /// Not specified if unknown or irrelevant for this object.
    pub fn os_index(&self) -> Option<u32> {
        const HWLOC_UNKNOWN_INDEX: c_uint = c_uint::MAX;
        (self.os_index != HWLOC_UNKNOWN_INDEX).then_some(self.os_index)
    }

    /// The name of the object
    pub fn name(&self) -> Option<&str> {
        unsafe { ffi::deref_string(&self.name) }
    }

    /// Set the object name
    ///
    /// This is something you'll often want to do when creating Group or Misc
    /// objects in order to make them more descriptive.
    ///
    /// # Panics
    ///
    /// This function will panic if the requested string contains NUL bytes, as
    /// hwloc, like all C libraries, doesn't handle that well.
    pub fn set_name(&mut self, name: &str) {
        self.name = LibcString::new(name)
            .expect("Can't have NUL bytes in name string")
            .into_raw()
    }

    /// Total memory (in bytes) in NUMA nodes below this object
    pub fn total_memory(&self) -> u64 {
        self.total_memory
    }

    /// Object type-specific attributes
    pub fn attributes(&self) -> Option<ObjectAttributes> {
        unsafe { ObjectAttributes::new(self.object_type(), &self.attr) }
    }

    /// Unsafe access to object type-specific attributes
    pub(crate) fn raw_attributes(&mut self) -> Option<&mut RawObjectAttributes> {
        unsafe { ffi::deref_mut_ptr(&mut self.attr) }
    }

    /// Vertical index in the hierarchy
    ///
    /// For normal objects, this is the depth of the horizontal level that
    /// contains this object and its cousins of the same type. If the topology
    /// is symmetric, this is equal to the parent depth plus one, and also equal
    /// to the number of parent/child links from the root object to here.
    ///
    /// For special objects (NUMA nodes, I/O and Misc) that are not in the main
    /// tree, this is a special value that is unique to their type.
    pub fn depth(&self) -> Depth {
        self.depth.try_into().expect("Got unexpected depth value")
    }

    /// Horizontal index in the whole list of similar objects, hence guaranteed
    /// unique across the entire machine.
    ///
    /// Could be a "cousin_rank" since it's the rank within the "cousin" list below.
    ///
    /// Note that this index may change when restricting the topology
    /// or when inserting a group.
    pub fn logical_index(&self) -> u32 {
        self.logical_index
    }

    /// Next object of same type and depth
    pub fn next_cousin(&self) -> Option<&TopologyObject> {
        unsafe { ffi::deref_ptr_mut(&self.next_cousin) }
    }

    /// Previous object of same type and depth
    pub fn prev_cousin(&self) -> Option<&TopologyObject> {
        unsafe { ffi::deref_ptr_mut(&self.prev_cousin) }
    }

    /// Parent object
    pub fn parent(&self) -> Option<&TopologyObject> {
        unsafe { ffi::deref_ptr_mut(&self.parent) }
    }

    /// Index in the parent's appropriate child list
    pub fn sibling_rank(&self) -> u32 {
        self.sibling_rank
    }

    /// Next object below the same parent in the same child list
    pub fn next_sibling(&self) -> Option<&TopologyObject> {
        unsafe { ffi::deref_ptr_mut(&self.next_sibling) }
    }

    /// Previous object below the same parent in the same child list
    pub fn prev_sibling(&self) -> Option<&TopologyObject> {
        unsafe { ffi::deref_ptr_mut(&self.prev_sibling) }
    }

    /// Number of normal children (excluding Memory, Misc and I/O)
    pub fn normal_arity(&self) -> u32 {
        self.arity
    }

    /// Normal children of this object (excluding Memory, Misc and I/O)
    pub fn normal_children(&self) -> impl Iterator<Item = &TopologyObject> {
        if self.children.is_null() {
            assert_eq!(
                self.normal_arity(),
                0,
                "Got null children pointer with nonzero arity"
            );
        }
        (0..self.normal_arity()).map(move |i| {
            // If this fails, it means self.arity does not fit in a
            // size_t, but by definition of size_t that cannot happen...
            let offset = isize::try_from(i).expect("Should not happen");
            let child = unsafe { *self.children.offset(offset) };
            assert!(!child.is_null(), "Got null child pointer");
            unsafe { &*child }
        })
    }

    /// First normal child
    pub fn first_normal_child(&self) -> Option<&TopologyObject> {
        unsafe { ffi::deref_ptr_mut(&self.first_child) }
    }

    /// Last normal child
    pub fn last_normal_child(&self) -> Option<&TopologyObject> {
        unsafe { ffi::deref_ptr_mut(&self.last_child) }
    }

    /// Truth that this object is symmetric, which means all normal children and
    /// their children have identical subtrees.
    ///
    /// Memory, I/O and Misc children are ignored.
    pub fn symmetric_subtree(&self) -> bool {
        self.symmetric_subtree != 0
    }

    /// Number of memory children
    pub fn memory_arity(&self) -> u32 {
        self.memory_arity
    }

    /// Memory children of this object
    ///
    /// NUMA nodes and Memory-side caches are listed here instead of in the
    /// [`TopologyObject::normal_children()`] list. See also
    /// [`ObjectType::is_memory()`].
    ///
    /// A memory hierarchy starts from a normal CPU-side object (e.g. Package)
    /// and ends with NUMA nodes as leaves. There might exist some memory-side
    /// caches between them in the middle of the memory subtree.
    pub fn memory_children(&self) -> impl Iterator<Item = &TopologyObject> {
        unsafe { Self::iter_linked_children(&self.memory_first_child) }
    }

    /// Number of I/O children.
    pub fn io_arity(&self) -> u32 {
        self.io_arity
    }

    /// I/O children of this object
    ///
    /// Bridges, PCI and OS devices are listed here instead of in the
    /// [`TopologyObject::normal_children()`] list. See also
    /// [`ObjectType::is_io()`].
    pub fn io_children(&self) -> impl Iterator<Item = &TopologyObject> {
        unsafe { Self::iter_linked_children(&self.io_first_child) }
    }

    /// Number of Misc children.
    pub fn misc_arity(&self) -> u32 {
        self.misc_arity
    }

    /// Misc children of this object
    ///
    /// Mist objects are listed here instead of in the
    /// [`TopologyObject::normal_children()`] list.
    pub fn misc_children(&self) -> impl Iterator<Item = &TopologyObject> {
        unsafe { Self::iter_linked_children(&self.io_first_child) }
    }

    /// CPUs covered by this object.
    ///
    /// This is the set of CPUs for which there are PU objects in the
    /// topology under this object, i.e. which are known to be physically
    /// contained in this object and known how (the children path between this
    /// object and the PU objects).
    ///
    /// If the [`BuildFlags::INCLUDE_DISALLOWED`] topology building
    /// configuration flag is set, some of these CPUs may be online but not
    /// allowed for binding, see `Topology::get_allowed_cpuset()` (TODO: wrap and link).
    ///
    /// All objects have CPU and node sets except Misc and I/O objects.
    pub fn cpuset(&self) -> Option<&CpuSet> {
        unsafe { CpuSet::borrow_from_raw(&self.cpuset) }
    }

    /// The complete CPU set of logical processors of this object.
    ///
    /// This includes not only the same as the cpuset field, but also the
    /// CPUs for which topology information is unknown or incomplete, some
    /// offline CPUs, and the CPUs that are ignored when the
    /// [`BuildFlags::INCLUDE_DISALLOWED`] topology building configuration flag
    /// is not set.
    ///
    /// Thus no corresponding PU object may be found in the topology, because
    /// the precise position is undefined. It is however known that it would be
    /// somewhere under this object.
    pub fn complete_cpuset(&self) -> Option<&CpuSet> {
        unsafe { CpuSet::borrow_from_raw(&self.complete_cpuset) }
    }

    /// NUMA nodes covered by this object or containing this object.
    ///
    /// This is the set of NUMA nodes for which there are NODE objects in the
    /// topology under or above this object, i.e. which are known to be
    /// physically contained in this object or containing it and known how (the
    /// children path between this object and the NODE objects).
    ///
    /// In the end, these nodes are those that are close to the current object.
    /// Function hwloc_get_local_numanode_objs() (TODO wrap and link) may be used to list
    /// those NUMA nodes more precisely.
    ///
    /// If the [`BuildFlags::INCLUDE_DISALLOWED`] topology building
    /// configuration flag is set, some of these nodes may not be allowed for
    /// allocation, see `Topology::allowed_nodeset()` (TODO wrap and link).
    ///
    /// If there are no NUMA nodes in the machine, all the memory is close to
    /// this object, so the nodeset is full.
    ///
    /// All objects have CPU and node sets except Misc and I/O objects.
    pub fn nodeset(&self) -> Option<&NodeSet> {
        unsafe { NodeSet::borrow_from_raw(&self.nodeset) }
    }

    /// The complete NUMA node set of this object,.
    ///
    /// This includes not only the same as the nodeset field, but also the NUMA
    /// nodes for which topology information is unknown or incomplete, some
    /// offline nodes, and the nodes that are ignored when the
    /// [`BuildFlags::INCLUDE_DISALLOWED`] topology building configuration flag
    /// is not set.
    ///
    /// Thus no corresponding NUMANode object may be found in the topology,
    /// because the precise position is undefined. It is however known that it
    /// would be somewhere under this object.
    ///
    /// If there are no NUMA nodes in the machine, all the memory is close to
    /// this object, so complete_nodeset is full.
    pub fn complete_nodeset(&self) -> Option<&NodeSet> {
        unsafe { NodeSet::borrow_from_raw(&self.complete_nodeset) }
    }

    /// Complete list of (key, value) textual info pairs
    pub fn infos(&self) -> &[ObjectInfo] {
        if self.children.is_null() {
            assert_eq!(
                self.infos_count, 0,
                "Got null infos pointer with nonzero info count"
            );
            return &[];
        }

        unsafe {
            std::slice::from_raw_parts(
                self.infos,
                // If this fails, it means infos_count does not fit in a
                // size_t, but by definition of size_t that cannot happen...
                usize::try_from(self.infos_count).expect("Should not happen"),
            )
        }
    }

    /// Search the given key name in object infos and return the corresponding value
    ///
    /// If multiple keys match the given name, only the first one is returned.
    ///
    /// Calling this operation multiple times will result in duplicate work. If
    /// you need to do this sort of search many times, you should collect
    /// `infos()` into a `HashMap` or `BTreeMap` for increased lookup efficiency.
    pub fn info(&self, key: &str) -> Option<&str> {
        self.infos()
            .iter()
            .find(|info| info.name() == key)
            .map(|info| info.value())
    }

    /// Add the given info name and value pair to the given object
    ///
    /// The info is appended to the existing info array even if another key with
    /// the same name already exists.
    ///
    /// The input strings are copied before being added in the object infos.
    ///
    /// This function may be used to enforce object colors in the lstopo
    /// graphical output by using "lstopoStyle" as a name and "Background=#rrggbb"
    /// as a value. See `CUSTOM COLORS` in the `lstopo(1)` manpage for details.
    ///
    /// If value contains some non-printable characters, they will be dropped
    /// when exporting to XML.
    pub fn add_info(&mut self, name: &str, value: &str) {
        let name = LibcString::new(name).expect("Name is not supported by hwloc");
        let value = LibcString::new(value).expect("Value is not supported by hwloc");
        let result = unsafe {
            ffi::hwloc_obj_add_info(self as *mut TopologyObject, name.borrow(), value.borrow())
        };
        assert_ne!(result, -1, "Failed to add info to object");
        assert_eq!(result, 0, "Unexpected result from hwloc_obj_add_info");
    }

    /// Iterate over a C-style linked list of child TopologyObjects
    unsafe fn iter_linked_children(
        start: &*mut TopologyObject,
    ) -> impl Iterator<Item = &TopologyObject> {
        let mut current = *start;
        std::iter::from_fn(move || {
            let child = (current.is_null()).then_some(unsafe { &*current })?;
            current = child.next_sibling;
            Some(child)
        })
    }

    /// Display the TopologyObject's type and attributes
    fn display(&self, f: &mut fmt::Formatter, verbose: bool) -> fmt::Result {
        let type_chars = ffi::call_snprintf(|buf, len| unsafe {
            ffi::hwloc_obj_type_snprintf(buf, len, self as *const TopologyObject, verbose.into())
        });

        let separator = if f.alternate() {
            b"\n  \0".as_ptr()
        } else {
            b"  \0".as_ptr()
        } as *const c_char;
        let attr_chars = ffi::call_snprintf(|buf, len| unsafe {
            ffi::hwloc_obj_attr_snprintf(
                buf,
                len,
                self as *const TopologyObject,
                separator,
                verbose.into(),
            )
        });

        unsafe {
            let type_str = CStr::from_ptr(type_chars.as_ptr())
                .to_str()
                .expect("Got invalid type string");
            let attr_str = CStr::from_ptr(attr_chars.as_ptr())
                .to_str()
                .expect("Got invalid attributes string");
            if attr_str.is_empty() {
                write!(f, "{type_str}")
            } else if f.alternate() {
                write!(f, "{type_str} (\n  {attr_str}\n)")
            } else {
                write!(f, "{type_str} ({attr_str})")
            }
        }
    }
}

impl fmt::Display for TopologyObject {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.display(f, false)
    }
}

impl fmt::Debug for TopologyObject {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.display(f, true)
    }
}

unsafe impl Send for TopologyObject {}
unsafe impl Sync for TopologyObject {}
