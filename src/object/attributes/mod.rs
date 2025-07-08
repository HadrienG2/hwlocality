//! Object attributes
//!
//! Some [`TopologyObject` types](ObjectType) come with supplementary attributes
//! that extend the object's description. These attributes can be accessed using
//! the [`TopologyObject::attributes()`] method, and are described using types
//! defined inside of this module.

// - Main docs: https://hwloc.readthedocs.io/en/v2.9/unionhwloc__obj__attr__u.html
// - Union semantics: https://hwloc.readthedocs.io/en/v2.9/attributes.html#attributes_normal

mod bridge;
mod cache;
mod group;
mod numa;
mod osdev;
mod pci;

#[cfg(doc)]
use crate::object::TopologyObject;
use crate::{ffi::transparent::AsNewtype, object::types::ObjectType};
use hwlocality_sys::hwloc_obj_attr_u;
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::fmt::Debug;

// Re-export all the attribute types
pub use self::{bridge::*, cache::*, group::*, numa::*, osdev::*, pci::*};

/// ObjectType-specific attributes
#[derive(Copy, Clone, Debug, PartialEq)]
#[doc(alias = "hwloc_obj_attr_u")]
pub enum ObjectAttributes<'object> {
    /// [`NUMANode`]-specific attributes
    ///
    /// [`NUMANode`]: ObjectType::NUMANode
    #[doc(alias = "hwloc_obj_attr_u::numanode")]
    NUMANode(&'object NUMANodeAttributes<'object>),

    /// CPU cache-specific attributes
    #[doc(alias = "hwloc_obj_attr_u::cache")]
    Cache(&'object CacheAttributes),

    /// [`Group`]-specific attributes
    ///
    /// [`Group`]: ObjectType::Group
    #[doc(alias = "hwloc_obj_attr_u::group")]
    Group(&'object GroupAttributes),

    /// [`PCIDevice`]-specific attributes
    ///
    /// [`PCIDevice`]: ObjectType::PCIDevice
    #[doc(alias = "hwloc_obj_attr_u::pcidev")]
    PCIDevice(&'object PCIDeviceAttributes),

    /// [`Bridge`]-specific attributes
    ///
    /// [`Bridge`]: ObjectType::Bridge
    #[doc(alias = "hwloc_obj_attr_u::bridge")]
    Bridge(&'object BridgeAttributes),

    /// [`OSDevice`]-specific attributes
    ///
    /// [`OSDevice`]: ObjectType::OSDevice
    #[doc(alias = "hwloc_obj_attr_u::osdev")]
    OSDevice(&'object OSDeviceAttributes),
}
//
impl<'object> ObjectAttributes<'object> {
    /// Wrap the hwloc object type specific attributes behind a safe API
    ///
    /// # Safety
    ///
    /// If non-null, the `attr` pointer must target `hwloc_obj_attr_u` that
    /// are valid for lifetime `'object` and consistent with object type `ty`.
    #[allow(clippy::wildcard_enum_match_arm)]
    pub(crate) unsafe fn new(ty: ObjectType, attr: &'object *mut hwloc_obj_attr_u) -> Option<Self> {
        if attr.is_null() {
            return None;
        }
        // SAFETY: Safe due to input precondition
        let attr: &hwloc_obj_attr_u = unsafe { &**attr };

        // SAFETY: - We checked for union field access validity via the type
        //         - Type is truted to match union state per input precondition
        unsafe {
            match ty {
                ObjectType::NUMANode => Some(Self::NUMANode((&attr.numa).as_newtype())),
                ObjectType::Group => Some(Self::Group((&attr.group).as_newtype())),
                ObjectType::PCIDevice => Some(Self::PCIDevice((&attr.pcidev).as_newtype())),
                ObjectType::Bridge => Some(Self::Bridge((&attr.bridge).as_newtype())),
                ObjectType::OSDevice => Some(Self::OSDevice((&attr.osdev).as_newtype())),
                _ if ty.is_cpu_cache() => Some(Self::Cache((&attr.cache).as_newtype())),
                _ => None,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::{
        bridge::tests::check_valid_bridge, cache::tests::check_valid_cache,
        group::tests::check_valid_group, numa::tests::check_valid_numa,
        osdev::tests::check_valid_osdev, pci::tests::check_valid_pci,
    };
    use crate::{
        object::{
            types::{BridgeType, CacheType},
            TopologyObject,
        },
        topology::Topology,
    };
    use proptest::{prelude::*, sample::Selector};
    #[allow(unused)]
    use similar_asserts::assert_eq;
    use static_assertions::{assert_impl_all, assert_not_impl_any};
    use std::{
        fmt::{self, Binary, Display, LowerExp, LowerHex, Octal, Pointer, UpperExp, UpperHex},
        io::{self, Read},
        ops::Deref,
        panic::UnwindSafe,
        sync::OnceLock,
    };

    // Check that public types in this module keep implementing all expected
    // traits, in the interest of detecting future semver-breaking changes
    assert_impl_all!(ObjectAttributes<'static>:
        Copy, Debug, PartialEq, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(ObjectAttributes<'static>:
        Binary, Default, Deref, Display, Drop, Eq, IntoIterator, LowerExp,
        LowerHex, Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex,
        fmt::Write, io::Write
    );

    proptest! {
        #[test]
        fn unary_nonexistent(ty: ObjectType, osdev_attr: OSDeviceAttributes) {
            // SAFETY: Sending in a null pointer is safe
            let is_nonexistent = unsafe { ObjectAttributes::new(ty, &std::ptr::null_mut()).is_none() };
            prop_assert!(is_nonexistent);

            // ...and types that have no attributes are safe as well
            let check_nonexistent = || {
                let mut raw = hwloc_obj_attr_u {
                    osdev: osdev_attr.0,
                };
                let ptr: *mut hwloc_obj_attr_u = &mut raw;
                // SAFETY: Types with associated attributes have all been
                //         covered above, so None is the only outcome and union
                //         variant doesn't matter.
                let is_nonexistent = unsafe { ObjectAttributes::new(ty, &ptr).is_none() };
                prop_assert!(is_nonexistent);
                Ok(())
            };
            match ty {
                ObjectType::NUMANode
                | ObjectType::Group
                | ObjectType::PCIDevice
                | ObjectType::Bridge
                | ObjectType::OSDevice
                | ObjectType::L1Cache
                | ObjectType::L2Cache
                | ObjectType::L3Cache
                | ObjectType::L4Cache
                | ObjectType::L5Cache
                | ObjectType::L1ICache
                | ObjectType::L2ICache
                | ObjectType::L3ICache => {}
                ObjectType::Machine
                | ObjectType::Package
                | ObjectType::Core
                | ObjectType::PU
                | ObjectType::Misc => check_nonexistent()?,
                #[cfg(feature = "hwloc-2_1_0")]
                ObjectType::MemCache | ObjectType::Die => check_nonexistent()?,
                ObjectType::Unknown(_) => {}
            }
        }
    }

    /// Check properties that should be true of all topology objects
    #[test]
    fn unary_valid() -> Result<(), TestCaseError> {
        for obj in Topology::test_objects() {
            check_valid_object(obj.object_type(), obj.attributes())?;
            match obj.attributes() {
                Some(ObjectAttributes::NUMANode(attr)) => {
                    prop_assert_eq!(
                        attr.local_memory().map_or(0u64, u64::from),
                        obj.total_memory()
                    );
                }
                Some(ObjectAttributes::Cache(attr)) => match attr.cache_type() {
                    CacheType::Unified | CacheType::Data => {
                        prop_assert!(obj.object_type().is_cpu_data_cache());
                    }
                    CacheType::Instruction => {
                        prop_assert!(obj.object_type().is_cpu_instruction_cache());
                    }
                    CacheType::Unknown(_) => {}
                },
                #[allow(unused)]
                Some(ObjectAttributes::Group(attr)) => {
                    #[cfg(feature = "hwloc-2_0_4")]
                    prop_assert!(!attr.merging_prevented());
                }
                Some(ObjectAttributes::PCIDevice(pci)) => {
                    let Some(ObjectAttributes::Bridge(bridge)) = obj.parent().unwrap().attributes()
                    else {
                        panic!("PCI devices should have a Bridge parent")
                    };
                    prop_assert_eq!(bridge.downstream_type(), BridgeType::PCI);
                    let Some(DownstreamAttributes::PCI(downstream)) =
                        bridge.downstream_attributes()
                    else {
                        panic!("Parent of PCI device should have a PCI downstream")
                    };
                    prop_assert_eq!(downstream.domain(), pci.domain());
                }
                Some(ObjectAttributes::Bridge(attr)) => {
                    let parent_type = obj.parent().unwrap().object_type();
                    let has_pci_parent = (parent_type == ObjectType::PCIDevice)
                        || (parent_type == ObjectType::Bridge);
                    match attr.upstream_type() {
                        BridgeType::PCI => prop_assert!(has_pci_parent),
                        BridgeType::Host => prop_assert!(!has_pci_parent),
                        BridgeType::Unknown(_) => {}
                    }
                }
                Some(ObjectAttributes::OSDevice(_attr)) => {
                    // Nothing else we can check knowing the topology around
                }
                None => {}
            }
        }
        Ok(())
    }

    /// List of objects from the test topology that have attributes
    pub(super) struct ObjectsWithAttrs {
        pub(crate) numa_nodes: Box<[&'static TopologyObject]>,
        pub(crate) caches: Box<[&'static TopologyObject]>,
        pub(crate) groups: Box<[&'static TopologyObject]>,
        pub(crate) pci_devices: Box<[&'static TopologyObject]>,
        pub(crate) bridges: Box<[&'static TopologyObject]>,
    }
    //
    impl ObjectsWithAttrs {
        /// Memoized instance of [`ObjectsWithAttrs`]
        pub(crate) fn instance() -> &'static Self {
            static INSTANCE: OnceLock<ObjectsWithAttrs> = OnceLock::new();
            INSTANCE.get_or_init(|| {
                let topology = Topology::test_instance();
                Self {
                    numa_nodes: topology.objects_with_type(ObjectType::NUMANode).collect(),
                    caches: topology
                        .normal_objects()
                        .filter(|obj| obj.object_type().is_cpu_cache())
                        .collect(),
                    groups: topology.objects_with_type(ObjectType::Group).collect(),
                    pci_devices: topology.objects_with_type(ObjectType::PCIDevice).collect(),
                    bridges: topology.objects_with_type(ObjectType::Bridge).collect(),
                }
            })
        }
    }

    /// Strategy that selects pairs of objects from pre-computed lists
    pub(super) fn object_pair(
        type1: &'static [&'static TopologyObject],
        type2: &'static [&'static TopologyObject],
    ) -> impl Strategy<Value = Option<[&'static TopologyObject; 2]>> {
        (any::<(Selector, Selector)>()).prop_map(move |(sel1, sel2)| {
            let obj1 = sel1.try_select(type1.iter().copied())?;
            let obj2 = sel2.try_select(type2.iter().copied())?;
            Some([obj1, obj2])
        })
    }

    /// Check object attributes under the assumption that the inner data is in a
    /// valid state (no boolean representation equal to 42, etc)
    fn check_valid_object(
        ty: ObjectType,
        attr: Option<ObjectAttributes<'_>>,
    ) -> Result<(), TestCaseError> {
        match (ty, attr) {
            (ObjectType::NUMANode, Some(ObjectAttributes::NUMANode(attr))) => {
                check_valid_numa(attr)?
            }
            (cache, Some(ObjectAttributes::Cache(attr))) if cache.is_cpu_cache() => {
                check_valid_cache(attr)?
            }
            (ObjectType::Group, Some(ObjectAttributes::Group(attr))) => check_valid_group(attr)?,
            (ObjectType::PCIDevice, Some(ObjectAttributes::PCIDevice(attr))) => {
                check_valid_pci(attr)?
            }
            (ObjectType::Bridge, Some(ObjectAttributes::Bridge(attr))) => check_valid_bridge(attr)?,
            (ObjectType::OSDevice, Some(ObjectAttributes::OSDevice(attr))) => {
                check_valid_osdev(attr)?
            }
            (_, None) => {}
            _ => unreachable!(),
        }
        Ok(())
    }

    /// If obj1 and obj2 have a parent-child relationship, provide their
    /// attributes in (parent, child) order.
    pub(crate) fn parent_child<Attributes>(
        [(obj1, attr1), (obj2, attr2)]: [(&TopologyObject, Attributes); 2],
    ) -> Option<[Attributes; 2]> {
        if obj1.is_in_subtree(obj2) {
            Some([attr2, attr1])
        } else if obj2.is_in_subtree(obj1) {
            Some([attr1, attr2])
        } else {
            None
        }
    }
}
