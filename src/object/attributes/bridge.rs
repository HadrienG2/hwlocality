//! [`Bridge`]-specific attributes
//!
//! [`Bridge`]: ObjectType::Bridge

use super::pci::{PCIDeviceAttributes, PCIDomain};
#[cfg(doc)]
use crate::object::types::ObjectType;
use crate::{
    ffi::{
        int,
        transparent::{AsNewtype, TransparentNewtype},
    },
    object::types::BridgeType,
};
#[cfg(any(test, feature = "proptest"))]
use hwlocality_sys::hwloc_obj_bridge_type_t;
use hwlocality_sys::{
    hwloc_bridge_attr_s, RawDownstreamAttributes, RawDownstreamPCIAttributes, RawUpstreamAttributes,
};
#[cfg(any(test, feature = "proptest"))]
use proptest::prelude::*;
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
#[cfg(any(test, feature = "proptest"))]
use std::ffi::c_uint;
use std::{
    fmt::{self, Debug},
    hash::Hash,
};

/// [`Bridge`]-specific attributes
///
/// [`Bridge`]: ObjectType::Bridge
//
// --- Implementation details ---
//
// # Safety
//
// - `upstream` and `upstream_type` are trusted to be in sync.
// - `downstream` and `downstream_type` are trusted to be in sync.
#[derive(Copy, Clone)]
#[doc(alias = "hwloc_bridge_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s")]
#[repr(transparent)]
pub struct BridgeAttributes(hwloc_bridge_attr_s);
//
impl BridgeAttributes {
    /// Upstream type
    #[doc(alias = "hwloc_bridge_attr_s::upstream_type")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::upstream_type")]
    pub fn upstream_type(&self) -> BridgeType {
        // SAFETY: Bridge type comes from hwloc
        unsafe { BridgeType::from_hwloc(self.0.upstream_type) }
    }

    /// Upstream attributes
    #[doc(alias = "hwloc_bridge_attr_s::upstream")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::upstream")]
    pub fn upstream_attributes(&self) -> Option<UpstreamAttributes<'_>> {
        // SAFETY: Per type invariant
        unsafe { UpstreamAttributes::new(self.upstream_type(), &self.0.upstream) }
    }

    /// Downstream type
    #[doc(alias = "hwloc_bridge_attr_s::downstream_type")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::downstream_type")]
    pub fn downstream_type(&self) -> BridgeType {
        // SAFETY: Bridge type comes from hwloc
        unsafe { BridgeType::from_hwloc(self.0.downstream_type) }
    }

    /// Downstream attributes
    #[doc(alias = "hwloc_bridge_attr_s::downstream")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::downstream")]
    pub fn downstream_attributes(&self) -> Option<DownstreamAttributes<'_>> {
        // SAFETY: Per type invariant
        unsafe { DownstreamAttributes::new(self.downstream_type(), &self.0.downstream) }
    }

    /// Bridge depth
    #[doc(alias = "hwloc_bridge_attr_s::depth")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_bridge_attr_s::depth")]
    pub fn depth(&self) -> usize {
        int::expect_usize(self.0.depth)
    }
}
//
#[cfg(any(test, feature = "proptest"))]
impl Arbitrary for BridgeAttributes {
    type Parameters =
        <(PCIDeviceAttributes, DownstreamPCIAttributes, c_uint) as Arbitrary>::Parameters;
    type Strategy = prop::strategy::Map<
        (
            [crate::strategies::EnumRepr<hwloc_obj_bridge_type_t>; 2],
            <(PCIDeviceAttributes, DownstreamPCIAttributes, c_uint) as Arbitrary>::Strategy,
        ),
        fn(
            (
                [hwloc_obj_bridge_type_t; 2],
                (PCIDeviceAttributes, DownstreamPCIAttributes, c_uint),
            ),
        ) -> Self,
    >;

    #[allow(unused)]
    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        let bridge_type = crate::strategies::enum_repr::<BridgeType, hwloc_obj_bridge_type_t>();
        (
            [bridge_type.clone(), bridge_type],
            <(PCIDeviceAttributes, DownstreamPCIAttributes, c_uint)>::arbitrary_with(args),
        )
            .prop_map(
                |([upstream_type, downstream_type], (upstream_pci, downstream_pci, depth))| {
                    Self(hwloc_bridge_attr_s {
                        upstream_type,
                        upstream: RawUpstreamAttributes {
                            pci: upstream_pci.0,
                        },
                        downstream_type,
                        downstream: RawDownstreamAttributes {
                            pci: downstream_pci.0,
                        },
                        depth,
                    })
                },
            )
    }
}
//
impl Debug for BridgeAttributes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug = f.debug_struct("BridgeAttributes");

        debug.field("upstream_type", &self.upstream_type());
        debug.field("upstream_attributes", &self.upstream_attributes());

        debug.field("downstream_type", &self.downstream_type());
        match self.downstream_type() {
            BridgeType::PCI => debug.field("downstream_attributes", &self.downstream_attributes()),
            BridgeType::Host | BridgeType::Unknown(_) => {
                debug.field("downstream_attributes", &format!("{:?}", self.0.downstream))
            }
        };

        debug.field("depth", &self.depth()).finish()
    }
}
//
impl PartialEq for BridgeAttributes {
    fn eq(&self, other: &Self) -> bool {
        self.upstream_type() == other.upstream_type()
            && self.upstream_attributes() == other.upstream_attributes()
            && self.downstream_type() == other.downstream_type()
            && self.downstream_attributes() == other.downstream_attributes()
            && self.depth() == other.depth()
    }
}
//
// SAFETY: BridgeAttributes is a repr(transparent) newtype of hwloc_bridge_attr_s
unsafe impl TransparentNewtype for BridgeAttributes {
    type Inner = hwloc_bridge_attr_s;
}

/// Bridge upstream attributes
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum UpstreamAttributes<'object> {
    /// PCI-specific attributes
    PCI(&'object PCIDeviceAttributes),
}
//
impl<'object> UpstreamAttributes<'object> {
    /// Wrap the upstream attributes behind a safe API
    ///
    /// # Safety
    ///
    /// `attr` must be consistent with `ty`.
    pub(crate) unsafe fn new(ty: BridgeType, attr: &'object RawUpstreamAttributes) -> Option<Self> {
        // SAFETY: attr.pci assumed valid if ty is PCI per input precondition
        unsafe {
            match ty {
                BridgeType::PCI => Some(Self::PCI((&attr.pci).as_newtype())),
                BridgeType::Host | BridgeType::Unknown(_) => None,
            }
        }
    }
}

/// Downstream PCI device attributes
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct DownstreamPCIAttributes(RawDownstreamPCIAttributes);
//
impl DownstreamPCIAttributes {
    /// PCI domain
    pub fn domain(&self) -> PCIDomain {
        self.0.domain
    }

    /// PCI secondary bus (= lowest downstream bus number)
    pub fn secondary_bus(&self) -> u8 {
        self.0.secondary_bus
    }

    /// PCI subordinate bus (= highest downstream bus number)
    pub fn subordinate_bus(&self) -> u8 {
        self.0.subordinate_bus
    }
}
//
#[cfg(any(test, feature = "proptest"))]
impl Arbitrary for DownstreamPCIAttributes {
    type Parameters = <(PCIDomain, [u8; 2]) as Arbitrary>::Parameters;
    type Strategy = prop::strategy::Map<
        <(PCIDomain, [u8; 2]) as Arbitrary>::Strategy,
        fn((PCIDomain, [u8; 2])) -> Self,
    >;

    #[allow(unused)]
    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        <(PCIDomain, [u8; 2])>::arbitrary_with(args).prop_map(
            |(domain, [secondary_bus, subordinate_bus])| {
                Self(RawDownstreamPCIAttributes {
                    domain,
                    secondary_bus,
                    subordinate_bus,
                })
            },
        )
    }
}
//
// SAFETY: DownstreamPCIAttributes is a repr(transparent) newtype of RawDownstreamPCIAttributes
unsafe impl TransparentNewtype for DownstreamPCIAttributes {
    type Inner = RawDownstreamPCIAttributes;
}

/// Bridge downstream attributes
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum DownstreamAttributes<'object> {
    /// PCI-specific attributes
    PCI(&'object DownstreamPCIAttributes),
}
//
impl<'object> DownstreamAttributes<'object> {
    /// Wrap the upstream attributes behind a safe API
    ///
    /// # Safety
    ///
    /// `attr` must be consistent with `ty`.
    #[allow(clippy::unnecessary_wraps)]
    pub(crate) unsafe fn new(
        ty: BridgeType,
        attr: &'object RawDownstreamAttributes,
    ) -> Option<Self> {
        // SAFETY: attr.pci assumed valid if ty is PCI per input precondition
        unsafe {
            match ty {
                BridgeType::PCI => Some(Self::PCI((&attr.pci).as_newtype())),
                BridgeType::Host => unreachable!("Host bridge type should not appear downstream"),
                BridgeType::Unknown(_) => None,
            }
        }
    }
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use crate::object::{
        attributes::{
            pci::tests::{check_any_pci, check_valid_pci, pci_attributes},
            tests::{object_pair, parent_child, ObjectsWithAttrs},
            ObjectAttributes,
        },
        ObjectType,
    };
    use crate::{ffi::transparent::AsInner, object::TopologyObject, tests::assert_panics};
    use hwlocality_sys::{hwloc_obj_attr_u, hwloc_pcidev_attr_s};
    #[allow(unused)]
    use similar_asserts::assert_eq;
    use static_assertions::{assert_impl_all, assert_not_impl_any};
    use std::{
        fmt::{Binary, Display, LowerExp, LowerHex, Octal, Pointer, UpperExp, UpperHex},
        io::{self, Read},
        ops::Deref,
        panic::UnwindSafe,
    };

    // Check that public types in this module keep implementing all expected
    // traits, in the interest of detecting future semver-breaking changes
    assert_impl_all!(DownstreamAttributes<'static>:
        Copy, Debug, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(DownstreamAttributes<'static>:
        Binary, Default, Deref, Display, Drop, IntoIterator, LowerExp, LowerHex,
        Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write,
        io::Write
    );
    assert_impl_all!(DownstreamPCIAttributes:
        Copy, Debug, Default, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(DownstreamPCIAttributes:
        Binary, Deref, Display, Drop, IntoIterator, LowerExp, LowerHex,
        Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write,
        io::Write
    );
    assert_impl_all!(UpstreamAttributes<'static>:
        Copy, Debug, PartialEq, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(UpstreamAttributes<'static>:
        Binary, Default, Deref, Display, Drop, Eq, IntoIterator, LowerExp,
        LowerHex, Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex,
        fmt::Write, io::Write
    );

    proptest! {
        #[test]
        fn unary_bridge(bridge_attr: BridgeAttributes) {
            check_any_bridge(&bridge_attr)?;
            let mut raw = hwloc_obj_attr_u {
                bridge: bridge_attr.0,
            };
            let ptr: *mut hwloc_obj_attr_u = &mut raw;
            // SAFETY: Type is consistent with union variant, data is valid
            unsafe {
                prop_assert!(matches!(
                    ObjectAttributes::new(ObjectType::Bridge, &ptr),
                    Some(ObjectAttributes::Bridge(attr)) if std::ptr::eq(attr.as_inner(), &raw.bridge)
                ));
            }
        }
    }

    /// Pick a pair of bridges in the test topology if possible
    fn bridge_pair() -> impl Strategy<Value = Option<[&'static TopologyObject; 2]>> {
        let bridges = &ObjectsWithAttrs::instance().bridges;
        object_pair(bridges, bridges)
    }

    proptest! {
        /// Check properties that should be true of any pair of bridges
        #[test]
        fn valid_bridge_pair(bridge_pair in bridge_pair()) {
            if let Some(pair) = bridge_pair {
                check_valid_bridge_pair(pair)?;
            }
        }
    }

    /// Pick a (bridge, PCI device) pair in the test topology if possible
    fn bridge_pci() -> impl Strategy<Value = Option<[&'static TopologyObject; 2]>> {
        let bridges = &ObjectsWithAttrs::instance().bridges;
        let pci_devices = &ObjectsWithAttrs::instance().pci_devices;
        object_pair(bridges, pci_devices)
    }

    proptest! {
        /// Check properties that should be true of any pair of bridges
        #[test]
        fn valid_bridge_pci(bridge_pci in bridge_pci()) {
            if let Some(pair) = bridge_pci {
                check_valid_bridge_pci(pair)?;
            }
        }
    }

    /// Check [`BridgeAttributes`] properties that should be true of valid
    /// [`TopologyObject`]s coming from hwloc
    pub(crate) fn check_valid_bridge(attr: &BridgeAttributes) -> Result<(), TestCaseError> {
        check_any_bridge(attr)?;

        prop_assert_eq!(attr.upstream_type() == BridgeType::Host, attr.depth() == 0);
        match attr.upstream_attributes() {
            Some(UpstreamAttributes::PCI(upstream)) => {
                check_valid_pci(upstream)?;
            }
            None => {
                prop_assert_eq!(attr.upstream_type(), BridgeType::Host);
            }
        }
        prop_assert_ne!(attr.downstream_type(), BridgeType::Host);
        match attr.downstream_attributes() {
            Some(DownstreamAttributes::PCI(downstream)) => {
                check_valid_downstream_pci(downstream)?;
            }
            None => unreachable!(),
        }

        Ok(())
    }

    /// Check [`BridgeAttributes`] properties that should be always true
    fn check_any_bridge(attr: &BridgeAttributes) -> Result<(), TestCaseError> {
        let hwloc_bridge_attr_s {
            upstream_type,
            downstream_type,
            downstream,
            depth,
            ..
        } = attr.0;

        // SAFETY: Value is from hwloc
        let upstream_type = unsafe { BridgeType::from_hwloc(upstream_type) };
        prop_assert_eq!(attr.upstream_type(), upstream_type);
        #[allow(clippy::single_match_else)]
        match attr.upstream_attributes() {
            Some(UpstreamAttributes::PCI(pci)) => {
                prop_assert_eq!(upstream_type, BridgeType::PCI);
                let actual_ptr: *const hwloc_pcidev_attr_s = pci.as_inner();
                // SAFETY: We must assume correct union tagging here
                let expected_ptr: *const hwloc_pcidev_attr_s = unsafe { &attr.0.upstream.pci };
                prop_assert_eq!(actual_ptr, expected_ptr);
                check_any_pci(pci)?;
            }
            None => prop_assert_ne!(upstream_type, BridgeType::PCI),
        }
        let upstream_dbg = format!(
            "upstream_type: {:?}, upstream_attributes: {:?}",
            attr.upstream_type(),
            attr.upstream_attributes()
        );

        // SAFETY: Value is from hwloc
        let downstream_type = unsafe { BridgeType::from_hwloc(downstream_type) };
        prop_assert_eq!(attr.downstream_type(), downstream_type);
        let downstream_type_dbg = format!("downstream_type: {downstream_type:?}");
        let downstream_dbg = match downstream_type {
            BridgeType::PCI => {
                #[allow(clippy::single_match_else)]
                match attr.downstream_attributes() {
                    Some(DownstreamAttributes::PCI(downstream)) => {
                        let actual_ptr: *const RawDownstreamPCIAttributes = downstream.as_inner();
                        let expected_ptr: *const RawDownstreamPCIAttributes =
                            // SAFETY: We must assume correct union tagging here
                            unsafe { &attr.0.downstream.pci };
                        prop_assert_eq!(actual_ptr, expected_ptr);
                        check_any_downstream_pci(downstream)?;
                        format!(
                            "{downstream_type_dbg}, downstream_attributes: {:?}",
                            attr.downstream_attributes()
                        )
                    }
                    None => {
                        prop_assert!(false, "should have returned PCI attributes");
                        unreachable!()
                    }
                }
            }
            BridgeType::Host | BridgeType::Unknown(_) => {
                assert_panics(|| attr.downstream_attributes())?;
                format!(
                    "{downstream_type_dbg}, \
                        downstream_attributes: \"{downstream:?}\""
                )
            }
        };

        prop_assert_eq!(attr.depth(), usize::try_from(depth).unwrap());

        prop_assert_eq!(
            format!("{attr:?}"),
            format!(
                "BridgeAttributes {{ \
                    {upstream_dbg}, \
                    {downstream_dbg}, \
                    depth: {:?} \
                }}",
                attr.depth()
            )
        );

        Ok(())
    }

    /// Check [`DownstreamPCIAttributes`] properties that should be true of
    /// valid [`TopologyObject`]s coming from hwloc
    #[allow(clippy::trivially_copy_pass_by_ref)]
    fn check_valid_downstream_pci(attr: &DownstreamPCIAttributes) -> Result<(), TestCaseError> {
        check_any_downstream_pci(attr)
    }

    /// Check [`DownstreamPCIAttributes`] properties that should always be true
    #[allow(clippy::trivially_copy_pass_by_ref)]
    fn check_any_downstream_pci(attr: &DownstreamPCIAttributes) -> Result<(), TestCaseError> {
        let RawDownstreamPCIAttributes {
            domain,
            secondary_bus,
            subordinate_bus,
        } = attr.0;
        prop_assert_eq!(attr.domain(), domain);
        prop_assert_eq!(attr.secondary_bus(), secondary_bus);
        prop_assert_eq!(attr.subordinate_bus(), subordinate_bus);
        Ok(())
    }

    /// Check attribute properties that should be true of any pair of valid
    /// bridge objects from the hwloc topology
    fn check_valid_bridge_pair(
        [bridge1, bridge2]: [&TopologyObject; 2],
    ) -> Result<(), TestCaseError> {
        let attr1 = bridge_attributes(bridge1)?;
        let attr2 = bridge_attributes(bridge2)?;

        let parent_child_attr = parent_child([(bridge1, attr1), (bridge2, attr2)]);
        if let Some([parent, child]) = parent_child_attr {
            if !std::ptr::eq(bridge1, bridge2) {
                prop_assert!(parent.depth() < child.depth());
            }
        }

        if attr1.upstream_type() == attr2.upstream_type()
            && attr1.upstream_attributes() == attr2.upstream_attributes()
            && attr1.downstream_type() == attr2.downstream_type()
            && attr1.downstream_attributes() == attr2.downstream_attributes()
            && attr1.depth() == attr2.depth()
        {
            prop_assert_eq!(attr1, attr2);
        } else {
            prop_assert_ne!(attr1, attr2);
        }

        Ok(())
    }

    /// Check attribute properties that should be true of any bridge + PCI
    /// object pair from the hwloc topology
    fn check_valid_bridge_pci([bridge, pci]: [&TopologyObject; 2]) -> Result<(), TestCaseError> {
        let bridge_attr = bridge_attributes(bridge)?;
        let pci_attr = pci_attributes(pci)?;
        prop_assert!(!bridge.is_in_subtree(pci));
        if pci.is_in_subtree(bridge) {
            if let Some(DownstreamAttributes::PCI(downstream_attr)) =
                bridge_attr.downstream_attributes()
            {
                prop_assert_eq!(downstream_attr.domain(), pci_attr.domain());
            }
        }
        Ok(())
    }

    /// Extract the bridge attributes from a bridge object
    fn bridge_attributes(bridge: &TopologyObject) -> Result<BridgeAttributes, TestCaseError> {
        let res = if let Some(ObjectAttributes::Bridge(attr)) = bridge.attributes() {
            *attr
        } else {
            prop_assert!(false, "Not an I/O bridge");
            unreachable!()
        };
        Ok(res)
    }
}
