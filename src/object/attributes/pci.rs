//! [`PCIDevice`]-specific attributes
//!
//! [`PCIDevice`]: ObjectType::PCIDevice

use crate::ffi::transparent::TransparentNewtype;
#[cfg(doc)]
use crate::object::types::ObjectType;
use hwlocality_sys::hwloc_pcidev_attr_s;
#[cfg(any(test, feature = "proptest"))]
use proptest::prelude::*;
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::fmt::Debug;

/// PCI domain width (depends on hwloc version)
#[cfg(feature = "hwloc-3_0_0")]
#[cfg_attr(docsrs, doc(cfg(all())))]
pub type PCIDomain = u32;

/// PCI domain width (depends on hwloc version)
#[cfg(not(feature = "hwloc-3_0_0"))]
#[cfg_attr(docsrs, doc(cfg(all())))]
pub type PCIDomain = u16;

/// [`PCIDevice`]-specific attributes
///
/// [`PCIDevice`]: ObjectType::PCIDevice
#[derive(Copy, Clone, Debug, Default, PartialEq)]
#[doc(alias = "hwloc_pcidev_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s")]
#[repr(transparent)]
pub struct PCIDeviceAttributes(pub(super) hwloc_pcidev_attr_s);
//
impl PCIDeviceAttributes {
    /// PCI domain
    #[doc(alias = "hwloc_pcidev_attr_s::domain")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::domain")]
    pub fn domain(&self) -> PCIDomain {
        self.0.domain
    }

    /// PCI bus id
    #[doc(alias = "hwloc_pcidev_attr_s::bus")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::bus")]
    pub fn bus_id(&self) -> u8 {
        self.0.bus
    }

    /// PCI bus device
    #[doc(alias = "hwloc_pcidev_attr_s::dev")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::dev")]
    pub fn bus_device(&self) -> u8 {
        self.0.dev
    }

    /// PCI function
    #[doc(alias = "hwloc_pcidev_attr_s::func")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::func")]
    pub fn function(&self) -> u8 {
        self.0.func
    }

    /// PCI class ID
    #[doc(alias = "hwloc_pcidev_attr_s::class_id")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::class_id")]
    pub fn class_id(&self) -> u16 {
        self.0.class_id
    }

    /// PCI vendor ID
    #[doc(alias = "hwloc_pcidev_attr_s::vendor_id")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::vendor_id")]
    pub fn vendor_id(&self) -> u16 {
        self.0.vendor_id
    }

    /// PCI device ID
    #[doc(alias = "hwloc_pcidev_attr_s::device_id")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::device_id")]
    pub fn device_id(&self) -> u16 {
        self.0.device_id
    }

    /// PCI sub-vendor ID
    #[doc(alias = "hwloc_pcidev_attr_s::subvendor_id")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::subvendor_id")]
    pub fn subvendor_id(&self) -> u16 {
        self.0.subvendor_id
    }

    /// PCI sub-device ID
    #[doc(alias = "hwloc_pcidev_attr_s::subdevice_id")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::subdevice_id")]
    pub fn subdevice_id(&self) -> u16 {
        self.0.subdevice_id
    }

    /// PCI revision
    #[doc(alias = "hwloc_pcidev_attr_s::revision")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::revision")]
    pub fn revision(&self) -> u8 {
        self.0.revision
    }

    /// Link speed in GB/s
    #[doc(alias = "hwloc_pcidev_attr_s::linkspeed")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_pcidev_attr_s::linkspeed")]
    pub fn link_speed(&self) -> f32 {
        self.0.linkspeed
    }
}
//
#[cfg(any(test, feature = "proptest"))]
impl Arbitrary for PCIDeviceAttributes {
    type Parameters = <(PCIDomain, [u8; 4], [u16; 5]) as Arbitrary>::Parameters;
    type Strategy = prop::strategy::Map<
        (
            <(PCIDomain, [u8; 4], [u16; 5]) as Arbitrary>::Strategy,
            prop::num::f32::Any,
        ),
        fn(((PCIDomain, [u8; 4], [u16; 5]), f32)) -> Self,
    >;

    #[allow(unused)]
    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        (
            <(PCIDomain, [u8; 4], [u16; 5])>::arbitrary_with(args),
            prop::num::f32::ANY,
        )
            .prop_map(
                |(
                    (
                        domain,
                        [bus, dev, func, revision],
                        [class_id, vendor_id, device_id, subvendor_id, subdevice_id],
                    ),
                    linkspeed,
                )| {
                    Self(hwloc_pcidev_attr_s {
                        domain,
                        bus,
                        dev,
                        func,
                        class_id,
                        vendor_id,
                        device_id,
                        subvendor_id,
                        subdevice_id,
                        revision,
                        linkspeed,
                    })
                },
            )
    }
}
//
// SAFETY: PCIDeviceAttributes is a repr(transparent) newtype of hwloc_pcidev_attr_s
unsafe impl TransparentNewtype for PCIDeviceAttributes {
    type Inner = hwloc_pcidev_attr_s;
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use crate::{
        ffi::transparent::AsInner,
        object::{
            attributes::{
                tests::{object_pair, parent_child, ObjectsWithAttrs},
                ObjectAttributes,
            },
            types::ObjectType,
            TopologyObject,
        },
    };
    use hwlocality_sys::hwloc_obj_attr_u;
    #[allow(unused)]
    use similar_asserts::assert_eq;
    use static_assertions::{assert_impl_all, assert_not_impl_any};
    use std::{
        error::Error,
        fmt::{self, Binary, Display, LowerExp, LowerHex, Octal, Pointer, UpperExp, UpperHex},
        hash::Hash,
        io::{self, Read},
        iter::{Product, Sum},
        ops::{
            Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Deref,
            Div, DivAssign, Mul, MulAssign, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign,
            Sub, SubAssign,
        },
        panic::UnwindSafe,
        str::FromStr,
    };

    // Check that public types in this module keep implementing all expected
    // traits, in the interest of detecting future semver-breaking changes
    assert_impl_all!(PCIDeviceAttributes:
        Copy, Debug, Default, PartialEq, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(PCIDeviceAttributes:
        Binary, Deref, Display, Drop, Eq, IntoIterator, LowerExp, LowerHex,
        Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write,
        io::Write
    );
    assert_impl_all!(PCIDomain:
        Add, AddAssign, Binary, BitAnd, BitAndAssign, BitOr, BitOrAssign,
        BitXor, BitXorAssign, Copy, Debug, Default, Display, Div, DivAssign,
        FromStr, Hash, LowerExp, LowerHex, Mul, MulAssign, Not, Octal, Ord,
        Product, Sized, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign, Sum, Sync,
        TryFrom<i8>, TryFrom<u8>,
        TryFrom<i16>, TryFrom<u16>,
        TryFrom<i32>, TryFrom<u32>,
        TryFrom<i64>, TryFrom<u64>,
        TryFrom<i128>, TryFrom<u128>,
        TryFrom<isize>, TryFrom<usize>,
        TryInto<i8>, TryInto<u8>,
        TryInto<i16>, TryInto<u16>,
        TryInto<i32>, TryInto<u32>,
        TryInto<i64>, TryInto<u64>,
        TryInto<i128>, TryInto<u128>,
        TryInto<isize>, TryInto<usize>,
        Unpin, UnwindSafe, UpperExp, UpperHex
    );
    assert_not_impl_any!(PCIDomain:
        Deref, Drop, Error, IntoIterator, Pointer, Read, fmt::Write, io::Write
    );

    #[test]
    fn default() -> Result<(), TestCaseError> {
        check_any_pci(&PCIDeviceAttributes::default())?;
        Ok(())
    }

    proptest! {
        #[test]
        fn unary_pci(pcidev_attr: PCIDeviceAttributes) {
            check_any_pci(&pcidev_attr)?;
            let mut raw_attr = hwloc_obj_attr_u {
                pcidev: pcidev_attr.0,
            };
            let ptr = &raw mut raw_attr;
            // SAFETY: Type is consistent with union variant, data is valid
            unsafe {
                prop_assert!(matches!(
                    ObjectAttributes::new(ObjectType::PCIDevice, &ptr),
                    Some(ObjectAttributes::PCIDevice(attr)) if std::ptr::eq(attr.as_inner(), &raw const raw_attr.pcidev)
                ));
            }
        }
    }

    /// Pick a pair of PCI devices in the test topology if possible
    fn pci_pair() -> impl Strategy<Value = Option<[&'static TopologyObject; 2]>> {
        let pci_devices = &ObjectsWithAttrs::instance().pci_devices;
        object_pair(pci_devices, pci_devices)
    }

    proptest! {
        /// Check properties that should be true of any pair of pcis
        #[test]
        fn valid_pci_pair(pci_pair in pci_pair()) {
            if let Some(pair) = pci_pair {
                check_valid_pci_pair(pair)?;
            }
        }
    }

    /// Check [`PCIDeviceAttributes`] properties that should be true of valid
    /// [`TopologyObject`]s coming from hwloc
    #[allow(
        clippy::cast_possible_truncation,
        clippy::cast_precision_loss,
        clippy::cast_sign_loss
    )]
    pub(crate) fn check_valid_pci(attr: &PCIDeviceAttributes) -> Result<(), TestCaseError> {
        check_any_pci(attr)?;

        let link_speed = attr.link_speed();
        prop_assert!(
            link_speed.is_finite() && link_speed >= 0.0 && link_speed < f32::from(u16::MAX)
        );

        Ok(())
    }

    /// Check [`PCIDeviceAttributes`] properties that should always be true
    pub(crate) fn check_any_pci(attr: &PCIDeviceAttributes) -> Result<(), TestCaseError> {
        let hwloc_pcidev_attr_s {
            domain,
            bus,
            dev,
            func,
            class_id,
            vendor_id,
            device_id,
            subvendor_id,
            subdevice_id,
            revision,
            linkspeed,
        } = attr.0;
        prop_assert_eq!(attr.domain(), domain);
        prop_assert_eq!(attr.bus_id(), bus);
        prop_assert_eq!(attr.bus_device(), dev);
        prop_assert_eq!(attr.function(), func);
        prop_assert_eq!(attr.class_id(), class_id);
        prop_assert_eq!(attr.device_id(), device_id);
        prop_assert_eq!(attr.vendor_id(), vendor_id);
        prop_assert_eq!(attr.subvendor_id(), subvendor_id);
        prop_assert_eq!(attr.subdevice_id(), subdevice_id);
        prop_assert_eq!(attr.revision(), revision);
        prop_assert_eq!(attr.link_speed().to_bits(), linkspeed.to_bits());
        Ok(())
    }

    /// Check attribute properties that should be true of any pair of valid PCI
    /// objects from the hwloc topology
    fn check_valid_pci_pair([pci1, pci2]: [&TopologyObject; 2]) -> Result<(), TestCaseError> {
        let attr1 = pci_attributes(pci1)?;
        let attr2 = pci_attributes(pci2)?;

        let parent_child_attr = parent_child([(pci1, attr1), (pci2, attr2)]);
        if let Some([parent, child]) = parent_child_attr {
            prop_assert!(child.revision() <= parent.revision());
            prop_assert!(child.link_speed() <= parent.link_speed());
        }

        Ok(())
    }

    /// Extract the PCI attributes from a PCI device object
    pub(crate) fn pci_attributes(
        pci: &TopologyObject,
    ) -> Result<PCIDeviceAttributes, TestCaseError> {
        let res = if let Some(ObjectAttributes::PCIDevice(attr)) = pci.attributes() {
            *attr
        } else {
            prop_assert!(false, "Not a PCI device");
            unreachable!()
        };
        Ok(res)
    }
}
