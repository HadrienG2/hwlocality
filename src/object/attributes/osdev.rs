//! [`OSDevice`]-specific attributes
//!
//! [`OSDevice`]: ObjectType::OSDevice

#[cfg(doc)]
use crate::object::types::ObjectType;
use crate::{ffi::transparent::TransparentNewtype, object::types::OSDeviceType};
use hwlocality_sys::hwloc_osdev_attr_s;
#[cfg(any(test, feature = "proptest"))]
use proptest::prelude::*;
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::{
    fmt::{self, Debug},
    hash::Hash,
};

/// [`OSDevice`]-specific attributes
///
/// [`OSDevice`]: ObjectType::OSDevice
#[derive(Copy, Clone, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_osdev_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_osdev_attr_s")]
#[repr(transparent)]
pub struct OSDeviceAttributes(pub(super) hwloc_osdev_attr_s);
//
impl OSDeviceAttributes {
    /// OS device type
    #[doc(alias = "hwloc_osdev_attr_s::type")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_osdev_attr_s::type")]
    pub fn device_type(&self) -> OSDeviceType {
        // SAFETY: Comes from hwloc
        unsafe { OSDeviceType::from_hwloc(self.0.ty) }
    }
}
//
#[cfg(any(test, feature = "proptest"))]
impl Arbitrary for OSDeviceAttributes {
    type Parameters = ();
    type Strategy = prop::strategy::Map<
        crate::strategies::EnumRepr<hwlocality_sys::hwloc_obj_osdev_type_t>,
        fn(hwlocality_sys::hwloc_obj_osdev_type_t) -> Self,
    >;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        use hwlocality_sys::hwloc_obj_osdev_type_t;
        crate::strategies::enum_repr::<OSDeviceType, hwloc_obj_osdev_type_t>()
            .prop_map(|ty| Self(hwloc_osdev_attr_s { ty }))
    }
}
//
impl Debug for OSDeviceAttributes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OSDeviceAttributes")
            .field("device_type", &self.device_type())
            .finish()
    }
}
//
// SAFETY: OSDeviceAttributes is a repr(transparent) newtype of hwloc_osdev_attr_s
unsafe impl TransparentNewtype for OSDeviceAttributes {
    type Inner = hwloc_osdev_attr_s;
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use crate::{
        ffi::transparent::AsInner,
        object::{attributes::ObjectAttributes, types::ObjectType},
    };
    use hwlocality_sys::hwloc_obj_attr_u;
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
    assert_impl_all!(OSDeviceAttributes:
        Copy, Debug, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(OSDeviceAttributes:
        Binary, Deref, Default, Display, Drop, IntoIterator, LowerExp, LowerHex,
        Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write,
        io::Write
    );

    proptest! {
        #[test]
        fn unary_osdev(osdev_attr: OSDeviceAttributes) {
            check_any_osdev(&osdev_attr)?;
            let mut raw = hwloc_obj_attr_u {
                osdev: osdev_attr.0,
            };
            let ptr: *mut hwloc_obj_attr_u = &mut raw;
            // SAFETY: Type is consistent with union variant, data is valid
            unsafe {
                prop_assert!(matches!(
                    ObjectAttributes::new(ObjectType::OSDevice, &ptr),
                    Some(ObjectAttributes::OSDevice(attr)) if std::ptr::eq(attr.as_inner(), &raw.osdev)
                ));
            }
        }
    }

    /// Check [`OSDeviceAttributes`] properties that should be true of valid
    /// [`TopologyObject`]s coming from hwloc
    #[allow(clippy::trivially_copy_pass_by_ref)]
    pub(crate) fn check_valid_osdev(attr: &OSDeviceAttributes) -> Result<(), TestCaseError> {
        check_any_osdev(attr)
    }

    /// Check [`OSDeviceAttributes`] properties that should always be true
    #[allow(clippy::option_if_let_else, clippy::trivially_copy_pass_by_ref)]
    fn check_any_osdev(attr: &OSDeviceAttributes) -> Result<(), TestCaseError> {
        let device_type_dbg = format!("{:?}", attr.device_type());
        prop_assert_eq!(
            format!("{attr:?}"),
            format!("OSDeviceAttributes {{ device_type: {device_type_dbg} }}")
        );
        Ok(())
    }
}
