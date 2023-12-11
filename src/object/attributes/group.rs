//! [`Group`]-specific attributes
//!
//! [`Group`]: ObjectType::Group

use crate::ffi::{int, transparent::TransparentNewtype};
#[cfg(doc)]
use crate::object::types::ObjectType;
use hwlocality_sys::hwloc_group_attr_s;
#[cfg(any(test, feature = "proptest"))]
use proptest::prelude::*;
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
#[cfg(any(test, feature = "proptest", feature = "hwloc-2_3_0"))]
use std::ffi::c_uint;
use std::{
    fmt::{self, Debug},
    hash::Hash,
};

/// [`Group`]-specific attributes
///
/// [`Group`]: ObjectType::Group
#[derive(Copy, Clone, Default, Eq, Hash, PartialEq)]
#[doc(alias = "hwloc_group_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_group_attr_s")]
#[repr(transparent)]
pub struct GroupAttributes(hwloc_group_attr_s);
//
impl GroupAttributes {
    /// Depth of group object
    ///
    /// It may change if intermediate Group objects are added.
    #[doc(alias = "hwloc_group_attr_s::depth")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_group_attr_s::depth")]
    pub fn depth(&self) -> usize {
        int::expect_usize(self.0.depth)
    }

    /// Internally-used kind of group
    #[allow(unused)]
    pub(crate) fn kind(&self) -> usize {
        int::expect_usize(self.0.kind)
    }

    /// Tell hwloc that this group object should always be discarded in favor of
    /// any existing `Group` with the same locality.
    #[cfg(feature = "hwloc-2_3_0")]
    pub(crate) fn favor_merging(&mut self) {
        self.0.kind = c_uint::MAX;
        self.0.dont_merge = 0;
    }

    /// Internally-used subkind to distinguish different levels of groups with
    /// the same kind
    #[allow(unused)]
    #[doc(alias = "hwloc_group_attr_s::subkind")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_group_attr_s::subkind")]
    pub(crate) fn subkind(&self) -> usize {
        int::expect_usize(self.0.subkind)
    }

    /// Flag preventing groups from being automatically merged with identical
    /// parent or children
    #[cfg(feature = "hwloc-2_0_4")]
    pub fn merging_prevented(&self) -> bool {
        assert!(
            self.0.dont_merge == 0 || self.0.dont_merge == 1,
            "unexpected hwloc_group_attr_s::dont_merge value"
        );
        self.0.dont_merge != 0
    }

    /// Tell hwloc that it should not merge this group object with other
    /// hierarchically-identical objects.
    #[cfg(feature = "hwloc-2_3_0")]
    pub(crate) fn prevent_merging(&mut self) {
        self.0.dont_merge = 1;
    }
}
//
#[cfg(any(test, feature = "proptest"))]
impl Arbitrary for GroupAttributes {
    type Parameters = <[c_uint; 3] as Arbitrary>::Parameters;
    type Strategy = prop::strategy::Map<
        (
            <[c_uint; 3] as Arbitrary>::Strategy,
            crate::strategies::HwlocBool,
        ),
        fn(([c_uint; 3], std::ffi::c_uchar)) -> Self,
    >;

    #[allow(unused)]
    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        let depth_kind_subkind = <[c_uint; 3] as Arbitrary>::arbitrary_with(args);
        let dont_merge = crate::strategies::hwloc_bool();
        (depth_kind_subkind, dont_merge).prop_map(|([depth, kind, subkind], dont_merge)| {
            Self(hwloc_group_attr_s {
                depth,
                kind,
                subkind,
                #[cfg(feature = "hwloc-2_0_4")]
                dont_merge,
            })
        })
    }
}
//
impl Debug for GroupAttributes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug = f.debug_struct("GroupAttributes");

        debug.field("depth", &self.depth());

        #[cfg(feature = "hwloc-2_0_4")]
        if self.0.dont_merge <= 1 {
            debug.field("merging_prevented", &self.merging_prevented());
        } else {
            debug.field("merging_prevented", &format!("{:?}", self.0.dont_merge));
        }

        debug
            .field("kind", &self.kind())
            .field("subkind", &self.subkind())
            .finish()
    }
}
//
// SAFETY: GroupAttributes is a repr(transparent) newtype of hwloc_group_attr_s
unsafe impl TransparentNewtype for GroupAttributes {
    type Inner = hwloc_group_attr_s;
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use crate::{
        ffi::transparent::AsInner,
        object::{
            attributes::{
                tests::{object_pair, ObjectsWithAttrs},
                ObjectAttributes,
            },
            depth::NormalDepth,
            types::ObjectType,
            TopologyObject,
        },
    };
    use hwlocality_sys::hwloc_obj_attr_u;
    #[allow(unused)]
    use similar_asserts::assert_eq;
    use static_assertions::{assert_impl_all, assert_not_impl_any};
    use std::{
        fmt::{
            self, Binary, Debug, Display, LowerExp, LowerHex, Octal, Pointer, UpperExp, UpperHex,
        },
        hash::Hash,
        io::{self, Read},
        ops::Deref,
        panic::UnwindSafe,
    };

    // Check that public types in this module keep implementing all expected
    // traits, in the interest of detecting future semver-breaking changes
    assert_impl_all!(GroupAttributes:
        Copy, Debug, Default, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(GroupAttributes:
        Binary, Deref, Display, Drop, IntoIterator, LowerExp, LowerHex,
        Octal, PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write,
        io::Write
    );

    #[test]
    fn default() -> Result<(), TestCaseError> {
        check_any_group(&GroupAttributes::default())?;
        Ok(())
    }

    proptest! {
        #[test]
        fn unary_group(group_attr: GroupAttributes) {
            check_any_group(&group_attr)?;
            let mut raw = hwloc_obj_attr_u {
                group: group_attr.0,
            };
            let ptr: *mut hwloc_obj_attr_u = &mut raw;
            // SAFETY: Type is consistent with union variant, data is valid
            unsafe {
                prop_assert!(matches!(
                    ObjectAttributes::new(ObjectType::Group, &ptr),
                    Some(ObjectAttributes::Group(attr)) if std::ptr::eq(attr.as_inner(), &raw.group)
                ));
            }
        }
    }

    /// Pick a pair of goups in the test topology if possible
    fn group_pair() -> impl Strategy<Value = Option<[&'static TopologyObject; 2]>> {
        let groups = &ObjectsWithAttrs::instance().groups;
        object_pair(groups, groups)
    }

    proptest! {
        /// Check properties that should be true of any pair of groups
        #[test]
        fn valid_group_pair(group_pair in group_pair()) {
            if let Some(pair) = group_pair {
                check_valid_group_pair(pair)?;
            }
        }
    }

    /// Check [`GroupAttributes`] properties that should be true of valid
    /// [`TopologyObject`]s coming from hwloc
    pub(crate) fn check_valid_group(attr: &GroupAttributes) -> Result<(), TestCaseError> {
        check_any_group(attr)
    }

    /// Check [`GroupAttributes`] properties that should always be true
    fn check_any_group(attr: &GroupAttributes) -> Result<(), TestCaseError> {
        #[cfg(feature = "hwloc-2_0_4")]
        let hwloc_group_attr_s {
            depth,
            kind,
            subkind,
            dont_merge,
        } = attr.0;
        #[cfg(not(feature = "hwloc-2_0_4"))]
        let hwloc_group_attr_s {
            depth,
            kind,
            subkind,
        } = attr.0;

        prop_assert_eq!(attr.depth(), usize::try_from(depth).unwrap());
        prop_assert_eq!(attr.kind(), usize::try_from(kind).unwrap());
        prop_assert_eq!(attr.subkind(), usize::try_from(subkind).unwrap());

        #[cfg(feature = "hwloc-2_0_4")]
        let merging_prevented_dbg = match dont_merge {
            0 | 1 => {
                prop_assert_eq!(attr.merging_prevented(), dont_merge != 0);
                format!("merging_prevented: {:?}, ", attr.merging_prevented())
            }
            _ => {
                crate::tests::assert_panics(|| attr.merging_prevented())?;
                format!("merging_prevented: \"{dont_merge:?}\", ")
            }
        };
        #[cfg(not(feature = "hwloc-2_0_4"))]
        let merging_prevented_dbg = String::new();

        prop_assert_eq!(
            format!("{attr:?}"),
            format!(
                "GroupAttributes {{ \
                    depth: {:?}, \
                    {}\
                    kind: {:?}, \
                    subkind: {:?} \
                }}",
                attr.depth(),
                merging_prevented_dbg,
                attr.kind(),
                attr.subkind(),
            )
        );

        #[cfg(feature = "hwloc-2_3_0")]
        {
            let mut buf = *attr;
            let mut expected = *attr;

            buf.prevent_merging();
            expected.0.dont_merge = 1;
            prop_assert_eq!(buf, expected);
            prop_assert!(buf.merging_prevented());

            buf.favor_merging();
            expected.0.dont_merge = 0;
            prop_assert!(buf.0.kind > 0);
            expected.0.kind = buf.0.kind;
            prop_assert_eq!(buf, expected);
            prop_assert!(!buf.merging_prevented());
        }

        Ok(())
    }

    /// Check attribute properties that should be true of any pair of valid group
    /// objects from the hwloc topology
    fn check_valid_group_pair([group1, group2]: [&TopologyObject; 2]) -> Result<(), TestCaseError> {
        fn group_depth(
            group: &TopologyObject,
        ) -> Result<(NormalDepth, GroupAttributes), TestCaseError> {
            let res = if let Some(ObjectAttributes::Group(attr)) = group.attributes() {
                (group.depth().expect_normal(), *attr)
            } else {
                prop_assert!(false, "Not a group");
                unreachable!()
            };
            Ok(res)
        }
        let (depth1, attr1) = group_depth(group1)?;
        let (depth2, attr2) = group_depth(group2)?;

        prop_assert_eq!(depth1.cmp(&depth2), attr1.depth().cmp(&attr2.depth()));

        Ok(())
    }
}
