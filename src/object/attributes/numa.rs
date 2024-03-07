//! [`NUMANode`]-specific attributes
//!
//! [`NUMANode`]: ObjectType::NUMANode

use crate::ffi::{
    int,
    transparent::{AsNewtype, TransparentNewtype},
};
#[cfg(doc)]
use crate::{object::types::ObjectType, topology::support::DiscoverySupport};
use hwlocality_sys::{hwloc_memory_page_type_s, hwloc_numanode_attr_s};
#[cfg(any(test, feature = "proptest"))]
use proptest::prelude::*;
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::{
    fmt::{self, Debug},
    hash::Hash,
    marker::PhantomData,
    num::NonZeroU64,
};

/// [`NUMANode`]-specific attributes
///
/// You cannot create an owned object of this type, it belongs to the topology.
///
/// [`NUMANode`]: ObjectType::NUMANode
//
// --- Implementation details ---
//
// # Safety
//
// If non-null, `page_types` is trusted to point to a C-style array of
// `page_types_len` memory page types, sorted by increasing page size.
#[allow(missing_copy_implementations)]
#[derive(Copy, Clone, Default)]
#[doc(alias = "hwloc_numanode_attr_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s")]
#[repr(transparent)]
pub struct NUMANodeAttributes<'object>(hwloc_numanode_attr_s, PhantomData<&'object MemoryPageType>);
//
impl<'object> NUMANodeAttributes<'object> {
    /// Node-local memory in bytes
    ///
    /// Requires [`DiscoverySupport::numa_memory()`], but may not be present
    /// even when this support flag is set.
    #[doc(alias = "hwloc_numanode_attr_s::local_memory")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::local_memory")]
    pub fn local_memory(&self) -> Option<NonZeroU64> {
        NonZeroU64::new(self.0.local_memory)
    }

    /// Memory page types, sorted by increasing page size
    #[doc(alias = "hwloc_numanode_attr_s::page_types")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::page_types")]
    pub fn page_types(&self) -> &'object [MemoryPageType] {
        if self.0.page_types.is_null() {
            assert_eq!(
                self.0.page_types_len, 0,
                "Got null pages types pointer with non-zero length"
            );
            return &[];
        }
        let page_types_len = int::expect_usize(self.0.page_types_len);
        type Element = MemoryPageType;
        int::assert_slice_len::<Element>(page_types_len);
        // SAFETY: - Pointer and length assumed valid per type invariant
        //         - AsNewtype is trusted to be implemented correctly
        //         - pages_types_len was checked for slice-safety above
        unsafe {
            std::slice::from_raw_parts::<Element>(self.0.page_types.as_newtype(), page_types_len)
        }
    }
}
//
impl Debug for NUMANodeAttributes<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug = f.debug_struct("NUMANodeAttributes");

        debug.field("local_memory", &self.local_memory());

        if self.0.page_types_len == 0 || !self.0.page_types.is_null() {
            debug.field("page_types", &self.page_types());
        } else {
            debug.field(
                "page_types",
                &format!("NULL with len={:?}", self.0.page_types_len),
            );
        }

        debug.finish()
    }
}
//
impl Eq for NUMANodeAttributes<'_> {}
//
impl Hash for NUMANodeAttributes<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.local_memory().hash(state);
        self.page_types().hash(state);
    }
}
//
impl PartialEq for NUMANodeAttributes<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.local_memory() == other.local_memory() && self.page_types() == other.page_types()
    }
}
//
// SAFETY: No internal mutability
unsafe impl Send for NUMANodeAttributes<'_> {}
//
// SAFETY: No internal mutability
unsafe impl Sync for NUMANodeAttributes<'_> {}
//
// SAFETY: NUMANodeAttributes is a repr(transparent) newtype of hwloc_numanode_attr_s
unsafe impl TransparentNewtype for NUMANodeAttributes<'_> {
    type Inner = hwloc_numanode_attr_s;
}

/// Local memory page type
#[derive(Copy, Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[doc(alias = "hwloc_memory_page_type_s")]
#[doc(alias = "hwloc_numanode_attr_s::hwloc_memory_page_type_s")]
#[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::hwloc_memory_page_type_s")]
#[repr(transparent)]
pub struct MemoryPageType(hwloc_memory_page_type_s);
//
impl MemoryPageType {
    /// Size of pages, if known
    #[doc(alias = "hwloc_memory_page_type_s::size")]
    #[doc(alias = "hwloc_numanode_attr_s::hwloc_memory_page_type_s::size")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::hwloc_memory_page_type_s::size")]
    pub fn size(&self) -> NonZeroU64 {
        NonZeroU64::new(self.0.size).expect("memory page types of unknown size are useless")
    }

    /// Number of pages of this size
    #[doc(alias = "hwloc_memory_page_type_s::count")]
    #[doc(alias = "hwloc_numanode_attr_s::hwloc_memory_page_type_s::count")]
    #[doc(alias = "hwloc_obj_attr_u::hwloc_numanode_attr_s::hwloc_memory_page_type_s::count")]
    pub fn count(&self) -> u64 {
        self.0.count
    }
}
//
#[cfg(any(test, feature = "proptest"))]
impl Arbitrary for MemoryPageType {
    type Parameters = <u64 as Arbitrary>::Parameters;
    type Strategy = prop::strategy::Map<
        (
            crate::strategies::IntSpecial0<u64>,
            <u64 as Arbitrary>::Strategy,
        ),
        fn((u64, u64)) -> Self,
    >;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        let size = crate::strategies::u64_special0();
        let count = u64::arbitrary_with(args);
        (size, count).prop_map(|(size, count)| Self(hwloc_memory_page_type_s { size, count }))
    }
}
//
impl Debug for MemoryPageType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug = f.debug_struct("MemoryPageType");

        if self.0.size == 0 {
            debug.field("size", &"0");
        } else {
            debug.field("size", &self.size());
        }

        debug.field("count", &self.count()).finish()
    }
}
//
// SAFETY: MemoryPageType is a repr(transparent) newtype of hwloc_memory_page_type_s
unsafe impl TransparentNewtype for MemoryPageType {
    type Inner = hwloc_memory_page_type_s;
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
            types::ObjectType,
            TopologyObject,
        },
        tests::assert_panics,
    };
    use hwlocality_sys::hwloc_obj_attr_u;
    #[allow(unused)]
    use similar_asserts::assert_eq;
    use static_assertions::{assert_impl_all, assert_not_impl_any};
    use std::{
        collections::hash_map::RandomState,
        fmt::{Binary, Display, LowerExp, LowerHex, Octal, Pointer, UpperExp, UpperHex},
        hash::BuildHasher,
        io::{self, Read},
        ops::Deref,
        panic::UnwindSafe,
    };

    // Check that public types in this module keep implementing all expected
    // traits, in the interest of detecting future semver-breaking changes
    assert_impl_all!(MemoryPageType:
        Copy, Debug, Hash, Ord, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(MemoryPageType:
        Binary, Default, Deref, Display, Drop, IntoIterator, LowerExp, LowerHex,
        Octal, Pointer, Read, UpperExp, UpperHex, fmt::Write, io::Write
    );
    assert_impl_all!(NUMANodeAttributes<'static>:
        Copy, Debug, Default, Hash, Sized, Sync, Unpin, UnwindSafe
    );
    assert_not_impl_any!(NUMANodeAttributes<'static>:
        Binary, Deref, Display, Drop, IntoIterator, LowerExp, LowerHex, Octal,
        PartialOrd, Pointer, Read, UpperExp, UpperHex, fmt::Write, io::Write
    );

    #[test]
    fn default() -> Result<(), TestCaseError> {
        check_any_numa(&NUMANodeAttributes::default())?;
        Ok(())
    }

    proptest! {
        #[test]
        fn unary_numa(local_memory: u64, page_types: Vec<MemoryPageType>, null: bool) {
            let numa_attr = if null {
                NUMANodeAttributes(
                    hwloc_numanode_attr_s {
                        local_memory,
                        page_types_len: u32::try_from(page_types.len()).unwrap_or(u32::MAX),
                        page_types: std::ptr::null_mut(),
                    },
                    PhantomData,
                )
            } else {
                let numa_attr = make_numa_attributes(local_memory, &page_types);
                prop_assert_eq!(numa_attr.page_types(), &page_types);
                numa_attr
            };
            prop_assert_eq!(numa_attr.local_memory(), NonZeroU64::new(local_memory));
            check_any_numa(&numa_attr)?;

            let mut raw = hwloc_obj_attr_u { numa: numa_attr.0 };
            let ptr: *mut hwloc_obj_attr_u = &mut raw;
            // SAFETY: Type is consistent with union variant, data is valid
            unsafe {
                prop_assert!(matches!(
                    ObjectAttributes::new(ObjectType::NUMANode, &ptr),
                    Some(ObjectAttributes::NUMANode(attr)) if std::ptr::eq(attr.as_inner(), &raw.numa)
                ));
            }
        }
    }

    /// Pick a pair of NUMA nodes in the test topology if possible
    fn numa_pair() -> impl Strategy<Value = Option<[&'static TopologyObject; 2]>> {
        let numa_nodes = &ObjectsWithAttrs::instance().numa_nodes;
        object_pair(numa_nodes, numa_nodes)
    }

    proptest! {
        /// Check properties that should be true of any pair of NUMA nodes
        #[test]
        fn valid_numa_pair(numa_pair in numa_pair()) {
            if let Some(pair) = numa_pair {
                check_valid_numa_pair(pair)?;
            }
        }
    }

    /// Check [`NUMANodeAttributes`] properties that should be true of valid
    /// [`TopologyObject`]s coming from hwloc
    pub(crate) fn check_valid_numa(attr: &NUMANodeAttributes<'_>) -> Result<(), TestCaseError> {
        check_any_numa(attr)?;

        let mut prev_page_size = None;
        for page_type in attr.page_types() {
            let page_size = page_type.size();
            prop_assert!(page_size.is_power_of_two());
            if let Some(prev_page_size) = prev_page_size {
                prop_assert!(page_size > prev_page_size);
            }
            prev_page_size = Some(page_size);

            prop_assert_eq!(
                format!("{page_type:?}"),
                format!(
                    "MemoryPageType {{ \
                        size: {:?}, \
                        count: {:?} \
                    }}",
                    page_type.size(),
                    page_type.count(),
                )
            )
        }

        prop_assert_eq!(
            format!("{attr:?}"),
            format!(
                "NUMANodeAttributes {{ \
                    local_memory: {:?}, \
                    page_types: {:?} \
                }}",
                attr.local_memory(),
                attr.page_types(),
            )
        );

        Ok(())
    }

    /// Check [`NUMANodeAttributes`] properties that should always be true
    fn check_any_numa(attr: &NUMANodeAttributes<'_>) -> Result<(), TestCaseError> {
        let hwloc_numanode_attr_s {
            local_memory,
            page_types_len,
            page_types,
        } = attr.0;

        prop_assert_eq!(attr.local_memory(), NonZeroU64::new(local_memory));

        if !page_types.is_null() {
            prop_assert_eq!(
                attr.page_types().as_ptr().as_inner(),
                page_types.cast_const()
            );
            prop_assert_eq!(
                attr.page_types().len(),
                usize::try_from(page_types_len).unwrap()
            );
            for page_type in attr.page_types() {
                check_any_page_type(page_type)?;
            }
        } else if page_types_len == 0 {
            prop_assert_eq!(attr.page_types(), &[]);
        } else {
            assert_panics(|| attr.page_types())?;
            prop_assert_eq!(
                format!("{attr:?}"),
                format!(
                    "NUMANodeAttributes {{ \
                        local_memory: {:?}, \
                        page_types: \"NULL with len={page_types_len}\" \
                    }}",
                    attr.local_memory(),
                )
            );
        }
        Ok(())
    }

    /// Check [`MemoryPageType`] properties that should always be true
    fn check_any_page_type(page_type: &MemoryPageType) -> Result<(), TestCaseError> {
        let hwloc_memory_page_type_s { size, count } = page_type.0;
        #[allow(clippy::option_if_let_else)]
        if let Some(size) = NonZeroU64::new(size) {
            prop_assert_eq!(page_type.size(), size);
        } else {
            assert_panics(|| page_type.size())?;
            prop_assert_eq!(
                format!("{page_type:?}"),
                format!(
                    "MemoryPageType {{ \
                        size: \"0\", \
                        count: {:?} \
                    }}",
                    page_type.count(),
                )
            );
        }
        prop_assert_eq!(page_type.count(), count);
        Ok(())
    }

    /// Check attribute properties that should be true of any pair of valid NUMA
    /// nodes from the hwloc topology
    fn check_valid_numa_pair(
        [numa1, numa2]: [&'static TopologyObject; 2],
    ) -> Result<(), TestCaseError> {
        fn numa_attr(
            numa: &'static TopologyObject,
        ) -> Result<NUMANodeAttributes<'static>, TestCaseError> {
            let res = if let Some(ObjectAttributes::NUMANode(attr)) = numa.attributes() {
                *attr
            } else {
                prop_assert!(false, "Not a NUMA node");
                unreachable!()
            };
            Ok(res)
        }
        let [attr1, attr2] = [numa_attr(numa1)?, numa_attr(numa2)?];

        if attr1.local_memory() == attr2.local_memory() && attr1.page_types() == attr2.page_types()
        {
            prop_assert_eq!(attr1, attr2);
            let state = RandomState::new();
            prop_assert_eq!(state.hash_one(attr1), state.hash_one(attr2));
        } else {
            prop_assert_ne!(attr1, attr2);
        }

        Ok(())
    }

    /// Create [`NUMANodeAttributes`] out of random building blocks
    fn make_numa_attributes(
        local_memory: u64,
        page_types: &[MemoryPageType],
    ) -> NUMANodeAttributes<'_> {
        NUMANodeAttributes(
            hwloc_numanode_attr_s {
                local_memory,
                page_types_len: page_types.len().try_into().unwrap(),
                page_types: page_types.as_ptr().as_inner().cast_mut(),
            },
            PhantomData,
        )
    }
}
