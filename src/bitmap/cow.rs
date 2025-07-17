//! Copy-on-write type analogous to [`std::borrow::Cow`] that can either be an
//! owned [`Bitmap`]/[`CpuSet`]/[`NodeSet`] or a [`BitmapRef`] thereof.

use super::{BitmapRef, OwnedBitmap};
#[cfg(doc)]
use crate::{bitmap::Bitmap, cpu::cpuset::CpuSet, memory::nodeset::NodeSet};
#[cfg(doc)]
use std::borrow::Cow;
use std::{
    borrow::Borrow,
    fmt::{self, Display, Formatter, Pointer},
    hash::{self, Hash},
    ops::Deref,
};

/// Clone-on-write smart pointer to a [`Bitmap`]-like `Target`
///
/// This is to [`Cow`] what [`BitmapRef`] is to `&Target`. It cannot literally
/// be a standard [`Cow`] because of the same C hwloc API peculiarities that
/// prevent [`BitmapRef`] from being a standard Rust reference.
///
/// You are not expected to use this type on a regular basis, it only exists to
/// serve the narrow use case of letting you return both owned and borrowed
/// bitmaps from topology-editing callbacks, without having to clone the
/// borrowed bitmaps. This is why its API is less extensive and convenient than
/// that of [`BitmapRef`].
#[derive(Clone, Debug)]
pub enum BitmapCow<'target, Target: OwnedBitmap> {
    /// Borrowed bitmap
    Borrowed(BitmapRef<'target, Target>),

    /// Owned bitmap
    Owned(Target),
}

impl<'target, Target: OwnedBitmap> BitmapCow<'target, Target> {
    /// Extracts the owned bitmap
    ///
    /// Clones the bitmap if it is not already owned.
    pub fn into_owned(self) -> Target {
        match self {
            Self::Borrowed(b) => b.clone_target(),
            Self::Owned(o) => o,
        }
    }
}

impl<'target, Target: OwnedBitmap> AsRef<Target> for BitmapCow<'target, Target> {
    fn as_ref(&self) -> &Target {
        match self {
            Self::Borrowed(b) => b.as_ref(),
            Self::Owned(o) => o,
        }
    }
}

impl<Target: OwnedBitmap> Borrow<Target> for BitmapCow<'_, Target> {
    fn borrow(&self) -> &Target {
        self.as_ref()
    }
}

impl<Target: OwnedBitmap> Deref for BitmapCow<'_, Target> {
    type Target = Target;

    fn deref(&self) -> &Target {
        self.as_ref()
    }
}

impl<Target: OwnedBitmap + Display> Display for BitmapCow<'_, Target> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        <Target as Display>::fmt(self.as_ref(), f)
    }
}

impl<Target: OwnedBitmap + Eq + PartialEq<Self>> Eq for BitmapCow<'_, Target> {}

impl<Target: OwnedBitmap> From<Target> for BitmapCow<'_, Target> {
    fn from(value: Target) -> Self {
        Self::Owned(value)
    }
}

impl<'target, Target: OwnedBitmap> From<&'target Target> for BitmapCow<'target, Target> {
    fn from(value: &'target Target) -> Self {
        Self::Borrowed(value.into())
    }
}

impl<'target, Target: OwnedBitmap> From<BitmapRef<'target, Target>> for BitmapCow<'target, Target> {
    fn from(value: BitmapRef<'target, Target>) -> Self {
        Self::Borrowed(value)
    }
}

impl<'target, Target: OwnedBitmap + Hash> Hash for BitmapCow<'target, Target> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.as_ref().hash(state)
    }
}

impl<Target, Rhs> PartialEq<Rhs> for BitmapCow<'_, Target>
where
    Target: OwnedBitmap + PartialEq<Rhs>,
{
    fn eq(&self, other: &Rhs) -> bool {
        self.as_ref() == other
    }
}

impl<Target: OwnedBitmap> Pointer for BitmapCow<'_, Target> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        <Target as fmt::Pointer>::fmt(self.as_ref(), f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        bitmap::{Bitmap, SpecializedBitmap},
        strategies::topology_related_set,
        topology::Topology,
    };
    use proptest::prelude::*;
    #[allow(unused)]
    use similar_asserts::assert_eq;
    use std::{collections::hash_map::RandomState, hash::BuildHasher};

    // Test BitmapCow construction and intrinsic properties
    proptest! {
        /// Test construction from cpuset
        #[test]
        fn from_cpuset(cpuset in topology_related_set(Topology::complete_cpuset)) {
            check_specialized_cow(cpuset)?;
        }

        /// Test construction from nodeset
        #[test]
        fn from_nodeset(nodeset in topology_related_set(Topology::complete_nodeset)) {
            check_specialized_cow(nodeset)?;
        }
    }

    /// Test construction of [`BitmapCow`] from specialized bitmaps
    fn check_specialized_cow(target: impl SpecializedBitmap) -> Result<(), TestCaseError> {
        check_any_cow(target.clone())?;
        check_any_cow::<Bitmap>(target.into())?;
        Ok(())
    }

    /// Test construction of [`BitmapCow`] from any bitmap
    fn check_any_cow<Target: OwnedBitmap>(target: Target) -> Result<(), TestCaseError> {
        {
            let from_owned = BitmapCow::from(target.clone());
            prop_assert!(matches!(
                &from_owned,
                BitmapCow::Owned(target2) if *target2 == target
            ));
            check_cow(from_owned)?;
        }
        {
            let from_rust_ref = BitmapCow::from(&target);
            prop_assert!(matches!(
                &from_rust_ref,
                BitmapCow::Borrowed(target2) if *target2 == target
            ));
            check_cow(from_rust_ref)?;
        }
        {
            let from_bitmap_ref = BitmapCow::from(BitmapRef::from(&target));
            prop_assert!(matches!(
                &from_bitmap_ref,
                BitmapCow::Borrowed(target2) if *target2 == target
            ));
            check_cow(from_bitmap_ref)?;
        }
        Ok(())
    }

    /// Test properties of a [`BitmapCow`]
    fn check_cow<Target: OwnedBitmap>(cow: BitmapCow<'_, Target>) -> Result<(), TestCaseError> {
        let owned: Target = cow.clone().into_owned();
        prop_assert_eq!(&cow, &owned);

        let mut target_ref: &Target = cow.as_ref();
        prop_assert_eq!(target_ref, &owned);

        target_ref = cow.borrow();
        prop_assert_eq!(target_ref, &owned);

        target_ref = &cow;
        prop_assert_eq!(target_ref, &owned);

        prop_assert_eq!(cow.to_string(), owned.to_string());

        let bh = RandomState::new();
        prop_assert_eq!(bh.hash_one(&cow), bh.hash_one(&owned));

        prop_assert_eq!(format!("{:p}", *target_ref), format!("{cow:p}"));
        prop_assert_ne!(format!("{owned:p}"), format!("{cow:p}"));
        Ok(())
    }

    // Test properties of pair of BitmapCows
    proptest! {
        /// Test construction from cpuset
        #[test]
        fn cpuset_pair(
            cpusets in prop::array::uniform2(topology_related_set(Topology::complete_cpuset))
        ) {
            check_specialized_cow_pair(cpusets)?;
        }

        /// Test construction from nodeset
        #[test]
        fn nodeset_pair(
            nodesets in prop::array::uniform2(topology_related_set(Topology::complete_nodeset))
        ) {
            check_specialized_cow_pair(nodesets)?;
        }
    }

    /// Test construction of [`BitmapCow`] from specialized bitmaps
    fn check_specialized_cow_pair(
        targets: [impl SpecializedBitmap; 2],
    ) -> Result<(), TestCaseError> {
        check_any_cow_pair(targets.clone())?;
        check_any_cow_pair::<Bitmap>(targets.map(Into::into))?;
        Ok(())
    }

    /// Test construction of [`BitmapCow`] from any bitmap
    fn check_any_cow_pair<Target: OwnedBitmap>(targets: [Target; 2]) -> Result<(), TestCaseError> {
        check_cow_pair(targets.clone().map(BitmapCow::from))?;
        let [target1_ref, target2_ref] = &targets;
        let target_refs = [target1_ref, target2_ref];
        check_cow_pair(target_refs.map(BitmapCow::from))?;
        Ok(())
    }

    /// Test properties of a [`BitmapCow`]
    fn check_cow_pair<Target: OwnedBitmap>(
        [cow1, cow2]: [BitmapCow<'_, Target>; 2],
    ) -> Result<(), TestCaseError> {
        let target1: &Target = &cow1;
        let target2: &Target = &cow2;
        prop_assert_eq!(cow1 == *target2, target1 == target2);
        Ok(())
    }
}
