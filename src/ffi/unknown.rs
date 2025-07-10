//! Handling of unknown enum variants

use derive_more::{AsRef, Binary, Deref, Display, LowerExp, LowerHex, Octal, UpperExp, UpperHex};

/// Unknown enum variant from hwloc
///
/// Values of this type represent enum values received from hwloc that
/// `hwlocality` was not built to handle. This can happen when `hwlocality` is
/// built to support a certain minimal hwloc version, but is then linked
/// against a newer hwloc version that defines new enum variants.
///
/// You may freely introspect the contents of these enum values, but are not
/// allowed to generate new ones from Rust integers. Thanks to this,
/// `hwlocality` can assume that these values are valid inputs that your hwloc
/// version can accept (since it originally emitted them as the output of
/// another query). And therefore you will be able to feed these values back to
/// hwloc in most circumstances.
///
/// This capability to feed back unknown enum values to hwloc will however be
/// restricted in circumstances where hwloc treats enum variants in such
/// a way that sending it an unknown enum variant could result in a memory-,
/// type- or thread-safety hazard.
#[derive(
    AsRef,
    Binary,
    Copy,
    Clone,
    Debug,
    Deref,
    Display,
    Eq,
    Hash,
    LowerExp,
    LowerHex,
    Octal,
    Ord,
    PartialEq,
    PartialOrd,
    UpperExp,
    UpperHex,
)]
pub struct UnknownVariant<T>(pub(crate) T);
