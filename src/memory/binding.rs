//! Memory binding

// Main docs: https://hwloc.readthedocs.io/en/v2.9/group__hwlocality__membinding.html

#[cfg(doc)]
use crate::support::MemoryBindingSupport;
use crate::{
    bitmaps::SpecializedBitmap,
    errors::{self, FlagsError, RawIntError, RawNullError},
    ffi, Topology,
};
use bitflags::bitflags;
use derive_more::Display;
use errno::{errno, Errno};
use libc::{ENOMEM, ENOSYS, EXDEV};
use num_enum::{IntoPrimitive, TryFromPrimitive};
use std::{
    borrow::{Borrow, BorrowMut},
    error::Error,
    ffi::{c_int, c_void},
    fmt::{self, Debug, Display},
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};
use thiserror::Error;

bitflags! {
    /// Memory binding flags.
    ///
    /// These bit flags can be used to refine the binding policy. All flags can
    /// be OR'ed together with the exception of `ASSUME_SINGLE_THREAD`, `THREAD`
    /// and `PROCESS`, of which at most one must be specified. The most portable
    /// option is `ASSUME_SINGLE_THREAD`, when it is applicable.
    ///
    /// Not all systems support all kinds of binding,
    /// [`Topology::feature_support()`] may be used to query the
    /// actual memory binding support in the currently used operating system.
    #[repr(C)]
    #[doc(alias = "hwloc_membind_flags_t")]
    pub struct MemoryBindingFlags: c_int {
        /// Assume that the target process is single threaded
        ///
        /// This lets hwloc pick between thread and process binding for
        /// increased portability.
        ///
        /// This is mutually exclusive with `PROCESS` and `THREAD`.
        const ASSUME_SINGLE_THREAD = 0;

        /// Set policy for all threads of the specified process
        ///
        /// This is mutually exclusive with `ASSUME_SINGLE_THREAD` and `PROCESS`.
        #[doc(alias = "HWLOC_MEMBIND_PROCESS")]
        const PROCESS = (1<<0);

        /// Set policy for a specific thread of the specified process
        ///
        /// This is mutually exclusive with `ASSUME_SINGLE_THREAD` and `THREAD`.
        #[doc(alias = "HWLOC_MEMBIND_THREAD")]
        const THREAD = (1<<1);

        /// Request strict binding from the OS
        ///
        /// If this flag is set, a binding function will fail if the binding can
        /// not be guaranteed or completely enforced. Otherwise, hwloc will
        /// attempt to achieve an approximation of the requested binding (e.g.
        /// targeting more or less threads and NUMA nodes).
        ///
        /// This flag has slightly different meanings depending on which
        /// function it is used with.
        #[doc(alias = "HWLOC_MEMBIND_STRICT")]
        const STRICT = (1<<2);

        /// Migrate existing allocated memory
        ///
        /// If the memory cannot be migrated and the `STRICT` flag is set, an
        /// error will be returned.
        ///
        /// Requires [`MemoryBindingSupport::migrate()`].
        #[doc(alias = "HWLOC_MEMBIND_MIGRATE")]
        const MIGRATE = (1<<3);

        /// Avoid any effect on CPU binding
        ///
        /// On some operating systems, some underlying memory binding
        /// functions also bind the application to the corresponding CPU(s).
        /// Using this flag will cause hwloc to avoid using OS functions that
        /// could potentially affect CPU bindings.
        ///
        /// Note, however, that using this flag may reduce hwloc's overall
        /// memory binding support.
        #[doc(alias = "HWLOC_MEMBIND_NOCPUBIND")]
        const NO_CPU_BINDING = (1<<4);

        /// Consider the bitmap argument as a nodeset.
        ///
        /// The bitmap argument is considered a nodeset if this flag is given,
        /// or a cpuset otherwise by default.
        ///
        /// Memory binding by CPU set cannot work for CPU-less NUMA memory nodes.
        /// Binding by nodeset should therefore be preferred whenever possible.
        //
        // NOTE: This flag is automatically set by the implementation
        #[doc(hidden)]
        #[doc(alias = "HWLOC_MEMBIND_BYNODESET")]
        const BY_NODE_SET = (1<<5);
    }
}
//
impl MemoryBindingFlags {
    /// Truth that these flags are in a valid state
    pub(crate) fn is_valid(
        self,
        target: MemoryBoundObject,
        operation: MemoryBindingOperation,
    ) -> bool {
        // Intrinsically incompatible flag combination
        if self.contains(Self::PROCESS | Self::THREAD) {
            return false;
        }

        // Support for PROCESS and THREAD
        let good_for_target = match target {
            MemoryBoundObject::Area => !self.intersects(Self::PROCESS | Self::THREAD),
            MemoryBoundObject::Process => !self.contains(Self::THREAD),
            MemoryBoundObject::ThisProgram => true,
        };

        // Support fo STRICT, MIGRATE and NO_CPU_BINDING
        good_for_target
            && match operation {
                MemoryBindingOperation::GetLastLocation => {
                    !self.intersects(Self::STRICT | Self::MIGRATE | Self::NO_CPU_BINDING)
                }
                MemoryBindingOperation::GetBinding => {
                    if self.intersects(Self::MIGRATE | Self::NO_CPU_BINDING) {
                        return false;
                    }
                    match target {
                        MemoryBoundObject::Area | MemoryBoundObject::Process => true,
                        MemoryBoundObject::ThisProgram => {
                            !self.contains(Self::STRICT) || self.contains(Self::PROCESS)
                        }
                    }
                }
                MemoryBindingOperation::Unbind => !self.intersects(Self::STRICT | Self::MIGRATE),
                MemoryBindingOperation::Allocate => !self.contains(Self::MIGRATE),
                MemoryBindingOperation::Bind => true,
            }
    }
}
//
// NOTE: No default because user must consciously think about the need for PROCESS
//
/// Object that is being bound to particular NUMA nodes
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum MemoryBoundObject {
    /// A process, identified by its PID
    Process,

    /// A range of memory adresses, identified by a reference
    Area,

    /// The currently running program
    ThisProgram,
}
//
impl Display for MemoryBoundObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let display = match self {
            Self::Process => "the target process",
            Self::Area => "the target location",
            Self::ThisProgram => "the current process/thread",
        };
        write!(f, "{display}")
    }
}
//
/// Binding operation
#[derive(Copy, Clone, Debug, Display, Eq, Hash, PartialEq)]
pub(crate) enum MemoryBindingOperation {
    GetBinding,
    Bind,
    Unbind,
    Allocate,
    GetLastLocation,
}

/// Rust mapping of the hwloc_membind_policy_t enum
///
/// We can't use Rust enums to model C enums in FFI because that results in
/// undefined behavior if the C API gets new enum variants and sends them to us.
///
pub(crate) type RawMemoryBindingPolicy = c_int;

/// Memory binding policy.
///
/// Not all systems support all kinds of binding.
/// [`Topology::feature_support()`] may be used to query the
/// actual memory binding support in the currently used operating system.
#[repr(i32)]
#[derive(
    Copy, Clone, Debug, Default, Display, Eq, Hash, IntoPrimitive, PartialEq, TryFromPrimitive,
)]
#[doc(alias = "hwloc_membind_policy_t")]
pub enum MemoryBindingPolicy {
    /// Allocate each memory page individually on the local NUMA
    /// node of the thread that touches it
    ///
    /// The given nodeset should usually be [`Topology::nodeset()`]
    /// so that the touching thread may run and allocate on any node in the
    /// system.
    ///
    /// On AIX, if the nodeset is smaller, pages are allocated locally (if the
    /// local node is in the nodeset) or from a random non-local node (otherwise).
    ///
    /// Requires [`MemoryBindingSupport::first_touch()`].
    #[doc(alias = "HWLOC_MEMBIND_FIRSTTOUCH")]
    FirstTouch = 1,

    /// Allocate memory on the specified nodes (most portable option)
    ///
    /// Requires [`MemoryBindingSupport::bind()`].
    #[default]
    #[doc(alias = "HWLOC_MEMBIND_BIND")]
    Bind = 2,

    /// Allocate memory on the given nodes in an interleaved round-robin manner
    ///
    /// The precise layout of the memory across multiple NUMA nodes is OS/system
    /// specific.
    ///
    /// Interleaving can be useful when threads distributed across the specified
    /// NUMA nodes will all be accessing the whole memory range concurrently,
    /// since the interleave will then balance the memory references.
    ///
    /// Requires [`MemoryBindingSupport::interleave()`].
    #[doc(alias = "HWLOC_MEMBIND_INTERLEAVE")]
    Interleave = 3,

    /// Migrate pages on next touch
    ///
    /// For each page bound with this policy, by next time it is touched (and
    /// next time only), it is moved from its current location to the local NUMA
    /// node of the thread where the memory reference occurred (if it needs to
    /// be moved at all).
    ///
    /// Requires [`MemoryBindingSupport::next_touch()`].
    #[doc(alias = "HWLOC_MEMBIND_NEXTTOUCH")]
    NextTouch = 4,
}

/// Errors that can occur when binding memory to NUMA nodes, querying bindings,
/// or allocating (possibly bound) memory
#[derive(Copy, Clone, Debug, Error, Eq, Hash, PartialEq)]
pub enum GenericMemoryBindingError<Set: SpecializedBitmap, RawHwlocError: Error> {
    /// The system does not support the specified action or policy
    ///
    /// For example, some systems only allow binding memory on a per-thread
    /// basis, whereas other systems only allow binding memory for all threads
    /// in a process.
    ///
    /// This error might not be reported if [`MemoryBindingFlags::STRICT`] is
    /// not set. Instead, the implementation is allowed to try to use a slightly
    /// different operation (with side-effects, binding more objects, etc.) when
    /// the requested operation is not exactly supported.
    #[error("requested memory binding action or policy is not supported")]
    Unsupported,

    /// Requested memory binding flags are not valid in this context
    ///
    /// Not all memory binding flag combinations make sense, either in isolation
    /// or in the context of a particular binding function. Please cross-check
    /// the documentation of [`MemoryBindingFlags`] and the function you were
    /// trying to call for more information.
    #[error(transparent)]
    BadFlags(FlagsError<MemoryBindingFlags>),

    /// Cannot bind to the target CPU or node set
    ///
    /// Operating systems can have various restrictions here, e.g. can only bind
    /// to NUMA node.
    ///
    /// This error should only be reported when trying to set memory bindings.
    ///
    /// This error might not be reported if [`MemoryBindingFlags::STRICT`] is
    /// not set. Instead, the implementation is allowed to try using a smaller
    /// or larger set to make the operation succeed.
    #[error("cannot bind {0} to {1}")]
    BadSet(MemoryBoundObject, Set),

    /// Memory allocation failed even before trying to bind
    ///
    /// This error may only be returned by [`Topology::allocate_bound_memory()`]
    /// and [`Topology::binding_allocate_memory()`].
    #[error("failed to allocate memory")]
    AllocationFailed,

    /// Memory policies and nodesets vary from one thread to another
    ///
    /// This error is returned when querying a process' memory bindings with the
    /// flags [`PROCESS`] and [`STRICT`] specified. It means that the default
    /// memory policies and nodesets are not homogeneous across all threads of
    /// the target process.
    ///
    /// [`PROCESS`]: MemoryBindingFlags::PROCESS
    /// [`STRICT`]: MemoryBindingFlags::STRICT
    #[error("binding varies from one thread of the process to another")]
    #[doc(alias = "HWLOC_MEMBIND_MIXED")]
    MixedResults,

    /// Unexpected hwloc error
    ///
    /// The hwloc documentation isn't exhaustive about what errors can occur in
    /// general, and new error cases could potentially be added by new hwloc
    /// releases. If we cannot provide a high-level error description, we will
    /// fall back to reporting the raw error from the hwloc API.
    #[error(transparent)]
    Unexpected(#[from] RawHwlocError),
}
//
impl<Set: SpecializedBitmap, RawHwlocError: Error> From<MemoryBindingFlags>
    for GenericMemoryBindingError<Set, RawHwlocError>
{
    fn from(value: MemoryBindingFlags) -> Self {
        Self::BadFlags(value.into())
    }
}

/// Errors that can occur when querying or setting memory bindings
pub type MemoryBindingError<Set> = GenericMemoryBindingError<Set, RawIntError>;

/// Call an hwloc API that is about manipulating memory bindings and translate
/// known errors into higher-level `MemoryBindingError`s.
///
/// Validating flags is left up to the caller, to avoid allocating result
/// objects when it can be proved upfront that the request is invalid.
pub(crate) fn call_hwloc_int<Set: SpecializedBitmap>(
    api: &'static str,
    object: MemoryBoundObject,
    operation: MemoryBindingOperation,
    set: Option<&Set>,
    ffi: impl FnOnce() -> c_int,
) -> Result<(), MemoryBindingError<Set>> {
    match errors::call_hwloc_int(api, ffi) {
        Ok(_positive) => Ok(()),
        Err(
            raw_err @ RawIntError::Errno {
                errno: Some(errno), ..
            },
        ) => {
            if let Some(error) = decode_errno(object, operation, set, errno) {
                Err(error)
            } else {
                Err(MemoryBindingError::Unexpected(raw_err))
            }
        }
        Err(raw_err) => Err(MemoryBindingError::Unexpected(raw_err)),
    }
}

/// Errors that can occur when allocating memory
pub type MemoryAllocationError<Set> = GenericMemoryBindingError<Set, RawNullError>;
//
impl<Set: SpecializedBitmap> From<MemoryBindingError<Set>> for MemoryAllocationError<Set> {
    fn from(value: MemoryBindingError<Set>) -> Self {
        match value {
            MemoryBindingError::Unsupported => Self::Unsupported,
            MemoryBindingError::BadFlags(flags) => Self::BadFlags(flags),
            MemoryBindingError::BadSet(memory_bound_object, set) => {
                Self::BadSet(memory_bound_object, set)
            }
            MemoryBindingError::AllocationFailed => Self::AllocationFailed,
            MemoryBindingError::MixedResults => Self::MixedResults,
            GenericMemoryBindingError::Unexpected(RawIntError::Errno { api, errno })
            | GenericMemoryBindingError::Unexpected(RawIntError::ReturnValue {
                api, errno, ..
            }) => Self::Unexpected(RawNullError { api, errno }),
        }
    }
}

/// Call an hwloc API that allocates (possibly bound) memory and translate
/// known errors into higher-level `MemoryBindingError`s.
///
/// Validating flags is left up to the caller, to avoid allocating result
/// objects when it can be proved upfront that the request is invalid.
pub(crate) fn call_hwloc_allocate<Set: SpecializedBitmap>(
    api: &'static str,
    set: Option<&Set>,
    ffi: impl FnOnce() -> *mut c_void,
) -> Result<NonNull<c_void>, MemoryAllocationError<Set>> {
    errors::call_hwloc_ptr_mut(api, ffi).map_err(|raw_err| {
        if let RawNullError {
            errno: Some(errno), ..
        } = raw_err
        {
            if let Some(error) = decode_errno(
                MemoryBoundObject::Area,
                MemoryBindingOperation::Allocate,
                set,
                errno,
            ) {
                return error;
            }
        }
        MemoryAllocationError::Unexpected(raw_err)
    })
}

/// Translating hwloc errno into high-level errors
fn decode_errno<Set: SpecializedBitmap, RawHwlocError: Error>(
    object: MemoryBoundObject,
    operation: MemoryBindingOperation,
    set: Option<&Set>,
    errno: Errno,
) -> Option<GenericMemoryBindingError<Set, RawHwlocError>> {
    match errno.0 {
        ENOSYS => Some(GenericMemoryBindingError::Unsupported),
        EXDEV => match operation {
            MemoryBindingOperation::Bind | MemoryBindingOperation::Allocate => {
                Some(GenericMemoryBindingError::BadSet(
                    object,
                    set.expect("This error should only be observed on commands that set bindings")
                        .clone(),
                ))
            }
            MemoryBindingOperation::GetBinding | MemoryBindingOperation::GetLastLocation => {
                Some(GenericMemoryBindingError::MixedResults)
            }
            MemoryBindingOperation::Unbind => {
                unreachable!("The empty set should always be considered valid")
            }
        },
        ENOMEM => Some(GenericMemoryBindingError::AllocationFailed),
        _ => None,
    }
}

/// Bytes allocated through hwloc
///
/// This behaves like a `Box<[MaybeUninit<u8>]>` and will similarly
/// automatically liberate the allocated memory when it goes out of scope.
pub struct Bytes<'topology> {
    /// Underlying hwloc topology
    topology: &'topology Topology,

    /// Previously allocated data pointer
    data: NonNull<[MaybeUninit<u8>]>,
}

impl<'topology> Bytes<'topology> {
    /// Wrap an hwloc allocation
    pub(crate) unsafe fn wrap(
        topology: &'topology Topology,
        base: NonNull<c_void>,
        len: usize,
    ) -> Self {
        let base = base.as_ptr() as *mut MaybeUninit<u8>;
        let data = std::ptr::slice_from_raw_parts_mut(base, len);
        Self {
            topology,
            data: NonNull::new_unchecked(data),
        }
    }
}

impl AsRef<[MaybeUninit<u8>]> for Bytes<'_> {
    fn as_ref(&self) -> &[MaybeUninit<u8>] {
        unsafe { self.data.as_ref() }
    }
}

impl AsMut<[MaybeUninit<u8>]> for Bytes<'_> {
    fn as_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        unsafe { self.data.as_mut() }
    }
}

impl Borrow<[MaybeUninit<u8>]> for Bytes<'_> {
    fn borrow(&self) -> &[MaybeUninit<u8>] {
        self.as_ref()
    }
}

impl BorrowMut<[MaybeUninit<u8>]> for Bytes<'_> {
    fn borrow_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.as_mut()
    }
}

impl Debug for Bytes<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(self.as_ref(), f)
    }
}

impl Deref for Bytes<'_> {
    type Target = [MaybeUninit<u8>];

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl DerefMut for Bytes<'_> {
    fn deref_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.as_mut()
    }
}

impl Drop for Bytes<'_> {
    fn drop(&mut self) {
        let addr = self.data.as_ptr() as *mut MaybeUninit<u8> as *mut c_void;
        let len = self.data.len();
        let result = unsafe { ffi::hwloc_free(self.topology.as_ptr(), addr, len) };
        assert_eq!(
            result,
            0,
            "Got unexpected result from hwloc_free with errno {}",
            errno()
        );
    }
}
