//! `repr(transparent)` newtypes over hwloc types
//!
//! A safe Rust binding to a C library can only function as intended if
//! structs of interest are kept in a valid state. For example pointers should
//! keep pointing to valid allocations containing valid data of the expected
//! lifetimes, be devoid of forbidden aliases when dereferenced, etc.
//! In other words, for safe Rust -> C bindings to be possible, C struct type
//! invariants must be enforced in such a way that safe code cannot modify the
//! struct in a manner that violates them.
//!
//! However, given access to a C struct's field access can trivially break its
//! invariants (e.g. replace a pointer that shouldn't be null with a null one,
//! replace a pointer to something of lifetime 'a with a pointer to another
//! thing of lifetime 'b). Therefore, type invariant preservation requires
//! field encapsulation.
//!
//! At the same time, we want to...
//!
//! - Have the raw `hwlocality-sys` FFI layer be purely defined in terms of
//!   un-encapsulated C struct definitions.
//! - Be able to translate a pointer to an un-encapsulated struct from the FFI
//!   layer into a pointer/reference to an encapsulated struct without needing
//!   any complicated/expensive code.
//!
//! The way to fulfill these constraints in Rust is to use
//! `repr(transparent)` newtypes for encapsulation, and this module is all about
//! doing that while minimizing the safety impact of all the pointer casting
//! that such a design inevitably leads to.

use std::ptr::NonNull;

/// Type that is a `repr(transparent)` wrapper around another type
///
/// # Safety
///
/// `Self` must be a `repr(transparent)` wrapper around `Self::Inner`
pub(crate) unsafe trait TransparentNewtype: Sized {
    /// Inner type that is being wrapped by `Self`
    type Inner;

    /// Assert that `Self` has the same size and alignment as `Self::Inner`
    ///
    /// This minimal layout check should be passed by any valid implementation
    /// of this trait, and be fully evaluated at compile time in optimized
    /// builds with no associated runtime costs.
    #[inline]
    fn check_basic_layout() {
        assert_eq!(
            std::mem::size_of::<Self>(),
            std::mem::size_of::<Self::Inner>(),
            "Incorrectly sized TransparentNewtype implementation detected"
        );
        assert_eq!(
            std::mem::align_of::<Self>(),
            std::mem::align_of::<Self::Inner>(),
            "Incorrectly aligned TransparentNewtype implementation detected"
        );
    }
}

/// Convert a pointer/reference to a C-style struct into the newtype equivalent
///
/// # Safety
///
/// Unsafe code can rely on this trait being implemented correctly for safety
pub(crate) unsafe trait ToNewtype<Newtype: TransparentNewtype> {
    /// Like this type, but with the C struct replaced with its newtype
    type Wrapped;

    /// Perform the conversion
    fn to_newtype(self) -> Self::Wrapped;
}

// SAFETY: Per TransparentNewtype contract, casting &'a T to &'a NewT is legal
unsafe impl<'a, T, NewT: TransparentNewtype<Inner = T> + 'a> ToNewtype<NewT> for &'a T {
    type Wrapped = &'a NewT;

    fn to_newtype(self) -> Self::Wrapped {
        NewT::check_basic_layout();
        let ptr: *const T = self;
        // SAFETY: - &mut *ptr is safe per se since ptr is just a reinterpreted &mut
        //         - Per TransparentNewtype contract, T can be reinterpreted as NewT
        unsafe { &*ptr.cast::<NewT>() }
    }
}

// SAFETY: Per TransparentNewtype contract, casting &'a mut T to &'a mut NewT is legal
unsafe impl<'a, T, NewT: TransparentNewtype<Inner = T> + 'a> ToNewtype<NewT> for &'a mut T {
    type Wrapped = &'a mut NewT;

    fn to_newtype(self) -> Self::Wrapped {
        NewT::check_basic_layout();
        let ptr: *mut T = self;
        // SAFETY: - &mut *ptr is safe per se since ptr is just a reinterpreted &mut
        //         - Per TransparentNewtype contract, T can be reinterpreted as NewT
        unsafe { &mut *ptr.cast::<NewT>() }
    }
}

// SAFETY: Per TransparentNewtype contract, casting NonNull<T> to NonNull<NewT> is legal
unsafe impl<T, NewT: TransparentNewtype<Inner = T>> ToNewtype<NewT> for NonNull<T> {
    type Wrapped = NonNull<NewT>;

    fn to_newtype(self) -> Self::Wrapped {
        NewT::check_basic_layout();
        self.cast()
    }
}

// SAFETY: Per TransparentNewtype contract, casting *const T to *const NewT is legal
unsafe impl<T, NewT: TransparentNewtype<Inner = T>> ToNewtype<NewT> for *const T {
    type Wrapped = *const NewT;

    fn to_newtype(self) -> Self::Wrapped {
        NewT::check_basic_layout();
        self.cast()
    }
}

// SAFETY: Per TransparentNewtype contract, casting *mut T to *mut NewT is legal
unsafe impl<T, NewT: TransparentNewtype<Inner = T>> ToNewtype<NewT> for *mut T {
    type Wrapped = *mut NewT;

    fn to_newtype(self) -> Self::Wrapped {
        NewT::check_basic_layout();
        self.cast()
    }
}

/// Convert a pointer/reference to a newtype into the inner struct equivalent
///
/// # Safety
///
/// Unsafe code can rely on this trait being implemented correctly for safety
pub(crate) unsafe trait ToInner {
    /// Like this type, but with the newtype replaced with its inner struct
    type Unwrapped;

    /// Perform the conversion
    fn to_inner(self) -> Self::Unwrapped;
}

// SAFETY: Per TransparentNewtype contract, casting &'a NewT to &'a NewT::Inner is legal
unsafe impl<'a, NewT: TransparentNewtype + 'a> ToInner for &'a NewT {
    type Unwrapped = &'a NewT::Inner;

    fn to_inner(self) -> Self::Unwrapped {
        NewT::check_basic_layout();
        let ptr: *const NewT = self;
        // SAFETY: - &mut *ptr is safe per se since ptr is just a reinterpreted &mut
        //         - Per TransparentNewtype contract, NewT can be reinterpreted
        //           as its inner type
        unsafe { &*ptr.cast::<NewT::Inner>() }
    }
}

// SAFETY: Per TransparentNewtype contract, casting &'a mut NewT to &'a mut NewT::Inner is legal
unsafe impl<'a, NewT: TransparentNewtype + 'a> ToInner for &'a mut NewT {
    type Unwrapped = &'a mut NewT::Inner;

    fn to_inner(self) -> Self::Unwrapped {
        NewT::check_basic_layout();
        let ptr: *mut NewT = self;
        // SAFETY: - &mut *ptr is safe per se since ptr is just a reinterpreted &mut
        //         - Per TransparentNewtype contract, NewT can be reinterpreted
        //           as its inner type
        unsafe { &mut *ptr.cast::<NewT::Inner>() }
    }
}

// SAFETY: Per TransparentNewtype contract, casting NonNull<NewT> to NonNull<NewT::Inner> is legal
unsafe impl<NewT: TransparentNewtype> ToInner for NonNull<NewT> {
    type Unwrapped = NonNull<NewT::Inner>;

    fn to_inner(self) -> Self::Unwrapped {
        NewT::check_basic_layout();
        self.cast()
    }
}

// SAFETY: Per TransparentNewtype contract, casting *const NewT to *const NewT::Inner is legal
unsafe impl<NewT: TransparentNewtype> ToInner for *const NewT {
    type Unwrapped = *const NewT::Inner;

    fn to_inner(self) -> Self::Unwrapped {
        NewT::check_basic_layout();
        self.cast()
    }
}

// SAFETY: Per TransparentNewtype contract, casting *mut NewT to *mut NewT::Inner is legal
unsafe impl<NewT: TransparentNewtype> ToInner for *mut NewT {
    type Unwrapped = *mut NewT::Inner;

    fn to_inner(self) -> Self::Unwrapped {
        NewT::check_basic_layout();
        self.cast()
    }
}
