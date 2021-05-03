//! # bytecheck
//!
//! bytecheck is a type validation framework for Rust.
//!
//! For some types, creating an invalid value immediately results in undefined
//! behavior. This can cause some issues when trying to validate potentially
//! invalid bytes, as just casting the bytes to your type can technically cause
//! errors. This makes it difficult to write validation routines, because until
//! you're certain that the bytes represent valid values you cannot cast them.
//!
//! bytecheck provides a framework for performing these byte-level validations
//! and implements checks for basic types along with a derive macro to implement
//! validation for custom structs and enums.
//!
//! ## Design
//!
//! [`CheckBytes`] is at the heart of bytecheck, and does the heavy lifting of
//! verifying that some bytes represent a valid type. Implementing it can be
//! done manually or automatically with the [derive macro](macro@CheckBytes).
//!
//! ## Examples
//!
//! ```
//! use bytecheck::CheckBytes;
//!
//! #[derive(CheckBytes, Debug)]
//! struct Test {
//!     a: u32,
//!     b: bool,
//!     c: char,
//! }
//!
//! // This type is laid out as (u32, char, bool)
//! unsafe {
//!     // These are valid bytes for (0, 'x', true)
//!     Test::check_bytes(
//!         (&[
//!             0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8,
//!             1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8).cast(),
//!         &mut ()
//!     ).unwrap();
//!
//!     // Changing the bytes for the u32 is OK, any bytes are a valid u32
//!     Test::check_bytes(
//!         (&[
//!             42u8, 16u8, 20u8, 3u8, 0x78u8, 0u8, 0u8, 0u8,
//!             1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8).cast(),
//!         &mut ()
//!     ).unwrap();
//!
//!     // Characters outside the valid ranges are invalid
//!     Test::check_bytes(
//!         (&[
//!             0u8, 0u8, 0u8, 0u8, 0x00u8, 0xd8u8, 0u8, 0u8,
//!             1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8).cast(),
//!         &mut ()
//!     ).unwrap_err();
//!     Test::check_bytes(
//!         (&[
//!             0u8, 0u8, 0u8, 0u8, 0x00u8, 0x00u8, 0x11u8, 0u8,
//!             1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8).cast(),
//!         &mut ()
//!     ).unwrap_err();
//!
//!     // 0 is a valid boolean value (false) but 2 is not
//!     Test::check_bytes(
//!         (&[
//!             0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8,
//!             0u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8).cast(),
//!         &mut ()
//!     ).unwrap();
//!     Test::check_bytes(
//!         (&[
//!             0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8,
//!             2u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8).cast(),
//!         &mut ()
//!     ).unwrap_err();
//! }
//! ```
//!
//! ## Features
//!
//! - `const_generics`: Extends the implementations of [`CheckBytes`] to all
//!   arrays and not just arrays up to length 32 (enabled by default).
//! - `log`: Logs errors using the `log` crate in `no_std` environments. Does nothing in `std`
//!   environments.
//! - `std`: Enables standard library support (enabled by default).

#![cfg_attr(not(feature = "std"), no_std)]

use core::{
    convert::TryFrom,
    fmt,
    marker::{PhantomData, PhantomPinned},
    num::{
        NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroU128, NonZeroU16,
        NonZeroU32, NonZeroU64, NonZeroU8,
    },
    ops,
    slice,
};
#[cfg(has_atomics)]
use core::sync::atomic::{
    AtomicBool, AtomicI8, AtomicI16, AtomicI32, AtomicU8, AtomicU16, AtomicU32
};
#[cfg(has_atomics_64)]
use core::sync::atomic::{AtomicI64, AtomicU64};
use ptr_meta::PtrExt;
#[cfg(feature = "std")]
use std::error::Error;
#[cfg(not(feature = "full_errors"))]
use simdutf8::basic::{Utf8Error, from_utf8};
#[cfg(feature = "full_errors")]
use simdutf8::compat::{Utf8Error, from_utf8};

pub use bytecheck_derive::CheckBytes;
pub use memoffset::offset_of;

/// A type that can check whether a pointer points to a valid value.
///
/// `CheckBytes` can be derived with [`CheckBytes`](macro@CheckBytes) or
/// implemented manually for custom behavior.
pub trait CheckBytes<C: ?Sized> {
    /// The error that may result from checking the type.
    #[cfg(feature = "std")]
    type Error: Error + 'static;
    #[cfg(not(feature = "std"))]
    type Error: fmt::Display + 'static;

    /// Checks whether the given pointer points to a valid value within the
    /// given context.
    ///
    /// # Safety
    ///
    /// The passed pointer must be aligned and point to enough bytes to
    /// represent the type.
    unsafe fn check_bytes<'a>(value: *const Self, context: &mut C) -> Result<&'a Self, Self::Error>;
}

// std error handling

/// The type of nested errors
#[cfg(feature = "std")]
pub type NestedError = Box<dyn Error>;

/// Nests errors according to user configuration
#[cfg(feature = "std")]
#[inline]
pub fn handle_error<E: Error + 'static>(error: E) -> NestedError {
    Box::new(error)
}

// no_std error handling

/// An error type that reminds users to enable logging
#[derive(Debug)]
pub struct EnableLoggingError;

impl fmt::Display for EnableLoggingError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "enable the `log` feature in bytecheck to log errors")
    }
}

// logless error handling

/// The type of nested errors
#[cfg(all(not(feature = "std"), not(feature = "log")))]
pub type NestedError = EnableLoggingError;

/// Nests errors according to user configuration
#[cfg(all(not(feature = "std"), not(feature = "log")))]
#[inline]
pub fn handle_error<E>(_: E) -> NestedError {
    EnableLoggingError
}

/// An error type that reminds users to check the logs
#[derive(Debug)]
pub struct CheckLogsError;

impl fmt::Display for CheckLogsError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "see logs")
    }
}

// logging error handling

/// The type of nested errors
#[cfg(all(not(feature = "std"), feature = "log"))]
pub type NestedError = CheckLogsError;

/// Nests errors according to user configuration
#[cfg(all(not(feature = "std"), feature = "log"))]
pub fn handle_error<E: Display>(error: E) -> NestedError {
    log::error!("[bytecheck] {}", error);
    CheckLogsError
}

/// An error that cannot be produced
///
/// This is used primarily for primitive types that do not have invalid values
/// such as integers and floats.
#[derive(Debug)]
pub enum Unreachable {}

impl fmt::Display for Unreachable {
    #[inline]
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unsafe { core::hint::unreachable_unchecked() }
    }
}

#[cfg(feature = "std")]
impl Error for Unreachable {}

macro_rules! impl_primitive {
    ($type:ty) => {
        impl<C: ?Sized> CheckBytes<C> for $type {
            type Error = Unreachable;

            #[inline]
            unsafe fn check_bytes<'a>(value: *const Self, _: &mut C) -> Result<&'a Self, Self::Error> {
                Ok(&*value)
            }
        }
    };
}

impl_primitive!(());
impl_primitive!(i8);
impl_primitive!(i16);
impl_primitive!(i32);
impl_primitive!(i64);
impl_primitive!(i128);
impl_primitive!(u8);
impl_primitive!(u16);
impl_primitive!(u32);
impl_primitive!(u64);
impl_primitive!(u128);
impl_primitive!(f32);
impl_primitive!(f64);
#[cfg(has_atomics)]
impl_primitive!(AtomicI8);
#[cfg(has_atomics)]
impl_primitive!(AtomicI16);
#[cfg(has_atomics)]
impl_primitive!(AtomicI32);
#[cfg(has_atomics_64)]
impl_primitive!(AtomicI64);
#[cfg(has_atomics)]
impl_primitive!(AtomicU8);
#[cfg(has_atomics)]
impl_primitive!(AtomicU16);
#[cfg(has_atomics)]
impl_primitive!(AtomicU32);
#[cfg(has_atomics_64)]
impl_primitive!(AtomicU64);

impl<T: ?Sized, C: ?Sized> CheckBytes<C> for PhantomData<T> {
    type Error = Unreachable;

    #[inline]
    unsafe fn check_bytes<'a>(
        value: *const Self,
        _: &mut C,
    ) -> Result<&'a Self, Self::Error> {
        Ok(&*value)
    }
}

impl<C: ?Sized> CheckBytes<C> for PhantomPinned {
    type Error = Unreachable;

    #[inline]
    unsafe fn check_bytes<'a>(
        value: *const Self,
        _: &mut C,
    ) -> Result<&'a Self, Self::Error> {
        Ok(&*value)
    }
}

/// An error resulting from an invalid boolean.
///
/// Booleans are one byte and may only have the value 0 or 1.
#[derive(Debug)]
pub struct BoolCheckError {
    /// The byte value of the invalid boolean
    pub invalid_value: u8,
}

impl fmt::Display for BoolCheckError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "check failed for bool: expected 0 or 1, found {}",
            self.invalid_value
        )
    }
}

#[cfg(feature = "std")]
impl Error for BoolCheckError {}

impl<C: ?Sized> CheckBytes<C> for bool {
    type Error = BoolCheckError;

    #[inline]
    unsafe fn check_bytes<'a>(value: *const Self, _: &mut C) -> Result<&'a Self, Self::Error> {
        let byte = *value.cast::<u8>();
        match byte {
            0 | 1 => Ok(&*value),
            _ => Err(BoolCheckError {
                invalid_value: byte,
            }),
        }
    }
}

#[cfg(has_atomics)]
impl<C: ?Sized> CheckBytes<C> for AtomicBool {
    type Error = BoolCheckError;

    #[inline]
    unsafe fn check_bytes<'a>(value: *const Self, _: &mut C) -> Result<&'a Self, Self::Error> {
        let byte = *value.cast::<u8>();
        match byte {
            0 | 1 => Ok(&*value),
            _ => Err(BoolCheckError {
                invalid_value: byte,
            }),
        }
    }
}

/// An error resulting from an invalid character.
///
/// Characters are four bytes and may only have values from `0x0` to `0xD7FF`
/// and `0xE000` to `0x10FFFF` inclusive.
#[derive(Debug)]
pub struct CharCheckError {
    /// The `u32` value of the invalid character
    pub invalid_value: u32,
}

impl From<Unreachable> for CharCheckError {
    #[inline]
    fn from(_: Unreachable) -> Self {
        unsafe { core::hint::unreachable_unchecked() }
    }
}

impl fmt::Display for CharCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "check failed for char: invalid value {}",
            self.invalid_value
        )
    }
}

#[cfg(feature = "std")]
impl Error for CharCheckError {}

impl<C: ?Sized> CheckBytes<C> for char {
    type Error = CharCheckError;

    #[inline]
    unsafe fn check_bytes<'a>(value: *const Self, context: &mut C) -> Result<&'a Self, Self::Error> {
        let c = *u32::check_bytes(value.cast(), context)?;
        char::try_from(c).map_err(|_| CharCheckError {
            invalid_value: c,
        })?;
        Ok(&*value)
    }
}

macro_rules! peel_tuple {
    ([$($error_rest:ident,)*], [$type:ident $index:tt, $($type_rest:ident $index_rest:tt,)*]) => { impl_tuple! { [$($error_rest,)*], [$($type_rest $index_rest,)*] } };
}

macro_rules! impl_tuple {
    ([], []) => {};
    ([$error:ident, $($error_rest:ident,)*], [$($type:ident $index:tt,)+]) => {
        /// An error resulting from an invalid tuple.
        #[derive(Debug)]
        pub enum $error<$($type),+> {
            $($type($type),)+
        }

        impl<$($type: fmt::Display),*> fmt::Display for $error<$($type),+> {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                const SIZE: usize = [$($index,)+].len();
                match self {
                    $($error::$type(e) => write!(f, "check failed for {}-tuple index {}: {}", SIZE, SIZE - $index - 1, e),)+
                }
            }
        }

        #[cfg(feature = "std")]
        impl<$($type: fmt::Display + fmt::Debug),*> Error for $error<$($type),+> {}

        impl<$($type: CheckBytes<C>,)+ C: ?Sized> CheckBytes<C> for ($($type,)+) {
            type Error = $error<$($type::Error),+>;

            #[inline]
            #[allow(clippy::unneeded_wildcard_pattern)]
            unsafe fn check_bytes<'a>(value: *const Self, context: &mut C) -> Result<&'a Self, Self::Error> {
                let bytes = value.cast::<u8>();
                let field_bytes = ($(bytes.add(memoffset::offset_of_tuple!(Self, $index)),)+);
                $($type::check_bytes(field_bytes.$index.cast::<$type>(), context).map_err($error::$type)?;)+
                Ok(&*value)
            }
        }

        peel_tuple! {
            [$($error_rest,)*],
            [$($type $index,)+]
        }
    }
}

impl_tuple! {
    [Tuple12CheckError, Tuple11CheckError, Tuple10CheckError, Tuple9CheckError, Tuple8CheckError, Tuple7CheckError, Tuple6CheckError, Tuple5CheckError, Tuple4CheckError, Tuple3CheckError, Tuple2CheckError, Tuple1CheckError, ],
    [T11 11, T10 10, T9 9, T8 8, T7 7, T6 6, T5 5, T4 4, T3 3, T2 2, T1 1, T0 0, ]
}

/// An error resulting from an invalid array.
#[derive(Debug)]
pub struct ArrayCheckError<T> {
    /// The index of the invalid element
    pub index: usize,
    /// The error that occured while validating the invalid element
    pub error: T,
}

impl<T: fmt::Display> fmt::Display for ArrayCheckError<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "check failed for array index {}: {}",
            self.index, self.error
        )
    }
}

#[cfg(feature = "std")]
impl<T: fmt::Debug + fmt::Display> Error for ArrayCheckError<T> {}

#[cfg(not(feature = "const_generics"))]
macro_rules! impl_array {
    () => {};
    ($len:expr, $($rest:expr,)*) => {
        impl<T: CheckBytes<C>, C: ?Sized> CheckBytes<C> for [T; $len] {
            type Error = ArrayCheckError<T::Error>;

            #[inline]
            unsafe fn check_bytes<'a>(value: *const Self, context: &mut C) -> Result<&'a Self, Self::Error> {
                #[allow(clippy::reversed_empty_ranges)]
                for index in 0..$len {
                    let el = value.cast::<T>().add(index);
                    T::check_bytes(el, context).map_err(|error| ArrayCheckError { index, error })?;
                }
                Ok(&*value)
            }
        }

        impl_array! { $($rest,)* }
    };
}

#[cfg(not(feature = "const_generics"))]
impl_array! { 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, }

#[cfg(feature = "const_generics")]
impl<T: CheckBytes<C>, C: ?Sized, const N: usize> CheckBytes<C> for [T; N] {
    type Error = ArrayCheckError<T::Error>;

    #[inline]
    unsafe fn check_bytes<'a>(value: *const Self, context: &mut C) -> Result<&'a Self, Self::Error> {
        for index in 0..N {
            let el = value.cast::<T>().add(index);
            T::check_bytes(el, context).map_err(|error| ArrayCheckError { index, error })?;
        }
        Ok(&*value)
    }
}

/// An error resulting from an invalid slice.
#[derive(Debug)]
pub enum SliceCheckError<T> {
    /// An element of the slice failed to validate
    CheckBytes {
        /// The index of the invalid element
        index: usize,
        /// The error that occured while validating the invalid element
        error: T,
    },
}

impl<T: fmt::Display> fmt::Display for SliceCheckError<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SliceCheckError::CheckBytes { index, error } => write!(f, "check failed for slice index {}: {}", index, error),
        }
    }
}

#[cfg(feature = "std")]
impl<T: fmt::Debug + fmt::Display> Error for SliceCheckError<T> {}

impl<T: CheckBytes<C>, C: ?Sized> CheckBytes<C> for [T] {
    type Error = SliceCheckError<T::Error>;

    #[inline]
    unsafe fn check_bytes<'a>(value: *const Self, context: &mut C) -> Result<&'a Self, Self::Error> {
        let (data, len) = PtrExt::to_raw_parts(value);
        for index in 0..len {
            let el = data.cast::<T>().add(index);
            T::check_bytes(el, context).map_err(|error| SliceCheckError::CheckBytes { index, error })?;
        }
        Ok(&*value)
    }
}

/// An error resulting from an invalid str.
#[derive(Debug)]
pub enum StrCheckError {
    /// The UTF-8 string failed to validate
    Utf8Error(Utf8Error),
}

impl From<Utf8Error> for StrCheckError {
    fn from(e: Utf8Error) -> Self {
        Self::Utf8Error(e)
    }
}

impl fmt::Display for StrCheckError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StrCheckError::Utf8Error(e) => write!(f, "utf8 error: {}", e),
        }
    }
}

#[cfg(feature = "std")]
impl Error for StrCheckError {
    #[inline]
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            StrCheckError::Utf8Error(e) => Some(e),
        }
    }
}

impl<C: ?Sized> CheckBytes<C> for str {
    type Error = StrCheckError;

    #[inline]
    unsafe fn check_bytes<'a>(value: *const Self, _: &mut C) -> Result<&'a Self, Self::Error> {
        let (data, len) = PtrExt::to_raw_parts(value);
        from_utf8(slice::from_raw_parts(data.cast(), len))?;
        Ok(&*value)
    }
}

/// An error resulting from an invalid struct.
#[derive(Debug)]
pub struct StructCheckError {
    /// The name of the struct field that was invalid
    pub field_name: &'static str,
    /// The error that occurred while validating the field
    pub inner: NestedError,
}

impl fmt::Display for StructCheckError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "check failed for struct member {}: {}",
            self.field_name, self.inner
        )
    }
}

#[cfg(feature = "std")]
impl Error for StructCheckError {}

/// An error resulting from an invalid tuple struct.
#[derive(Debug)]
pub struct TupleStructCheckError {
    /// The index of the struct field that was invalid
    pub field_index: usize,
    /// The error that occurred while validating the field
    pub inner: NestedError,
}

impl fmt::Display for TupleStructCheckError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "check failed for tuple struct member {}: {}",
            self.field_index, self.inner
        )
    }
}

#[cfg(feature = "std")]
impl Error for TupleStructCheckError {}

/// An error resulting from an invalid enum.
#[derive(Debug)]
pub enum EnumCheckError<T> {
    /// A struct variant was invalid
    InvalidStruct {
        /// The name of the variant that was invalid
        variant_name: &'static str,
        /// The error that occurred while validating the variant
        inner: StructCheckError,
    },
    /// A tuple variant was invalid
    InvalidTuple {
        /// The name of the variant that was invalid
        variant_name: &'static str,
        /// The error that occurred while validating the variant
        inner: TupleStructCheckError,
    },
    /// The enum tag was invalid
    InvalidTag(
        /// The invalid value of the tag
        T,
    ),
}

impl<T: fmt::Display> fmt::Display for EnumCheckError<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EnumCheckError::InvalidStruct {
                variant_name,
                inner,
            } => write!(
                f,
                "check failed for enum struct variant {}: {}",
                variant_name, inner
            ),
            EnumCheckError::InvalidTuple {
                variant_name,
                inner,
            } => write!(
                f,
                "check failed for enum tuple variant {}: {}",
                variant_name, inner
            ),
            EnumCheckError::InvalidTag(tag) => write!(f, "invalid tag for enum: {}", tag),
        }
    }
}

#[cfg(feature = "std")]
impl<T: fmt::Debug + fmt::Display> Error for EnumCheckError<T> {}

// Range types
impl<T: CheckBytes<C>, C: ?Sized> CheckBytes<C> for ops::Range<T> {
    type Error = StructCheckError;

    #[inline]
    unsafe fn check_bytes<'a>(value: *const Self, context: &mut C) -> Result<&'a Self, Self::Error> {
        let bytes = value.cast::<u8>();
        T::check_bytes(bytes.add(offset_of!(Self, start)).cast(), context).map_err(|error| {
            StructCheckError {
                field_name: "start",
                inner: handle_error(error),
            }
        })?;
        T::check_bytes(bytes.add(offset_of!(Self, end)).cast(), context).map_err(|error| {
            StructCheckError {
                field_name: "end",
                inner: handle_error(error),
            }
        })?;
        Ok(&*value)
    }
}

impl<T: CheckBytes<C>, C: ?Sized> CheckBytes<C> for ops::RangeFrom<T> {
    type Error = StructCheckError;

    #[inline]
    unsafe fn check_bytes<'a>(value: *const Self, context: &mut C) -> Result<&'a Self, Self::Error> {
        let bytes = value.cast::<u8>();
        T::check_bytes(bytes.add(offset_of!(Self, start)).cast(), context).map_err(|error| {
            StructCheckError {
                field_name: "start",
                inner: handle_error(error),
            }
        })?;
        Ok(&*bytes.cast())
    }
}

impl<C: ?Sized> CheckBytes<C> for ops::RangeFull {
    type Error = Unreachable;

    #[inline]
    unsafe fn check_bytes<'a>(value: *const Self, _: &mut C) -> Result<&'a Self, Self::Error> {
        Ok(&*value)
    }
}

impl<T: CheckBytes<C>, C: ?Sized> CheckBytes<C> for ops::RangeTo<T> {
    type Error = StructCheckError;

    #[inline]
    unsafe fn check_bytes<'a>(value: *const Self, context: &mut C) -> Result<&'a Self, Self::Error> {
        let bytes = value.cast::<u8>();
        T::check_bytes(bytes.add(offset_of!(Self, end)).cast(), context).map_err(|error| {
            StructCheckError {
                field_name: "end",
                inner: handle_error(error),
            }
        })?;
        Ok(&*value)
    }
}

impl<T: CheckBytes<C>, C: ?Sized> CheckBytes<C> for ops::RangeToInclusive<T> {
    type Error = StructCheckError;

    #[inline]
    unsafe fn check_bytes<'a>(value: *const Self, context: &mut C) -> Result<&'a Self, Self::Error> {
        let bytes = value.cast::<u8>();
        T::check_bytes(bytes.add(offset_of!(Self, end)).cast(), context).map_err(|error| {
            StructCheckError {
                field_name: "end",
                inner: handle_error(error),
            }
        })?;
        Ok(&*value)
    }
}

/// An error resulting from an invalid `NonZero` integer.
#[derive(Debug)]
pub enum NonZeroCheckError {
    /// The integer was zero
    IsZero,
}

impl From<Unreachable> for NonZeroCheckError {
    #[inline]
    fn from(_: Unreachable) -> Self {
        unsafe { core::hint::unreachable_unchecked() }
    }
}

impl fmt::Display for NonZeroCheckError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NonZeroCheckError::IsZero => write!(f, "nonzero integer is zero"),
        }
    }
}

#[cfg(feature = "std")]
impl Error for NonZeroCheckError {}

macro_rules! impl_nonzero {
    ($nonzero:ident, $underlying:ident) => {
        impl<C: ?Sized> CheckBytes<C> for $nonzero {
            type Error = NonZeroCheckError;

            #[inline]
            unsafe fn check_bytes<'a>(
                value: *const Self,
                context: &mut C,
            ) -> Result<&'a Self, Self::Error> {
                if *$underlying::check_bytes(value.cast(), context)? == 0 {
                    Err(NonZeroCheckError::IsZero)
                } else {
                    Ok(&*value)
                }
            }
        }
    };
}

impl_nonzero!(NonZeroI8, i8);
impl_nonzero!(NonZeroI16, i16);
impl_nonzero!(NonZeroI32, i32);
impl_nonzero!(NonZeroI64, i64);
impl_nonzero!(NonZeroI128, i128);
impl_nonzero!(NonZeroU8, u8);
impl_nonzero!(NonZeroU16, u16);
impl_nonzero!(NonZeroU32, u32);
impl_nonzero!(NonZeroU64, u64);
impl_nonzero!(NonZeroU128, u128);
