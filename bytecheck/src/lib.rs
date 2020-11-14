//! # bytecheck
//!
//! bytecheck is a type validation framework for Rust.
//!
//! For some types, creating an invalid value immediately results in
//! undefined behavior. This can cause some issues when trying to validate
//! potentially invalid bytes, as just casting the bytes to your type can
//! technically cause errors. This makes it difficult to write validation
//! routines, because until you're certain that the bytes represent valid
//! values you cannot cast them.
//!
//! bytecheck provides a framework for performing these byte-level
//! validations and implements checks for basic types along with a derive
//! macro to implement validation for custom structs and enums.
//!
//! ## Design
//!
//! There are two traits at the core of bytecheck, [`Context`](trait@Context) and
//! [`CheckBytes`]. [`CheckBytes`] does the heavy lifting of verifying
//! that some bytes represent a valid type, whereas [`Context`] provides
//! any contextual information that may be needed to properly do so. For
//! core types no context is required, but for more complex and custom
//! types there may be context needed to properly validate bytes.
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
//!         &[
//!             0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8,
//!             1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8,
//!         &()
//!     ).unwrap();
//!
//!     // Changing the bytes for the u32 is OK, any bytes are a valid u32
//!     Test::check_bytes(
//!         &[
//!             42u8, 16u8, 20u8, 3u8, 0x78u8, 0u8, 0u8, 0u8,
//!             1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8,
//!         &()
//!     ).unwrap();
//!
//!     // Characters outside the valid ranges are invalid
//!     Test::check_bytes(
//!         &[
//!             0u8, 0u8, 0u8, 0u8, 0x00u8, 0xd8u8, 0u8, 0u8,
//!             1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8,
//!         &()
//!     ).unwrap_err();
//!     Test::check_bytes(
//!         &[
//!             0u8, 0u8, 0u8, 0u8, 0x00u8, 0x00u8, 0x11u8, 0u8,
//!             1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8,
//!         &()
//!     ).unwrap_err();
//!
//!     // 0 is a valid boolean value (false) but 2 is not
//!     Test::check_bytes(
//!         &[
//!             0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8,
//!             0u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8,
//!         &()
//!     ).unwrap();
//!     Test::check_bytes(
//!         &[
//!             0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8,
//!             2u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8,
//!         &()
//!     ).unwrap_err();
//! }
//! ```
//!
//! ## Features
//!
//! - `const_generics`: Extends the implementations of [`CheckBytes`] to
//! to all arrays and not just arrays up to length 32.
//! - `silent`: Silently consumes nested errors in `#![no_std]` instead of
//! printing them to stderr.
//! - `std`: Enables standard library support.
//!
//! By default, the `std` feature is enabled.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "const_generics", feature(const_generics))]
#![cfg_attr(feature = "const_generics", allow(incomplete_features))]

use core::{
    convert::TryFrom,
    fmt,
    mem,
};
#[cfg(feature = "std")]
use std::error;

pub use memoffset::offset_of;
pub use bytecheck_derive::CheckBytes;

/// A context that can provide some typed context for validating types.
pub trait Context<T: ?Sized> {
    /// Provides some context for validation.
    fn provide(&self) -> &T;
}

impl<T> Context<()> for T {
    fn provide(&self) -> &() {
        &()
    }
}

/// A type that can validate whether some bytes represent a valid value.
///
/// `CheckBytes` can be derived with [`CheckBytes`](macro@CheckBytes) or
/// implemented manually for custom behavior.
pub trait CheckBytes<C: Context<Self::Context>> {
    /// The type that given contexts must be able to provide for
    /// validation.
    type Context;

    /// The error that may result from validating the type.
    type Error: fmt::Debug + fmt::Display;

    /// Checks whether the given bytes represent a valid value within the
    /// given context.
    ///
    /// # Safety
    /// The passed pointer must be aligned and point to enough bytes to
    /// represent the type. Instead of calling `check_bytes` directly, top
    /// level consumers should call [`check_buffer`] which validates these
    /// constraints.
    unsafe fn check_bytes<'a>(bytes: *const u8, context: &C) -> Result<&'a Self, Self::Error>;
}

/// An error resulting from an invalid buffer.
#[derive(Debug)]
pub enum CheckBufferError<T> {
    /// The buffer does not have enough bytes to represent the given type
    /// at the given offset.
    Overrun,
    /// The address of the position in the buffer is not properly aligned
    /// to represent the given type.
    Unaligned,
    /// The buffer checks passed but there was an error validating the
    /// bytes of the type.
    CheckBytes(T),
}

impl<T: fmt::Display> fmt::Display for CheckBufferError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Overrun => write!(f, "buffer check failed: struct overrun"),
            Self::Unaligned => write!(f, "buffer check failed: data unaligned"),
            Self::CheckBytes(e) => e.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl<T: fmt::Debug + fmt::Display> error::Error for CheckBufferError<T> {}

/// Checks whether a valid value of the given type is located in the given
/// buffer at the given position.
pub fn check_buffer<'a, T: CheckBytes<C>, C: Context<T::Context>>(buf: &'a [u8], pos: usize, context: &C) -> Result<&'a T, CheckBufferError<T::Error>> {
    if pos > buf.len() || buf.len() - pos < mem::size_of::<T>() {
        Err(CheckBufferError::Overrun)
    } else {
        let ptr = unsafe { buf.as_ptr().add(pos) };
        if ptr as usize & (mem::align_of::<T>() - 1) != 0 {
            Err(CheckBufferError::Unaligned)
        } else {
            let result = unsafe { T::check_bytes(ptr, context) };
            Ok(result.map_err(|e| CheckBufferError::CheckBytes(e))?)
        }
    }
}

/// An error that cannot be produced.
///
/// This is used primarily for primitive types that do not have invalid
/// values such as integers and floats.
#[derive(Debug)]
pub enum Unreachable {}

impl fmt::Display for Unreachable {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unreachable!();
    }
}

#[cfg(feature = "std")]
impl error::Error for Unreachable {}

macro_rules! impl_primitive {
    ($type:ty) => {
        impl<C> CheckBytes<C> for $type {
            type Context = ();
            type Error = Unreachable;

            unsafe fn check_bytes<'a>(bytes: *const u8, _context: &C) -> Result<&'a Self, Self::Error> {
                Ok(&*bytes.cast::<Self>())
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

/// An error resulting from an invalid boolean.
///
/// Booleans are one byte and may only have the value 0 or 1.
#[derive(Debug)]
pub struct BoolCheckError {
    /// The byte value of the invalid boolean
    pub invalid_value: u8,
}

impl fmt::Display for BoolCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "check failed for bool: expected 0 or 1, found {}", self.invalid_value)
    }
}

#[cfg(feature = "std")]
impl error::Error for BoolCheckError {}

impl<C> CheckBytes<C> for bool {
    type Context = ();
    type Error = BoolCheckError;

    unsafe fn check_bytes<'a>(bytes: *const u8, _context: &C) -> Result<&'a Self, Self::Error> {
        let byte = *bytes;
        match byte {
            0 | 1 => Ok(&*bytes.cast::<Self>()),
            _ => Err(BoolCheckError { invalid_value: byte }),
        }
    }
}

/// An error resulting from an invalid character.
///
/// Characters are four bytes and may only have values from `0x0` to
// `0xD7FF` and `0xE000` to `0x10FFFF` inclusive.
#[derive(Debug)]
pub struct CharCheckError {
    /// The `u32` value of the invalid character
    pub invalid_value: u32,
}

impl fmt::Display for CharCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "check failed for char: invalid value {}", self.invalid_value)
    }
}

#[cfg(feature = "std")]
impl error::Error for CharCheckError {}

impl<C> CheckBytes<C> for char {
    type Context = ();
    type Error = CharCheckError;

    unsafe fn check_bytes<'a>(bytes: *const u8, _context: &C) -> Result<&'a Self, Self::Error> {
        let value = *bytes.cast::<u32>();
        char::try_from(value).map_err(|_| CharCheckError { invalid_value: value })?;
        Ok(&*bytes.cast::<Self>())
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
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self {
                    $($error::$type(e) => write!(f, "check failed for tuple index {}: {}", $index, e),)+
                }
            }
        }

        impl<$($type: CheckBytes<C>,)+ C> CheckBytes<C> for ($($type,)+)
        where
            $(C: Context<$type::Context>,)+
        {
            type Context = ();
            type Error = $error<$($type::Error),+>;

            #[allow(clippy::unneeded_wildcard_pattern)]
            unsafe fn check_bytes<'a>(bytes: *const u8, context: &C) -> Result<&'a Self, Self::Error> {
                $($type::check_bytes(bytes.add(memoffset::offset_of_tuple!(Self, $index)), &context).map_err(|e| $error::$type(e))?;)+
                Ok(&*bytes.cast::<Self>())
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "check failed for array index {}: {}", self.index, self.error)
    }
}

#[cfg(feature = "std")]
impl<T: fmt::Debug + fmt::Display> error::Error for ArrayCheckError<T> {}

#[cfg(not(feature = "const_generics"))]
macro_rules! impl_array {
    () => {};
    ($len:expr, $($rest:expr,)*) => {
        impl<T: CheckBytes<C>, C: Context<T::Context>> CheckBytes<C> for [T; $len] {
            type Context = ();
            type Error = ArrayCheckError<T::Error>;

            unsafe fn check_bytes<'a>(bytes: *const u8, context: &C) -> Result<&'a Self, Self::Error> {
                for index in 0..$len {
                    let el_bytes = bytes.add(index * mem::size_of::<T>());
                    T::check_bytes(el_bytes, context).map_err(|error| ArrayCheckError { index, error })?;
                }
                Ok(&*bytes.cast::<Self>())
            }
        }

        impl_array! { $($rest,)* }
    };
}

#[cfg(not(feature = "const_generics"))]
impl_array! { 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, }

#[cfg(feature = "const_generics")]
impl<T: CheckBytes<C>, C: Context<T::Context>, const N: usize> CheckBytes<C> for [T; N] {
    type Context = ();
    type Error = ArrayCheckError<T::Error>;

    unsafe fn check_bytes<'a>(bytes: *const u8, context: &C) -> Result<&'a Self, Self::Error> {
        for index in 0..N {
            let el_bytes = bytes.add(index * mem::size_of::<T>());
            T::check_bytes(el_bytes, context).map_err(|error| ArrayCheckError { index, error })?;
        }
        Ok(&*bytes.cast::<Self>())
    }
}

/// An error resulting from an invalid struct.
#[derive(Debug)]
pub struct StructCheckError<T> {
    /// The name of the struct field that was invalid
    pub field_name: &'static str,
    /// The error that occurred while validating the field
    pub inner: T,
}

impl<T: fmt::Display> fmt::Display for StructCheckError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "check failed for struct member {}: {}", self.field_name, self.inner)
    }
}

#[cfg(feature = "std")]
impl<T: fmt::Debug + fmt::Display> error::Error for StructCheckError<T> {}

/// An error resulting from an invalid tuple struct.
#[derive(Debug)]
pub struct TupleStructCheckError<T> {
    /// The index of the struct field that was invalid
    pub field_index: usize,
    /// The error that occurred while validating the field
    pub inner: T,
}

impl<T: fmt::Display> fmt::Display for TupleStructCheckError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "check failed for tuple struct member {}: {}", self.field_index, self.inner)
    }
}

#[cfg(feature = "std")]
impl<T: fmt::Debug + fmt::Display> error::Error for TupleStructCheckError<T> {}

/// An error resulting from an invalid enum.
#[derive(Debug)]
pub enum EnumCheckError<T, U> {
    /// A struct variant was invalid
    InvalidStruct {
        /// The name of the variant that was invalid
        variant_name: &'static str,
        /// The error that occurred while validating the variant
        inner: StructCheckError<T>,
    },
    /// A tuple variant was invalid
    InvalidTuple {
        /// The name of the variant that was invalid
        variant_name: &'static str,
        /// The error that occurred while validating the variant
        inner: TupleStructCheckError<T>,
    },
    /// The enum tag was invalid
    InvalidTag(
        /// The invalid value of the tag
        U
    ),
}

impl<T: fmt::Display, U: fmt::Display> fmt::Display for EnumCheckError<T, U> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EnumCheckError::InvalidStruct { variant_name, inner } => write!(f, "check failed for enum struct variant {}: {}", variant_name, inner),
            EnumCheckError::InvalidTuple { variant_name, inner } => write!(f, "check failed for enum tuple variant {}: {}", variant_name, inner),
            EnumCheckError::InvalidTag(tag) => write!(f, "invalid tag for enum: {}", tag),
        }
    }
}

#[cfg(feature = "std")]
impl<T: fmt::Debug + fmt::Display, U: fmt::Debug + fmt::Display> error::Error for EnumCheckError<T, U> {}

/// An error that consumes source errors and may log to stderr.
pub struct ErrorSink;

#[cfg(not(feature = "silent"))]
impl<T: fmt::Debug> From<T> for ErrorSink {
    fn from(error: T) -> Self {
        eprintln!("error: {:?}", error);
        Self
    }
}

#[cfg(feature = "silent")]
impl<T: fmt::Debug> From<T> for ErrorSink {
    fn from(error: T) -> Self {
        Self
    }
}

#[cfg(not(feature = "std"))]
pub type DefaultError = ErrorSink;

/// The default error type that must be convertible from all other error
/// types.
///
/// In `#![no_std]` builds, this defaults to [`ErrorSink`].
#[cfg(feature = "std")]
pub type DefaultError = Box<dyn std::error::Error>;
