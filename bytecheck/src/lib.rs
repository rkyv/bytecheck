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
//!         &[
//!             0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8,
//!             1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8,
//!         &mut ()
//!     ).unwrap();
//!
//!     // Changing the bytes for the u32 is OK, any bytes are a valid u32
//!     Test::check_bytes(
//!         &[
//!             42u8, 16u8, 20u8, 3u8, 0x78u8, 0u8, 0u8, 0u8,
//!             1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8,
//!         &mut ()
//!     ).unwrap();
//!
//!     // Characters outside the valid ranges are invalid
//!     Test::check_bytes(
//!         &[
//!             0u8, 0u8, 0u8, 0u8, 0x00u8, 0xd8u8, 0u8, 0u8,
//!             1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8,
//!         &mut ()
//!     ).unwrap_err();
//!     Test::check_bytes(
//!         &[
//!             0u8, 0u8, 0u8, 0u8, 0x00u8, 0x00u8, 0x11u8, 0u8,
//!             1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8,
//!         &mut ()
//!     ).unwrap_err();
//!
//!     // 0 is a valid boolean value (false) but 2 is not
//!     Test::check_bytes(
//!         &[
//!             0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8,
//!             0u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8,
//!         &mut ()
//!     ).unwrap();
//!     Test::check_bytes(
//!         &[
//!             0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8,
//!             2u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8
//!         ] as *const u8,
//!         &mut ()
//!     ).unwrap_err();
//! }
//! ```
//!
//! ## Features
//!
//! - `const_generics`: Extends the implementations of [`CheckBytes`] to all
//! arrays and not just arrays up to length 32.

#![cfg_attr(feature = "const_generics", feature(const_generics))]
#![cfg_attr(feature = "const_generics", allow(incomplete_features))]

use core::{convert::TryFrom, fmt, mem};
use std::error::Error;

pub use bytecheck_derive::CheckBytes;
pub use memoffset::offset_of;

/// A type that can validate whether some bytes represent a valid value.
///
/// `CheckBytes` can be derived with [`CheckBytes`](macro@CheckBytes) or
/// implemented manually for custom behavior.
pub trait CheckBytes<C> {
    /// The error that may result from validating the type.
    type Error: Error + 'static;

    /// Checks whether the given bytes represent a valid value within the given
    /// context.
    ///
    /// # Safety
    ///
    /// The passed pointer must be aligned and point to enough bytes to
    /// represent the type.
    unsafe fn check_bytes<'a>(bytes: *const u8, context: &mut C) -> Result<&'a Self, Self::Error>;
}

/// An error that cannot be produced.
///
/// This is used primarily for primitive types that do not have invalid values
/// such as integers and floats.
#[derive(Debug)]
pub enum Unreachable {}

impl fmt::Display for Unreachable {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unreachable!();
    }
}

impl Error for Unreachable {}

macro_rules! impl_primitive {
    ($type:ty) => {
        impl<C> CheckBytes<C> for $type {
            type Error = Unreachable;

            unsafe fn check_bytes<'a>(
                bytes: *const u8,
                _context: &mut C,
            ) -> Result<&'a Self, Self::Error> {
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
        write!(
            f,
            "check failed for bool: expected 0 or 1, found {}",
            self.invalid_value
        )
    }
}

impl Error for BoolCheckError {}

impl<C> CheckBytes<C> for bool {
    type Error = BoolCheckError;

    unsafe fn check_bytes<'a>(bytes: *const u8, _context: &mut C) -> Result<&'a Self, Self::Error> {
        let byte = *bytes;
        match byte {
            0 | 1 => Ok(&*bytes.cast::<Self>()),
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

impl fmt::Display for CharCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "check failed for char: invalid value {}",
            self.invalid_value
        )
    }
}

impl Error for CharCheckError {}

impl<C> CheckBytes<C> for char {
    type Error = CharCheckError;

    unsafe fn check_bytes<'a>(bytes: *const u8, _context: &mut C) -> Result<&'a Self, Self::Error> {
        let value = *bytes.cast::<u32>();
        char::try_from(value).map_err(|_| CharCheckError {
            invalid_value: value,
        })?;
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
                const SIZE: usize = [$($index,)+].len();
                match self {
                    $($error::$type(e) => write!(f, "check failed for {}-tuple index {}: {}", SIZE, SIZE - $index - 1, e),)+
                }
            }
        }

        impl<$($type: fmt::Display + fmt::Debug),*> Error for $error<$($type),+> {}

        impl<$($type: CheckBytes<C>,)+ C> CheckBytes<C> for ($($type,)+) {
            type Error = $error<$($type::Error),+>;

            #[allow(clippy::unneeded_wildcard_pattern)]
            unsafe fn check_bytes<'a>(bytes: *const u8, context: &mut C) -> Result<&'a Self, Self::Error> {
                $($type::check_bytes(bytes.add(memoffset::offset_of_tuple!(Self, $index)), context).map_err($error::$type)?;)+
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
        write!(
            f,
            "check failed for array index {}: {}",
            self.index, self.error
        )
    }
}

impl<T: fmt::Debug + fmt::Display> Error for ArrayCheckError<T> {}

#[cfg(not(feature = "const_generics"))]
macro_rules! impl_array {
    () => {};
    ($len:expr, $($rest:expr,)*) => {
        impl<T: CheckBytes<C>, C> CheckBytes<C> for [T; $len] {
            type Error = ArrayCheckError<T::Error>;

            unsafe fn check_bytes<'a>(bytes: *const u8, context: &mut C) -> Result<&'a Self, Self::Error> {
                #[allow(clippy::reversed_empty_ranges)]
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
impl<T: CheckBytes<C>, C, const N: usize> CheckBytes<C> for [T; N] {
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
pub struct StructCheckError {
    /// The name of the struct field that was invalid
    pub field_name: &'static str,
    /// The error that occurred while validating the field
    pub inner: Box<dyn Error>,
}

impl fmt::Display for StructCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "check failed for struct member {}: {}",
            self.field_name, self.inner
        )
    }
}

impl Error for StructCheckError {}

/// An error resulting from an invalid tuple struct.
#[derive(Debug)]
pub struct TupleStructCheckError {
    /// The index of the struct field that was invalid
    pub field_index: usize,
    /// The error that occurred while validating the field
    pub inner: Box<dyn Error>,
}

impl fmt::Display for TupleStructCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "check failed for tuple struct member {}: {}",
            self.field_index, self.inner
        )
    }
}

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

impl<T: fmt::Debug + fmt::Display> Error for EnumCheckError<T> {}
