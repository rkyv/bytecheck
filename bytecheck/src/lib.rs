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

pub trait Context<T: ?Sized> {
    fn provide(&self) -> &T;
}

impl<T> Context<()> for T {
    fn provide(&self) -> &() {
        &()
    }
}

pub trait CheckBytes<C: Context<Self::Context>> {
    type Context;
    type Error: fmt::Debug + fmt::Display;

    // safety: pointer must be aligned and point to enough bytes for the type
    unsafe fn check_bytes<'a>(bytes: *const u8, context: &C) -> Result<&'a Self, Self::Error>;
}

#[derive(Debug)]
pub enum CheckBufferError<T> {
    Overrun,
    Unaligned,
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

#[derive(Debug)]
pub struct BoolCheckError {
    invalid_value: u8,
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

impl<C> CheckBytes<C> for char {
    type Context = ();
    type Error = core::char::CharTryFromError;

    unsafe fn check_bytes<'a>(bytes: *const u8, _context: &C) -> Result<&'a Self, Self::Error> {
        let value = *bytes.cast::<u32>();
        char::try_from(value)?;
        Ok(&*bytes.cast::<Self>())
    }
}

macro_rules! peel_tuple {
    ([$($error_rest:ident,)*], [$type:ident $index:tt, $($type_rest:ident $index_rest:tt,)*]) => { impl_tuple! { [$($error_rest,)*], [$($type_rest $index_rest,)*] } };
}

macro_rules! impl_tuple {
    ([], []) => {};
    ([$error:ident, $($error_rest:ident,)*], [$($type:ident $index:tt,)+]) => {
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

#[derive(Debug)]
pub struct ArrayCheckError<T> {
    pub index: usize,
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

#[derive(Debug)]
pub struct StructCheckError<T> {
    pub field_name: &'static str,
    pub inner: T,
}

impl<T: fmt::Display> fmt::Display for StructCheckError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "check failed for struct member {}: {}", self.field_name, self.inner)
    }
}

#[cfg(feature = "std")]
impl<T: fmt::Debug + fmt::Display> error::Error for StructCheckError<T> {}

#[derive(Debug)]
pub struct TupleStructCheckError<T> {
    pub field_index: usize,
    pub inner: T,
}

impl<T: fmt::Display> fmt::Display for TupleStructCheckError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "check failed for tuple struct member {}: {}", self.field_index, self.inner)
    }
}

#[cfg(feature = "std")]
impl<T: fmt::Debug + fmt::Display> error::Error for TupleStructCheckError<T> {}

#[derive(Debug)]
pub enum EnumCheckError<T, U> {
    InvalidStruct {
        variant_name: &'static str,
        inner: StructCheckError<T>,
    },
    InvalidTuple {
        variant_name: &'static str,
        inner: TupleStructCheckError<T>,
    },
    InvalidTag(U),
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
#[cfg(feature = "std")]
pub type DefaultError = Box<dyn std::error::Error>;
