//! # bytecheck
//!
//! bytecheck is a memory validation framework for Rust.
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
//! ## Layout stability
//!
//! The layouts of types may change between compiler versions, or even different
//! compilations. To guarantee stable type layout between compilations, structs,
//! enums, and unions can be annotated with `#[repr(C)]`, and enums specifically
//! can be annotated with `#[repr(int)]` or `#[repr(C, int)]` as well. See
//! [the reference's page on type layout][reference] for more details.
//!
//! [reference]: https://doc.rust-lang.org/reference/type-layout.html
//!
//! ## Features
//!
//! - `derive`: Re-exports the macros from `bytecheck_derive`. Enabled by
//!   default.
//! - `simdutf8`: Uses the `simdutf8` crate to validate UTF-8 strings. Enabled
//!   by default.
//!
//! ### Crates
//!
//! Bytecheck provides integrations for some common crates by default. In the
//! future, crates should depend on bytecheck and provide their own integration.
//!
//! - [`uuid`](https://docs.rs/uuid)
//!
//! ## Example
#![doc = include_str!("../example.md")]
#![deny(
    future_incompatible,
    missing_docs,
    nonstandard_style,
    unsafe_op_in_unsafe_fn,
    unused,
    warnings,
    clippy::all,
    clippy::missing_safety_doc,
    clippy::undocumented_unsafe_blocks,
    rustdoc::broken_intra_doc_links,
    rustdoc::missing_crate_level_docs
)]
#![no_std]
#![cfg_attr(all(docsrs, not(doctest)), feature(doc_cfg, doc_auto_cfg))]

// Support for various common crates. These are primarily to get users off the
// ground and build some momentum.

// These are NOT PLANNED to remain in bytecheck for the final release. Much like
// serde, these implementations should be moved into their respective crates
// over time. Before adding support for another crate, please consider getting
// bytecheck support in the crate instead.

#[cfg(feature = "uuid")]
mod uuid;

#[cfg(not(feature = "simdutf8"))]
use core::str::from_utf8;
#[cfg(target_has_atomic = "8")]
use core::sync::atomic::{AtomicBool, AtomicI8, AtomicU8};
#[cfg(target_has_atomic = "16")]
use core::sync::atomic::{AtomicI16, AtomicU16};
#[cfg(target_has_atomic = "32")]
use core::sync::atomic::{AtomicI32, AtomicU32};
#[cfg(target_has_atomic = "64")]
use core::sync::atomic::{AtomicI64, AtomicU64};
use core::{
    cell::{Cell, UnsafeCell},
    error::Error,
    ffi::CStr,
    fmt,
    marker::{PhantomData, PhantomPinned},
    mem::ManuallyDrop,
    num::{
        NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8,
        NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8,
    },
    ops, ptr,
};

pub use bytecheck_derive::CheckBytes;
pub use rancor;
use rancor::{fail, Fallible, ResultExt as _, Source, Strategy, Trace};
#[cfg(feature = "simdutf8")]
use simdutf8::basic::from_utf8;

/// A type that can check whether a pointer points to a valid value.
///
/// `CheckBytes` can be derived with [`CheckBytes`](macro@CheckBytes) or
/// implemented manually for custom behavior.
///
/// # Safety
///
/// `check_bytes` must only return `Ok` if `value` points to a valid instance of
/// `Self`. Because `value` must always be properly aligned for `Self` and point
/// to enough bytes to represent the type, this implies that `value` may be
/// dereferenced safely.
pub unsafe trait CheckBytes<C: Fallible + ?Sized> {
    /// Checks whether the given pointer points to a valid value within the
    /// given context.
    ///
    /// # Safety
    ///
    /// The passed pointer must be aligned and point to enough initialized bytes
    /// to represent the type.
    unsafe fn check_bytes(
        value: *const Self,
        context: &mut C,
    ) -> Result<(), C::Error>;
}

/// A type that can check whether its invariants are upheld.
///
/// # Safety
///
/// - `verify` must only return `Ok` if all of the invariants of this type are
///   upheld by `self`.
/// - `verify` may not assume that its type invariants are upheld by the given
///   `self.`
pub unsafe trait Verify<C: Fallible + ?Sized> {
    /// Checks whether the invariants of this type are upheld by `self`.
    fn verify(&self, context: &mut C) -> Result<(), C::Error>;
}

/// Checks whether the given pointer points to a valid value.
///
/// # Safety
///
/// The passed pointer must be aligned and point to enough initialized bytes to
/// represent the type.
#[inline]
pub unsafe fn check_bytes<T, E>(value: *const T) -> Result<(), E>
where
    T: CheckBytes<Strategy<(), E>> + ?Sized,
{
    // SAFETY: The safety conditions of `check_bytes_with_context` are the same
    // as the safety conditions of this function.
    unsafe { check_bytes_with_context(value, &mut ()) }
}

/// Checks whether the given pointer points to a valid value within the given
/// context.
///
/// # Safety
///
/// The passed pointer must be aligned and point to enough initialized bytes to
/// represent the type.
pub unsafe fn check_bytes_with_context<T, C, E>(
    value: *const T,
    context: &mut C,
) -> Result<(), E>
where
    T: CheckBytes<Strategy<C, E>> + ?Sized,
{
    // SAFETY: The safety conditions of `check_bytes` are the same as the safety
    // conditions of this function.
    unsafe { CheckBytes::check_bytes(value, Strategy::wrap(context)) }
}

macro_rules! impl_primitive {
    ($type:ty) => {
        // SAFETY: All bit patterns are valid for these primitive types.
        unsafe impl<C: Fallible + ?Sized> CheckBytes<C> for $type {
            #[inline]
            unsafe fn check_bytes(
                _: *const Self,
                _: &mut C,
            ) -> Result<(), C::Error> {
                Ok(())
            }
        }
    };
}

macro_rules! impl_primitives {
    ($($type:ty),* $(,)?) => {
        $(
            impl_primitive!($type);
        )*
    }
}

impl_primitives! {
    (),
    i8, i16, i32, i64, i128,
    u8, u16, u32, u64, u128,
    f32, f64,
}
#[cfg(target_has_atomic = "8")]
impl_primitives!(AtomicI8, AtomicU8);
#[cfg(target_has_atomic = "16")]
impl_primitives!(AtomicI16, AtomicU16);
#[cfg(target_has_atomic = "32")]
impl_primitives!(AtomicI32, AtomicU32);
#[cfg(target_has_atomic = "64")]
impl_primitives!(AtomicI64, AtomicU64);

// SAFETY: `PhantomData` is a zero-sized type and so all bit patterns are valid.
unsafe impl<T: ?Sized, C: Fallible + ?Sized> CheckBytes<C> for PhantomData<T> {
    #[inline]
    unsafe fn check_bytes(_: *const Self, _: &mut C) -> Result<(), C::Error> {
        Ok(())
    }
}

// SAFETY: `PhantomPinned` is a zero-sized type and so all bit patterns are
// valid.
unsafe impl<C: Fallible + ?Sized> CheckBytes<C> for PhantomPinned {
    #[inline]
    unsafe fn check_bytes(_: *const Self, _: &mut C) -> Result<(), C::Error> {
        Ok(())
    }
}

// SAFETY: `ManuallyDrop<T>` is a `#[repr(transparent)]` wrapper around a `T`,
// and so `value` points to a valid `ManuallyDrop<T>` if it also points to a
// valid `T`.
unsafe impl<T, C> CheckBytes<C> for ManuallyDrop<T>
where
    T: CheckBytes<C> + ?Sized,
    C: Fallible + ?Sized,
    C::Error: Trace,
{
    #[inline]
    unsafe fn check_bytes(
        value: *const Self,
        c: &mut C,
    ) -> Result<(), C::Error> {
        // SAFETY: Because `ManuallyDrop<T>` is `#[repr(transparent)]`, a
        // pointer to a `ManuallyDrop<T>` is guaranteed to be the same as a
        // pointer to `T`. We can't call `.cast()` here because `T` may be
        // an unsized type.
        let inner_ptr =
            unsafe { core::mem::transmute::<*const Self, *const T>(value) };
        // SAFETY: The caller has guaranteed that `value` is aligned for
        // `ManuallyDrop<T>` and points to enough bytes to represent
        // `ManuallyDrop<T>`. Since `ManuallyDrop<T>` is `#[repr(transparent)]`,
        // `inner_ptr` is also aligned for `T` and points to enough bytes to
        // represent it.
        unsafe {
            T::check_bytes(inner_ptr, c)
                .trace("while checking inner value of `ManuallyDrop`")
        }
    }
}

// SAFETY: `UnsafeCell<T>` has the same memory layout as `T`, and so `value`
// points to a valid `UnsafeCell<T>` if it also points to a valid `T`.
unsafe impl<T, C> CheckBytes<C> for UnsafeCell<T>
where
    T: CheckBytes<C> + ?Sized,
    C: Fallible + ?Sized,
    C::Error: Trace,
{
    #[inline]
    unsafe fn check_bytes(
        value: *const Self,
        c: &mut C,
    ) -> Result<(), C::Error> {
        // SAFETY: Because `UnsafeCell<T>` has the same memory layout as
        // `T`, a pointer to an `UnsafeCell<T>` is guaranteed to be the same
        // as a pointer to `T`. We can't call `.cast()` here because `T` may
        // be an unsized type.
        let inner_ptr =
            unsafe { core::mem::transmute::<*const Self, *const T>(value) };
        // SAFETY: The caller has guaranteed that `value` is aligned for
        // `UnsafeCell<T>` and points to enough bytes to represent
        // `UnsafeCell<T>`. Since `UnsafeCell<T>` has the same layout `T`,
        // `inner_ptr` is also aligned for `T` and points to enough bytes to
        // represent it.
        unsafe {
            T::check_bytes(inner_ptr, c)
                .trace("while checking inner value of `UnsafeCell`")
        }
    }
}

// SAFETY: `Cell<T>` has the same memory layout as `UnsafeCell<T>` (and
// therefore `T` itself), and so `value` points to a valid `UnsafeCell<T>` if it
// also points to a valid `T`.
unsafe impl<T, C> CheckBytes<C> for Cell<T>
where
    T: CheckBytes<C> + ?Sized,
    C: Fallible + ?Sized,
    C::Error: Trace,
{
    #[inline]
    unsafe fn check_bytes(
        value: *const Self,
        c: &mut C,
    ) -> Result<(), C::Error> {
        // SAFETY: Because `Cell<T>` has the same memory layout as
        // `UnsafeCell<T>` (and therefore `T` itself), a pointer to a
        // `Cell<T>` is guaranteed to be the same as a pointer to `T`. We
        // can't call `.cast()` here because `T` may be an unsized type.
        let inner_ptr =
            unsafe { core::mem::transmute::<*const Self, *const T>(value) };
        // SAFETY: The caller has guaranteed that `value` is aligned for
        // `Cell<T>` and points to enough bytes to represent `Cell<T>`. Since
        // `Cell<T>` has the same layout as `UnsafeCell<T>` ( and therefore `T`
        // itself), `inner_ptr` is also aligned for `T` and points to enough
        // bytes to represent it.
        unsafe {
            T::check_bytes(inner_ptr, c)
                .trace("while checking inner value of `Cell`")
        }
    }
}

#[derive(Debug)]
struct BoolCheckError {
    byte: u8,
}

impl fmt::Display for BoolCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "bool set to invalid byte {}, expected either 0 or 1",
            self.byte,
        )
    }
}

impl Error for BoolCheckError {}

// SAFETY: A bool is a one byte value that must either be 0 or 1. `check_bytes`
// only returns `Ok` if `value` is 0 or 1.
unsafe impl<C> CheckBytes<C> for bool
where
    C: Fallible + ?Sized,
    C::Error: Source,
{
    #[inline]
    unsafe fn check_bytes(
        value: *const Self,
        _: &mut C,
    ) -> Result<(), C::Error> {
        // SAFETY: `value` is a pointer to a `bool`, which has a size and
        // alignment of one. `u8` also has a size and alignment of one, and all
        // bit patterns are valid for `u8`. So we can cast `value` to a `u8`
        // pointer and read from it.
        let byte = unsafe { *value.cast::<u8>() };
        match byte {
            0 | 1 => Ok(()),
            _ => fail!(BoolCheckError { byte }),
        }
    }
}

#[cfg(target_has_atomic = "8")]
// SAFETY: `AtomicBool` has the same ABI as `bool`, so if `value` points to a
// valid `bool` then it also points to a valid `AtomicBool`.
unsafe impl<C> CheckBytes<C> for AtomicBool
where
    C: Fallible + ?Sized,
    C::Error: Source,
{
    #[inline]
    unsafe fn check_bytes(
        value: *const Self,
        context: &mut C,
    ) -> Result<(), C::Error> {
        // SAFETY: `AtomicBool` has the same ABI as `bool`, so a pointer that is
        // aligned for `AtomicBool` and points to enough bytes for `AtomicBool`
        // is also aligned for `bool` and points to enough bytes for `bool`.
        unsafe { bool::check_bytes(value.cast(), context) }
    }
}

// SAFETY: If `char::try_from` succeeds with the pointed-to-value, then it must
// be a valid value for `char`.
unsafe impl<C> CheckBytes<C> for char
where
    C: Fallible + ?Sized,
    C::Error: Source,
{
    #[inline]
    unsafe fn check_bytes(ptr: *const Self, _: &mut C) -> Result<(), C::Error> {
        // SAFETY: `char` and `u32` are both four bytes, but we're not
        // guaranteed that they have the same alignment. Using `read_unaligned`
        // ensures that we can read a `u32` regardless and try to convert it to
        // a `char`.
        let value = unsafe { ptr.cast::<u32>().read_unaligned() };
        char::try_from(value).into_error()?;
        Ok(())
    }
}

#[derive(Debug)]
struct TupleIndexContext {
    index: usize,
}

impl fmt::Display for TupleIndexContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "while checking index {} of tuple", self.index)
    }
}

macro_rules! impl_tuple {
    ($($type:ident $index:tt),*) => {
        // SAFETY: A tuple is valid if all of its elements are valid, and
        // `check_bytes` only returns `Ok` when all of the elements validated
        // successfully.
        unsafe impl<$($type,)* C> CheckBytes<C> for ($($type,)*)
        where
            $($type: CheckBytes<C>,)*
            C: Fallible + ?Sized,
            C::Error: Trace,
        {
            #[inline]
            #[allow(clippy::unneeded_wildcard_pattern)]
            unsafe fn check_bytes(
                value: *const Self,
                context: &mut C,
            ) -> Result<(), C::Error> {
                $(
                    // SAFETY: The caller has guaranteed that `value` points to
                    // enough bytes for this tuple and is properly aligned, so
                    // we can create pointers to each element and check them.
                    unsafe {
                        <$type>::check_bytes(
                            ptr::addr_of!((*value).$index),
                            context,
                        ).with_trace(|| TupleIndexContext { index: $index })?;
                    }
                )*
                Ok(())
            }
        }
    }
}

impl_tuple!(T0 0);
impl_tuple!(T0 0, T1 1);
impl_tuple!(T0 0, T1 1, T2 2);
impl_tuple!(T0 0, T1 1, T2 2, T3 3);
impl_tuple!(T0 0, T1 1, T2 2, T3 3, T4 4);
impl_tuple!(T0 0, T1 1, T2 2, T3 3, T4 4, T5 5);
impl_tuple!(T0 0, T1 1, T2 2, T3 3, T4 4, T5 5, T6 6);
impl_tuple!(T0 0, T1 1, T2 2, T3 3, T4 4, T5 5, T6 6, T7 7);
impl_tuple!(T0 0, T1 1, T2 2, T3 3, T4 4, T5 5, T6 6, T7 7, T8 8);
impl_tuple!(T0 0, T1 1, T2 2, T3 3, T4 4, T5 5, T6 6, T7 7, T8 8, T9 9);
impl_tuple!(T0 0, T1 1, T2 2, T3 3, T4 4, T5 5, T6 6, T7 7, T8 8, T9 9, T10 10);
impl_tuple!(
    T0 0, T1 1, T2 2, T3 3, T4 4, T5 5, T6 6, T7 7, T8 8, T9 9, T10 10, T11 11
);
impl_tuple!(
    T0 0, T1 1, T2 2, T3 3, T4 4, T5 5, T6 6, T7 7, T8 8, T9 9, T10 10, T11 11,
    T12 12
);

#[derive(Debug)]
struct ArrayCheckContext {
    index: usize,
}

impl fmt::Display for ArrayCheckContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "while checking index '{}' of array", self.index)
    }
}

// SAFETY: `check_bytes` only returns `Ok` if each element of the array is
// valid. If each element of the array is valid then the whole array is also
// valid.
unsafe impl<T, const N: usize, C> CheckBytes<C> for [T; N]
where
    T: CheckBytes<C>,
    C: Fallible + ?Sized,
    C::Error: Trace,
{
    #[inline]
    unsafe fn check_bytes(
        value: *const Self,
        context: &mut C,
    ) -> Result<(), C::Error> {
        let base = value.cast::<T>();
        for index in 0..N {
            // SAFETY: The caller has guaranteed that `value` points to enough
            // bytes for this array and is properly aligned, so we can create
            // pointers to each element and check them.
            unsafe {
                T::check_bytes(base.add(index), context)
                    .with_trace(|| ArrayCheckContext { index })?;
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
struct SliceCheckContext {
    index: usize,
}

impl fmt::Display for SliceCheckContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "while checking index '{}' of slice", self.index)
    }
}

// SAFETY: `check_bytes` only returns `Ok` if each element of the slice is
// valid. If each element of the slice is valid then the whole slice is also
// valid.
unsafe impl<T, C> CheckBytes<C> for [T]
where
    T: CheckBytes<C>,
    C: Fallible + ?Sized,
    C::Error: Trace,
{
    #[inline]
    unsafe fn check_bytes(
        value: *const Self,
        context: &mut C,
    ) -> Result<(), C::Error> {
        let (data_address, len) = ptr_meta::to_raw_parts(value);
        let base = data_address.cast::<T>();
        for index in 0..len {
            // SAFETY: The caller has guaranteed that `value` points to enough
            // bytes for this slice and is properly aligned, so we can create
            // pointers to each element and check them.
            unsafe {
                T::check_bytes(base.add(index), context)
                    .with_trace(|| SliceCheckContext { index })?;
            }
        }
        Ok(())
    }
}

// SAFETY: `check_bytes` only returns `Ok` if the bytes pointed to by `str` are
// valid UTF-8. If they are valid UTF-8 then the overall `str` is also valid.
unsafe impl<C> CheckBytes<C> for str
where
    C: Fallible + ?Sized,
    C::Error: Source,
{
    #[inline]
    unsafe fn check_bytes(
        value: *const Self,
        _: &mut C,
    ) -> Result<(), C::Error> {
        #[derive(Debug)]
        struct Utf8Error;

        impl fmt::Display for Utf8Error {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "invalid UTF-8")
            }
        }

        impl Error for Utf8Error {}

        let slice_ptr = value as *const [u8];
        // SAFETY: The caller has guaranteed that `value` is properly-aligned
        // and points to enough bytes for its `str`. Because a `u8` slice has
        // the same layout as a `str`, we can dereference it for UTF-8
        // validation.
        let slice = unsafe { &*slice_ptr };
        from_utf8(slice).map_err(|_| Utf8Error).into_error()?;
        Ok(())
    }
}

// SAFETY: `check_bytes` only returns `Ok` when the bytes constitute a valid
// `CStr` per `CStr::from_bytes_with_nul`.
unsafe impl<C> CheckBytes<C> for CStr
where
    C: Fallible + ?Sized,
    C::Error: Source,
{
    #[inline]
    unsafe fn check_bytes(
        value: *const Self,
        _: &mut C,
    ) -> Result<(), C::Error> {
        let slice_ptr = value as *const [u8];
        // SAFETY: The caller has guaranteed that `value` is properly-aligned
        // and points to enough bytes for its `CStr`. Because a `u8` slice has
        // the same layout as a `CStr`, we can dereference it for validation.
        let slice = unsafe { &*slice_ptr };
        CStr::from_bytes_with_nul(slice).into_error()?;
        Ok(())
    }
}

// Generic contexts used by the derive.

/// Context for errors resulting from invalid structs.
#[derive(Debug)]
pub struct StructCheckContext {
    /// The name of the struct with an invalid field.
    pub struct_name: &'static str,
    /// The name of the struct field that was invalid.
    pub field_name: &'static str,
}

impl fmt::Display for StructCheckContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "while checking field '{}' of struct '{}'",
            self.field_name, self.struct_name
        )
    }
}

/// Context for errors resulting from invalid tuple structs.
#[derive(Debug)]
pub struct TupleStructCheckContext {
    /// The name of the tuple struct with an invalid field.
    pub tuple_struct_name: &'static str,
    /// The index of the tuple struct field that was invalid.
    pub field_index: usize,
}

impl fmt::Display for TupleStructCheckContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "while checking field index {} of tuple struct '{}'",
            self.field_index, self.tuple_struct_name,
        )
    }
}

/// An error resulting from an invalid enum tag.
#[derive(Debug)]
pub struct InvalidEnumDiscriminantError<T> {
    /// The name of the enum with an invalid discriminant.
    pub enum_name: &'static str,
    /// The invalid value of the enum discriminant.
    pub invalid_discriminant: T,
}

impl<T: fmt::Display> fmt::Display for InvalidEnumDiscriminantError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "invalid discriminant '{}' for enum '{}'",
            self.invalid_discriminant, self.enum_name
        )
    }
}

impl<T> Error for InvalidEnumDiscriminantError<T> where
    T: fmt::Debug + fmt::Display
{
}

/// Context for errors resulting from checking enum variants with named fields.
#[derive(Debug)]
pub struct NamedEnumVariantCheckContext {
    /// The name of the enum with an invalid variant.
    pub enum_name: &'static str,
    /// The name of the variant that was invalid.
    pub variant_name: &'static str,
    /// The name of the field that was invalid.
    pub field_name: &'static str,
}

impl fmt::Display for NamedEnumVariantCheckContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "while checking field '{}' of variant '{}' of enum '{}'",
            self.field_name, self.variant_name, self.enum_name,
        )
    }
}

/// Context for errors resulting from checking enum variants with unnamed
/// fields.
#[derive(Debug)]
pub struct UnnamedEnumVariantCheckContext {
    /// The name of the enum with an invalid variant.
    pub enum_name: &'static str,
    /// The name of the variant that was invalid.
    pub variant_name: &'static str,
    /// The name of the field that was invalid.
    pub field_index: usize,
}

impl fmt::Display for UnnamedEnumVariantCheckContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "while checking field index {} of variant '{}' of enum '{}'",
            self.field_index, self.variant_name, self.enum_name,
        )
    }
}

// Range types

// SAFETY: A `Range<T>` is valid if its `start` and `end` are both valid, and
// `check_bytes` only returns `Ok` when both `start` and `end` are valid. Note
// that `Range` does not require `start` be less than `end`.
unsafe impl<T, C> CheckBytes<C> for ops::Range<T>
where
    T: CheckBytes<C>,
    C: Fallible + ?Sized,
    C::Error: Trace,
{
    #[inline]
    unsafe fn check_bytes(
        value: *const Self,
        context: &mut C,
    ) -> Result<(), C::Error> {
        // SAFETY: The caller has guaranteed that `value` is aligned for a
        // `Range<T>` and points to enough initialized bytes for one, so a
        // pointer projected to the `start` field will be properly aligned for
        // a `T` and point to enough initialized bytes for one too.
        unsafe {
            T::check_bytes(ptr::addr_of!((*value).start), context).with_trace(
                || StructCheckContext {
                    struct_name: "Range",
                    field_name: "start",
                },
            )?;
        }
        // SAFETY: Same reasoning as above, but for `end`.
        unsafe {
            T::check_bytes(ptr::addr_of!((*value).end), context).with_trace(
                || StructCheckContext {
                    struct_name: "Range",
                    field_name: "end",
                },
            )?;
        }
        Ok(())
    }
}

// SAFETY: A `RangeFrom<T>` is valid if its `start` is valid, and `check_bytes`
// only returns `Ok` when its `start` is valid.
unsafe impl<T, C> CheckBytes<C> for ops::RangeFrom<T>
where
    T: CheckBytes<C>,
    C: Fallible + ?Sized,
    C::Error: Trace,
{
    #[inline]
    unsafe fn check_bytes(
        value: *const Self,
        context: &mut C,
    ) -> Result<(), C::Error> {
        // SAFETY: The caller has guaranteed that `value` is aligned for a
        // `RangeFrom<T>` and points to enough initialized bytes for one, so a
        // pointer projected to the `start` field will be properly aligned for
        // a `T` and point to enough initialized bytes for one too.
        unsafe {
            T::check_bytes(ptr::addr_of!((*value).start), context).with_trace(
                || StructCheckContext {
                    struct_name: "RangeFrom",
                    field_name: "start",
                },
            )?;
        }
        Ok(())
    }
}

// SAFETY: `RangeFull` is a ZST and so every pointer to one is valid.
unsafe impl<C: Fallible + ?Sized> CheckBytes<C> for ops::RangeFull {
    #[inline]
    unsafe fn check_bytes(_: *const Self, _: &mut C) -> Result<(), C::Error> {
        Ok(())
    }
}

// SAFETY: A `RangeTo<T>` is valid if its `end` is valid, and `check_bytes` only
// returns `Ok` when its `end` is valid.
unsafe impl<T, C> CheckBytes<C> for ops::RangeTo<T>
where
    T: CheckBytes<C>,
    C: Fallible + ?Sized,
    C::Error: Trace,
{
    #[inline]
    unsafe fn check_bytes(
        value: *const Self,
        context: &mut C,
    ) -> Result<(), C::Error> {
        // SAFETY: The caller has guaranteed that `value` is aligned for a
        // `RangeTo<T>` and points to enough initialized bytes for one, so a
        // pointer projected to the `end` field will be properly aligned for
        // a `T` and point to enough initialized bytes for one too.
        unsafe {
            T::check_bytes(ptr::addr_of!((*value).end), context).with_trace(
                || StructCheckContext {
                    struct_name: "RangeTo",
                    field_name: "end",
                },
            )?;
        }
        Ok(())
    }
}

// SAFETY: A `RangeToInclusive<T>` is valid if its `end` is valid, and
// `check_bytes` only returns `Ok` when its `end` is valid.
unsafe impl<T, C> CheckBytes<C> for ops::RangeToInclusive<T>
where
    T: CheckBytes<C>,
    C: Fallible + ?Sized,
    C::Error: Trace,
{
    #[inline]
    unsafe fn check_bytes(
        value: *const Self,
        context: &mut C,
    ) -> Result<(), C::Error> {
        // SAFETY: The caller has guaranteed that `value` is aligned for a
        // `RangeToInclusive<T>` and points to enough initialized bytes for one,
        // so a pointer projected to the `end` field will be properly aligned
        // for a `T` and point to enough initialized bytes for one too.
        unsafe {
            T::check_bytes(ptr::addr_of!((*value).end), context).with_trace(
                || StructCheckContext {
                    struct_name: "RangeToInclusive",
                    field_name: "end",
                },
            )?;
        }
        Ok(())
    }
}

#[derive(Debug)]
struct NonZeroCheckError;

impl fmt::Display for NonZeroCheckError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "nonzero integer is zero")
    }
}

impl Error for NonZeroCheckError {}

macro_rules! impl_nonzero {
    ($nonzero:ident, $underlying:ident) => {
        // SAFETY: `check_bytes` only returns `Ok` when `value` is not zero, the
        // only validity condition for non-zero integer types.
        unsafe impl<C> CheckBytes<C> for $nonzero
        where
            C: Fallible + ?Sized,
            C::Error: Source,
        {
            #[inline]
            unsafe fn check_bytes(
                value: *const Self,
                _: &mut C,
            ) -> Result<(), C::Error> {
                // SAFETY: Non-zero integer types are guaranteed to have the
                // same ABI as their corresponding integer types. Those integers
                // have no validity requirements, so we can cast and dereference
                // value to check if it is equal to zero.
                if unsafe { *value.cast::<$underlying>() } == 0 {
                    fail!(NonZeroCheckError);
                } else {
                    Ok(())
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

#[cfg(test)]
#[macro_use]
mod tests {
    use core::ffi::CStr;

    use rancor::{Failure, Fallible, Infallible, Source, Strategy};

    use crate::{check_bytes, check_bytes_with_context, CheckBytes, Verify};

    #[derive(Debug)]
    #[repr(transparent)]
    pub struct CharLE(u32);

    impl From<char> for CharLE {
        fn from(c: char) -> Self {
            #[cfg(target_endian = "little")]
            {
                Self(c as u32)
            }
            #[cfg(target_endian = "big")]
            {
                Self((c as u32).swap_bytes())
            }
        }
    }

    unsafe impl<C> CheckBytes<C> for CharLE
    where
        C: Fallible + ?Sized,
        C::Error: Source,
    {
        unsafe fn check_bytes(
            value: *const Self,
            context: &mut C,
        ) -> Result<(), C::Error> {
            #[cfg(target_endian = "little")]
            unsafe {
                char::check_bytes(value.cast(), context)
            }
            #[cfg(target_endian = "big")]
            unsafe {
                let mut bytes = *value.cast::<[u8; 4]>();
                bytes.reverse();
                char::check_bytes(bytes.as_ref().as_ptr().cast(), context)
            }
        }
    }

    #[repr(C, align(16))]
    pub struct Aligned<const N: usize>(pub [u8; N]);

    macro_rules! bytes {
        ($($byte:literal),* $(,)?) => {
            (&$crate::tests::Aligned([$($byte,)*]).0 as &[u8]).as_ptr()
        }
    }

    #[test]
    fn test_tuples() {
        unsafe {
            check_bytes::<_, Failure>(&(42u32, true, 'x')).unwrap();
        }
        unsafe {
            check_bytes::<_, Failure>(&(true,)).unwrap();
        }

        unsafe {
            // These tests assume the tuple is packed (u32, bool, char)
            check_bytes::<(u32, bool, CharLE), Failure>(
                bytes![
                    0u8, 0u8, 0u8, 0u8, 1u8, 255u8, 255u8, 255u8, 0x78u8, 0u8,
                    0u8, 0u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap();
            check_bytes::<(u32, bool, CharLE), Failure>(
                bytes![
                    42u8, 16u8, 20u8, 3u8, 1u8, 255u8, 255u8, 255u8, 0x78u8,
                    0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap();
            check_bytes::<(u32, bool, CharLE), Failure>(
                bytes![
                    0u8, 0u8, 0u8, 0u8, 1u8, 255u8, 255u8, 255u8, 0x00u8,
                    0xd8u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap_err();
            check_bytes::<(u32, bool, CharLE), Failure>(
                bytes![
                    0u8, 0u8, 0u8, 0u8, 1u8, 255u8, 255u8, 255u8, 0x00u8,
                    0x00u8, 0x11u8, 0u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap_err();
            check_bytes::<(u32, bool, CharLE), Failure>(
                bytes![
                    0u8, 0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 0x78u8, 0u8,
                    0u8, 0u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap();
            check_bytes::<(u32, bool, CharLE), Failure>(
                bytes![
                    0u8, 0u8, 0u8, 0u8, 2u8, 255u8, 255u8, 255u8, 0x78u8, 0u8,
                    0u8, 0u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap_err();
        }
    }

    #[test]
    fn test_arrays() {
        unsafe {
            check_bytes::<_, Failure>(&[true, false, true, false]).unwrap();
        }
        unsafe {
            check_bytes::<_, Failure>(&[false, true]).unwrap();
        }

        unsafe {
            check_bytes::<[bool; 4], Failure>(
                bytes![1u8, 0u8, 1u8, 0u8].cast(),
            )
            .unwrap();
            check_bytes::<[bool; 4], Failure>(
                bytes![1u8, 2u8, 1u8, 0u8].cast(),
            )
            .unwrap_err();
            check_bytes::<[bool; 4], Failure>(
                bytes![2u8, 0u8, 1u8, 0u8].cast(),
            )
            .unwrap_err();
            check_bytes::<[bool; 4], Failure>(
                bytes![1u8, 0u8, 1u8, 2u8].cast(),
            )
            .unwrap_err();
            check_bytes::<[bool; 4], Failure>(
                bytes![1u8, 0u8, 1u8, 0u8, 2u8].cast(),
            )
            .unwrap();
        }
    }

    #[test]
    fn test_unsized() {
        unsafe {
            check_bytes::<[i32], Infallible>(
                &[1, 2, 3, 4] as &[i32] as *const [i32]
            )
            .unwrap();
            check_bytes::<str, Failure>("hello world" as *const str).unwrap();
        }
    }

    #[test]
    fn test_c_str() {
        macro_rules! test_cases {
            ($($bytes:expr, $pat:pat,)*) => {
                $(
                    let bytes = $bytes;
                    let c_str = ::ptr_meta::from_raw_parts(
                        bytes.as_ptr().cast(),
                        bytes.len(),
                    );
                    assert!(matches!(
                        check_bytes::<CStr, Failure>(c_str),
                        $pat,
                    ));
                )*
            }
        }

        unsafe {
            test_cases! {
                b"hello world\0", Ok(_),
                b"hello world", Err(_),
                b"", Err(_),
                [0xc3u8, 0x28u8, 0x00u8], Ok(_),
                [0xc3u8, 0x28u8, 0x00u8, 0xc3u8, 0x28u8, 0x00u8], Err(_),
            }
        }
    }

    #[test]
    fn test_unit_struct() {
        #[derive(CheckBytes)]
        #[check_bytes(crate)]
        struct Test;

        unsafe {
            check_bytes::<_, Infallible>(&Test).unwrap();
        }
    }

    #[test]
    fn test_tuple_struct() {
        #[derive(CheckBytes, Debug)]
        #[check_bytes(crate)]
        struct Test(u32, bool, CharLE);

        let value = Test(42, true, 'x'.into());

        unsafe {
            check_bytes::<_, Failure>(&value).unwrap();
        }

        unsafe {
            // These tests assume the struct is packed (u32, char, bool)
            check_bytes::<Test, Failure>(
                bytes![
                    0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8, 1u8, 255u8,
                    255u8, 255u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap();
            check_bytes::<Test, Failure>(
                bytes![
                    42u8, 16u8, 20u8, 3u8, 0x78u8, 0u8, 0u8, 0u8, 1u8, 255u8,
                    255u8, 255u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap();
            check_bytes::<Test, Failure>(
                bytes![
                    0u8, 0u8, 0u8, 0u8, 0x00u8, 0xd8u8, 0u8, 0u8, 1u8, 255u8,
                    255u8, 255u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap_err();
            check_bytes::<Test, Failure>(
                bytes![
                    0u8, 0u8, 0u8, 0u8, 0x00u8, 0x00u8, 0x11u8, 0u8, 1u8,
                    255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap_err();
            check_bytes::<Test, Failure>(
                bytes![
                    0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8, 0u8, 255u8,
                    255u8, 255u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap();
            check_bytes::<Test, Failure>(
                bytes![
                    0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8, 2u8, 255u8,
                    255u8, 255u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap_err();
        }
    }

    #[test]
    fn test_struct() {
        #[derive(CheckBytes, Debug)]
        #[check_bytes(crate)]
        struct Test {
            a: u32,
            b: bool,
            c: CharLE,
        }

        let value = Test {
            a: 42,
            b: true,
            c: 'x'.into(),
        };

        unsafe {
            check_bytes::<_, Failure>(&value).unwrap();
        }

        unsafe {
            // These tests assume the struct is packed (u32, char, bool)
            check_bytes::<Test, Failure>(
                bytes![
                    0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8, 1u8, 255u8,
                    255u8, 255u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap();
            check_bytes::<Test, Failure>(
                bytes![
                    42u8, 16u8, 20u8, 3u8, 0x78u8, 0u8, 0u8, 0u8, 1u8, 255u8,
                    255u8, 255u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap();
            check_bytes::<Test, Failure>(
                bytes![
                    0u8, 0u8, 0u8, 0u8, 0x00u8, 0xd8u8, 0u8, 0u8, 1u8, 255u8,
                    255u8, 255u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap_err();
            check_bytes::<Test, Failure>(
                bytes![
                    0u8, 0u8, 0u8, 0u8, 0x00u8, 0x00u8, 0x11u8, 0u8, 1u8,
                    255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap_err();
            check_bytes::<Test, Failure>(
                bytes![
                    0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8, 0u8, 255u8,
                    255u8, 255u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap();
            check_bytes::<Test, Failure>(
                bytes![
                    0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8, 2u8, 255u8,
                    255u8, 255u8, 255u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap_err();
        }
    }

    #[test]
    fn test_generic_struct() {
        #[derive(CheckBytes, Debug)]
        #[check_bytes(crate)]
        struct Test<T> {
            a: u32,
            b: T,
        }

        let value = Test { a: 42, b: true };

        unsafe {
            check_bytes::<_, Failure>(&value).unwrap();
        }

        unsafe {
            check_bytes::<Test<bool>, Failure>(
                bytes![0u8, 0u8, 0u8, 0u8, 1u8, 255u8, 255u8, 255u8].cast(),
            )
            .unwrap();
            check_bytes::<Test<bool>, Failure>(
                bytes![12u8, 34u8, 56u8, 78u8, 1u8, 255u8, 255u8, 255u8].cast(),
            )
            .unwrap();
            check_bytes::<Test<bool>, Failure>(
                bytes![0u8, 0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8].cast(),
            )
            .unwrap();
            check_bytes::<Test<bool>, Failure>(
                bytes![0u8, 0u8, 0u8, 0u8, 2u8, 255u8, 255u8, 255u8].cast(),
            )
            .unwrap_err();
        }
    }

    #[test]
    fn test_enum() {
        #[allow(dead_code)]
        #[derive(CheckBytes, Debug)]
        #[check_bytes(crate)]
        #[repr(u8)]
        enum Test {
            A(u32, bool, CharLE),
            B { a: u32, b: bool, c: CharLE },
            C,
        }

        let value = Test::A(42, true, 'x'.into());

        unsafe {
            check_bytes::<_, Failure>(&value).unwrap();
        }

        let value = Test::B {
            a: 42,
            b: true,
            c: 'x'.into(),
        };

        unsafe {
            check_bytes::<_, Failure>(&value).unwrap();
        }

        let value = Test::C;

        unsafe {
            check_bytes::<_, Failure>(&value).unwrap();
        }

        unsafe {
            check_bytes::<Test, Failure>(
                bytes![
                    0u8, 0u8, 0u8, 0u8, 12u8, 34u8, 56u8, 78u8, 1u8, 255u8,
                    255u8, 255u8, 120u8, 0u8, 0u8, 0u8,
                ]
                .cast(),
            )
            .unwrap();
            check_bytes::<Test, Failure>(
                bytes![
                    1u8, 0u8, 0u8, 0u8, 12u8, 34u8, 56u8, 78u8, 1u8, 255u8,
                    255u8, 255u8, 120u8, 0u8, 0u8, 0u8,
                ]
                .cast(),
            )
            .unwrap();
            check_bytes::<Test, Failure>(
                bytes![
                    2u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8,
                    255u8, 255u8, 255u8, 255u8, 25u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap();
            check_bytes::<Test, Failure>(
                bytes![
                    3u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8,
                    255u8, 255u8, 255u8, 255u8, 25u8, 255u8, 255u8, 255u8,
                ]
                .cast(),
            )
            .unwrap_err();
        }
    }

    #[test]
    fn test_explicit_enum_values() {
        #[derive(CheckBytes, Debug)]
        #[check_bytes(crate)]
        #[repr(u8)]
        enum Test {
            A,
            B = 100,
            C,
            D = 200,
            E,
        }

        unsafe {
            check_bytes::<_, Failure>(&Test::A).unwrap();
        }
        unsafe {
            check_bytes::<_, Failure>(&Test::B).unwrap();
        }
        unsafe {
            check_bytes::<_, Failure>(&Test::C).unwrap();
        }
        unsafe {
            check_bytes::<_, Failure>(&Test::D).unwrap();
        }
        unsafe {
            check_bytes::<_, Failure>(&Test::E).unwrap();
        }

        unsafe {
            check_bytes::<Test, Failure>(bytes![1u8].cast()).unwrap_err();
            check_bytes::<Test, Failure>(bytes![99u8].cast()).unwrap_err();
            check_bytes::<Test, Failure>(bytes![102u8].cast()).unwrap_err();
            check_bytes::<Test, Failure>(bytes![199u8].cast()).unwrap_err();
            check_bytes::<Test, Failure>(bytes![202u8].cast()).unwrap_err();
            check_bytes::<Test, Failure>(bytes![255u8].cast()).unwrap_err();
        }
    }

    #[test]
    fn test_recursive() {
        struct MyBox<T: ?Sized> {
            inner: *const T,
        }

        unsafe impl<T, C> CheckBytes<C> for MyBox<T>
        where
            T: CheckBytes<C>,
            C: Fallible + ?Sized,
        {
            unsafe fn check_bytes(
                value: *const Self,
                context: &mut C,
            ) -> Result<(), C::Error> {
                unsafe { T::check_bytes((*value).inner, context) }
            }
        }

        #[allow(dead_code)]
        #[derive(CheckBytes)]
        #[check_bytes(crate)]
        #[repr(u8)]
        enum Node {
            Nil,
            Cons(#[omit_bounds] MyBox<Node>),
        }

        unsafe {
            let nil = Node::Nil;
            let cons = Node::Cons(MyBox {
                inner: &nil as *const Node,
            });
            check_bytes::<Node, Failure>(&cons).unwrap();
        }
    }

    #[test]
    fn test_explicit_crate_root() {
        mod bytecheck {}
        mod m {
            pub use crate as bc;
        }

        #[derive(CheckBytes)]
        #[check_bytes(crate = m::bc)]
        struct Test;

        unsafe {
            check_bytes::<_, Infallible>(&Test).unwrap();
        }

        #[derive(CheckBytes)]
        #[check_bytes(crate = crate)]
        struct Test2;

        unsafe {
            check_bytes::<_, Infallible>(&Test2).unwrap();
        }
    }

    trait MyContext {
        fn set_value(&mut self, value: i32);
    }

    impl<T: MyContext, E> MyContext for Strategy<T, E> {
        fn set_value(&mut self, value: i32) {
            T::set_value(self, value)
        }
    }

    struct FooContext {
        value: i32,
    }

    impl MyContext for FooContext {
        fn set_value(&mut self, value: i32) {
            self.value = value;
        }
    }

    #[test]
    fn test_derive_verify_unit_struct() {
        unsafe impl<C: Fallible + MyContext + ?Sized> Verify<C> for UnitStruct {
            fn verify(&self, context: &mut C) -> Result<(), C::Error> {
                context.set_value(1);
                Ok(())
            }
        }

        #[derive(CheckBytes)]
        #[check_bytes(crate)]
        #[check_bytes(verify)]
        struct UnitStruct;

        let mut context = FooContext { value: 0 };
        unsafe {
            check_bytes_with_context::<_, _, Infallible>(
                &UnitStruct,
                &mut context,
            )
            .unwrap();
        }

        assert_eq!(context.value, 1);
    }

    #[test]
    fn test_derive_verify_struct() {
        unsafe impl<C: Fallible + MyContext + ?Sized> Verify<C> for Struct {
            fn verify(&self, context: &mut C) -> Result<(), C::Error> {
                context.set_value(self.value);
                Ok(())
            }
        }

        #[derive(CheckBytes)]
        #[check_bytes(crate)]
        #[check_bytes(verify)]
        struct Struct {
            value: i32,
        }

        let mut context = FooContext { value: 0 };
        unsafe {
            check_bytes_with_context::<_, _, Infallible>(
                &Struct { value: 4 },
                &mut context,
            )
            .unwrap();
        }

        assert_eq!(context.value, 4);
    }

    #[test]
    fn test_derive_verify_tuple_struct() {
        unsafe impl<C> Verify<C> for TupleStruct
        where
            C: Fallible + MyContext + ?Sized,
        {
            fn verify(&self, context: &mut C) -> Result<(), C::Error> {
                context.set_value(self.0);
                Ok(())
            }
        }

        #[derive(CheckBytes)]
        #[check_bytes(crate)]
        #[check_bytes(verify)]
        struct TupleStruct(i32);

        let mut context = FooContext { value: 0 };
        unsafe {
            check_bytes_with_context::<_, _, Infallible>(
                &TupleStruct(10),
                &mut context,
            )
            .unwrap();
        }

        assert_eq!(context.value, 10);
    }

    #[test]
    fn test_derive_verify_enum() {
        unsafe impl<C: Fallible + MyContext + ?Sized> Verify<C> for Enum {
            fn verify(&self, context: &mut C) -> Result<(), C::Error> {
                match self {
                    Enum::A => context.set_value(2),
                    Enum::B(value) => context.set_value(*value),
                    Enum::C { value } => context.set_value(*value),
                }
                Ok(())
            }
        }

        #[derive(CheckBytes)]
        #[check_bytes(crate)]
        #[check_bytes(verify)]
        #[repr(u8)]
        enum Enum {
            A,
            B(i32),
            C { value: i32 },
        }

        // Unit variant
        let mut context = FooContext { value: 0 };
        unsafe {
            check_bytes_with_context::<_, _, Failure>(&Enum::A, &mut context)
                .unwrap();
        }

        assert_eq!(context.value, 2);

        // Tuple variant
        let mut context = FooContext { value: 0 };
        unsafe {
            check_bytes_with_context::<_, _, Failure>(
                &Enum::B(5),
                &mut context,
            )
            .unwrap();
        }

        assert_eq!(context.value, 5);

        // Struct variant
        let mut context = FooContext { value: 0 };
        unsafe {
            check_bytes_with_context::<_, _, Failure>(
                &Enum::C { value: 7 },
                &mut context,
            )
            .unwrap();
        }

        assert_eq!(context.value, 7);
    }
}
