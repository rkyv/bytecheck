use core::{
    alloc::Layout,
    fmt,
    marker::PhantomData,
    mem::size_of,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

#[cfg(not(feature = "std"))]
use alloc::alloc;
#[cfg(feature = "std")]
use std::alloc;

use ptr_meta::Pointee;

pub struct ThinBox<T: Pointee + ?Sized> {
    ptr: NonNull<()>,
    _phantom: PhantomData<T>,
}

// SAFETY: `ThinBox` owns the value it points to, so it is `Send` if `T` is also
// `Send`.
unsafe impl<T: Pointee + Send + ?Sized> Send for ThinBox<T> {}

// SAFETY: `ThinBox` owns the value it points to, so it is `Sync` if `T` is also
// `Sync`.
unsafe impl<T: Pointee + Sync + ?Sized> Sync for ThinBox<T> {}

impl<T: Pointee + ?Sized> Drop for ThinBox<T> {
    fn drop(&mut self) {
        let ptr = self.as_ptr();
        // SAFETY: `ptr` always points to a valid `T`, even when it's dangling.
        let value = unsafe { &*ptr };
        let value_layout = Layout::for_value(value);
        // SAFETY: `ptr` is always initialized and we own it, so we may drop it.
        // We only ever drop it during `drop`, so it won't get dropped twice.
        unsafe {
            self.as_ptr().drop_in_place();
        }
        let (layout, header) = Self::layout_for(value_layout);
        if layout.size() > 0 {
            // SAFETY: The pointer passed to `dealloc` is our raw pointer moved
            // backwards to the beginning of the allocation. `layout` is the
            // same layout used to allocate the memory because it is from
            // `Self::layout_for` given the layout of the owned value.
            unsafe {
                alloc::dealloc(ptr.cast::<u8>().sub(header), layout);
            }
        }
    }
}

impl<T: fmt::Debug + Pointee + ?Sized> fmt::Debug for ThinBox<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<T: fmt::Display + Pointee + ?Sized> fmt::Display for ThinBox<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<T: Pointee + ?Sized> ThinBox<T> {
    fn layout_for(value_layout: Layout) -> (Layout, usize) {
        let meta_layout = Layout::new::<T::Metadata>();
        if meta_layout.size() == 0 {
            (value_layout, 0)
        } else {
            let align = usize::max(value_layout.align(), meta_layout.align());
            let header = usize::max(align, meta_layout.size());
            let size = value_layout.size() + header;
            let layout = Layout::from_size_align(size, align).unwrap();
            (layout, header)
        }
    }

    /// # Safety
    ///
    /// `cast` must return the same pointer _unsized_ to a pointer to `T`.
    pub unsafe fn new_unchecked<U, F>(value: U, cast: F) -> Self
    where
        F: FnOnce(*mut U) -> *mut T,
    {
        let (layout, header) = Self::layout_for(Layout::new::<U>());
        if layout.size() == 0 {
            Self {
                ptr: NonNull::dangling(),
                _phantom: PhantomData,
            }
        } else {
            let raw_ptr =
                // SAFETY: We checked that `layout` has non-zero size.
                unsafe { NonNull::new(alloc::alloc(layout)).unwrap() };
            // SAFETY: `layout_for` returns a layout that is aligned for and has
            // space for `value` after the first `header` bytes. Adding `header`
            // bytes to `raw_ptr` will always be in-bounds.
            let value_ptr = unsafe { raw_ptr.as_ptr().add(header).cast::<U>() };
            // SAFETY: `value_ptr` points to a memory location suitable for
            // `value`.
            unsafe {
                value_ptr.write(value);
            }
            let ptr = cast(value_ptr);
            // SAFETY: The metadata for the thin box is always located right
            // before the end of the header, so offsetting part-way into the
            // header will always be in-bounds.
            let meta_ptr = unsafe {
                raw_ptr
                    .as_ptr()
                    .add(header - size_of::<T::Metadata>())
                    .cast::<T::Metadata>()
            };
            // SAFETY: `meta_ptr` points to memory properly aligned for the
            // metadata of `T`.
            unsafe {
                meta_ptr.write(ptr_meta::metadata(ptr));
            }
            Self {
                // SAFETY: `value_ptr` is offset from `raw_ptr`, which we made
                // sure was not null.
                ptr: unsafe { NonNull::new_unchecked(ptr.cast()) },
                _phantom: PhantomData,
            }
        }
    }

    pub fn as_ptr(&self) -> *mut T {
        let data_address = self.ptr.as_ptr();
        // SAFETY: The metadata for the value is held immediately before the
        // address the pointer points to and it always initialized, even when
        // `T` is a ZST with metadata.
        let metadata = unsafe { *data_address.cast::<T::Metadata>().sub(1) };
        ptr_meta::from_raw_parts_mut(data_address, metadata)
    }
}

impl<T: Pointee + ?Sized> Deref for ThinBox<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: `ThinBox` always points to a valid `T`.
        unsafe { &*self.as_ptr().cast_const() }
    }
}

impl<T: Pointee + ?Sized> DerefMut for ThinBox<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: `ThinBox` always points to a valid `T`.
        unsafe { &mut *self.as_ptr() }
    }
}

#[cfg(test)]
mod tests {
    use super::ThinBox;

    use ptr_meta::pointee;

    #[pointee]
    trait DynTrait {
        fn int(&self) -> i32;
    }

    impl DynTrait for () {
        fn int(&self) -> i32 {
            10
        }
    }

    impl DynTrait for i32 {
        fn int(&self) -> i32 {
            *self
        }
    }

    impl DynTrait for String {
        fn int(&self) -> i32 {
            self.parse().unwrap()
        }
    }

    #[test]
    fn sized_types() {
        let box_unit = unsafe { ThinBox::new_unchecked((), |x| x) };
        assert_eq!(*box_unit, ());

        let box_int = unsafe { ThinBox::new_unchecked(10, |x| x) };
        assert_eq!(*box_int, 10);

        let box_string =
            unsafe { ThinBox::new_unchecked("hello world".to_string(), |x| x) };
        assert_eq!(*box_string, "hello world");
    }

    #[test]
    fn unsized_types() {
        let box_dyn_int =
            unsafe { ThinBox::new_unchecked(10, |x| x as *mut dyn DynTrait) };
        assert_eq!(box_dyn_int.int(), 10);

        let box_dyn_string = unsafe {
            ThinBox::new_unchecked("10".to_string(), |x| x as *mut dyn DynTrait)
        };
        assert_eq!(box_dyn_string.int(), 10);

        let box_slice = unsafe {
            ThinBox::new_unchecked([1, 2, 3, 4], |x| x as *mut [i32])
        };
        assert_eq!(*box_slice, [1, 2, 3, 4]);
    }

    #[test]
    fn zst_dst() {
        let box_unit_debug =
            unsafe { ThinBox::new_unchecked((), |x| x as *mut dyn DynTrait) };
        assert_eq!(box_unit_debug.int(), 10);

        let box_empty_slice =
            unsafe { ThinBox::new_unchecked([], |x| x as *mut [i32]) };
        assert_eq!(*box_empty_slice, []);
    }
}
