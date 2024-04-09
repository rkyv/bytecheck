#![deny(
    rust_2018_compatibility,
    rust_2018_idioms,
    future_incompatible,
    nonstandard_style,
    unused,
    clippy::all
)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod tests {
    use bytecheck::{
        check_bytes, check_bytes_with_context,
        rancor::{Source, Failure, Fallible, Infallible},
        CheckBytes, Verify,
    };
    use rancor::Strategy;

    #[derive(Debug)]
    #[repr(transparent)]
    struct CharLE(u32);

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
            {
                char::check_bytes(value.cast(), context)
            }
            #[cfg(target_endian = "big")]
            {
                let mut bytes = *value.cast::<[u8; 4]>();
                bytes.reverse();
                char::check_bytes(bytes.as_ref().as_ptr().cast(), context)
            }
        }
    }

    #[repr(C, align(16))]
    struct Aligned<const N: usize>([u8; N]);

    macro_rules! bytes {
        ($($byte:literal),* $(,)?) => {
            (&Aligned([$($byte,)*]).0 as &[u8]).as_ptr()
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
    fn test_unit_struct() {
        #[derive(CheckBytes)]
        struct Test;

        unsafe {
            check_bytes::<_, Infallible>(&Test).unwrap();
        }
    }

    #[test]
    fn test_tuple_struct() {
        #[derive(CheckBytes, Debug)]
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
        #[derive(CheckBytes, Debug)]
        #[repr(u8)]
        enum Test {
            A(u32, bool, CharLE),
            #[allow(dead_code)]
            B {
                a: u32,
                b: bool,
                c: CharLE,
            },
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
    #[cfg(feature = "std")]
    fn test_c_str() {
        use ::std::ffi::CStr;

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
                T::check_bytes((*value).inner, context)?;
                Ok(())
            }
        }

        #[derive(CheckBytes)]
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
            pub use ::bytecheck as bc;
        }

        #[derive(CheckBytes)]
        #[check_bytes(crate = "m::bc")]
        struct Test;

        unsafe {
            check_bytes::<_, Infallible>(&Test).unwrap();
        }

        #[derive(CheckBytes)]
        #[check_bytes(crate = "::bytecheck")]
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
