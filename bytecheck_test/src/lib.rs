#[cfg(test)]
mod tests {
    use bytecheck::{
        check_buffer,
        CheckBytes,
        Context,
    };

    fn as_bytes<T>(value: &T) -> &[u8] {
        unsafe { core::slice::from_raw_parts((value as *const T).cast::<u8>(), core::mem::size_of::<T>()) }
    }

    fn check_as_bytes<T: CheckBytes<C>, C: Context<T::Context>>(value: &T, context: &C) {
        check_buffer::<T, C>(as_bytes(value), 0, context).unwrap();
    }

    #[test]
    fn test_unit_struct() {
        #[derive(CheckBytes)]
        struct Test;

        check_as_bytes(&Test, &());
    }

    #[test]
    fn test_tuple_struct() {
        #[derive(CheckBytes, Debug)]
        struct Test(u32, bool, char);

        let value = Test(42, true, 'x');

        check_as_bytes(&value, &());

        unsafe {
            // These tests assume the struct is packed (u32, char, bool)
            Test::check_bytes(&[0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8, 1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap();
            Test::check_bytes(&[42u8, 16u8, 20u8, 3u8, 0x78u8, 0u8, 0u8, 0u8, 1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap();
            Test::check_bytes(&[0u8, 0u8, 0u8, 0u8, 0x00u8, 0xd8u8, 0u8, 0u8, 1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap_err();
            Test::check_bytes(&[0u8, 0u8, 0u8, 0u8, 0x00u8, 0x00u8, 0x11u8, 0u8, 1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap_err();
            Test::check_bytes(&[0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap();
            Test::check_bytes(&[0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8, 2u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap_err();
        }
    }

    #[test]
    fn test_struct() {
        #[derive(CheckBytes, Debug)]
        struct Test {
            a: u32,
            b: bool,
            c: char,
        }

        let value = Test {
            a: 42,
            b: true,
            c: 'x',
        };

        check_as_bytes(&value, &());

        unsafe {
            // These tests assume the struct is packed (u32, char, bool)
            Test::check_bytes(&[0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8, 1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap();
            Test::check_bytes(&[42u8, 16u8, 20u8, 3u8, 0x78u8, 0u8, 0u8, 0u8, 1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap();
            Test::check_bytes(&[0u8, 0u8, 0u8, 0u8, 0x00u8, 0xd8u8, 0u8, 0u8, 1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap_err();
            Test::check_bytes(&[0u8, 0u8, 0u8, 0u8, 0x00u8, 0x00u8, 0x11u8, 0u8, 1u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap_err();
            Test::check_bytes(&[0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap();
            Test::check_bytes(&[0u8, 0u8, 0u8, 0u8, 0x78u8, 0u8, 0u8, 0u8, 2u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap_err();
        }
    }

    #[test]
    fn generic_struct() {
        #[derive(CheckBytes, Debug)]
        struct Test<T> {
            a: u32,
            b: T,
        }

        let value = Test {
            a: 42,
            b: true,
        };

        check_as_bytes(&value, &());

        unsafe {
            Test::<bool>::check_bytes(&[0u8, 0u8, 0u8, 0u8, 1u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap();
            Test::<bool>::check_bytes(&[12u8, 34u8, 56u8, 78u8, 1u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap();
            Test::<bool>::check_bytes(&[0u8, 0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap();
            Test::<bool>::check_bytes(&[0u8, 0u8, 0u8, 0u8, 2u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap_err();
        }
    }

    #[test]
    fn test_enum() {
        #[derive(CheckBytes, Debug)]
        #[repr(u8)]
        enum Test {
            A(u32, bool, char),
            #[allow(dead_code)]
            B {
                a: u32,
                b: bool,
                c: char,
            },
            C,
        }

        let value = Test::A(42, true, 'x');

        check_as_bytes(&value, &());

        let value = Test::B { a: 42, b: true, c: 'x' };

        check_as_bytes(&value, &());

        let value = Test::C;

        check_as_bytes(&value, &());

        unsafe {
            Test::check_bytes(&[0u8, 0u8, 0u8, 0u8, 12u8, 34u8, 56u8, 78u8, 1u8, 255u8, 255u8, 255u8, 120u8, 0u8, 0u8, 0u8] as *const u8, &())
                .unwrap();
            Test::check_bytes(&[1u8, 0u8, 0u8, 0u8, 12u8, 34u8, 56u8, 78u8, 1u8, 255u8, 255u8, 255u8, 120u8, 0u8, 0u8, 0u8] as *const u8, &())
                .unwrap();
            Test::check_bytes(&[2u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 25u8, 255u8, 255u8, 255u8] as *const u8, &())
                .unwrap();
            Test::check_bytes(&[3u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 25u8, 255u8, 255u8, 255u8] as *const u8, &())
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

        check_as_bytes(&Test::A, &());
        check_as_bytes(&Test::B, &());
        check_as_bytes(&Test::C, &());
        check_as_bytes(&Test::D, &());
        check_as_bytes(&Test::E, &());

        unsafe {
            Test::check_bytes(&[1u8] as *const u8, &()).unwrap_err();
            Test::check_bytes(&[99u8] as *const u8, &()).unwrap_err();
            Test::check_bytes(&[102u8] as *const u8, &()).unwrap_err();
            Test::check_bytes(&[199u8] as *const u8, &()).unwrap_err();
            Test::check_bytes(&[202u8] as *const u8, &()).unwrap_err();
            Test::check_bytes(&[255u8] as *const u8, &()).unwrap_err();
        }
    }
}
