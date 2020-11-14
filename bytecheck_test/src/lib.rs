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
        #[derive(CheckBytes)]
        struct Test(u32, bool, char);

        let value = Test(42, true, 'x');

        check_as_bytes(&value, &());
    }

    #[test]
    fn test_struct() {
        #[derive(CheckBytes)]
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
    }

    #[test]
    fn generic_struct() {
        #[derive(CheckBytes)]
        struct Test<T> {
            a: u32,
            b: T,
        }

        let value = Test {
            a: 42,
            b: -1,
        };

        check_as_bytes(&value, &());
    }

    #[test]
    fn test_enum() {
        #[derive(CheckBytes)]
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
    }
}