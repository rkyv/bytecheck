# bytecheck &emsp; [![Latest Version]][crates.io] [![License]][license path]

[Latest Version]: https://img.shields.io/crates/v/bytecheck.svg
[crates.io]: https://crates.io/crates/bytecheck
[License]: https://img.shields.io/badge/license-MIT-blue.svg
[license path]: https://github.com/djkoloski/bytecheck/blob/master/LICENSE

bytecheck is a type validation framework for Rust.

## bytecheck in action

```rust
use bytecheck::{CheckBytes, check_bytes, rancor::Failure};

#[derive(CheckBytes, Debug)]
#[repr(C)]
struct Test {
    a: u32,
    b: char,
    c: bool,
}

#[repr(C, align(4))]
struct Aligned<const N: usize>([u8; N]);

macro_rules! bytes {
    ($($byte:literal,)*) => {
        (&Aligned([$($byte,)*]).0 as &[u8]).as_ptr()
    };
    ($($byte:literal),*) => {
        bytes!($($byte,)*)
    };
}

// In this example, the architecture is assumed to be little-endian
#[cfg(target_endian = "little")]
unsafe {
    // These are valid bytes for a `Test`
    check_bytes::<Test, Failure>(
        bytes![
            0u8, 0u8, 0u8, 0u8,
            0x78u8, 0u8, 0u8, 0u8,
            1u8, 255u8, 255u8, 255u8,
        ].cast()
    ).unwrap();

    // Changing the bytes for the u32 is OK, any bytes are a valid u32
    check_bytes::<Test, Failure>(
        bytes![
            42u8, 16u8, 20u8, 3u8,
            0x78u8, 0u8, 0u8, 0u8,
            1u8, 255u8, 255u8, 255u8,
        ].cast()
    ).unwrap();

    // Characters outside the valid ranges are invalid
    check_bytes::<Test, Failure>(
        bytes![
            0u8, 0u8, 0u8, 0u8,
            0x00u8, 0xd8u8, 0u8, 0u8,
            1u8, 255u8, 255u8, 255u8,
        ].cast()
    ).unwrap_err();
    check_bytes::<Test, Failure>(
        bytes![
            0u8, 0u8, 0u8, 0u8,
            0x00u8, 0x00u8, 0x11u8, 0u8,
            1u8, 255u8, 255u8, 255u8,
        ].cast()
    ).unwrap_err();

    // 0 is a valid boolean value (false) but 2 is not
    check_bytes::<Test, Failure>(
        bytes![
            0u8, 0u8, 0u8, 0u8,
            0x78u8, 0u8, 0u8, 0u8,
            0u8, 255u8, 255u8, 255u8,
        ].cast()
    ).unwrap();
    check_bytes::<Test, Failure>(
        bytes![
            0u8, 0u8, 0u8, 0u8,
            0x78u8, 0u8, 0u8, 0u8,
            2u8, 255u8, 255u8, 255u8,
        ].cast()
    ).unwrap_err();
}
```
