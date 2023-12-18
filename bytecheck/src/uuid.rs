//! [`CheckBytes`] implementations for uuid.

use uuid::Uuid;

use crate::{CheckBytes, rancor::Fallible};

// SAFETY: `Uuid` is `#[repr(transparent)]` around an inner `Bytes`, which is a
// simple byte array. Byte arrays are always valid.
unsafe impl<C: Fallible + ?Sized> CheckBytes<C> for Uuid {
    #[inline]
    unsafe fn check_bytes(_: *const Self, _: &mut C) -> Result<(), C::Error> {
        Ok(())
    }
}

#[cfg(test)]
mod bytecheck_tests {
    use uuid::Uuid;

    use crate::{check_bytes, rancor::Infallible};

    #[test]
    fn test_check_bytes() {
        let uuid_str = "f9168c5e-ceb2-4faa-b6bf-329bf39fa1e4";
        let u = Uuid::parse_str(uuid_str).unwrap();

        // SAFETY: `&u` is aligned and points to enough bytes to represent a
        // `Uuid`.
        unsafe {
            check_bytes::<_, Infallible>(&u).expect("failed to check uuid");
        }
    }
}
