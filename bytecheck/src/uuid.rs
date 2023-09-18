//! [`CheckBytes`](crate::CheckBytes) implementations for uuid.

use crate::{CheckBytes, Context};
use uuid::Uuid;

// SAFETY: `Uuid` is `#[repr(transparent)]` around an inner `Bytes`, which is a
// simple byte array. Byte arrays are always valid.
unsafe impl<C: Context + ?Sized> CheckBytes<C> for Uuid {
    unsafe fn check_bytes(_: *const Self, _: &mut C) -> Result<(), C::Error> {
        Ok(())
    }
}

#[cfg(test)]
mod bytecheck_tests {
    use crate::{CheckBytes, FailureContext};
    use uuid::Uuid;

    #[test]
    fn test_check_bytes() {
        let uuid_str = "f9168c5e-ceb2-4faa-b6bf-329bf39fa1e4";
        let u = Uuid::parse_str(uuid_str).unwrap();

        // SAFETY: `&u` is aligned and points to enough bytes to represent a
        // `Uuid`.
        unsafe {
            Uuid::check_bytes(&u as *const Uuid, &mut FailureContext)
                .expect("failed to check uuid");
        }
    }
}
