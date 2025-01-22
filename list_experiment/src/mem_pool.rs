use crate::err::Error;

pub trait MemoryPool: Sized {
    fn len(&self) -> u64;

    fn write(&mut self, offset: u64, bytes: &[u8]) -> Result<(), Error>;

    fn read(&self, offset: u64, len: u64) -> Result<Vec<u8>, Error>;

    fn flush(&self);
}

// Not the same PmCopy used in the verified code! Does not perform
// the same safety checks, just makes it faster to convert
// a data structure to bytes to be written to a memory pool
pub trait PmCopy: Sized {
    fn to_bytes(&self) -> &[u8] {
        let ptr = self as *const Self as *const u8;
        // SAFETY: self is a valid Self, so it is contiguous/non-null/valid
        // for reads up to size_of::<Self>().
        unsafe { core::slice::from_raw_parts(ptr, core::mem::size_of::<Self>()) }
    }

    // SAFETY: bytes must be a properly-aligned valid value for Self.
    // Unlike in the verified version, this trait does not require
    // that these safety properties are checked.
    unsafe fn from_bytes(bytes: &[u8]) -> &Self {
        if bytes.len() != core::mem::size_of::<Self>() {
            panic!(
                "byte slice of len {:?} does not match expected length {:?}",
                bytes.len(),
                core::mem::size_of::<Self>()
            );
        } else {
            let ptr = bytes.as_ptr() as *const Self;
            unsafe { &*ptr }
        }
    }
}
