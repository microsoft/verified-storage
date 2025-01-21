use crate::err::Error;

pub trait MemoryPool: Sized {
    fn len(&self) -> u64;

    fn write(&mut self, offset: u64, bytes: &[u8]) -> Result<(), Error>;

    fn read(&self, offset: u64, len: u64) -> Result<Vec<u8>, Error>;
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
}
