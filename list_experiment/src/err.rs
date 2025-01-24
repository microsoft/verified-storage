#[derive(Debug)]
pub enum Error {
    OutOfSpace,
    InvalidAddr,
    OutOfBounds,
    InvalidCDB,
    InvalidCRC,
    ListTooShort,
    InvalidMemPoolSize,
    KeyNotFound,
    NotInCache,
}
