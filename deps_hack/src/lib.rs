#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

pub use core;
pub use crc64fast;
pub use nix;
pub use rand;
// pub use winapi;
// pub use winapi::shared::winerror::SUCCEEDED;
// pub use winapi::um::fileapi::{CreateFileA, OPEN_ALWAYS};
// pub use winapi::um::handleapi::INVALID_HANDLE_VALUE;
// pub use winapi::um::memoryapi::{MapViewOfFile, FILE_MAP_ALL_ACCESS};
// pub use winapi::um::winbase::CreateFileMappingA;
// pub use winapi::um::winnt::{PAGE_READWRITE, FILE_SHARE_WRITE, FILE_SHARE_READ, FILE_SHARE_DELETE, GENERIC_READ, GENERIC_WRITE, FILE_ATTRIBUTE_NORMAL, ULARGE_INTEGER};

pub mod pmem;

include!("./bindings.rs");
