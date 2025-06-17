#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

pub use core;
pub use crc64fast;
pub use rand;
#[cfg(target_os = "linux")]
pub use nix;
#[cfg(target_os = "windows")]
pub use winapi;
#[cfg(target_os = "windows")]
pub use winapi::shared::winerror::SUCCEEDED;
#[cfg(target_os = "windows")]
pub use winapi::um::errhandlingapi::GetLastError;
#[cfg(target_os = "windows")]
pub use winapi::um::fileapi::{CreateFileA, OPEN_ALWAYS};
#[cfg(target_os = "windows")]
pub use winapi::um::handleapi::INVALID_HANDLE_VALUE;
#[cfg(target_os = "windows")]
pub use winapi::um::memoryapi::{MapViewOfFile, FILE_MAP_ALL_ACCESS};
#[cfg(target_os = "windows")]
pub use winapi::um::winbase::CreateFileMappingA;
#[cfg(target_os = "windows")]
pub use winapi::um::winnt::{
    FILE_ATTRIBUTE_NORMAL, FILE_SHARE_DELETE, FILE_SHARE_READ, FILE_SHARE_WRITE, GENERIC_READ,
    GENERIC_WRITE, PAGE_READWRITE, ULARGE_INTEGER,
};
#[cfg(target_family = "unix")]
pub use memmap;

pub use pmcopy::{PmCopy, pmcopy_primitive};

#[cfg(all(target_os = "linux", feature = "pmem"))]
pub mod pmem;

#[cfg(all(target_os = "linux", feature = "pmem"))]
include!("./bindings.rs");
