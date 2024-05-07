//! This file contains the trusted implementation for
//! `FileBackedPersistentMemoryRegions`, a collection of persistent
//! memory regions backed by files. It implements trait
//! `PersistentMemoryRegions`.

use core::ffi::c_void;
use crate::pmem::pmemspec_t::{
    PersistentMemoryByte, PersistentMemoryConstants, PersistentMemoryRegion,
    PersistentMemoryRegionView, PersistentMemoryRegions, PersistentMemoryRegionsView,
    PmemError,
};
use crate::pmem::serialization_t::*;
use builtin::*;
use builtin_macros::*;
use deps_hack::rand::Rng;
use deps_hack::winapi::shared::winerror::SUCCEEDED;
use deps_hack::winapi::um::errhandlingapi::GetLastError;
use deps_hack::winapi::um::fileapi::{CreateFileA, DeleteFileA, CREATE_NEW, OPEN_EXISTING};
use deps_hack::winapi::um::handleapi::INVALID_HANDLE_VALUE;
use deps_hack::winapi::um::memoryapi::{MapViewOfFile, FILE_MAP_ALL_ACCESS};
use deps_hack::winapi::um::winbase::CreateFileMappingA;
use deps_hack::winapi::um::winnt::{
    FILE_ATTRIBUTE_NORMAL, FILE_ATTRIBUTE_TEMPORARY, FILE_SHARE_DELETE, FILE_SHARE_READ,
    FILE_SHARE_WRITE, GENERIC_READ, GENERIC_WRITE, HANDLE, PAGE_READWRITE, ULARGE_INTEGER,
};
use std::convert::*;
use std::ffi::CString;
use std::slice;
use vstd::prelude::*;

#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::_mm_clflush;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::_mm_sfence;
    
// The `MemoryMappedFile` struct represents a memory-mapped file.

pub struct MemoryMappedFile {
    media_type: MemoryMappedFileMediaType,  // type of media on which the file is stored
    size: usize,                            // number of bytes in the file
    h_file: HANDLE,                         // handle to the file
    h_map_file: HANDLE,                     // handle to the mapping
    h_map_addr: HANDLE,                     // address of the first byte of the mapping
}

impl MemoryMappedFile {
    // The function `from_file` memory-maps a file and returns a
    // `MemoryMappedFile` to represent it.

    pub fn from_file(path: &str, size: usize, media_type: MemoryMappedFileMediaType,
                     open_behavior: FileOpenBehavior, close_behavior: FileCloseBehavior)
                     -> Result<Self, PmemError>
    {
        unsafe {
            // Since str in rust is not null terminated, we need to convert it to a null-terminated string.
            let path_cstr = std::ffi::CString::new(path).unwrap().as_ptr();

            let create_or_open = match open_behavior {
                FileOpenBehavior::CreateNew => CREATE_NEW,
                FileOpenBehavior::OpenExisting => OPEN_EXISTING,
            };
            let attributes = match close_behavior {
                FileCloseBehavior::TestingSoDeleteOnClose => FILE_ATTRIBUTE_TEMPORARY,
                FileCloseBehavior::Persistent => FILE_ATTRIBUTE_NORMAL,
            };
            let h_file = CreateFileA(
                path_cstr,
                GENERIC_READ | GENERIC_WRITE,
                FILE_SHARE_WRITE | FILE_SHARE_READ | FILE_SHARE_DELETE,
                core::ptr::null_mut(),
                create_or_open,
                attributes,
                core::ptr::null_mut());

            let error_code = GetLastError();

            if h_file.is_null() {
                println!("Could not open file {}. err={}", path, error_code);
                return Err(PmemError::CannotOpenPmFile);
            }

            if h_file == INVALID_HANDLE_VALUE {
                println!("Could not find file {}. err={}", path, error_code);
                return Err(PmemError::CannotOpenPmFile);
            }

            let mut li : ULARGE_INTEGER = std::mem::zeroed();
            *li.QuadPart_mut() = size as u64;

            // Create a file mapping object backed by the system paging file
            let h_map_file = CreateFileMappingA(
                h_file,
                core::ptr::null_mut(),
                PAGE_READWRITE,
                li.u().HighPart,
                li.u().LowPart,
                core::ptr::null_mut()
            );

            if h_map_file.is_null() {
                println!("Could not create file mapping object for {}.", path);
                return Err(PmemError::CannotOpenPmFile);
            }

            // Map a view of the file mapping into the address space of the process
            let h_map_addr = MapViewOfFile(
                h_map_file,
                FILE_MAP_ALL_ACCESS,
                0,
                0,
                size.try_into().unwrap(),
            );

            if h_map_addr.is_null() {
                let err = GetLastError();
                println!("Could not map view of file, got error {}", err);
                return Err(PmemError::CannotOpenPmFile);
            }

            if let FileCloseBehavior::TestingSoDeleteOnClose = close_behavior {
                // After opening the file, mark it for deletion when the file is closed.
                // Obviously, we should only do this during testing!
                deps_hack::winapi::um::fileapi::DeleteFileA(path_cstr);
            }

            let mmf = MemoryMappedFile {
                media_type,
                size,
                h_file,
                h_map_file,
                h_map_addr,
            };
            Ok(mmf)
        }
    }
}

impl Drop for MemoryMappedFile {
    fn drop(&mut self)
    {
        unsafe {
            deps_hack::winapi::um::memoryapi::UnmapViewOfFile(self.h_map_addr);
            deps_hack::winapi::um::handleapi::CloseHandle(self.h_map_file);

            if !self.h_file.is_null() {
                deps_hack::winapi::um::handleapi::CloseHandle(self.h_file);
            }
        }
    }
}

// The `MemoryMappedFileSection` struct represents a section of a memory-mapped file.

#[verifier::external_body]
pub struct MemoryMappedFileSection {
    mmf: std::rc::Rc<MemoryMappedFile>,  // reference to the MemoryMappedFile this is part of
    size: usize,                         // number of bytes in the section
    h_map_addr: HANDLE,                  // address of the first byte of the section
}

impl MemoryMappedFileSection {
    pub fn new(mmf: std::rc::Rc<MemoryMappedFile>, offset: usize, len: usize) -> Self
    {
        let h_map_addr = unsafe { (mmf.h_map_addr as *mut u8).offset(offset.try_into().unwrap()) };

        Self {
            mmf: mmf.clone(),
            size: len,
            h_map_addr: h_map_addr as HANDLE,
        }
    }

    // The function `flush` flushes updated parts of the
    // memory-mapped file back to the media.

    pub fn flush(&mut self) {
        unsafe {
            match self.mmf.media_type {
                MemoryMappedFileMediaType::BatteryBackedDRAM => {
                    // If using battery-backed DRAM, there's no need
                    // to flush cache lines, since those will be
                    // flushed during the battery-enabled graceful
                    // shutdown after power loss.
                    _mm_sfence();
                },
                _ => {
                    let hr = deps_hack::winapi::um::memoryapi::FlushViewOfFile(
                        self.h_map_addr as *const deps_hack::winapi::ctypes::c_void,
                        self.size
                    );

                    if !SUCCEEDED(hr) {
                        panic!("Failed to flush view of file. err={}", hr);
                    }
                },
            }
        }
    }
}

verus! {

// The `MemoryMappedFileMediaType` enum represents a type of media
// from which a file can be memory-mapped.

#[derive(Clone)]
pub enum MemoryMappedFileMediaType {
    HDD,
    SSD,
    BatteryBackedDRAM,
}

#[derive(Copy, Clone)]
pub enum FileOpenBehavior {
    CreateNew,
    OpenExisting,
}

#[derive(Copy, Clone)]
pub enum FileCloseBehavior {
    TestingSoDeleteOnClose,
    Persistent,
}

// The `FileBackedPersistentMemoryRegion` struct represents a
// persistent-memory region backed by a memory-mapped file.

#[allow(dead_code)]
pub struct FileBackedPersistentMemoryRegion
{
    section: MemoryMappedFileSection,
}

impl FileBackedPersistentMemoryRegion
{
    #[verifier::external_body]
    fn new_internal(path: &StrSlice, media_type: MemoryMappedFileMediaType, region_size: u64,
                    open_behavior: FileOpenBehavior, close_behavior: FileCloseBehavior)
                    -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(region) => region.inv() && region@.len() == region_size,
                Err(_) => true,
            }
    {
        let mmf = MemoryMappedFile::from_file(
            path.into_rust_str(),
            region_size.try_into().unwrap(),
            media_type,
            open_behavior,
            close_behavior
        )?;
        let mmf = std::rc::Rc::<MemoryMappedFile>::new(mmf);
        let section = MemoryMappedFileSection::new(mmf, 0, region_size.try_into().unwrap());
        Ok(Self { section })
    }

    pub fn new(path: &StrSlice, media_type: MemoryMappedFileMediaType, region_size: u64,
               close_behavior: FileCloseBehavior) -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(region) => region.inv() && region@.len() == region_size,
                Err(_) => true,
            }
    {
        Self::new_internal(path, media_type, region_size, FileOpenBehavior::CreateNew, close_behavior)
    }

    pub fn restore(path: &StrSlice, media_type: MemoryMappedFileMediaType, region_size: u64)
               -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(region) => region.inv() && region@.len() == region_size,
                Err(_) => true,
            }
    {
        Self::new_internal(path, media_type, region_size, FileOpenBehavior::OpenExisting, FileCloseBehavior::Persistent)
    }

    #[verifier::external_body]
    fn new_from_section(section: MemoryMappedFileSection) -> (result: Self)
    {
        Self{ section }
    }
}

impl PersistentMemoryRegion for FileBackedPersistentMemoryRegion
{
    closed spec fn view(&self) -> PersistentMemoryRegionView;

    closed spec fn inv(&self) -> bool;

    closed spec fn constants(&self) -> PersistentMemoryConstants;

    #[verifier::external_body]
    fn get_region_size(&self) -> u64
    {
        self.section.size as u64
    }

    #[verifier::external_body]
    fn read(&self, addr: u64, num_bytes: u64) -> (bytes: Vec<u8>)
    {
        let offset: isize = addr.try_into().unwrap();
        let num_bytes_usize: usize = num_bytes.try_into().unwrap();
        let h_map_addr = unsafe { self.section.h_map_addr.offset(offset) as *const u8 };
        let slice = unsafe { core::slice::from_raw_parts(h_map_addr, num_bytes_usize) };
        slice.to_vec()
    }

    #[verifier::external_body]
    fn read_and_deserialize<S>(&self, addr: u64) -> &S
        where
            S: Serializable + Sized
    {
        // SAFETY: The `offset` method is safe as long as both the start
        // and resulting pointer are in bounds and the computed offset does
        // not overflow `isize`. `addr` and `num_bytes` are unsigned and
        // the precondition requires that `addr + num_bytes` is in bounds.
        // The precondition does not technically prevent overflowing `isize`
        // but the value is large enough (assuming a 64-bit architecture)
        // that we will not violate this restriction in practice.
        // TODO: put it in the precondition anyway
        let addr_on_pm: *const u8 = unsafe {
            (self.section.h_map_addr as *const u8).offset(addr.try_into().unwrap())
        };

        // Cast the pointer to PM bytes to an S pointer
        let s_pointer: *const S = addr_on_pm as *const S;

        // SAFETY: The precondition establishes that `S::serialized_len()` bytes
        // after the offset specified by `addr` are valid PM bytes, so it is
        // safe to dereference s_pointer. The borrow checker should treat this object
        // as borrowed from the MappedPM object, preventing mutable borrows of any
        // other part of the object until this one is dropped.
        unsafe { &(*s_pointer) }
    }

    #[verifier::external_body]
    fn write(&mut self, addr: u64, bytes: &[u8])
    {
        let offset: isize = addr.try_into().unwrap();
        let h_map_addr = unsafe { self.section.h_map_addr.offset(offset) as *mut u8 };
        let slice = unsafe { core::slice::from_raw_parts_mut(h_map_addr, bytes.len()) };
        slice.copy_from_slice(bytes)
    }

    #[verifier::external_body]
    #[allow(unused_variables)]
    fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S)
        where
            S: Serializable + Sized
    {
        let num_bytes: usize = S::serialized_len().try_into().unwrap();

        // SAFETY: The `offset` method is safe as long as both the start
        // and resulting pointer are in bounds and the computed offset does
        // not overflow `isize`. `addr` and `num_bytes` are unsigned and
        // the precondition requires that `addr + num_bytes` is in bounds.
        // The precondition does not technically prevent overflowing `isize`
        // but the value is large enough (assuming a 64-bit architecture)
        // that we will not violate this restriction in practice.
        // TODO: put it in the precondition anyway
        let addr_on_pm: *mut u8 = unsafe {
            (self.section.h_map_addr as *mut u8).offset(addr.try_into().unwrap())
        };

        // convert the given &S to a pointer, then a slice of bytes
        let s_pointer = to_write as *const S as *const u8;

        unsafe {
            std::ptr::copy_nonoverlapping(
                s_pointer as *const c_void,
                addr_on_pm as *mut c_void,
                num_bytes
            );
        }
    }

    #[verifier::external_body]
    fn flush(&mut self)
    {
        self.section.flush();
    }
}

// The `FileBackedPersistentMemoryRegions` struct contains a
// vector of volatile memory regions. It implements the trait
// `PersistentMemoryRegions` so that it can be used by a multilog.

pub struct FileBackedPersistentMemoryRegions
{
    media_type: MemoryMappedFileMediaType,           // common media file type used
    regions: Vec<FileBackedPersistentMemoryRegion>,  // all regions
}

impl FileBackedPersistentMemoryRegions {
    #[verifier::external_body]
    fn new_internal(path: &StrSlice, media_type: MemoryMappedFileMediaType, region_sizes: &[u64],
                    open_behavior: FileOpenBehavior, close_behavior: FileCloseBehavior)
                    -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(regions) => {
                    &&& regions.inv()
                    &&& regions@.no_outstanding_writes()
                    &&& regions@.len() == region_sizes@.len()
                    &&& forall |i| 0 <= i < region_sizes@.len() ==> #[trigger] regions@[i].len() == region_sizes@[i]
                },
                Err(_) => true
            }
    {
        let mut total_size = 0;
        for region_size in region_sizes {
            total_size = total_size + region_size;
        }
        let mmf = MemoryMappedFile::from_file(
            path.into_rust_str(),
            total_size.try_into().unwrap(),
            media_type.clone(),
            open_behavior,
            close_behavior
        )?;
        let mmf = std::rc::Rc::<MemoryMappedFile>::new(mmf);
        let mut regions = Vec::<FileBackedPersistentMemoryRegion>::new();
        let mut offset: usize = 0;
        for i in 0..region_sizes.len() {
            let region_size: usize = region_sizes[i].try_into().unwrap();
            let section = MemoryMappedFileSection::new(mmf.clone(), offset, region_size.try_into().unwrap());
            let region = FileBackedPersistentMemoryRegion::new_from_section(section);
            regions.push(region);
            offset += region_size;
        }
        Ok(Self { media_type, regions })
    }

    // The static function `new` creates a
    // `FileBackedPersistentMemoryRegions` object by creating a file
    // and dividing it into memory-mapped sections.
    //
    // `path` -- the path to use for the file
    //
    // `media_type` -- the type of media the path refers to
    //
    // `region_sizes` -- a vector of region sizes, where
    // `region_sizes[i]` is the length of file `log<i>`
    //
    // `close_behavior` -- what to do when the file is closed
    pub fn new(path: &StrSlice, media_type: MemoryMappedFileMediaType, region_sizes: &[u64],
               close_behavior: FileCloseBehavior)
               -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(regions) => {
                    &&& regions.inv()
                    &&& regions@.no_outstanding_writes()
                    &&& regions@.len() == region_sizes@.len()
                    &&& forall |i| 0 <= i < region_sizes@.len() ==> #[trigger] regions@[i].len() == region_sizes@[i]
                },
                Err(_) => true
            }
    {
        Self::new_internal(path, media_type, region_sizes, FileOpenBehavior::CreateNew, close_behavior)
    }

    // The static function `restore` creates a
    // `FileBackedPersistentMemoryRegions` object by opening an
    // existing file and dividing it into memory-mapped sections.
    //
    // `path` -- the path to use for the file
    //
    // `media_type` -- the type of media the path refers to
    //
    // `region_sizes` -- a vector of region sizes, where
    // `region_sizes[i]` is the length of file `log<i>`
    pub fn restore(path: &StrSlice, media_type: MemoryMappedFileMediaType, region_sizes: &[u64])
                   -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(regions) => {
                    &&& regions.inv()
                    &&& regions@.no_outstanding_writes()
                    &&& regions@.len() == region_sizes@.len()
                    &&& forall |i| 0 <= i < region_sizes@.len() ==> #[trigger] regions@[i].len() == region_sizes@[i]
                },
                Err(_) => true
            }
    {
        Self::new_internal(
            path, media_type, region_sizes, FileOpenBehavior::OpenExisting, FileCloseBehavior::Persistent
        )
    }
}

impl PersistentMemoryRegions for FileBackedPersistentMemoryRegions {
    closed spec fn view(&self) -> PersistentMemoryRegionsView;
    closed spec fn inv(&self) -> bool;
    closed spec fn constants(&self) -> PersistentMemoryConstants;

    #[verifier::external_body]
    fn get_num_regions(&self) -> usize
    {
        self.regions.len()
    }

    #[verifier::external_body]
    fn get_region_size(&self, index: usize) -> u64
    {
        self.regions[index].get_region_size()
    }

    #[verifier::external_body]
    fn read(&self, index: usize, addr: u64, num_bytes: u64) -> (bytes: Vec<u8>)
    {
        self.regions[index].read(addr, num_bytes)
    }

    #[verifier::external_body]
    fn read_and_deserialize<S>(&self, index: usize, addr: u64) -> &S
        where
            S: Serializable + Sized
    {
        self.regions[index].read_and_deserialize(addr)
    }

    #[verifier::external_body]
    fn write(&mut self, index: usize, addr: u64, bytes: &[u8])
    {
        self.regions[index].write(addr, bytes)
    }

    #[verifier::external_body]
    fn serialize_and_write<S>(&mut self, index: usize, addr: u64, to_write: &S)
        where
            S: Serializable + Sized
    {
        self.regions[index].serialize_and_write(addr, to_write);
    }

    #[verifier::external_body]
    fn flush(&mut self)
    {
        match self.media_type {
            MemoryMappedFileMediaType::BatteryBackedDRAM => {
                // If using battery-backed DRAM, a single sfence
                // instruction will fence all of memory, so
                // there's no need to iterate through all the
                // regions. Also, there's no need to flush cache
                // lines, since those will be flushed during the
                // battery-enabled graceful shutdown after power
                // loss.
                unsafe {
                    core::arch::x86_64::_mm_sfence();
                }
            },
            _ => {
                for i in 0..self.regions.len() {
                    self.regions[i].flush();
                }
            },
        }
    }
}

}
