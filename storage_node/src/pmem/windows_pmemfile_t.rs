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
use crate::pmem::device_t::*;
use crate::pmem::serialization_t::*;
use crate::pmem::timestamp_t::*;
use builtin::*;
use builtin_macros::*;
use deps_hack::rand::Rng;
use deps_hack::winapi::shared::winerror::SUCCEEDED;
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
    
// Must be external body because Verus does not currently support raw pointers
// TODO: is there a better/safer way to handle this? UnsafeCell maybe?
#[verifier::external_body]
#[derive(Clone, Copy)]
pub struct WindowsHandle {
    pub h: deps_hack::winapi::um::winnt::HANDLE,
}

#[verifier::external_body]
pub struct ByteSlice {
    pub slice: &'static mut [u8],
}


// The `MemoryMappedFile` struct represents a memory-mapped file.

pub struct MemoryMappedFile {
    pub media_type: MemoryMappedFileMediaType,  // type of media on which the file is stored
    pub size: usize,                            // number of bytes in the file
    pub h_file: WindowsHandle,                  // handle to the file
    pub h_map_file: WindowsHandle,              // handle to the mapping
}

impl MemoryMappedFile {

    // The function `from_file` memory-maps a file and returns a
    // `MemoryMappedFile` to represent it.

    #[verifier::external_body]
    pub fn from_file(path: &StrSlice, size: usize, media_type: MemoryMappedFileMediaType,
                     open_behavior: FileOpenBehavior, close_behavior: FileCloseBehavior) -> Self {
        unsafe {
            let path = path.into_rust_str();
            // Since str in rust is not null terminated, we need to convert it to a null-terminated string.
            let path_cstr = std::ffi::CString::new(path).unwrap();

            let create_or_open = match open_behavior {
                FileOpenBehavior::CreateNew => CREATE_NEW,
                FileOpenBehavior::OpenExisting => OPEN_EXISTING,
            };
            let attributes = match close_behavior {
                FileCloseBehavior::TestingSoDeleteOnClose => FILE_ATTRIBUTE_TEMPORARY,
                FileCloseBehavior::Persistent => FILE_ATTRIBUTE_NORMAL,
            };
            let h_file = CreateFileA(
                path_cstr.as_ptr(),
                GENERIC_READ | GENERIC_WRITE,
                FILE_SHARE_WRITE | FILE_SHARE_READ | FILE_SHARE_DELETE,
                core::ptr::null_mut(),
                create_or_open,
                attributes,
                core::ptr::null_mut());

            let error_code = deps_hack::winapi::um::errhandlingapi::GetLastError();

            if h_file.is_null() {
                panic!("Could not open file {}. err={}", path, error_code);
            }

            if h_file == INVALID_HANDLE_VALUE {
                panic!("Could not find file {}. err={}", path, error_code);
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
                panic!("Could not create file mapping object for {}.", path);
            }

            if let FileCloseBehavior::TestingSoDeleteOnClose = close_behavior {
                // After opening the file, mark it for deletion when the file is closed.
                // Obviously, we should only do this during testing!
                deps_hack::winapi::um::fileapi::DeleteFileA(path_cstr.as_ptr());
            }

            MemoryMappedFile {
                media_type,
                size,
                h_file: WindowsHandle{ h: h_file },
                h_map_file: WindowsHandle{ h: h_map_file },
            }
        }
    }
}

impl Drop for MemoryMappedFile {
    #[verifier::external_body]
    fn drop(&mut self)
        opens_invariants none
    {
        unsafe {
            deps_hack::winapi::um::handleapi::CloseHandle(self.h_map_file.h);

            if !self.h_file.h.is_null() {
                deps_hack::winapi::um::handleapi::CloseHandle(self.h_file.h);
            }
        }
    }
}

// The `MemoryMappedFileSection` struct represents a section of a memory-mapped file.

pub struct MemoryMappedFileSection {
    pub mmf: std::rc::Rc<MemoryMappedFile>,  // reference to the MemoryMappedFile this is part of
    pub size: usize,                         // number of bytes in the section
    pub h_map_addr: WindowsHandle,           // address of the first byte of the section
    pub slice: ByteSlice,                    // above address viewed as a Rust slice
}

impl MemoryMappedFileSection {
    #[verifier::external_body]
    pub fn new(mmf: std::rc::Rc<MemoryMappedFile>, offset: usize, len: usize) -> (result: Self)
        requires
            offset + len <= mmf.size,
    {
        // Map a view of the file mapping into the address space of the process
        let h_map_addr = unsafe { MapViewOfFile(
            mmf.h_map_file.h,
            FILE_MAP_ALL_ACCESS,
            (offset / 0x100000000).try_into().unwrap(),
            (offset % 0x100000000).try_into().unwrap(),
            len.try_into().unwrap(),
        ) };

        if h_map_addr.is_null() {
            panic!("Could not map view of file");
        }

        // Convert the address into a static Rust slice.
        let slice = unsafe { core::slice::from_raw_parts_mut(h_map_addr as *mut u8, len) };

        Self {
            mmf: mmf.clone(),
            size: len,
            h_map_addr: WindowsHandle{ h: h_map_addr },
            slice: ByteSlice{ slice: slice },
        }
    }

    // The function `update_region` updates part of a
    // memory-mapped a file. Specifically, it overwrites the
    // contents starting at offset `offset` with the data in
    // slice `data`.

    #[inline(always)]
    #[verifier::external_body]
    pub fn update_region(&mut self, offset: usize, data: &[u8]) -> Result<(), ()> {
        if offset + data.len() > self.size {
            return Err(())
        }

        self.slice.slice[offset .. offset + data.len()].copy_from_slice(data);

        Ok(())
    }

    // The function `read_region` reads part of a memory-mapped a
    // file into a returned vector.

    #[inline(always)]
    #[verifier::external_body]
    pub fn read_region(&self, offset: usize, num_bytes: usize) -> Vec<u8>
    {
        self.slice.slice[offset .. offset + num_bytes].to_vec()
    }

    // The function `flush` flushes updated parts of the
    // memory-mapped file back to the media.

    #[verifier::external_body]
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
                        self.h_map_addr.h as *const deps_hack::winapi::ctypes::c_void,
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

impl Drop for MemoryMappedFileSection {
    #[verifier::external_body]
    fn drop(&mut self)
        opens_invariants none
    {
        unsafe {
            deps_hack::winapi::um::memoryapi::UnmapViewOfFile(self.h_map_addr.h);
        }
    }
}

}

unsafe impl Send for MemoryMappedFile {}
unsafe impl Sync for MemoryMappedFile {}

verus! {

// This executable method can be called to compute a random GUID.
// It uses the external `rand` crate.
#[verifier::external_body]
pub exec fn generate_fresh_device_id() -> (out: u128)
{
    deps_hack::rand::thread_rng().gen::<u128>()
}

pub struct FileBackedPersistentMemoryRegionDescription
{
    mmf: std::rc::Rc<MemoryMappedFile>,  // the memory-mapped file
    offset: u64,                         // the offset into the file where the region starts
    size: u64,                           // the length of the region
    device_id: u128,                     // device ID
    timestamp: Ghost<PmTimestamp>,       // timestamp of last flush
}

impl RegionDescriptor for FileBackedPersistentMemoryRegionDescription
{
    closed spec fn view(&self) -> RegionDescriptorView {
        RegionDescriptorView {
            len: self.size,
            timestamp: self.timestamp@,
            device_id: self.device_id,
        }
    }

    fn device_id(&self) -> u128 {
        self.device_id
    }

    fn len(&self) -> u64 {
        self.size
    }
}

pub struct FileBackedPersistentMemoryDevice
{
    mmf: std::rc::Rc<MemoryMappedFile>, // the memory-mapped file
    size: u64,                          // the length of the file
    device_id: u128,                    // device ID
    cursor: u64,                        // offset beyond which file hasn't yet been allocated to regions
}

impl PmDevice for FileBackedPersistentMemoryDevice
{
    type RegionDesc = FileBackedPersistentMemoryRegionDescription;

    closed spec fn len(&self) -> u64
    {
        self.size
    }

    fn capacity(&self) -> u64
    {
        self.size
    }

    closed spec fn spec_device_id(&self) -> u128
    {
        self.device_id
    }

    fn device_id(&self) -> u128
    {
        self.device_id
    }

    closed spec fn spec_get_cursor(&self) -> Option<u64>
    {
        if self.cursor >= self.size {
            None
        } else {
            Some(self.cursor)
        }
    }

    fn get_cursor(&self) -> Option<u64>
    {
        if self.cursor >= self.size {
            None
        } else {
            Some(self.cursor)
        }
    }

    fn inc_cursor(&mut self, len: u64)
    {
        self.cursor = self.cursor + len;
    }

    // Must be external body to operate on raw pointers
    #[verifier::external_body]
    fn get_new_region(&mut self, len: u64) -> Result<Self::RegionDesc, PmemError>
    {
        let offset = self.cursor;
        self.inc_cursor(len);
        Ok(FileBackedPersistentMemoryRegionDescription {
            mmf: self.mmf.clone(),
            offset,
            size: len,
            timestamp: Ghost(PmTimestamp::new(self.spec_device_id() as int)),
            device_id: self.device_id()
        })
    }
}

impl FileBackedPersistentMemoryDevice
{
    // The static function `new` creates the file with the given path,
    // maps it into memory, and returns a `FileBackedPersistentMemoryDevice`.

    #[verifier::external_body]
    pub fn new(file_path: &StrSlice, media_type: MemoryMappedFileMediaType, size: u64,
               close_behavior: FileCloseBehavior)
               -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(pm) => pm.len() == size,
                Err(_) => true
            }
    {
        let mmf = MemoryMappedFile::from_file(file_path, size as usize, media_type.clone(),
                                              FileOpenBehavior::CreateNew, close_behavior);
        Ok(Self {
            mmf: std::rc::Rc::new(mmf),
            size,
            device_id: generate_fresh_device_id(),
            cursor: 0
        })
    }

    // The static function `restore` maps the existing file with the given path
    // into memory and returns a `FileBackedPersistentMemoryRegion`.

    #[verifier::external_body]
    pub fn restore(file_path: &StrSlice, media_type: MemoryMappedFileMediaType, size: u64)
                  -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(pm) => pm.len() == size,
                Err(_) => true
            }
    {
        let mmf = MemoryMappedFile::from_file(file_path, size as usize, media_type.clone(),
                                              FileOpenBehavior::OpenExisting, FileCloseBehavior::Persistent);
        Ok(Self {
            mmf: std::rc::Rc::new(mmf),
            size,
            device_id: generate_fresh_device_id(),
            cursor: 0
        })
    }
}

// The `FileBackedPersistentMemoryRegion` struct represents a
// persistent-memory region backed by a memory-mapped file.

#[allow(dead_code)]
pub struct FileBackedPersistentMemoryRegion
{
    pub section: MemoryMappedFileSection,                          // the memory-mapped file section
    pub persistent_memory_view: Ghost<PersistentMemoryRegionView>, // an abstract view of the contents
    pub device_id: u128,                                           // device ID
    pub timestamp: Ghost<PmTimestamp>,                             // timestamp of last flush
}

impl PersistentMemoryRegion for FileBackedPersistentMemoryRegion
{
    type RegionDesc = FileBackedPersistentMemoryRegionDescription;

    closed spec fn view(&self) -> PersistentMemoryRegionView
    {
        self.persistent_memory_view@
    }

    closed spec fn inv(&self) -> bool
    {
        &&& self@.len() == self.section.size
        &&& self.device_id == self@.device_id
        &&& self@.timestamp.device_id() == self.spec_device_id()
    }

    fn device_id(&self) -> u128
    {
        self.device_id
    }

    closed spec fn spec_device_id(&self) -> u128
    {
        self.device_id
    }

    fn get_region_size(&self) -> u64
    {
        self.section.size as u64
    }

    #[verifier::external_body]
    fn new(region_descriptor: Self::RegionDesc) -> Result<Self, PmemError>
    {
        // We don't really know what the contents of memory are,
        // so just make something up (all zeroes). The
        // postcondition doesn't expose the contents, so all
        // that matters is the length.
        let ghost state = Seq::new(
            region_descriptor.size as nat,
            |i| PersistentMemoryByte {
                state_at_last_flush: 0,
                outstanding_write: None,
            }
        );
        let persistent_memory_view = Ghost(
            PersistentMemoryRegionView {
                state,
                device_id: region_descriptor.device_id,
                timestamp: region_descriptor@.timestamp
            }
        );
        let section = MemoryMappedFileSection::new(
            region_descriptor.mmf,
            region_descriptor.offset.try_into().unwrap(),
            region_descriptor.size.try_into().unwrap(),
        );
        Ok(Self {
            section,
            persistent_memory_view,
            device_id: region_descriptor.device_id,
            timestamp: region_descriptor.timestamp,
        })
    }

    #[verifier::external_body]
    fn read(&self, addr: u64, num_bytes: u64) -> (bytes: Vec<u8>)
    {
        let addr_usize: usize = addr.try_into().unwrap();
        let num_bytes_usize: usize = num_bytes.try_into().unwrap();
        self.section.read_region(addr_usize, num_bytes_usize)
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
            (self.section.h_map_addr.h as *const u8).offset(addr.try_into().unwrap())
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
        let addr_usize: usize = addr.try_into().unwrap();
        let _ = self.section.update_region(addr_usize, bytes);
        self.persistent_memory_view = Ghost(self.persistent_memory_view@.write(addr as int, bytes@))
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
            (self.section.h_map_addr.h as *mut u8).offset(addr.try_into().unwrap())
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
        self.persistent_memory_view = Ghost(self.persistent_memory_view@.flush());
        self.section.flush();
    }

    #[allow(unused_variables)]
    fn update_region_timestamp(&mut self, new_timestamp: Ghost<PmTimestamp>)
    {
        self.persistent_memory_view = Ghost(self.persistent_memory_view@.update_region_with_timestamp(new_timestamp@));
    }
}

// The `FileBackedPersistentMemoryRegions` struct contains a
// vector of volatile memory regions. It implements the trait
// `PersistentMemoryRegions` so that it can be used by a multilog.

pub struct FileBackedPersistentMemoryRegions
{
    media_type: MemoryMappedFileMediaType,       // common media file type used
    dev: FileBackedPersistentMemoryDevice,       // device corresponding to the file all regions are part of
    pms: Vec<FileBackedPersistentMemoryRegion>,  // all regions
}

impl FileBackedPersistentMemoryRegions {

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
    #[verifier::external_body]
    pub fn new(path: &StrSlice, media_type: MemoryMappedFileMediaType, region_sizes: &[u64],
               close_behavior: FileCloseBehavior)
               -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(pm_regions) => {
                    &&& pm_regions.inv()
                    &&& pm_regions@.no_outstanding_writes()
                    &&& pm_regions@.len() == region_sizes@.len()
                    &&& forall |i| 0 <= i < region_sizes@.len() ==> #[trigger] pm_regions@[i].len() == region_sizes@[i]
                },
                Err(_) => true
            }
    {
        let mut total_size = 0;
        for region_size in region_sizes {
            total_size = total_size + region_size;
        }
        let mut dev = FileBackedPersistentMemoryDevice::new(&path, media_type.clone(), total_size, close_behavior)?;
        let mut pms = Vec::<FileBackedPersistentMemoryRegion>::new();
        for i in 0..region_sizes.len() {
            let region_size = region_sizes[i];
            let region_desc = dev.get_new_region(region_size)?;
            let pm = FileBackedPersistentMemoryRegion::new(region_desc)?;
            pms.push(pm);
        }
        Ok(Self { media_type, dev, pms })
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
    #[verifier::external_body]
    pub fn restore(path: &StrSlice, media_type: MemoryMappedFileMediaType, region_sizes: &[u64])
                   -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(pm_regions) => {
                    &&& pm_regions.inv()
                    &&& pm_regions@.no_outstanding_writes()
                    &&& pm_regions@.len() == region_sizes@.len()
                    &&& forall |i| 0 <= i < region_sizes@.len() ==> #[trigger] pm_regions@[i].len() == region_sizes@[i]
                },
                Err(_) => true
            }
    {
        let mut total_size = 0;
        for region_size in region_sizes {
            total_size = total_size + region_size;
        }
        let mut dev = FileBackedPersistentMemoryDevice::restore(&path, media_type.clone(), total_size)?;
        let mut pms = Vec::<FileBackedPersistentMemoryRegion>::new();
        for i in 0..region_sizes.len() {
            let region_size = region_sizes[i];
            let region_desc = dev.get_new_region(region_size)?;
            let pm = FileBackedPersistentMemoryRegion::new(region_desc)?;
            pms.push(pm);
        }
        Ok(Self { media_type, dev, pms })
    }
}

impl PersistentMemoryRegions for FileBackedPersistentMemoryRegions {
    closed spec fn view(&self) -> PersistentMemoryRegionsView
    {
        PersistentMemoryRegionsView {
            regions: self.pms@.map(|_idx, pm: FileBackedPersistentMemoryRegion| pm@),
            timestamp: self.pms[0]@.timestamp,
            device_id: self.dev.device_id,
        }
    }

    closed spec fn inv(&self) -> bool
    {
        forall |i: int| #![trigger(self.pms[i])] 0 <= i < self.pms.len() ==> self.pms[i].inv()
    }

    closed spec fn constants(&self) -> PersistentMemoryConstants
    {
        PersistentMemoryConstants { impervious_to_corruption: true }
    }

    closed spec fn spec_device_id(&self) -> u128
    {
        self.dev.spec_device_id()
    }

    fn device_id(&self) -> (result: u128)
    {
        self.dev.device_id()
    }

    fn get_num_regions(&self) -> usize
    {
        self.pms.len()
    }

    fn get_region_size(&self, index: usize) -> u64
    {
        self.pms[index].get_region_size()
    }

    fn read(&self, index: usize, addr: u64, num_bytes: u64) -> (bytes: Vec<u8>)
    {
        self.pms[index].read(addr, num_bytes)
    }

    fn read_and_deserialize<S>(&self, index: usize, addr: u64) -> &S
        where
            S: Serializable + Sized
    {
        self.pms[index].read_and_deserialize(addr)
    }

    #[verifier::external_body]
    fn write(&mut self, index: usize, addr: u64, bytes: &[u8])
    {
        self.pms[index].write(addr, bytes)
    }

    #[verifier::external_body]
    fn serialize_and_write<S>(&mut self, index: usize, addr: u64, to_write: &S)
        where
            S: Serializable + Sized
    {
        self.pms[index].serialize_and_write(addr, to_write);
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
                for i in 0..self.pms.len() {
                    self.pms[i].flush();
                }
            },
        }
    }

    #[verifier::external_body]
    fn update_timestamps(&mut self, new_timestamp: Ghost<PmTimestamp>)
    {
        for i in iter: 0..self.pms.len()
            invariant
                iter.end == self.pms.len(),
        {
            self.pms[i].update_region_timestamp(new_timestamp);
        }
    }
}

}
