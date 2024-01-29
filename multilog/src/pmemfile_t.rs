//! This file contains the trusted implementation for
//! `FileBackedPersistentMemoryRegions`, a collection of persistent
//! memory regions backed by files. It implements trait
//! `PersistentMemoryRegions`.

use builtin::*;
use builtin_macros::*;
use crate::pmemspec_t::{PersistentMemoryByte, PersistentMemoryConstants, PersistentMemoryRegions,
                        PersistentMemoryRegionView, PersistentMemoryRegionsView};
use deps_hack::winapi::shared::winerror::SUCCEEDED;
use deps_hack::winapi::um::fileapi::{CreateFileA, OPEN_ALWAYS};
use deps_hack::winapi::um::handleapi::INVALID_HANDLE_VALUE;
use deps_hack::winapi::um::memoryapi::{MapViewOfFile, FILE_MAP_ALL_ACCESS};
use deps_hack::winapi::um::winbase::CreateFileMappingA;
use deps_hack::winapi::um::winnt::{PAGE_READWRITE, FILE_SHARE_WRITE, FILE_SHARE_READ, FILE_SHARE_DELETE, GENERIC_READ, GENERIC_WRITE, FILE_ATTRIBUTE_NORMAL, ULARGE_INTEGER};
use std::convert::*;
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

    // The `MemoryMappedFile` struct represents a memory-mapped file.

    #[verifier::external_body]
    pub struct MemoryMappedFile {
        pub media_type: MemoryMappedFileMediaType,         // type of media on which the file is stored
        pub size: usize,                                   // number of bytes in the file
        h_file: deps_hack::winapi::um::winnt::HANDLE,      // handle to the file
        h_map_file: deps_hack::winapi::um::winnt::HANDLE,  // handle to the mapping
        h_map_addr: deps_hack::winapi::um::winnt::HANDLE,  // address where file is mapped
        slice: &'static mut [u8],                          // above address viewed as a Rust slice
    }
    
    impl MemoryMappedFile {

        // The function `from_file` memory-maps a file and returns a
        // `MemoryMappedFile` to represent it.
    
        #[verifier::external_body]
        pub fn from_file(path: &StrSlice, size: usize, media_type: MemoryMappedFileMediaType) -> Self {
            unsafe {
                // Since str in rust is not null terminated, we need to convert it to a null-terminated string.
                let cstr = std::ffi::CString::new(path.into_rust_str()).unwrap();
    
                let h_file = CreateFileA(
                    cstr.as_ptr(),
                    GENERIC_READ | GENERIC_WRITE,
                    FILE_SHARE_WRITE | FILE_SHARE_READ | FILE_SHARE_DELETE,
                    core::ptr::null_mut(),
                    OPEN_ALWAYS,
                    FILE_ATTRIBUTE_NORMAL,
                    core::ptr::null_mut());
                
                let error_code = deps_hack::winapi::um::errhandlingapi::GetLastError();
    
                if h_file.is_null() {
                    panic!("Could not open file. err={}", error_code);
                }
    
                if h_file == INVALID_HANDLE_VALUE {
                    panic!("Could not find file. err={}", error_code);
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
                    panic!("Could not create file mapping object.");
                }
    
                // Map a view of the file mapping into the address space of the process
                let h_map_addr = MapViewOfFile(
                    h_map_file,
                    FILE_MAP_ALL_ACCESS,
                    0,
                    0,
                    size
                );
    
                if h_map_addr.is_null() {
                    panic!("Could not map view of file.");
                }

                // Convert the address into a static Rust slice.
                let slice = core::slice::from_raw_parts_mut(h_map_addr as *mut u8, size);
    
                MemoryMappedFile { media_type, size, h_file, h_map_file, h_map_addr, slice }
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
    
            self.slice[offset .. offset + data.len()].copy_from_slice(data);
    
            Ok(())
        }

        // The function `read_region` reads part of a memory-mapped a
        // file into a returned vector.
    
        #[inline(always)]
        #[verifier::external_body]
        pub fn read_region(&self, offset: usize, num_bytes: usize) -> Vec<u8>
        {
            self.slice[offset .. offset + num_bytes].to_vec()
        }

        // The function `flush` flushes updated parts of the
        // memory-mapped file back to the media.
    
        #[verifier::external_body]
        pub fn flush(&mut self) {
            unsafe {
                match self.media_type {
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
    
    impl Drop for MemoryMappedFile {
        #[verifier::external_body]
        fn drop(&mut self)
            opens_invariants none
        {
            unsafe {
                // Don't forget to unmap the view and close the handle when done
                deps_hack::winapi::um::memoryapi::UnmapViewOfFile(self.h_map_addr);
                deps_hack::winapi::um::handleapi::CloseHandle(self.h_map_file);
    
                if !self.h_file.is_null() {
                    deps_hack::winapi::um::handleapi::CloseHandle(self.h_file);
                }
            }
        }
    }
}

    unsafe impl Send for MemoryMappedFile {}
    unsafe impl Sync for MemoryMappedFile {}

verus! {

    // The `FileBackedPersistentMemoryRegion` struct represents a
    // persistent-memory region backed by a memory-mapped file.

    #[allow(dead_code)]
    pub struct FileBackedPersistentMemoryRegion
    {
        mmf: MemoryMappedFile,                                    // the memory-mapped file
        size: u64,                                                // the length of the file
        persistent_memory_view: Ghost<PersistentMemoryRegionView> // an abstract view of the contents
    }

    impl FileBackedPersistentMemoryRegion {

        // The static function `new` maps the file with the given path
        // into memory and returns a `FileBackedPersistentMemoryRegion`.
        
        #[verifier::external_body]
        pub fn new(file_path: &StrSlice, media_type: MemoryMappedFileMediaType, size: u64)
                   -> (result: Result<Self, ()>)
            ensures
                match result {
                    Ok(pm) => {
                        &&& pm@.len() == size
                        &&& pm.inv()
                        &&& pm@.no_outstanding_writes()
                    },
                    Err(_) => true
                }
        {
            // We don't really know what the contents of memory are,
            // so just make something up (all zeroes). The
            // postcondition doesn't expose the contents, so all
            // that matters is the length.
            let ghost state: Seq<PersistentMemoryByte> =
                Seq::<PersistentMemoryByte>::new(size as nat,
                                                 |i| PersistentMemoryByte {
                                                     state_at_last_flush: 0,
                                                     outstanding_write: None
                                                 });
            let ghost persistent_memory_view = PersistentMemoryRegionView{ state };
            let mmf = MemoryMappedFile::from_file(file_path, size as usize, media_type.clone());
            Ok(Self { mmf, size, persistent_memory_view: Ghost(persistent_memory_view) })
        }

        pub closed spec fn view(self) -> PersistentMemoryRegionView
        {
            self.persistent_memory_view@
        }

        pub closed spec fn inv(self) -> bool
        {
            self.size == self.persistent_memory_view@.len()
        }

        pub fn get_region_size(&self) -> (result: u64)
            requires
                self.inv()
            ensures
                result == self@.len()
        {
            self.size
        }

        #[verifier::external_body]
        pub fn read(&self, addr: u64, num_bytes: u64) -> (bytes: Vec<u8>)
            requires
                self.inv(),
                addr + num_bytes <= self@.len()
            ensures
                bytes@ == self@.committed().subrange(addr as int, addr + num_bytes)
        {
            let addr_usize: usize = addr.try_into().unwrap();
            let num_bytes_usize: usize = num_bytes.try_into().unwrap();
            self.mmf.read_region(addr_usize, num_bytes_usize)
        }

        #[verifier::external_body]
        pub fn write(&mut self, addr: u64, bytes: &[u8])
            requires
                old(self).inv(),
                addr + bytes@.len() <= old(self)@.len(),
                addr + bytes@.len() <= u64::MAX
            ensures
                self.inv(),
                self@ == self@.write(addr as int, bytes@)
        {
            let addr_usize: usize = addr.try_into().unwrap();
            let _ = self.mmf.update_region(addr_usize, bytes);
            self.persistent_memory_view = Ghost(self.persistent_memory_view@.write(addr as int, bytes@))
        }

        pub fn flush(&mut self)
            requires
                old(self).inv()
            ensures
                self.inv(),
                self@ == old(self)@.flush()
        {
            self.persistent_memory_view = Ghost(self.persistent_memory_view@.flush());
            self.mmf.flush();
        }
    }

    // The `FileBackedPersistentMemoryRegions` struct contains a
    // vector of volatile memory regions. It implements the trait
    // `PersistentMemoryRegions` so that it can be used by a multilog.
    
    pub struct FileBackedPersistentMemoryRegions
    {
        media_type: MemoryMappedFileMediaType,       // common media file type used
        pms: Vec<FileBackedPersistentMemoryRegion>,  // all regions
    }

    impl FileBackedPersistentMemoryRegions {

        // The static function `new` creates a
        // `FileBackedPersistentMemoryRegions` object using files in
        // the given directory of the given sizes.
        //
        // `dir_path` -- the directory in which to find files named
        //  log1, log2, ..., log<n> where <n> is the length of
        //  `region_sizes`
        //
        // `region_sizes` -- a vector of region sizes, where
        // `region_sizes[i]` is the length of file `log<i>`.

        #[verifier::external_body]
        pub fn new(dir_path: &StrSlice, media_type: MemoryMappedFileMediaType, region_sizes: &[u64])
                   -> (result: Result<Self, ()>)
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
            let mut pms = Vec::<FileBackedPersistentMemoryRegion>::new();
            let dir_path = dir_path.into_rust_str();
            for i in 0..region_sizes.len() {
                let region_size = region_sizes[i];
                let file_path = format!("{}/log{}", dir_path, i + 1);
                let file_path = StrSlice::from_rust_str(file_path.as_str());
                let pm = FileBackedPersistentMemoryRegion::new(&file_path, media_type.clone(), region_size)?;
                pms.push(pm);
            }
            Ok(Self { media_type, pms })
        }
    }

    impl PersistentMemoryRegions for FileBackedPersistentMemoryRegions {
        closed spec fn view(&self) -> PersistentMemoryRegionsView
        {
            PersistentMemoryRegionsView {
                regions: self.pms@.map(|_idx, pm: FileBackedPersistentMemoryRegion| pm@)
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

        #[verifier::external_body]
        fn write(&mut self, index: usize, addr: u64, bytes: &[u8])
        {
            self.pms[index].write(addr, bytes)
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
    }

}
