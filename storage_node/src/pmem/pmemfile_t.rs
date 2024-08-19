//! This file contains the trusted implementation for
//! `FileBackedPersistentMemoryRegions`, a collection of persistent
//! memory regions backed by files. It implements trait
//! `PersistentMemoryRegions`.
use crate::pmemspec_t::*;
use builtin::*;
use builtin_macros::*;
use deps_hack::winapi::shared::winerror::SUCCEEDED;
use deps_hack::winapi::um::fileapi::{CreateFileA, DeleteFileA, CREATE_NEW, OPEN_EXISTING};
use deps_hack::winapi::um::handleapi::INVALID_HANDLE_VALUE;
use deps_hack::winapi::um::memoryapi::{MapViewOfFile, FILE_MAP_ALL_ACCESS};
use deps_hack::winapi::um::winbase::CreateFileMappingA;
use deps_hack::winapi::um::winnt::{
    FILE_ATTRIBUTE_NORMAL, FILE_ATTRIBUTE_TEMPORARY, FILE_SHARE_DELETE, FILE_SHARE_READ,
    FILE_SHARE_WRITE, GENERIC_READ, GENERIC_WRITE, PAGE_READWRITE, ULARGE_INTEGER,
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

                // Map a view of the file mapping into the address space of the process
                let h_map_addr = MapViewOfFile(
                    h_map_file,
                    FILE_MAP_ALL_ACCESS,
                    0,
                    0,
                    size
                );

                if h_map_addr.is_null() {
                    panic!("Could not map view of file {}.", path);
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
    #[verus::trusted]
    pub struct FileBackedPersistentMemoryRegion
    {
        mmf: MemoryMappedFile,                                    // the memory-mapped file
        size: u64,                                                // the length of the file
        persistent_memory_view: Ghost<PersistentMemoryRegionView> // an abstract view of the contents
    }

    #[verus::trusted]
    impl FileBackedPersistentMemoryRegion {
        // The static function `new` creates the file with the given path,
        // maps it into memory, and returns a `FileBackedPersistentMemoryRegion`.

        #[verifier::external_body]
        pub fn new(file_path: &StrSlice, media_type: MemoryMappedFileMediaType, size: u64,
                   close_behavior: FileCloseBehavior)
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
            let mmf = MemoryMappedFile::from_file(file_path, size as usize, media_type.clone(),
                                                  FileOpenBehavior::CreateNew, close_behavior);
            Ok(Self { mmf, size, persistent_memory_view: Ghost(persistent_memory_view) })
        }

        // The static function `restore` maps the existing file with the given path
        // into memory and returns a `FileBackedPersistentMemoryRegion`.

        #[verifier::external_body]
        pub fn restore(file_path: &StrSlice, media_type: MemoryMappedFileMediaType, size: u64)
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
            let mmf = MemoryMappedFile::from_file(file_path, size as usize, media_type.clone(),
                                                  FileOpenBehavior::OpenExisting, FileCloseBehavior::Persistent);
            Ok(Self { mmf, size, persistent_memory_view: Ghost(persistent_memory_view) })
        }
    }

    #[verus::trusted]
    impl PersistentMemoryRegion for FileBackedPersistentMemoryRegion
    {
        closed spec fn view(self) -> PersistentMemoryRegionView
        {
            self.persistent_memory_view@
        }

        closed spec fn inv(self) -> bool
        {
            self.size == self.persistent_memory_view@.len()
        }

        fn get_region_size(&self) -> (result: u64)
        {
            self.size
        }

        #[verifier::external_body]
        fn read(&self, addr: u64, num_bytes: u64) -> (bytes: Vec<u8>)
        {
            let addr_usize: usize = addr.try_into().unwrap();
            let num_bytes_usize: usize = num_bytes.try_into().unwrap();
            self.mmf.read_region(addr_usize, num_bytes_usize)
        }

        #[verifier::external_body]
        fn write(&mut self, addr: u64, bytes: &[u8])
        {
            let addr_usize: usize = addr.try_into().unwrap();
            let _ = self.mmf.update_region(addr_usize, bytes);
            self.persistent_memory_view = Ghost(self.persistent_memory_view@.write(addr as int, bytes@))
        }

        fn flush(&mut self)
        {
            self.persistent_memory_view = Ghost(self.persistent_memory_view@.flush());
            self.mmf.flush();
        }
    }

    // The `FileBackedPersistentMemoryRegions` struct contains a
    // vector of volatile memory regions. It implements the trait
    // `PersistentMemoryRegions` so that it can be used by a multilog.

    #[verus::trusted]
    pub struct FileBackedPersistentMemoryRegions
    {
        media_type: MemoryMappedFileMediaType,       // common media file type used
        pms: Vec<FileBackedPersistentMemoryRegion>,  // all regions
    }

    #[verus::trusted]
    impl FileBackedPersistentMemoryRegions {

        // The static function `new` creates a
        // `FileBackedPersistentMemoryRegions` object by creating
        // files of the given sizes using the given path prefix.
        // Region #1 will be in `path_prefix + "1"`, region #2
        // will be in `path_prefix + "2"`, etc.
        //
        // `path_prefix` -- the prefix of file paths to use
        //  log1, log2, ..., log<n> where <n> is the length of
        //  `region_sizes`
        //
        // `region_sizes` -- a vector of region sizes, where
        // `region_sizes[i]` is the length of file `log<i>`.

        #[verifier::external_body]
        pub fn new(path_prefix: &StrSlice, media_type: MemoryMappedFileMediaType, region_sizes: &[u64],
                   close_behavior: FileCloseBehavior)
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
            let path_prefix = path_prefix.into_rust_str();
            for i in 0..region_sizes.len() {
                let region_size = region_sizes[i];
                let file_path = format!("{}{}", path_prefix, i + 1);
                let file_path = StrSlice::from_rust_str(file_path.as_str());
                let pm = FileBackedPersistentMemoryRegion::new(&file_path, media_type.clone(), region_size,
                                                               close_behavior)?;
                pms.push(pm);
            }
            Ok(Self { media_type, pms })
        }

        // The static function `restore` creates a
        // `FileBackedPersistentMemoryRegions` object using existing
        // files of the given sizes using the given path prefix.
        // Region #1 will be in `path_prefix + "1"`, region #2
        // will be in `path_prefix + "2"`, etc.
        //
        // `path_prefix` -- the prefix of file paths to use
        //  log1, log2, ..., log<n> where <n> is the length of
        //  `region_sizes`
        //
        // `region_sizes` -- a vector of region sizes, where
        // `region_sizes[i]` is the length of file `log<i>`.

        #[verifier::external_body]
        pub fn restore(path_prefix: &StrSlice, media_type: MemoryMappedFileMediaType, region_sizes: &[u64])
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
            let path_prefix = path_prefix.into_rust_str();
            for i in 0..region_sizes.len() {
                let region_size = region_sizes[i];
                let file_path = format!("{}{}", path_prefix, i + 1);
                let file_path = StrSlice::from_rust_str(file_path.as_str());
                let pm = FileBackedPersistentMemoryRegion::restore(&file_path, media_type.clone(), region_size)?;
                pms.push(pm);
            }
            Ok(Self { media_type, pms })
        }
    }

    #[verus::trusted]
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
