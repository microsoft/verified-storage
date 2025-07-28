#![cfg_attr(verus_keep_ghost, verus::trusted)]
//
// MacOSX does not support PMDK, so we simply support mmap-based
// memory-mapped files, for development purposes.
//
// This file implements the `FileBackedPersistentMemoryRegions` type, which
// simulates a persistent memory region backed by a file. The type implements the
// `PersistentMemoryRegions` trait, allowing operations like reading, writing, and flushing.
// Besides that, it also implements static functions `new` and `restore`. `new` creates
// a new file with unknown contents; `restore` opens an existing file, so named because
// it's typically used after a crash and restart to restore system state.

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use core::ffi::c_void;
use core::slice;
use std::{cell::RefCell, convert::TryInto, ffi::CString, rc::Rc};

use deps_hack::memmap::MmapMut;
use std::fs::OpenOptions;

use vstd::prelude::*;

pub struct MemoryMappedFile {
    mmap: MmapMut,
    num_bytes_sectioned: usize,
}

impl MemoryMappedFile {
    fn from_file<'a>(
        file_to_map: &str,
        size: usize,
        file_open_behavior: FileOpenBehavior,
    ) -> Result<Self, PmemError> {
        let file;
        match file_open_behavior {
            FileOpenBehavior::CreateNew => {
                file = match OpenOptions::new()
                    .read(true)
                    .write(true)
                    .create_new(true)
                    .open(file_to_map)
                {
                    Ok(file) => file,
                    Err(e) => {
                        eprintln!("open: {:?}", e);
                        return Err(PmemError::CannotOpenPmFile);
                    }
                };

                match file.set_len(size as u64) {
                    Ok(_) => (),
                    Err(e) => {
                        eprintln!("set_len: {:?}", e);
                        return Err(PmemError::CannotOpenPmFile);
                    }
                };
            }
            FileOpenBehavior::OpenExisting => {
                file = match OpenOptions::new().read(true).write(true).open(file_to_map) {
                    Ok(file) => file,
                    Err(e) => {
                        eprintln!("open: {:?}", e);
                        return Err(PmemError::CannotOpenPmFile);
                    }
                };
            }
        };

        let mmap = match unsafe { MmapMut::map_mut(&file) } {
            Ok(mmap) => mmap,
            Err(e) => {
                eprintln!("mmap: {:?}", e);
                return Err(PmemError::CannotOpenPmFile);
            }
        };

        Ok(Self {
            mmap: mmap,
            num_bytes_sectioned: 0,
        })
    }
}

verus! {

#[verifier::external_body]
pub struct MemoryMappedFileSection {
    mmf: Rc<RefCell<MemoryMappedFile>>,
    offset: usize,
    size: usize,
}

impl MemoryMappedFileSection {
    #[verifier::external]
    fn new(mmf: Rc<RefCell<MemoryMappedFile>>, len: usize) -> Result<Self, PmemError> {
        let mut mmf_borrowed = mmf.borrow_mut();
        let offset = mmf_borrowed.num_bytes_sectioned;

        if len > mmf_borrowed.mmap.len() - offset {
            eprintln!("Can't allocate {} bytes because only {} remain", len, mmf_borrowed.mmap.len() - offset);
            return Err(PmemError::AccessOutOfRange);
        }
        mmf_borrowed.num_bytes_sectioned += len;

        std::mem::drop(mmf_borrowed);

        let section = Self {
            mmf,
            offset: offset,
            size: len,
        };
        Ok(section)
    }
}

#[derive(Clone, Copy)]
pub enum FileOpenBehavior {
    CreateNew,
    OpenExisting,
}

pub struct FileBackedPersistentMemoryRegion {
    section: MemoryMappedFileSection,
}

impl FileBackedPersistentMemoryRegion {
    #[verifier::external_body]
    fn new_internal(path: &str, region_size: u64, open_behavior: FileOpenBehavior) -> (result:
        Result<Self, PmemError>)
        ensures
            match result {
                Ok(region) => region.inv() && region@.len() == region_size,
                Err(_) => true,
            },
    {
        let mmf = MemoryMappedFile::from_file(path, region_size as usize, open_behavior)?;
        let mmf = Rc::<RefCell<MemoryMappedFile>>::new(RefCell::<MemoryMappedFile>::new(mmf));
        let section = MemoryMappedFileSection::new(mmf, region_size as usize)?;
        Ok(Self { section })
    }

    pub fn new(path: &str, region_size: u64) -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(region) => region.inv() && region@.len() == region_size,
                Err(_) => true,
            },
    {
        Self::new_internal(path, region_size, FileOpenBehavior::CreateNew)
    }

    pub fn restore(path: &str, region_size: u64) -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(region) => region.inv() && region@.len() == region_size,
                Err(_) => true,
            },
    {
        Self::new_internal(path, region_size, FileOpenBehavior::OpenExisting)
    }

    #[verifier::external_body]
    fn new_from_section(section: MemoryMappedFileSection) -> (result: Self) {
        Self { section }
    }
}

impl PersistentMemoryRegion for FileBackedPersistentMemoryRegion {
    uninterp spec fn view(&self) -> PersistentMemoryRegionView;

    uninterp spec fn constants(&self) -> PersistentMemoryConstants;

    uninterp spec fn inv(&self) -> bool;

    #[verifier::external_body]
    fn get_region_size(&self) -> u64 {
        self.section.size as u64
    }

    #[verifier::external_body]
    fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<
        MaybeCorruptedBytes<S>,
        PmemError,
    >) where S: PmCopy {
        let addr = addr + self.section.offset as u64;
        let mmf_borrowed = self.section.mmf.borrow_mut();
        let pm_slice: &[u8] = &mmf_borrowed.mmap[addr as usize..addr as usize + S::size_of()];

        let ghost addrs = Seq::new(S::spec_size_of() as nat, |i: int| addr + i);
        let ghost true_bytes = self@.committed().subrange(addr as int, addr + S::spec_size_of());
        let ghost true_val = S::spec_from_bytes(true_bytes);
        let mut maybe_corrupted_val = MaybeCorruptedBytes::new();

        maybe_corrupted_val.copy_from_slice(
            pm_slice,
            Ghost(true_val),
            Ghost(addrs),
            Ghost(self.constants().impervious_to_corruption),
        );

        Ok(maybe_corrupted_val)
    }

    #[verifier::external_body]
    fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>) {
        let addr = addr + self.section.offset as u64;
        let mmf_borrowed = self.section.mmf.borrow_mut();
        let pm_slice: &[u8] = &mmf_borrowed.mmap[addr as usize..(addr + num_bytes) as usize];

        // Allocate an unaligned buffer to copy the bytes into
        let unaligned_buffer = copy_from_slice(pm_slice);

        Ok(unaligned_buffer)
    }

    #[verifier::external_body]
    fn write(&mut self, addr: u64, bytes: &[u8]) {
        let addr = addr + self.section.offset as u64;
        let mut mmf_borrowed = self.section.mmf.borrow_mut();
        mmf_borrowed.mmap[addr as usize..addr as usize + bytes.len()].copy_from_slice(bytes);
    }

    #[verifier::external_body]
    #[allow(unused_variables)]
    fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S) where S: PmCopy + Sized {
        let addr = addr + self.section.offset as u64;
        let num_bytes: usize = S::size_of() as usize;

        // convert the given &S to a pointer, then a slice of bytes
        let s_pointer = to_write as *const S as *const u8;
        let s_slice = unsafe { std::slice::from_raw_parts(s_pointer, num_bytes) };

        let mut mmf_borrowed = self.section.mmf.borrow_mut();
        mmf_borrowed.mmap[addr as usize..addr as usize + num_bytes].copy_from_slice(s_slice);
    }

    #[verifier::external_body]
    fn flush(&mut self) {
        let mmf_borrowed = self.section.mmf.borrow_mut();
        match mmf_borrowed.mmap.flush() {
            Ok(_) => (),
            Err(e) => {
                eprintln!("flush: {:?}", e);
            },
        };
    }
}

pub struct FileBackedPersistentMemoryRegions {
    regions: Vec<FileBackedPersistentMemoryRegion>,
}

impl FileBackedPersistentMemoryRegions {
    // TODO: detailed information for error returns
    #[verifier::external_body]
    #[allow(dead_code)]
    pub fn new_internal(path: &str, region_sizes: &[u64], open_behavior: FileOpenBehavior) 
            -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(regions) => {
                    &&& regions.inv()
                    &&& regions@.no_outstanding_writes()
                    &&& regions@.len() == region_sizes@.len()
                    &&& forall |i| 0 <= i < regions@.len() ==> #[trigger] regions@[i].len() == region_sizes@[i]
                },
                Err(_) => true,
            }
    {
        let mut total_size: usize = 0;
        for &region_size in region_sizes {
            let region_size = region_size as usize;
            if region_size >= usize::MAX - total_size {
                return Err(PmemError::AccessOutOfRange);
            }
            total_size += region_size;
        }
        let mmf = MemoryMappedFile::from_file(
            path,
            total_size,
            open_behavior
        )?;
        let mmf = Rc::<RefCell<MemoryMappedFile>>::new(RefCell::<MemoryMappedFile>::new(mmf));
        let mut regions = Vec::<FileBackedPersistentMemoryRegion>::new();
        for &region_size in region_sizes {
            let region_size: usize = region_size as usize;
            let section = MemoryMappedFileSection::new(mmf.clone(), region_size)?;
            let region = FileBackedPersistentMemoryRegion::new_from_section(section);
            regions.push(region);
        }
        Ok(Self { regions })
    }
    
    pub fn new(path: &str, region_sizes: &[u64])
               -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(regions) => {
                    &&& regions.inv()
                    &&& regions@.no_outstanding_writes()
                    &&& regions@.len() == region_sizes@.len()
                    &&& forall |i| 0 <= i < regions@.len() ==> #[trigger] regions@[i].len() == region_sizes@[i]
                },
                Err(_) => true,
            }
    {
        Self::new_internal(path, region_sizes, FileOpenBehavior::CreateNew)
    }
    
    pub fn restore(path: &str, region_sizes: &[u64])
                   -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(regions) => {
                    &&& regions.inv()
                    &&& regions@.no_outstanding_writes()
                    &&& regions@.len() == region_sizes@.len()
                    &&& forall |i| 0 <= i < regions@.len() ==> #[trigger] regions@[i].len() == region_sizes@[i]
                },
                Err(_) => true,
            }
    {
        Self::new_internal(path, region_sizes, FileOpenBehavior::OpenExisting)
    }
}

impl PersistentMemoryRegions for FileBackedPersistentMemoryRegions {
    uninterp spec fn view(&self) -> PersistentMemoryRegionsView;
    uninterp spec fn inv(&self) -> bool;
    uninterp spec fn constants(&self) -> PersistentMemoryConstants;

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
    fn read_aligned<S>(&self, index: usize, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy
    {
        self.regions[index].read_aligned::<S>(addr)
    }

    #[verifier::external_body]
    fn read_unaligned(&self, index: usize, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>)
    {
        self.regions[index].read_unaligned(addr, num_bytes)
    }

    #[verifier::external_body]
    fn write(&mut self, index: usize, addr: u64, bytes: &[u8])
    {
        self.regions[index].write(addr, bytes)
    }

    #[verifier::external_body]
    fn serialize_and_write<S>(&mut self, index: usize, addr: u64, to_write: &S)
        where
            S: PmCopy + Sized
    {
        self.regions[index].serialize_and_write(addr, to_write);
    }

    #[verifier::external_body]
    fn flush(&mut self)
    {
        for region in &mut self.regions {
            region.flush();
        }
    }
}

}