use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use core::ffi::c_void;
use std::{convert::TryInto, ffi::CString};

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use deps_hack::{
    pmem::pmem_memcpy_nodrain_helper, pmem_drain, pmem_errormsg, pmem_flush, pmem_map_file,
    pmem_memcpy_nodrain, pmem_unmap, rand::Rng, PMEM_FILE_CREATE, PMEM_FILE_EXCL,
};

#[verifier::external_body]
pub struct MemoryMappedFile {
    virt_addr: *mut u8,
    size: usize,
}

impl Drop for MemoryMappedFile
{
    fn drop(&mut self)
    {
        unsafe { pmem_unmap(self.virt_addr as *mut c_void, self.size) };
    }
}

impl MemoryMappedFile
{
    // TODO: detailed information for error returns
    fn from_file<'a>(file_to_map: &str, size: usize, file_open_behavior: FileOpenBehavior,
                     persistent_memory_check: PersistentMemoryCheck) -> Result<Self, PmemError>
    {
        let mut mapped_len = 0;
        let mut is_pm = 0;
        let file = CString::new(file_to_map).map_err(|_| PmemError::InvalidFileName )?;
        let file = file.as_c_str();

        let require_pm = match persistent_memory_check {
            PersistentMemoryCheck::CheckForPersistentMemory => true,
            PersistentMemoryCheck::DontCheckForPersistentMemory => false,
        };
        let create_flags = match file_open_behavior {
            FileOpenBehavior::CreateNew => PMEM_FILE_CREATE | PMEM_FILE_EXCL,
            FileOpenBehavior::OpenExisting => 0,
        };

        let addr = unsafe {
            pmem_map_file(
                file.as_ptr(),
                size,
                create_flags.try_into().unwrap(),
                0666,
                &mut mapped_len,
                &mut is_pm,
            )
        };

        if addr.is_null() {
            eprintln!("{}", unsafe {
                CString::from_raw(pmem_errormsg() as *mut i8)
                    .into_string()
                    .unwrap()
            });
            Err(PmemError::CannotOpenPmFile)
        } else if is_pm == 0 && require_pm {
            eprintln!("{}", unsafe {
                CString::from_raw(pmem_errormsg() as *mut i8)
                    .into_string()
                    .unwrap()
            });
            Err(PmemError::NotPm)
        } else {
            Ok(Self {
                virt_addr: addr as *mut u8,
                size: mapped_len.try_into().unwrap(),
                num_bytes_sectioned: 0,
            })
        }
    }
}

verus! {

#[derive(Clone, Copy)]
pub enum FileOpenBehavior {
    CreateNew,
    OpenExisting,
}

#[derive(Clone, Copy)]
pub enum PersistentMemoryCheck {
    CheckForPersistentMemory,
    DontCheckForPersistentMemory,
}

pub struct FileBackedPersistentMemoryRegion
{
    mmf: MemoryMappedFileSection,
}

impl FileBackedPersistentMemoryRegion
{
    #[verifier::external_body]
    fn new_internal(path: &StrSlice, region_size: u64, open_behavior: FileOpenBehavior,
                    persistent_memory_check: PersistentMemoryCheck)
                    -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(region) => region.inv() && region@.len() == region_size,
                Err(_) => true,
            }
    {
        let mmf = MemoryMappedFile::from_file(
            path.into_rust_str(),
            region_size as usize,
            open_behavior,
            persistent_memory_check,
        )?;
        Ok(Self { mmf })
    }

    pub fn new(path: &StrSlice, region_size: u64, persistent_memory_check: PersistentMemoryCheck)
               -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(region) => region.inv() && region@.len() == region_size,
                Err(_) => true,
            }
    {
        Self::new_internal(path, region_size, FileOpenBehavior::CreateNew, persistent_memory_check)
    }

    pub fn restore(path: &StrSlice, region_size: u64) -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(region) => region.inv() && region@.len() == region_size,
                Err(_) => true,
            }
    {
        Self::new_internal(path, region_size, FileOpenBehavior::OpenExisting,
                           PersistentMemoryCheck::DontCheckForPersistentMemory)
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
        // SAFETY: The `offset` method is safe as long as both the start
        // and resulting pointer are in bounds and the computed offset does
        // not overflow `isize`. `addr` and `num_bytes` are unsigned and
        // the precondition requires that `addr + num_bytes` is in bounds.
        // The precondition does not technically prevent overflowing `isize`
        // but the value is large enough (assuming a 64-bit architecture)
        // that we will not violate this restriction in practice.
        // TODO: put it in the precondition anyway
        let addr_on_pm: *const u8 = unsafe {
            self.section.virt_addr.offset(addr.try_into().unwrap())
        };

        // SAFETY: The precondition establishes that `num_bytes as usize` bytes
        // from `addr_on_pm` are valid bytes on PM. We do not modify the
        // bytes backing this slice while the slice is live because
        // this function does not modify them and it returns a copy of the bytes,
        // not a direct reference to them.
        let pm_slice: &[u8] = unsafe {
            std::slice::from_raw_parts(addr_on_pm, num_bytes as usize)
        };

        // `to_vec` clones the bytes in `pm_slice`
        pm_slice.to_vec()
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
            self.section.virt_addr.offset(addr.try_into().unwrap())
        };

        // Cast the pointer to PM bytes to an S pointer
        let s_pointer: *const S = addr_on_pm as *const S;

        // SAFETY: The precondition establishes that `S::serialized_len()` bytes
        // after the offset specified by `addr` are valid PM bytes, so it is
        // safe to dereference s_pointer. The borrow checker should treat this object
        // as borrowed from the FileBackedPersistentMemoryRegion object, preventing mutable borrows of any
        // other part of the object until this one is dropped.
        unsafe { &(*s_pointer) }
    }

    #[verifier::external_body]
    fn write(&mut self, addr: u64, bytes: &[u8])
    {
        // SAFETY: The `offset` method is safe as long as both the start
        // and resulting pointer are in bounds and the computed offset does
        // not overflow `isize`. `addr` and `num_bytes` are unsigned and
        // the precondition requires that `addr + num_bytes` is in bounds.
        // The precondition does not technically prevent overflowing `isize`
        // but the value is large enough (assuming a 64-bit architecture)
        // that we will not violate this restriction in practice.
        // TODO: put it in the precondition anyway
        let addr_on_pm: *mut u8 = unsafe {
            self.section.virt_addr.offset(addr.try_into().unwrap())
        };

        // pmem_memcpy_nodrain() does a memcpy to PM with no cache line flushes or
        // ordering; it makes no guarantees about durability. pmem_flush() does cache
        // line flushes but does not use an ordering primitive, so updates are still
        // not guaranteed to be durable yet.
        // Verus doesn't like calling pmem_memcpy_nodrain directly because it returns
        // a raw pointer, so we define a wrapper around pmem_memcpy_nodrain in deps_hack
        // that does not return anything and call that instead
        unsafe {
            pmem_memcpy_nodrain_helper(
                addr_on_pm as *mut c_void,
                bytes.as_ptr() as *const c_void,
                bytes.len()
            );
        }
    }

    #[verifier::external_body]
    #[allow(unused_variables)]
    fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S)
        where
            S: Serializable + Sized
    {
        let num_bytes: usize = S::serialized_len() as usize;

        // SAFETY: The `offset` method is safe as long as both the start
        // and resulting pointer are in bounds and the computed offset does
        // not overflow `isize`. `addr` and `num_bytes` are unsigned and
        // the precondition requires that `addr + num_bytes` is in bounds.
        // The precondition does not technically prevent overflowing `isize`
        // but the value is large enough (assuming a 64-bit architecture)
        // that we will not violate this restriction in practice.
        // TODO: put it in the precondition anyway
        let addr_on_pm: *mut u8 = unsafe {
            self.section.virt_addr.offset(addr.try_into().unwrap())
        };

        // convert the given &S to a pointer, then a slice of bytes
        let s_pointer = to_write as *const S as *const u8;

        // pmem_memcpy_nodrain() does a memcpy to PM with no cache line flushes or
        // ordering; it makes no guarantees about durability. pmem_flush() does cache
        // line flushes but does not use an ordering primitive, so updates are still
        // not guaranteed to be durable yet.
        // Verus doesn't like calling pmem_memcpy_nodrain directly because it returns
        // a raw pointer, so we define a wrapper around pmem_memcpy_nodrain in deps_hack
        // that does not return anything and call that instead
        unsafe {
            pmem_memcpy_nodrain_helper(
                addr_on_pm as *mut c_void,
                s_pointer as *const c_void,
                num_bytes
            );
        }
    }

    #[verifier::external_body]
    fn flush(&mut self)
    {
        // `pmem_drain()` invokes an ordering primitive to drain store buffers and
        // ensure that all cache lines that were flushed since the previous ordering
        // primitive are durable. This guarantees that all updates made with `write`/
        // `serialize_and_write` since the last `flush` call will be durable before
        // any new updates become durable.
        unsafe { pmem_drain(); }
    }
}

}
