use crate::pmem::device_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use crate::pmem::timestamp_t::*;
use core::ffi::c_void;
use std::{convert::TryInto, ffi::CString};

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use deps_hack::{
    nix::{
        errno::{errno, from_i32},
        Error,
    },
    pmem::pmem_memcpy_nodrain_helper,
    pmem_drain, pmem_errormsg, pmem_flush, pmem_map_file, pmem_memcpy_nodrain, pmem_unmap,
    rand::Rng,
    PMEM_FILE_CREATE,
};

verus! {

    // This executable method can be called to compute a random GUID.
    // It uses the external `rand` crate.
    #[verifier::external_body]
    pub exec fn generate_fresh_device_id() -> (out: u128)
    {
        deps_hack::rand::thread_rng().gen::<u128>()
    }


    // Must be external body because Verus does not currently support raw pointers
    // TODO: is there a better/safer way to handle this? UnsafeCell maybe?
    #[verifier::external_body]
    #[derive(Clone, Copy)]
    struct PmPointer { virt_addr: *mut u8 }

    pub struct MappedPmDesc {
        virt_addr: PmPointer,
        len: u64,
        device_id: u128,
        timestamp: Ghost<PmTimestamp>,
    }

    impl RegionDescriptor for MappedPmDesc {
        closed spec fn view(&self) -> RegionDescriptorView {
            RegionDescriptorView {
                len: self.len,
                timestamp: self.timestamp@,
                device_id: self.device_id
            }
        }

        fn device_id(&self) -> u128 {
            self.device_id
        }

        fn len(&self) -> u64 {
            self.len
        }
    }

    // TODO: is this actually how we should represent this? Maybe
    // multiple separate mmap'ings?
    pub struct MappedPmDevice {
        virt_addr: PmPointer,
        len: u64,
        device_id: u128,
        cursor: u64
    }

    impl PmDevice for MappedPmDevice {
        type RegionDesc = MappedPmDesc;

        closed spec fn len(&self) -> u64
        {
            self.len
        }

        fn capacity(&self) -> u64
        {
            self.len
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
            if self.cursor >= self.len {
                None
            } else {
                Some(self.cursor)
            }
        }

        fn get_cursor(&self) -> Option<u64>
        {
            if self.cursor >= self.len {
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
            // the precondition requires that the device has enough space for the
            // region, so we don't have to check on that
            let new_virt_addr = unsafe {
                PmPointer {
                    virt_addr: self.virt_addr.virt_addr.offset(self.cursor.try_into().unwrap())
                }
            };
            self.inc_cursor(len);
            Ok(MappedPmDesc {
                virt_addr: new_virt_addr,
                len,
                timestamp: Ghost(PmTimestamp::new(self.spec_device_id() as int)),
                device_id: self.device_id()
            })
        }
    }

    impl MappedPmDevice {
        // TODO: detailed information for error returns
        #[verifier::external_body]
        #[allow(dead_code)]
        pub fn new<'a>(file_to_map: &str, size: usize) -> (result: Result<Self, PmemError>)
            ensures
                match result {
                    Ok(device) => {
                        &&& device.spec_get_cursor() == Some(0u64)
                        &&& device.len() == size
                        // TODO: check virt addr in postcondition
                    }
                    Err(_) => true // TODO
                }
        {
            let mut mapped_len = 0;
            let mut is_pm = 0;
            let file = CString::new(file_to_map).map_err(|_| PmemError::InvalidFileName )?;
            let file = file.as_c_str();

            let addr = unsafe {
                pmem_map_file(
                    file.as_ptr(),
                    size,
                    PMEM_FILE_CREATE.try_into().unwrap(),
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
            } else if is_pm == 0 {
                eprintln!("{}", unsafe {
                    CString::from_raw(pmem_errormsg() as *mut i8)
                        .into_string()
                        .unwrap()
                });
                Err(PmemError::NotPm)
            } else {
                Ok(MappedPmDevice {
                    virt_addr: PmPointer { virt_addr: addr as *mut u8 },
                    len: mapped_len.try_into().unwrap(),
                    device_id: generate_fresh_device_id(),
                    cursor: 0,
                })
            }
        }
    }

    #[allow(dead_code)]
    pub struct MappedPM {
        virt_addr: PmPointer,
        mapped_len: u64,
        device_id: u128,
        persistent_memory_view: Ghost<PersistentMemoryRegionView>,
        timestamp: Ghost<PmTimestamp>,
    }

    impl Drop for MappedPM {
        #[verifier::external_body]
        fn drop(&mut self)
            opens_invariants none
            no_unwind
        {
            unsafe { pmem_unmap(self.virt_addr.virt_addr as *mut c_void, self.mapped_len.try_into().unwrap()) };
        }
    }

    impl PersistentMemoryRegion for MappedPM {
        type RegionDesc = MappedPmDesc;

        closed spec fn view(&self) -> PersistentMemoryRegionView
        {
            self.persistent_memory_view@
        }

        fn device_id(&self) -> u128
        {
            self.device_id
        }

        closed spec fn spec_device_id(&self) -> u128
        {
            self.device_id
        }

        closed spec fn inv(&self) -> bool
        {
            &&& self.mapped_len <= u64::MAX
            &&& self.mapped_len == self@.len()
            &&& self.device_id == self@.device_id
            &&& self@.timestamp.device_id() == self.spec_device_id()
        }

        fn get_region_size(&self) -> u64
        {
            self.mapped_len
        }

        #[verifier::external_body]
        fn new(region_descriptor: Self::RegionDesc) -> Result<Self, PmemError>
        {
            // TODO: we don't actually know what the state at last flush was;
            // should this instead be represented by some unknown value?
            let ghost state = Seq::new(
                region_descriptor.len as nat,
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
            Ok(Self {
                virt_addr: region_descriptor.virt_addr,
                mapped_len: region_descriptor.len,
                device_id: region_descriptor.device_id,
                persistent_memory_view,
                timestamp: region_descriptor.timestamp
            })
        }

        #[verifier::external_body]
        fn read(&self, addr: u64, num_bytes: u64) -> (bytes: Vec<u8>)
        {
            let num_bytes_usize: usize = num_bytes.try_into().unwrap();

            // SAFETY: The `offset` method is safe as long as both the start
            // and resulting pointer are in bounds and the computed offset does
            // not overflow `isize`. `addr` and `num_bytes` are unsigned and
            // the precondition requires that `addr + num_bytes` is in bounds.
            // The precondition does not technically prevent overflowing `isize`
            // but the value is large enough (assuming a 64-bit architecture)
            // that we will not violate this restriction in practice.
            // TODO: put it in the precondition anyway
            let addr_on_pm: *const u8 = unsafe {
                self.virt_addr.virt_addr.offset(addr.try_into().unwrap())
            };

            // SAFETY: The precondition establishes that `num_bytes_usize` bytes
            // from `addr_on_pm` are valid bytes on PM. We do not modify the
            // bytes backing this slice while the slice is live because
            // this function does not modify them and it returns a copy of the bytes,
            // not a direct reference to them.
            let pm_slice: &[u8] = unsafe {
                std::slice::from_raw_parts(addr_on_pm, num_bytes_usize)
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
                self.virt_addr.virt_addr.offset(addr.try_into().unwrap())
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
            // SAFETY: The `offset` method is safe as long as both the start
            // and resulting pointer are in bounds and the computed offset does
            // not overflow `isize`. `addr` and `num_bytes` are unsigned and
            // the precondition requires that `addr + num_bytes` is in bounds.
            // The precondition does not technically prevent overflowing `isize`
            // but the value is large enough (assuming a 64-bit architecture)
            // that we will not violate this restriction in practice.
            // TODO: put it in the precondition anyway
            let addr_on_pm: *mut u8 = unsafe {
                self.virt_addr.virt_addr.offset(addr.try_into().unwrap())
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
                self.virt_addr.virt_addr.offset(addr.try_into().unwrap())
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
            self.persistent_memory_view = Ghost(self.persistent_memory_view@.flush());

            // `pmem_drain()` invokes an ordering primitive to drain store buffers and
            // ensure that all cache lines that were flushed since the previous ordering
            // primitive are durable. This guarantees that all updates made with `write`/
            // `serialize_and_write` since the last `flush` call will be durable before
            // any new updates become durable.
            unsafe { pmem_drain(); }
        }

        #[allow(unused_variables)]
        fn update_region_timestamp(&mut self, new_timestamp: Ghost<PmTimestamp>)
        {
            self.persistent_memory_view = Ghost(self.persistent_memory_view@.update_region_with_timestamp(new_timestamp@));
        }
    }

    pub struct MappedPmRegions {
        pms: Vec<MappedPM>,
        device_id: u128,
    }

    impl PersistentMemoryRegions for MappedPmRegions {
        closed spec fn view(&self) -> PersistentMemoryRegionsView
        {
            PersistentMemoryRegionsView {
                regions: self.pms@.map(|_idx, pm: MappedPM| pm@),
                timestamp: self.pms[0]@.timestamp,
                device_id: self.device_id
            }
        }

        closed spec fn inv(&self) -> bool
        {
            &&& forall |i| 0 <= i < self.pms.len() ==> #[trigger] self.pms[i].inv()
            &&& forall |i| 0 <= i < self.pms.len() ==> #[trigger] self.pms[i].device_id == self.device_id
        }

        closed spec fn constants(&self) -> PersistentMemoryConstants
        {
            PersistentMemoryConstants { impervious_to_corruption: true }
        }

        closed spec fn spec_device_id(&self) -> u128
        {
            self.device_id
        }

        fn device_id(&self) -> u128
        {
            self.device_id
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
            // we only loop over PM views, since we don't want to invoke one drain for
            // every region, since all of the regions are from the same device
            for which_region in iter: 0..self.pms.len()
                invariant
                    iter.end == self.pms.len(),
                    forall |i: int| 0 <= i < which_region ==>
                        self.pms[which_region as int]@ == old(self).pms[which_region as int]@.flush()
            {
                self.pms[which_region].persistent_memory_view = Ghost(self.pms[which_region as int].persistent_memory_view@.flush())
            }
            unsafe { pmem_drain(); }
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

    // TODO: make this a trait method of PersistentMemoryRegions
    impl MappedPmRegions {
        pub fn combine_regions(regions: Vec<MappedPM>) -> (result: Self)
            requires
                regions@.len() > 0,
                forall |i| 0 <= i < regions@.len() ==> {
                    let region = #[trigger] regions[i];
                    &&& region.inv()
                    &&& region@.timestamp == regions[0]@.timestamp
                    &&& region.spec_device_id() == regions[0].spec_device_id()
                }
            ensures
                result@.len() == regions@.len(),
                result.inv(),
                forall |i: int| 0 <= i < result@.len() ==> {
                    let region = #[trigger] result@[i];
                    region.timestamp == result@[0].timestamp
                },
                forall |i: int| 0 <= i < result@.len() ==> {
                    let region = #[trigger] result@[i];
                    region.device_id == result@[0].device_id
                },
                result@.timestamp == regions[0]@.timestamp,
                result.spec_device_id() == regions[0].spec_device_id()
        {
            let device_id = regions[0].device_id();
            Self {
                pms: regions,
                device_id
            }
        }
    }
}
