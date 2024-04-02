use crate::pmem::device_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use crate::pmem::timestamp_t::*;
use core::ffi::c_void;
use std::convert::TryInto;

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use deps_hack::{pmem_drain, pmem_flush, pmem_memcpy_nodrain, pmem_unmap};

verus! {
    #[verifier::external_body]
    struct PmPointer { virt_addr: *mut u8 }

    struct MappedPmDesc {
        virt_addr: PmPointer,
        len: u64,
        device_id: u128,
        current_timestamp: Ghost<PmTimestamp>,
    }

    impl RegionDescriptor for MappedPmDesc {
        closed spec fn view(&self) -> RegionDescriptorView {
            RegionDescriptorView {
                len: self.len,
                timestamp: self.current_timestamp@,
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

    struct MappedPM {
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
            &&& self@.current_timestamp.device_id() == self.spec_device_id()
        }

        fn get_region_size(&self) -> u64
        {
            self.mapped_len
        }

        #[verifier::external_body]
        fn new(region_descriptor: Self::RegionDesc) -> Result<Self, ()>
        {
            // TODO: we don't actually know what the state at last flush was;
            // should this instead be represented by some unknown value?
            let ghost state = Seq::new(
                region_descriptor.len as nat,
                |i| PersistentMemoryByte {
                    state_at_last_flush: 0,
                    outstanding_write: None,
                    write_timestamp: region_descriptor@.timestamp
                }
            );
            let persistent_memory_view = Ghost(
                PersistentMemoryRegionView {
                    state,
                    device_id: region_descriptor.device_id,
                    current_timestamp: region_descriptor@.timestamp
                }
            );
            Ok(Self {
                virt_addr: region_descriptor.virt_addr,
                mapped_len: region_descriptor.len,
                device_id: region_descriptor.device_id,
                persistent_memory_view,
                timestamp: region_descriptor.current_timestamp
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
            // not guaranteed to be durable yet
            // TODO: these should be unsafe?
            pmem_memcpy_nodrain(
                addr_on_pm as *mut c_void,
                bytes.as_ptr() as *const c_void,
                bytes.len()
            );
            pmem_flush(addr_on_pm as *mut c_void, bytes.len());

            self.persistent_memory_view = Ghost(self.persistent_memory_view@.write(addr as int, bytes@))
        }

        #[verifier::external_body]
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

            // TODO: can we remove this without messing up management of PM view?
            let bytes = unsafe {
                std::slice::from_raw_parts(s_pointer, num_bytes)
            };

            // pmem_memcpy_nodrain() does a memcpy to PM with no cache line flushes or
            // ordering; it makes no guarantees about durability. pmem_flush() does cache
            // line flushes but does not use an ordering primitive, so updates are still
            // not guaranteed to be durable yet
            // TODO: these should be unsafe?
            pmem_memcpy_nodrain(
                addr_on_pm as *mut c_void,
                s_pointer as *const c_void,
                num_bytes
            );
            pmem_flush(addr_on_pm as *mut c_void, num_bytes);

            self.persistent_memory_view = Ghost(self.persistent_memory_view@.write(addr as int, bytes@))
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
            // TODO: this should be unsafe?
            pmem_drain();
        }

        #[allow(unused_variables)]
        fn update_region_timestamp(&mut self, new_timestamp: Ghost<PmTimestamp>)
        {
            self.persistent_memory_view = Ghost(self.persistent_memory_view@.update_region_with_timestamp(new_timestamp@));
        }

    }

    struct MappedPmRegions {
        regions: Vec<MappedPM>,
    }

    // impl PersistentMemoryRegions for MappedPmRegions {}
}
