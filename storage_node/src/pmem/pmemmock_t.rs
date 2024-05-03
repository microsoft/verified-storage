//! This file contains the trusted implementation for
//! `VolatileMemoryMockingPersistentMemoryRegions`, a collection of
//! volatile memory regions. It serves as a mock of persistent memory
//! regions by implementing trait `PersistentMemoryRegions`.
//!
//! THIS IS ONLY INTENDED FOR USE IN TESTING! In practice, one should
//! use actually persistent memory to implement persistent memory!

use crate::pmem::device_t::*;
use crate::pmem::pmemspec_t::{
    PersistentMemoryByte, PersistentMemoryConstants, PersistentMemoryRegion,
    PersistentMemoryRegionView, PersistentMemoryRegions, PersistentMemoryRegionsView, PmemError,
};
use crate::pmem::serialization_t::*;
use crate::pmem::timestamp_t::*;
use builtin::*;
use builtin_macros::*;
use deps_hack::rand::Rng;
use std::convert::*;
use vstd::prelude::*;

verus! {

    // A `VolatileMemoryMockingPersistentMemoryDevice` is a placeholder;
    // it will let us get PM regions and a timestamp but does not actually
    // represent or store any bytes or physical space.
    pub struct VolatileMemoryMockingPersistentMemoryDevice {
        capacity: u64,
        cursor: u64,
        id: u128,
    }

    // This executable method can be called to compute a random GUID.
    // It uses the external `rand` crate.
    #[verifier::external_body]
    pub exec fn generate_fresh_device_id() -> (out: u128)
    {
        deps_hack::rand::thread_rng().gen::<u128>()
    }

    #[allow(dead_code)]
    pub struct VolatileMemoryMockingPersistentMemoryRegionDescriptor
    {
        len: u64,
        timestamp: Ghost<PmTimestamp>,
        device_id: u128,
    }

    impl RegionDescriptor for VolatileMemoryMockingPersistentMemoryRegionDescriptor
    {
        closed spec fn view(&self) -> RegionDescriptorView
        {
            RegionDescriptorView {
                len: self.len,
                timestamp: self.timestamp@,
                device_id: self.device_id
            }
        }

        fn device_id(&self) -> u128
        {
            self.device_id
        }

        fn len(&self) -> u64
        {
            self.len
        }
    }

    impl VolatileMemoryMockingPersistentMemoryDevice {
        pub fn new(capacity: u64) -> (result: Self)
            requires
                capacity > 0,
            ensures
                result.len() == capacity,
                result.spec_get_cursor() == Some(0u64),
        {
            Self {
                capacity,
                cursor: 0,
                id: generate_fresh_device_id()
            }
        }
    }

    impl PmDevice for VolatileMemoryMockingPersistentMemoryDevice {
        type RegionDesc = VolatileMemoryMockingPersistentMemoryRegionDescriptor;

        closed spec fn len(&self) -> u64 {
            self.capacity
        }

        fn capacity(&self) -> u64 {
            self.capacity
        }

        closed spec fn spec_device_id(&self) -> u128
        {
            self.id
        }

        fn device_id(&self) -> u128
        {
            self.id
        }

        closed spec fn spec_get_cursor(&self) -> Option<u64>
        {
            if self.cursor >= self.capacity {
                None
            } else {
                Some(self.cursor)
            }
        }

        fn get_cursor(&self) -> Option<u64>
        {
            if self.cursor >= self.capacity {
                None
            } else {
                Some(self.cursor)
            }
        }

        fn inc_cursor(&mut self, len: u64)
        {
            self.cursor = self.cursor + len;
        }

        fn get_new_region(&mut self, len: u64) -> Result<Self::RegionDesc, PmemError>
        {
            // the precondition requires that the device has enough space for the
            // region, so we don't have to check on that
            self.inc_cursor(len);
            Ok(VolatileMemoryMockingPersistentMemoryRegionDescriptor {
                len,
                timestamp: Ghost(PmTimestamp::new(self.spec_device_id() as int)),
                device_id: self.device_id()
            })
        }
    }

    // The `VolatileMemoryMockingPersistentMemoryRegion` struct
    // contains a vector of volatile memory to hold the contents, as
    // well as a ghost field that keeps track of the virtual modeled
    // state. This ghost field pretends that outstanding writes remain
    // outstanding even though in the concrete `contents` field we
    // actually overwrite all data in place immediately.
    pub struct VolatileMemoryMockingPersistentMemoryRegion
    {
        contents: Vec<u8>,
        persistent_memory_view: Ghost<PersistentMemoryRegionView>,
        device_id: u128,
    }

    impl PersistentMemoryRegion for VolatileMemoryMockingPersistentMemoryRegion
    {
        type RegionDesc = VolatileMemoryMockingPersistentMemoryRegionDescriptor;

        #[verifier::external_body]
        fn new(region_descriptor: Self::RegionDesc) -> (result: Result<Self, PmemError>)
        {
            let region_size = region_descriptor.len();
            let device_id = region_descriptor.device_id();
            let contents: Vec<u8> = vec![0; region_size as usize];
            let ghost state: Seq<PersistentMemoryByte> = Seq::new(
                region_size as nat,
                |i| PersistentMemoryByte {
                    state_at_last_flush: 0,
                    outstanding_write: None,
                }
            );
            let persistent_memory_view = Ghost(PersistentMemoryRegionView { state, device_id, timestamp: region_descriptor@.timestamp });
            Ok(Self { contents, persistent_memory_view, device_id })
        }

        closed spec fn view(&self) -> PersistentMemoryRegionView
        {
            self.persistent_memory_view@
        }

        closed spec fn inv(&self) -> bool
        {
            // We maintain the invariant that our size fits in a `u64`.
            &&& self.contents.len() <= u64::MAX

            // We also maintain the invariant that the contents of our
            // volatile buffer matches the result of flushing the
            // abstract state.
            &&& self.contents@ == self.persistent_memory_view@.flush().committed()
            &&& self.device_id == self@.device_id
            &&& self@.timestamp.device_id() == self.spec_device_id()
        }

        closed spec fn spec_device_id(&self) -> u128
        {
            self.device_id
        }

        fn device_id(&self) -> u128
        {
            self.device_id
        }

        fn get_region_size(&self) -> (result: u64)
        {
            self.contents.len() as u64
        }

        #[verifier::external_body]
        fn read(&self, addr: u64, num_bytes: u64) -> (bytes: Vec<u8>)
        {
            let addr_usize: usize = addr.try_into().unwrap();
            let num_bytes_usize: usize = num_bytes.try_into().unwrap();
            self.contents[addr_usize..addr_usize+num_bytes_usize].to_vec()
        }

        #[verifier::external_body]
        fn read_and_deserialize<S>(&self, addr: u64) -> &S
            where
                S: Serializable + Sized
        {
            let addr_usize: usize = addr.try_into().unwrap();
            let num_bytes: usize = S::serialized_len().try_into().unwrap();
            let bytes = &self.contents[addr_usize..addr_usize+num_bytes];
            // SAFETY: The precondition of the method ensures that we do not
            // attempt to read out of bounds. The user of the mock is responsible
            // for ensuring that there is a valid S at this address and checking
            // for corruption. The function signature should (TODO: make sure)
            // borrow check the returned value properly.
            unsafe {
                let bytes_pointer = bytes.as_ptr();
                let s_pointer = bytes_pointer as *const S;
                &(*s_pointer)
            }
        }

        #[verifier::external_body]
        fn write(&mut self, addr: u64, bytes: &[u8])
        {
            let addr_usize: usize = addr.try_into().unwrap();
            self.contents.splice(addr_usize..addr_usize+bytes.len(), bytes.iter().cloned());
            self.persistent_memory_view = Ghost(self.persistent_memory_view@.write(addr as int, bytes@))
        }

        #[verifier::external_body]
        fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S)
            where
                S: Serializable + Sized
        {
            let addr_usize: usize = addr.try_into().unwrap();
            let num_bytes: usize = S::serialized_len().try_into().unwrap();
            let s_pointer = to_write as *const S;
            let bytes_pointer = s_pointer as *const u8;
            // SAFETY: `bytes_pointer` always points to `num_bytes` consecutive, initialized
            // bytes because it was obtained by casting a regular Rust object reference
            // to a raw pointer. The borrow checker will ensure that `to_write` is not modified
            // by someone else during this function.
            let bytes = unsafe {
                std::slice::from_raw_parts(bytes_pointer, num_bytes)
            };
            self.contents.splice(addr_usize..addr_usize+num_bytes, bytes.iter().cloned());
            self.persistent_memory_view = Ghost(self.persistent_memory_view@.write(addr as int, bytes@))
        }

        fn flush(&mut self)
        {
            // Because of our invariant, we don't have to do anything
            // to the actual contents. We just have to update the
            // abstract view to reflect the flush having happened.
            self.persistent_memory_view = Ghost(self.persistent_memory_view@.flush());
            proof {
                lemma_auto_timestamp_helpers();
            }
            assert (self.contents@ =~= self.persistent_memory_view@.flush().committed());
        }

        #[allow(unused_variables)]
        fn update_region_timestamp(&mut self, new_timestamp: Ghost<PmTimestamp>)
        {
            self.persistent_memory_view = Ghost(self.persistent_memory_view@.update_region_with_timestamp(new_timestamp@));
            assert(self.contents@ == self.persistent_memory_view@.flush().committed());
        }
    }

    // The `VolatileMemoryMockingPersistentMemoryRegions` struct
    // contains a vector of volatile memory regions.
    pub struct VolatileMemoryMockingPersistentMemoryRegions
    {
        pub pms: Vec<VolatileMemoryMockingPersistentMemoryRegion>,
        pub device_id: u128,
    }

    /// So that `VolatileMemoryMockingPersistentMemoryRegions` can be
    /// used to mock a collection of persistent memory regions, it
    /// implements the trait `PersistentMemoryRegions`.

    // TODO: should maintain as an invariant that the view's current timestamp
    // matches the current timestamps of all of the regions in it
    impl PersistentMemoryRegions for VolatileMemoryMockingPersistentMemoryRegions {
        closed spec fn view(&self) -> PersistentMemoryRegionsView
        {
            PersistentMemoryRegionsView {
                regions: self.pms@.map(|_idx, pm: VolatileMemoryMockingPersistentMemoryRegion| pm@),
                timestamp: self.pms[0]@.timestamp,
                device_id: self.device_id
            }
        }

        closed spec fn inv(&self) -> bool
        {
            forall |i| 0 <= i < self.pms.len() ==> #[trigger] self.pms[i].inv()
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

        fn split_off(&mut self, at: usize) -> Self
        {
            let regions2 = self.pms.split_off(at);
            let ret = Self {
                pms: regions2,
                device_id: self.device_id
            };
            assert(self@.regions == old(self)@.regions.subrange(0, at as int));
            assert(ret@.regions == old(self)@.regions.subrange(at as int, old(self)@.len() as int));
            ret
        }

        // TODO: same issue as the other update timestamp function -- this shouldn't really
        // be exec but I don't know how to do it with a spec function. Maybe the compiler
        // will just see that it's a no-op and optimize it out?
        // TODO: This shouldn't be external_body but the indexing syntax we need to use
        // is not supported in non-external_body functions right now
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
            for which_region in iter: 0..self.pms.len()
                invariant
                    iter.end == self.pms.len(),
                    forall |i: int| 0 <= i < which_region ==>
                        self.pms[which_region as int]@ == old(self).pms[which_region as int]@.flush()
            {
                self.pms[which_region].flush();
            }
        }
    }

    impl VolatileMemoryMockingPersistentMemoryRegions {
        // TODO: ideally this would be a trait method of PersistentMemoryRegions, but the generics don't work out very well.
        pub fn combine_regions(regions: Vec<VolatileMemoryMockingPersistentMemoryRegion>) -> (result: Self)
            requires
                regions@.len() > 0,
                forall |i| 0 <= i < regions@.len() ==> {
                    let region = #[trigger] regions[i];
                    &&& region.inv()
                    &&& region@.timestamp == regions[0]@.timestamp
                    &&& region.spec_device_id() == regions[0].spec_device_id()
                },
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
