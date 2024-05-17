//! This file contains the trusted implementation for
//! `VolatileMemoryMockingPersistentMemoryRegions`, a collection of
//! volatile memory regions. It serves as a mock of persistent memory
//! regions by implementing trait `PersistentMemoryRegions`.
//!
//! THIS IS ONLY INTENDED FOR USE IN TESTING! In practice, one should
//! use actually persistent memory to implement persistent memory!

use crate::pmem::pmemspec_t::{
    PersistentMemoryByte, PersistentMemoryConstants, PersistentMemoryRegion,
    PersistentMemoryRegionView, PersistentMemoryRegions, PersistentMemoryRegionsView, PmemError,
};
use crate::pmem::serialization_t::*;
use builtin::*;
use builtin_macros::*;
use deps_hack::rand::Rng;
use std::convert::*;
use vstd::prelude::*;

verus! {

    // The `VolatileMemoryMockingPersistentMemoryRegion` struct
    // contains a vector of volatile memory to hold the contents, as
    // well as a ghost field that keeps track of the virtual modeled
    // state. This ghost field pretends that outstanding writes remain
    // outstanding even though in the concrete `contents` field we
    // actually overwrite all data in place immediately.
    pub struct VolatileMemoryMockingPersistentMemoryRegion
    {
        contents: Vec<u8>,
    }

    impl VolatileMemoryMockingPersistentMemoryRegion
    {
        #[verifier::external_body]
        fn new(region_size: u64) -> (result: Self)
            ensures
                result.inv(),
                result@.len() == region_size,
        {
            let contents: Vec<u8> = vec![0; region_size as usize];
            Self { contents }
        }
    }

    impl PersistentMemoryRegion for VolatileMemoryMockingPersistentMemoryRegion
    {
        #[verifier::external_body]
        closed spec fn view(&self) -> PersistentMemoryRegionView;

        closed spec fn inv(&self) -> bool
        {
            // We maintain the invariant that our size fits in a `u64`.
            &&& self.contents.len() <= u64::MAX
            &&& self.contents.len() == self@.len()

            // We also maintain the invariant that the contents of our
            // volatile buffer matches the result of flushing the
            // abstract state.
            &&& self.contents@ == self@.flush().committed()
        }

        closed spec fn constants(&self) -> PersistentMemoryConstants;

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
        }

        #[verifier::external_body]
        fn flush(&mut self)
        {
        }
    }

    // The `VolatileMemoryMockingPersistentMemoryRegions` struct
    // contains a vector of volatile memory regions.
    pub struct VolatileMemoryMockingPersistentMemoryRegions
    {
        pub regions: Vec<VolatileMemoryMockingPersistentMemoryRegion>,
    }

    impl VolatileMemoryMockingPersistentMemoryRegions
    {
        #[verifier::external_body]
        pub fn new(region_sizes: &[u64]) -> (result: Self)
            ensures
                result.inv(),
                result@.len() == region_sizes@.len(),
                forall |i| 0 <= i < region_sizes@.len() ==> #[trigger] result@[i].len() == region_sizes[i],
        {
            let mut regions = Vec::<VolatileMemoryMockingPersistentMemoryRegion>::new();
            let num_regions = region_sizes.len();
            for pos in 0..num_regions
                invariant
                    regions.len() == pos,
                    forall |i| 0 <= i < pos ==> regions[i]@.len() == region_sizes[i],
            {
                let region = VolatileMemoryMockingPersistentMemoryRegion::new(region_sizes[pos]);
                regions.push(region);
            }
            Self{ regions }
        }
    }

    /// So that `VolatileMemoryMockingPersistentMemoryRegions` can be
    /// used to mock a collection of persistent memory regions, it
    /// implements the trait `PersistentMemoryRegions`.
    impl PersistentMemoryRegions for VolatileMemoryMockingPersistentMemoryRegions {
        #[verifier::external_body]
        closed spec fn view(&self) -> PersistentMemoryRegionsView
        {
            PersistentMemoryRegionsView{
                regions: self.regions@.map(|_i, r: VolatileMemoryMockingPersistentMemoryRegion| r@)
            }
        }

        closed spec fn inv(&self) -> bool
        {
            forall |i| 0 <= i < self.regions.len() ==> #[trigger] self.regions[i].inv()
        }

        #[verifier::external_body]
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
        }
    }
}
