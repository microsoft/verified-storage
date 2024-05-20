//! This file contains the trusted implementation for
//! `VolatileMemoryMockingPersistentMemoryRegions`, a collection of
//! volatile memory regions. It serves as a mock of persistent memory
//! regions by implementing trait `PersistentMemoryRegions`.
//!
//! THIS IS ONLY INTENDED FOR USE IN TESTING! In practice, one should
//! use actually persistent memory to implement persistent memory!

use crate::pmem::pmemspec_t::{
    PersistentMemoryAccessToken, PersistentMemoryByte, PersistentMemoryDevice, PersistentMemoryRegionView, PmemError,
};
use crate::pmem::serialization_t::*;
use builtin::*;
use builtin_macros::*;
use deps_hack::rand::Rng;
use std::convert::*;
use std::cell::RefCell;
use std::rc::Rc;
use vstd::invariant::*;
use vstd::prelude::*;

verus! {

    #[verifier::external_body]
    pub struct VolatileMemoryMockingPersistentMemoryDevice
    {
        id: Ghost<int>,
        contents: Rc<RefCell<Vec<u8>>>,
    }

    #[verifier::external_body]
    pub struct VolatileMemoryMockingPersistentMemoryAccessToken
    {
        id: int,
    }

    impl PersistentMemoryAccessToken for VolatileMemoryMockingPersistentMemoryAccessToken
    {
        closed spec fn id(self) -> int
        {
            self.id
        }

        #[verifier::external_body]
        closed spec fn view(self) -> PersistentMemoryRegionView;
    }

    impl VolatileMemoryMockingPersistentMemoryDevice
    {
        #[verifier::external_body]
        fn new(region_size: u64) -> (result: (Self, Tracked<VolatileMemoryMockingPersistentMemoryAccessToken>))
            ensures
                ({
                    let (dev, tok) = result;
                    &&& dev.inv()
                    &&& tok@.id() == dev.id()
                    &&& tok@@.len() == region_size
                })
        {
            let contents = vec![0u8; region_size as usize];
            let contents = Rc::new(RefCell::new(contents));
            let dev = VolatileMemoryMockingPersistentMemoryDevice{ id: Ghost(0int), contents };
            let tracked tok = VolatileMemoryMockingPersistentMemoryAccessToken{ id: 0 };
            (dev, Tracked(tok))
        }
    }

    impl PersistentMemoryDevice for VolatileMemoryMockingPersistentMemoryDevice
    {
        type AccessToken = VolatileMemoryMockingPersistentMemoryAccessToken;
    
        closed spec fn id(self) -> int
        {
            self.id@
        }

        #[verifier::external_body]
        closed spec fn impervious_to_corruption(self) -> bool;

        closed spec fn inv(self) -> bool
        {
            true
        }

        #[verifier::external_body]
        fn get_region_size(
            &self,
            Tracked(tok): Tracked<&Self::AccessToken>
        ) -> (result: u64)
        {
            self.contents.borrow().len() as u64
        }

        #[verifier::external_body]
        fn read(
            &self,
            Tracked(tok): Tracked<&Self::AccessToken>,
            addr: u64,
            num_bytes: u64
        ) -> (bytes: Vec<u8>)
        {
            let addr_usize: usize = addr.try_into().unwrap();
            let num_bytes_usize: usize = num_bytes.try_into().unwrap();
            self.contents.borrow()[addr_usize..addr_usize+num_bytes_usize].to_vec()
        }

        #[verifier::external_body]
        fn read_and_deserialize<S>(
            &self,
            Tracked(tok): Tracked<&Self::AccessToken>,
            addr: u64
        ) -> &S
            where
                S: Serializable + Sized
        {
            let addr_usize: usize = addr.try_into().unwrap();
            let num_bytes: usize = S::serialized_len().try_into().unwrap();
            let bytes = &self.contents.borrow()[addr_usize..addr_usize+num_bytes];
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
        fn write(
            &self,
            Tracked(tok): Tracked<&mut Self::AccessToken>,
            addr: u64,
            bytes: &[u8]
        )
        {
            let addr_usize: usize = addr.try_into().unwrap();
            self.contents.borrow_mut().splice(addr_usize..addr_usize+bytes.len(), bytes.iter().cloned());
        }

        #[verifier::external_body]
        fn serialize_and_write<S>(
            &self,
            Tracked(tok): Tracked<&mut Self::AccessToken>,
            addr: u64,
            to_write: &S
        )
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
            self.contents.borrow_mut().splice(addr_usize..addr_usize+num_bytes, bytes.iter().cloned());
        }

        #[verifier::external_body]
        fn flush(
            &self,
            Tracked(tok): Tracked<&mut Self::AccessToken>
        )
        {
        }
    }
}
