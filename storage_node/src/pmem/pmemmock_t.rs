//! This file contains the trusted implementation for
//! `VolatileMemoryMockingPersistentMemoryRegions`, a collection of
//! volatile memory regions. It serves as a mock of persistent memory
//! regions by implementing trait `PersistentMemoryRegions`.
//!
//! THIS IS ONLY INTENDED FOR USE IN TESTING! In practice, one should
//! use actually persistent memory to implement persistent memory!

use crate::pmem::pmemspec_t::{
    PersistentMemoryByte, PersistentMemoryConstants, PersistentMemoryRegionView,
    PersistentMemoryRegions, PersistentMemoryRegionsView,
};
use builtin::*;
use builtin_macros::*;
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
        persistent_memory_view: Ghost<PersistentMemoryRegionView>
    }

    impl VolatileMemoryMockingPersistentMemoryRegion {
        #[verifier::external_body]
        pub fn new(region_size: u64) -> (result: Result<Self, ()>)
            ensures
                match result {
                    Ok(pm) => {
                        &&& pm@.len() == region_size
                        &&& pm.inv()
                        &&& pm@.no_outstanding_writes()
                    },
                    Err(_) => true
                }
        {
            let contents: Vec<u8> = vec![0; region_size as usize];
            let ghost state: Seq<PersistentMemoryByte> =
                Seq::<PersistentMemoryByte>::new(region_size as nat,
                                                 |i| PersistentMemoryByte {
                                                     state_at_last_flush: 0,
                                                     outstanding_write: None
                                                 });
            let persistent_memory_view = Ghost(PersistentMemoryRegionView { state });
            Ok(Self { contents, persistent_memory_view })
        }

        pub closed spec fn view(self) -> PersistentMemoryRegionView
        {
            self.persistent_memory_view@
        }

        pub closed spec fn inv(self) -> bool
        {
            // We maintain the invariant that our size fits in a `u64`.
            &&& self.contents.len() <= u64::MAX

            // We also maintain the invariant that the contents of our
            // volatile buffer matches the result of flushing the
            // abstract state.
            &&& self.contents@ == self.persistent_memory_view@.flush().committed()
        }

        pub fn get_region_size(&self) -> (result: u64)
            requires
                self.inv()
            ensures
                result == self@.len()
        {
            self.contents.len() as u64
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
            self.contents[addr_usize..addr_usize+num_bytes_usize].to_vec()
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
            self.contents.splice(addr_usize..addr_usize+bytes.len(), bytes.iter().cloned());
            self.persistent_memory_view = Ghost(self.persistent_memory_view@.write(addr as int, bytes@))
        }

        pub fn flush(&mut self)
            requires
                old(self).inv()
            ensures
                self.inv(),
                self@ == old(self)@.flush()
        {
            // Because of our invariant, we don't have to do anything
            // to the actual contents. We just have to update the
            // abstract view to reflect the flush having happened.

            self.persistent_memory_view = Ghost(self.persistent_memory_view@.flush());
            assert (self.contents@ =~= self.persistent_memory_view@.flush().committed());
        }
    }

    // The `VolatileMemoryMockingPersistentMemoryRegions` struct
    // contains a vector of volatile memory regions.
    pub struct VolatileMemoryMockingPersistentMemoryRegions
    {
        pub pms: Vec<VolatileMemoryMockingPersistentMemoryRegion>
    }

    /// So that `VolatileMemoryMockingPersistentMemoryRegions` can be
    /// used to mock a collection of persistent memory regions, it
    /// implements the trait `PersistentMemoryRegions`.

    impl PersistentMemoryRegions for VolatileMemoryMockingPersistentMemoryRegions {
        closed spec fn view(&self) -> PersistentMemoryRegionsView
        {
            PersistentMemoryRegionsView {
                regions: self.pms@.map(|_idx, pm: VolatileMemoryMockingPersistentMemoryRegion| pm@)
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

    /// We also implement a constructor for
    /// `VolatileMemoryMockingPersistentMemoryRegions` so it can be
    /// created by test code. We name this constructor
    /// `new_mock_only_for_use_in_testing` to make clear that it
    /// shouldn't be used in production.

    impl VolatileMemoryMockingPersistentMemoryRegions {
        #[verifier::external_body]
        pub fn new_mock_only_for_use_in_testing(region_sizes: &[u64]) -> (result: Result<Self, ()>)
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
            let mut pms = Vec::<VolatileMemoryMockingPersistentMemoryRegion>::new();
            for &region_size in region_sizes {
                let pm = VolatileMemoryMockingPersistentMemoryRegion::new(region_size)?;
                pms.push(pm);
            }
            Ok(Self {pms})
        }
    }

}
