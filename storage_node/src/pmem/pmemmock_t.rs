//! This file contains the trusted implementation for
//! `VolatileMemoryMockingPersistentMemoryRegions`, a collection of
//! volatile memory regions. It serves as a mock of persistent memory
//! regions by implementing trait `PersistentMemoryRegions`.
//!
//! THIS IS ONLY INTENDED FOR USE IN TESTING! In practice, one should
//! use actually persistent memory to implement persistent memory!

use crate::pmem::device_t::*;
use crate::pmem::pmemspec_t::{
    PersistentMemoryByte, PersistentMemoryConstants, PersistentMemoryRegionView,
    PersistentMemoryRegions, PersistentMemoryRegionsView,
};
use crate::pmem::timestamp_t::*;
use builtin::*;
use builtin_macros::*;
use std::convert::*;
use vstd::prelude::*;

verus! {

    // A `VolatileMemoryMockingPersistentMemoryDevice` is a placeholder;
    // it will let us get PM regions and a timestamp but does not actually
    // represent or store any bytes or physical space.
    pub struct VolatileMemoryMockingPersistentMemoryDevice {
        capacity: u64
    }

    impl VolatileMemoryMockingPersistentMemoryDevice {
        pub fn new(capacity: u64) -> (result: Self)
            ensures
                result.len() == capacity
        {
            Self {
                capacity
            }
        }
    }

    impl PmDevice<VolatileMemoryMockingPersistentMemoryRegions> for VolatileMemoryMockingPersistentMemoryDevice {
        closed spec fn len(&self) -> u64 {
            self.capacity
        }

        fn capacity(&self) -> u64 {
            self.capacity
        }

        /// Converts a 2D vector into a vector of VolatileMemoryMockingPersistentMemoryRegions.
        /// regions[i][j] should contain the capacity of the jth region in the ith VolatileMemoryMockingPersistentMemoryRegions
        /// This function allows us to obtain multiple VolatileMemoryMockingPersistentMemoryRegions objects from a single device
        /// and is the only way to get a timestamp to coordinate flushes across all of the separate region lists.
        fn get_regions(self, regions: Vec<Vec<u64>>) -> Result<(Vec<VolatileMemoryMockingPersistentMemoryRegions>, Ghost<PmTimestamp>), ()> {
            let mut pm_regions: Vec<VolatileMemoryMockingPersistentMemoryRegions> = Vec::new();
            let timestamp: Ghost<PmTimestamp> = Ghost(PmTimestamp::new());

            // This is easier to prove with a while loop than a for loop -- it's hard to establish a relationship
            // between `idx` and the length of pm_regions in a for loop
            let mut idx = 0;
            while idx < regions.len()
                invariant
                    0 <= idx <= regions@.len(),
                    pm_regions@.len() == idx,
                    forall |j| #![auto] 0 <= j < idx ==> pm_regions[j]@.timestamp_corresponds_to_regions(timestamp@),
                    forall |j| #![auto] 0 <= j < idx ==> pm_regions[j]@.len() == regions[j]@.len(),
                    forall |j| #![auto] 0 <= j < idx ==> pm_regions[j].inv()
            {
                let mock_regions = VolatileMemoryMockingPersistentMemoryRegions::new_mock_only_for_use_in_testing(regions[idx].as_slice(), timestamp)?;
                pm_regions.push(mock_regions);
                idx += 1;
            }

            Ok((pm_regions, timestamp))
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
        persistent_memory_view: Ghost<PersistentMemoryRegionView>
    }

    impl VolatileMemoryMockingPersistentMemoryRegion {
        #[verifier::external_body]
        pub fn new(region_size: u64, timestamp: Ghost<PmTimestamp>) -> (result: Result<Self, ()>)
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
                                                     outstanding_write: None,
                                                     write_timestamp: timestamp@,
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
        pub fn write(&mut self, addr: u64, bytes: &[u8], timestamp: Ghost<PmTimestamp>)
            requires
                old(self).inv(),
                addr + bytes@.len() <= old(self)@.len(),
                addr + bytes@.len() <= u64::MAX
            ensures
                self.inv(),
                self@ == self@.write(addr as int, bytes@, timestamp@)
        {
            let addr_usize: usize = addr.try_into().unwrap();
            self.contents.splice(addr_usize..addr_usize+bytes.len(), bytes.iter().cloned());
            self.persistent_memory_view = Ghost(self.persistent_memory_view@.write(addr as int, bytes@, timestamp@))
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
        pub pms: Vec<VolatileMemoryMockingPersistentMemoryRegion>,
        pub fence_timestamp: Ghost<PmTimestamp>
    }

    /// So that `VolatileMemoryMockingPersistentMemoryRegions` can be
    /// used to mock a collection of persistent memory regions, it
    /// implements the trait `PersistentMemoryRegions`.

    impl PersistentMemoryRegions for VolatileMemoryMockingPersistentMemoryRegions {
        closed spec fn view(&self) -> PersistentMemoryRegionsView
        {
            PersistentMemoryRegionsView {
                regions: self.pms@.map(|_idx, pm: VolatileMemoryMockingPersistentMemoryRegion| pm@),
                fence_timestamp: self.fence_timestamp@
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
        fn write(&mut self, index: usize, addr: u64, bytes: &[u8], timestamp: Ghost<PmTimestamp>)
        {
            self.pms[index].write(addr, bytes, timestamp)
        }

        #[verifier::external_body]
        fn flush(&mut self, Ghost(timestamp): Ghost<PmTimestamp>) -> Ghost<PmTimestamp>
        {
            for which_region in iter: 0..self.pms.len()
                invariant
                    iter.end == self.pms.len(),
                    forall |i: int| 0 <= i < which_region ==>
                        self.pms[which_region as int]@ == old(self).pms[which_region as int]@.flush()
            {
                self.pms[which_region].flush();
            }
            Ghost(timestamp.inc_timestamp())
        }
    }

    /// We also implement a constructor for
    /// `VolatileMemoryMockingPersistentMemoryRegions` so it can be
    /// created by test code. We name this constructor
    /// `new_mock_only_for_use_in_testing` to make clear that it
    /// shouldn't be used in production.

    impl VolatileMemoryMockingPersistentMemoryRegions {
        #[verifier::external_body]
        pub fn new_mock_only_for_use_in_testing(region_sizes: &[u64], timestamp: Ghost<PmTimestamp>) -> (result: Result<Self, ()>)
            ensures
                match result {
                    Ok(pm_regions) => {
                        &&& pm_regions.inv()
                        &&& pm_regions@.no_outstanding_writes()
                        &&& pm_regions@.len() == region_sizes@.len()
                        &&& forall |i| 0 <= i < region_sizes@.len() ==> #[trigger] pm_regions@[i].len() == region_sizes@[i]
                        &&& pm_regions@.timestamp_corresponds_to_regions(timestamp@)
                    },
                    Err(_) => true
                }
        {
            let mut pms = Vec::<VolatileMemoryMockingPersistentMemoryRegion>::new();
            for &region_size in region_sizes {
                let pm = VolatileMemoryMockingPersistentMemoryRegion::new(region_size, timestamp)?;
                pms.push(pm);
            }
            Ok(Self {pms, fence_timestamp: timestamp})
        }
    }

}
