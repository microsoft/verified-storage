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
    PersistentMemoryRegionView, PersistentMemoryRegions, PersistentMemoryRegionsView,
};
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
        id: u128,
    }

    // This executable method can be called to compute a random GUID.
    // It uses the external `rand` crate.
    #[verifier::external_body]
    pub exec fn generate_fresh_device_id() -> (out: u128)
    {
        deps_hack::rand::thread_rng().gen::<u128>()
    }

    impl VolatileMemoryMockingPersistentMemoryDevice {
        pub fn new(capacity: u64) -> (result: Self)
            ensures
                result.len() == capacity
        {
            Self {
                capacity,
                id: generate_fresh_device_id()
            }
        }
    }

    impl PmDevice<VolatileMemoryMockingPersistentMemoryRegion> for VolatileMemoryMockingPersistentMemoryDevice {
        closed spec fn len(&self) -> u64 {
            self.capacity
        }

        fn capacity(&self) -> u64 {
            self.capacity
        }

        /// Returns a vector of `VolatileMemoryMockingPersistentMemoryRegion`s based on the given vector of sizes.
        /// The caller can later combine these into `VolatileMemoryMockingPersistentMemoryRegions` in whatever
        /// configuration they want.
        fn get_regions(self, regions: Vec<u64>) -> Result<(Vec<VolatileMemoryMockingPersistentMemoryRegion>), ()> {
            let mut pm_regions: Vec<VolatileMemoryMockingPersistentMemoryRegion> = Vec::new();
            let timestamp: Ghost<PmTimestamp> = Ghost(PmTimestamp::new(self.id as int));

            // This is easier to prove with a while loop than a for loop -- it's hard to establish a relationship
            // between `idx` and the length of pm_regions in a for loop
            let mut idx = 0;
            while idx < regions.len()
                invariant
                    0 <= idx <= regions@.len(),
                    pm_regions@.len() == idx,
                    forall |j| #![auto] 0 <= j < idx ==> pm_regions[j].spec_device_id() == timestamp@.device_id(),
                    forall |j| #![auto] 0 <= j < idx ==> pm_regions[j]@.len() == regions[j]@,
                    forall |j| #![auto] 0 <= j < idx ==> pm_regions[j].inv()
            {
                let mock_regions = VolatileMemoryMockingPersistentMemoryRegion::new(regions[idx], self.id, timestamp)?;
                pm_regions.push(mock_regions);
                idx += 1;
            }

            Ok(pm_regions)
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

    impl PersistentMemoryRegion for VolatileMemoryMockingPersistentMemoryRegion {
        #[verifier::external_body]
        fn new(region_size: u64, device_id: u128, timestamp: Ghost<PmTimestamp>) -> (result: Result<Self, ()>)
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
            let persistent_memory_view = Ghost(PersistentMemoryRegionView { state, device_id, current_timestamp: timestamp@ });
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
        fn write(&mut self, addr: u64, bytes: &[u8])
        {
            let addr_usize: usize = addr.try_into().unwrap();
            self.contents.splice(addr_usize..addr_usize+bytes.len(), bytes.iter().cloned());
            self.persistent_memory_view = Ghost(self.persistent_memory_view@.write(addr as int, bytes@))
        }

        fn flush(&mut self)
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
        pub current_timestamp: Ghost<PmTimestamp>,
        pub device_id: u128,
    }

    /// So that `VolatileMemoryMockingPersistentMemoryRegions` can be
    /// used to mock a collection of persistent memory regions, it
    /// implements the trait `PersistentMemoryRegions`.

    impl PersistentMemoryRegions for VolatileMemoryMockingPersistentMemoryRegions {
        closed spec fn view(&self) -> PersistentMemoryRegionsView
        {
            PersistentMemoryRegionsView {
                regions: self.pms@.map(|_idx, pm: VolatileMemoryMockingPersistentMemoryRegion| pm@),
                current_timestamp: self.current_timestamp@,
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
            // Ghost(timestamp.inc_timestamp())
            self.current_timestamp = Ghost(self.current_timestamp@.inc_timestamp());
        }
    }

    impl VolatileMemoryMockingPersistentMemoryRegions {
        // TODO: ideally this would be a trait method of PersistentMemoryRegions, but the generics don't work out very well.
        fn combine_regions(regions: Vec<VolatileMemoryMockingPersistentMemoryRegion>, timestamp: Ghost<PmTimestamp>) -> (result: Self)
            requires
                regions@.len() > 0,
                forall |i| 0 <= i < regions@.len() ==> {
                    let region = #[trigger] regions[i];
                    &&& region.inv()
                    &&& region.spec_device_id() == timestamp@.device_id()
                }
            ensures
                result@.len() == regions@.len(),
                result.inv(),
                result.spec_device_id() == timestamp@.device_id()
        {
            let device_id = regions[0].device_id();
            Self {
                pms: regions,
                current_timestamp: timestamp,
                device_id
            }
        }
    }

    // impl VolatileMemoryMockingPersistentMemoryRegion {
    //     #[verifier::external_body]
    //     pub fn new_mock_only_for_use_in_testing(region_size: u64, device_id: u128, timestamp: Ghost<PmTimestamp>) -> (result: Result<Self, ()>)
    //         requires
    //             device_id == timestamp@.device_id(),
    //         ensures
    //             match result {
    //                 Ok(pm_region) => {
    //                     &&& pm_region.inv()
    //                     &&& pm_region@.no_outstanding_writes()
    //                     &&& pm_region@.len() == region_size
    //                     &&& pm_region.device_id() == device_id
    //                 }
    //             }
    //     {

    //     }
    // }

    // /// We also implement a constructor for
    // /// `VolatileMemoryMockingPersistentMemoryRegions` so it can be
    // /// created by test code. We name this constructor
    // /// `new_mock_only_for_use_in_testing` to make clear that it
    // /// shouldn't be used in production.

    // impl VolatileMemoryMockingPersistentMemoryRegions {
    //     #[verifier::external_body]
    //     pub fn new_mock_only_for_use_in_testing(region_sizes: &[u64], timestamp: Ghost<PmTimestamp>) -> (result: Result<Self, ()>)
    //         ensures
    //             match result {
    //                 Ok(pm_regions) => {
    //                     &&& pm_regions.inv()
    //                     &&& pm_regions@.no_outstanding_writes()
    //                     &&& pm_regions@.len() == region_sizes@.len()
    //                     &&& forall |i| 0 <= i < region_sizes@.len() ==> #[trigger] pm_regions@[i].len() == region_sizes@[i]
    //                     &&& pm_regions@.timestamp_corresponds_to_regions(timestamp@)
    //                 },
    //                 Err(_) => true
    //             }
    //     {
    //         let mut pms = Vec::<VolatileMemoryMockingPersistentMemoryRegion>::new();
    //         for &region_size in region_sizes {
    //             let pm = VolatileMemoryMockingPersistentMemoryRegion::new(region_size, timestamp)?;
    //             pms.push(pm);
    //         }
    //         Ok(Self {pms, fence_timestamp: timestamp})
    //     }
    // }

}
