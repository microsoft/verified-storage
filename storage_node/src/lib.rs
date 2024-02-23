#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

pub mod multilog;
pub mod pmem;

use crate::multilog::multilogimpl_t::*;
use crate::multilog::multilogimpl_v::*;
use crate::pmem::device_t::*;
use crate::pmem::pmemmock_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;

verus! {
    fn main() {}

    fn test_multilog_with_timestamps() -> bool {
        proof { lemma_auto_if_no_outstanding_writes_then_flush_is_idempotent(); }

        let device_capacity: u64 = 1024;
        let log_capacity: u64 = 256;
        let mut regions1 = Vec::new();
        let mut regions2 = Vec::new();
        regions1.push(log_capacity);
        regions1.push(log_capacity);
        regions2.push(log_capacity);
        regions2.push(log_capacity);

        let mut device_regions = Vec::new();
        device_regions.push(regions1);
        device_regions.push(regions2);
        let ghost old_device_regions = device_regions@;

        let device = VolatileMemoryMockingPersistentMemoryDevice::new(device_capacity);

        // Required to pass the precondition for get_regions -- we need to unroll the
        // recursive spec fn `fold_left` enough times to calculate the sum of
        // all of the PM regions specified in our 2D vector.
        proof { reveal_with_fuel(Seq::fold_left, 3); }
        let result = device.get_regions(device_regions);

        let (mut regions, timestamp) = match result {
            Ok((regions, timestamp)) => (regions, timestamp),
            Err(()) => return false
        };

        // We have to pop from `regions` so we can get ownership over its elements.
        // Ideally, this would be a `pop_front` so that we don't have to go backwards,
        // but in this example it's fine because all of the regions are identical.
        let mut region1 = regions.pop().unwrap();
        let mut region2 = regions.pop().unwrap();
        assert(regions@.len() == 0);


        let result = MultiLogImpl::setup(&mut region1, timestamp);
        let (log1_capacities, timestamp, multilog_id1) = match result {
            Ok((log1_capacities, timestamp, multilog_id)) => (log1_capacities, timestamp, multilog_id),
            Err(_) => return false
        };

        let result = MultiLogImpl::setup(&mut region2, timestamp);
        let (log2_capacities, timestamp, multilog_id2) = match result {
            Ok((log1_capacities, timestamp, multilog_id)) => (log1_capacities, timestamp, multilog_id),
            Err(_) => return false
        };

        let mut regions3 = Vec::new();
        let mut regions4 = Vec::new();
        regions3.push(log_capacity);
        regions3.push(log_capacity);
        regions4.push(log_capacity);
        regions4.push(log_capacity);

        let mut device_regions2 = Vec::new();
        device_regions2.push(regions3);
        device_regions2.push(regions4);

        let device2 = VolatileMemoryMockingPersistentMemoryDevice::new(device_capacity);
        let result = device2.get_regions(device_regions2);

        let (mut regions, timestamp2) = match result {
            Ok((regions, timestamp)) => (regions, timestamp),
            Err(()) => return false
        };

        let mut region3 = regions.pop().unwrap();
        let mut region4 = regions.pop().unwrap();

        let result = MultiLogImpl::setup(&mut region3, timestamp2);
        let (log3_capacities, timestamp2, multilog_id3) = match result {
            Ok((log3_capacities, timestamp, multilog_id)) => (log3_capacities, timestamp, multilog_id),
            Err(_) => return false
        };

        let result = MultiLogImpl::setup(&mut region4, timestamp2);
        let (log4_capacities, timestamp2, multilog_id4) = match result {
            Ok((log4_capacities, timestamp, multilog_id)) => (log4_capacities, timestamp, multilog_id),
            Err(_) => return false
        };

        proof {
            let (flushed_regions, new_timestamp) = region1@.flush(timestamp@);
            assert(flushed_regions.committed() =~= region1@.committed());

            let (flushed_regions, new_timestamp) = region2@.flush(timestamp@);
            assert(flushed_regions.committed() =~= region2@.committed());
        }

        // This should work, because `timestamp` corresponds to `region1`.
        let result = MultiLogImpl::start(region1, multilog_id1, timestamp);

        // // This should not verify, because `timestamp2` does not correspond to `region2`,
        // // even though `timestamp` and `timestamp2` have the same numerical value right now.
        // let result2 = MultiLogImpl::start(region2, multilog_id1, timestamp2);

        true
    }
}
