#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

pub mod multilog;
pub mod pmem;

use crate::multilog::multilogimpl_t::*;
use crate::pmem::device_t::*;
use crate::pmem::pmemmock_t::*;
use crate::pmem::pmemspec_t::*;

verus! {
    fn main() {}

    fn test_multilog_with_timestamps() -> bool {
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
        let (log1_capacities, timestamp, multilog_id) = match result {
            Ok((log1_capacities, timestamp, multilog_id)) => (log1_capacities, timestamp, multilog_id),
            Err(_) => return false
        };

        let result = MultiLogImpl::setup(&mut region2, timestamp);
        let (log2_capacities, timestamp, multilog_id) = match result {
            Ok((log1_capacities, timestamp, multilog_id)) => (log1_capacities, timestamp, multilog_id),
            Err(_) => return false
        };

        // TODO: is this handling of timestamp sound? Could we grab a timestamp from a different
        // device that happens to be the same value as this one at some point, and use it
        // to make it look like data has been fenced when it hasn't?

        true
    }
}
