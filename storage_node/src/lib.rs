#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

pub mod multilog;
pub mod paged_kv;
pub mod pmem;

use crate::multilog::multilogimpl_t::*;
use crate::multilog::multilogimpl_v::*;
use crate::pmem::device_t::*;
use crate::pmem::pmemmock_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::timestamp_t::*;

verus! {
    fn main() {}

    fn test_multilog_with_timestamps() -> bool {
        // TODO: ideally we wouldn't invoke this from trusted code, but we need it to prove the relationships
        // between different timestamps from the same region
        proof { lemma_auto_timestamp_helpers(); }

        // set up vectors to mock persistent memory
        let device_capacity = 1024;
        let log_capacity = 256;
        let mut device_regions = Vec::new();
        device_regions.push(log_capacity); device_regions.push(log_capacity);
        device_regions.push(log_capacity); device_regions.push(log_capacity);
        let ghost old_device_regions = device_regions@;

        // obtain a device abstraction with enough space for the requested regions
        let device = VolatileMemoryMockingPersistentMemoryDevice::new(device_capacity);

        // Required to pass the precondition for get_regions -- we need to unroll the
        // recursive spec fn `fold_left` enough times to calculate the sum of
        // all of the PM regions.
        proof { reveal_with_fuel(Seq::fold_left, 5); }
        let result = device.get_regions(device_regions);

        let mut regions = match result {
            Ok(regions) => regions,
            Err(()) => return false
        };

        let mut multilog1_regions = Vec::new();
        let mut multilog2_regions = Vec::new();
        multilog1_regions.push(regions.pop().unwrap());
        multilog1_regions.push(regions.pop().unwrap());
        multilog2_regions.push(regions.pop().unwrap());
        multilog2_regions.push(regions.pop().unwrap());

        // combine individual regions into groups so we can use them to set up multilogs
        let mut multilog1_regions = VolatileMemoryMockingPersistentMemoryRegions::combine_regions(multilog1_regions);
        let mut multilog2_regions = VolatileMemoryMockingPersistentMemoryRegions::combine_regions(multilog2_regions);

        let result = MultiLogImpl::setup(&mut multilog1_regions);
        let (log1_capacities, multilog_id1) = match result {
            Ok((log1_capacities, multilog_id)) => (log1_capacities, multilog_id),
            Err(_) => return false
        };

        let result = MultiLogImpl::setup(&mut multilog2_regions);
        let (log2_capacities, multilog_id2) = match result {
            Ok((log2_capacities, multilog_id)) => (log2_capacities, multilog_id),
            Err(_) => return false
        };

        // set up vectors for a second PM device (which we are pretending is separate in terms of
        // flush/fence effects from the first device)
        let mut device2_regions = Vec::new();
        device2_regions.push(log_capacity); device2_regions.push(log_capacity);
        device2_regions.push(log_capacity); device2_regions.push(log_capacity);

        let device2 = VolatileMemoryMockingPersistentMemoryDevice::new(device_capacity);
        let result = device2.get_regions(device2_regions);

        let mut regions = match result {
            Ok(regions) => regions,
            Err(()) => return false
        };

        let mut multilog3_regions = Vec::new();
        let mut multilog4_regions = Vec::new();
        multilog3_regions.push(regions.pop().unwrap());
        multilog3_regions.push(regions.pop().unwrap());
        multilog4_regions.push(regions.pop().unwrap());
        multilog4_regions.push(regions.pop().unwrap());

        let mut multilog3_regions = VolatileMemoryMockingPersistentMemoryRegions::combine_regions(multilog3_regions);
        let mut multilog4_regions = VolatileMemoryMockingPersistentMemoryRegions::combine_regions(multilog4_regions);

        let result = MultiLogImpl::setup(&mut multilog3_regions);
        let (log3_capacities, multilog_id3) = match result {
            Ok((log3_capacities, multilog_id)) => (log3_capacities, multilog_id),
            Err(_) => return false
        };


        let result = MultiLogImpl::setup(&mut multilog4_regions);
        let (log4_capacities, multilog_id4) = match result {
            Ok((log4_capacities, multilog_id)) => (log4_capacities, multilog_id),
            Err(_) => return false
        };

        // start the logs
        let result = MultiLogImpl::start(multilog1_regions, multilog_id1);
        let mut multilog1 = match result {
            Ok(multilog) => multilog,
            Err(_) => return false
        };

        let result = MultiLogImpl::start(multilog2_regions, multilog_id2);
        let mut multilog2 = match result {
            Ok(multilog) => multilog,
            Err(_) => return false
        };

        let result = MultiLogImpl::start(multilog3_regions, multilog_id3);
        let mut multilog3 = match result {
            Ok(multilog) => multilog,
            Err(_) => return false
        };

        let result = MultiLogImpl::start(multilog4_regions, multilog_id4);
        let multilog4 = match result {
            Ok(multilog) => multilog,
            Err(_) => return false
        };

        let mut vec = Vec::new();
        vec.push(1); vec.push(2); vec.push(3);

        let ghost old1 = multilog1;
        let ghost old2 = multilog2;

        let result1 = multilog1.tentatively_append(0, vec.as_slice());
        let result2 = multilog1.tentatively_append(1, vec.as_slice());
        match (result1, result2) {
            (Ok(_), Ok(_)) => {}
            _=> return false
        }

        let result1 = multilog2.tentatively_append(0, vec.as_slice());
        let result2 = multilog2.tentatively_append(1, vec.as_slice());
        match (result1, result2) {
            (Ok(_), Ok(_)) => {}
            _=> return false
        }

        let result = multilog2.commit();
        match result {
            Ok(_) => {}
            _ => return false
        }

        // we should now be able to (attempt) to update multilog1's ghost state using multilog2's
        // timestamp. doing so here is kind of silly (we can't do anything differently); it's just
        // to make sure the interface works and makes some sense.

        // I should be allowed to (as in, verification will succeed) try to update
        // multilog1's timestamp using multilog2's.
        multilog1.update_timestamp(Ghost(multilog2.get_timestamp()));

        // // this should not verify, because multilog3 is on a different device from
        // // multilog2
        // multilog3.update_timestamp(Ghost(multilog2.get_timestamp()));

        let result = multilog1.commit();
        match result {
            Ok(_) => {}
            _ => return false
        }

        let result = multilog2.advance_head(0, 2);
        match result {
            Ok(_) => {}
            _ => return false
        }

        let result = multilog1.advance_head(0, 2);
        match result {
            Ok(_) => {}
            _ => return false
        }

        // multilog1's timestamp is now ahead of multilog2's, so we can update
        // multilog2
        multilog2.update_timestamp(Ghost(multilog1.get_timestamp()));

        // Note: The timestamp function can only be called with a timestamp
        // that is provably greater than the timestamp of the component
        // we are trying to update. We could write it as a no-op when the
        // given timestamp is lte the component, but that just kicks the can
        // down the road to the next time you want prove something about what
        // is and is not persistent.

        true
    }
}
