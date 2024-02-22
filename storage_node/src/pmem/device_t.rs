//! The `PmDevice` trait represents a single persistent memory device,
//! which may contain multiple regions. For example, a struct that
//! implements `PmDevice` may store a path to a directory in a PM file system,
//! a path to a character device, a handle for a single mmap'ed file.
//! The implementer is responsible for defining how the device is separated
//! into PMRegion(s).
//! Each `PmDevice` has a single `PmTimestamp`, which also encompasses all
//! of its regions.

use crate::pmem::pmemspec_t::*;
use crate::pmem::timestamp_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

    pub trait PmDevice<PMRegions: PersistentMemoryRegions> {
        spec fn len(&self) -> u64; // is this doing anything?

        exec fn capacity(&self) -> (result: u64)
            ensures
                result == self.len();

        /// `get_regions` consumes the PmDevice so it cannot be used to obtain any more regions or another timestamp.
        /// It returns a set of PersistentMemoryRegions based on the given sizes and a single ghost timestamp
        /// that can be used with all of the regions.
        /// TODO: the recursive spec function in the precondition makes it hard to satisfy the precondition...
        exec fn get_regions(self, regions: Vec<Vec<u64>>) -> (result: Result<(Vec<PMRegions>, Ghost<PmTimestamp>), ()>)
        where
            Self: Sized
        requires
            ({
                // the sum of region sizes must not exceed the actual size of the device
                let acc_seq = Seq::new(regions@.len(), |i| regions[i]@.fold_left(0, |acc: int, x| acc + x));
                let region_size_sum = acc_seq.fold_left(0, |acc: int, x| acc + x);
                region_size_sum <= self.len()
            }),
            1 <= regions@.len() < usize::MAX,
        ensures
            match result {
                Ok((regions_list, timestamp)) => {
                    &&& regions@.len() == regions_list@.len()
                    // NOTE: asserting each of these separately after this function only works
                    // if they get their own foralls here. Why?
                    &&& forall |i| #![auto] 0 <= i < regions_list@.len() ==> {
                            regions_list[i]@.timestamp_corresponds_to_regions(timestamp@)
                        }
                    &&& forall |i| #![auto] 0 <= i < regions_list@.len() ==> {
                        regions_list[i]@.len() == regions@[i].len()
                    }
                    &&& forall |i| #![auto] 0 <= i < regions_list@.len() ==> {
                        regions_list[i].inv()
                    }
                }
                Err(_) => true // TODO
            };
}
}
