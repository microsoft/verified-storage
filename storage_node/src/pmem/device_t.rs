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

    pub trait PmDevice<PMRegion: PersistentMemoryRegion> {
        spec fn len(&self) -> u64;

        exec fn capacity(&self) -> (result: u64)
            ensures
                result == self.len();

        /// `get_regions` consumes the PmDevice so it cannot be used to obtain any more regions or another timestamp.
        /// It returns a set of `PersistentMemoryRegion`s based on the given sizes and a single ghost timestamp
        /// that can be used with all of the regions.
        /// TODO: the recursive spec function in the precondition makes it hard to satisfy the precondition...
        exec fn get_regions(self, regions: Vec<u64>) -> (result: Result<Vec<PMRegion>, ()>)
        where
            Self: Sized
        requires
            ({
                let region_size_sum = regions@.fold_left(0, |acc: int, x| acc + x);
                region_size_sum <= self.len()
            }),
            1 <= regions@.len() < usize::MAX,
        ensures
            match result {
                Ok(regions_list) => {
                    &&& regions@.len() == regions_list@.len()
                    // TODO: why does verification only go through if these are split up
                    // into separate forall statements?
                    &&& forall |i| #![auto] 0 <= i < regions_list@.len() ==> {
                        &&& regions_list[i]@.len() == regions[i]
                    }
                    &&& forall |i| #![auto] 0 <= i < regions_list@.len() ==> {
                        &&& regions_list[i].inv()
                    }
                    &&& forall |i| 0 <= i < regions_list@.len() ==> {
                        let region = #[trigger] regions_list[i];
                        &&& region@.current_timestamp == regions_list[0]@.current_timestamp
                    }
                    &&& forall |i| 0 <= i < regions_list@.len() ==> {
                        let region = #[trigger] regions_list[i];
                        &&& region.spec_device_id() == regions_list[0].spec_device_id()
                    }
                }
                Err(_) => true // TODO
            };
}
}
