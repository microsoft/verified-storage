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

    pub trait PmDevice {
        type RegionDesc : RegionDescriptor;

        spec fn len(&self) -> u64;

        exec fn capacity(&self) -> (result: u64)
            ensures
                result == self.len();

        spec fn spec_device_id(&self) -> u128;

        exec fn device_id(&self) -> (result: u128)
            ensures
                result == self.spec_device_id();

        // We treat a device like a stream with a cursor indicating the current offset.
        // Requesting x bytes from the device for a new region moves the cursor along by
        // x bytes, to prevent bytes from being included in multiple regions.
        // If there are no more bytes left, cursor is None.
        spec fn spec_get_cursor(&self) -> Option<u64>;

        exec fn get_cursor(&self) -> (result: Option<u64>)
            ensures
                result == self.spec_get_cursor();

        // spec fn spec_inc_curspor(&mut self, len: u64);

        exec fn inc_cursor(&mut self, len: u64)
            requires
                match old(self).spec_get_cursor() {
                    Some(cursor) => cursor + len < old(self).len(),
                    None => false
                }
            ensures
                match (old(self).spec_get_cursor(), self.spec_get_cursor()) {
                    (Some(old_cursor), Some(new_cursor)) => old_cursor + len == new_cursor,
                    (Some(old_cursor), None) => old_cursor + len == self.len(),
                    _ => false
                };

        // Getting a new region returns a RegionDescriptor that we can use to construct a
        // persistent memory region of serializable objects.
        // `len` is in terms of BYTES, as we don't yet know the size of the object the region will store
        exec fn get_new_region(&mut self, len: u64) -> (result: Result<Self::RegionDesc, ()>)
            requires
                old(self).spec_get_cursor().is_Some(),
                match old(self).spec_get_cursor() {
                    Some(cursor) => cursor + len < old(self).len(),
                    None => false
                }
            ensures
                match result {
                    Ok(region_desc) => {
                        &&& match (old(self).spec_get_cursor(), self.spec_get_cursor()) {
                            (Some(old_cursor), Some(new_cursor)) => old_cursor + len == new_cursor,
                            (Some(old_cursor), None) => old_cursor + len == self.len(),
                            _ => false
                        }
                        &&& region_desc@.device_id == self.spec_device_id()
                        &&& region_desc@.len == len
                        // TODO: check timestamp(s)
                    }
                    Err(()) => true // TODO
                }
            ;
    }

    pub trait RegionDescriptor {
        spec fn view(&self) -> RegionDescriptorView;

        fn device_id(&self) -> (result: u128)
            ensures
                result == self@.device_id;

        // NOTE: this is the length in BYTES
        fn len(&self) -> (result: u64)
            ensures
                result == self@.len;
    }

    pub struct RegionDescriptorView {
        // pub bytes: Seq<u8>,
        pub len: u64,
        pub timestamp: PmTimestamp,
        pub device_id: u128,
    }
}
