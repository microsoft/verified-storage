use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::size_of;
use crate::pmem::wrpm_t::*;
use super::entry_v::*;
use super::*;
use super::inv_v::*;
use super::recover_v::*;
use super::setup_v::*;
use super::spec_v::*;
use super::start_v::*;

verus! {

impl <Perm, PM> Journal<Perm, PM>
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
{
    pub exec fn read_object<T>(&self, start: u64, crc_addr: u64) -> (result: Option<T>)
        where
            T: PmCopy,
        requires
            self.valid(),
            recover_object::<T>(self@.read_state, start as int, crc_addr as int) is Some,
            crc_addr + u64::spec_size_of() <= start || start + T::spec_size_of() <= crc_addr, // object doesn't overlap CRC
        ensures
            match result {
                None => !self@.pm_constants.impervious_to_corruption(),
                Some(x) => recover_object::<T>(self@.read_state, start as int, crc_addr as int) == Some(x),
            },
    {
        exec_recover_object::<PM, T>(self.wrpm.get_pm_region_ref(), start, crc_addr)
    }

    pub exec fn read_cdb(&self, addr: u64) -> (result: Option<bool>)
        requires
            self.valid(),
            recover_cdb(self@.read_state, addr as int) is Some,
        ensures
            match result {
                None => !self@.pm_constants.impervious_to_corruption(),
                Some(b) => recover_cdb(self@.read_state, addr as int) == Some(b),
            },
    {
        exec_recover_cdb(self.wrpm.get_pm_region_ref(), addr)
    }
    
    pub exec fn read_bytes(&self, start: u64, num_bytes: u64, crc_addr: u64) -> (result: Option<Vec<u8>>)
        requires
            self.valid(),
            recover_bytes(self@.read_state, start as int, num_bytes as nat, crc_addr as int) is Some,
            crc_addr + u64::spec_size_of() <= start || start + num_bytes <= crc_addr, // bytes don't overlap CRC
        ensures
            match result {
                None => !self@.pm_constants.impervious_to_corruption(),
                Some(s) => s@ == recover_bytes(self@.read_state, start as int, num_bytes as nat, crc_addr as int).unwrap(),
            },
    {
        exec_recover_bytes(self.wrpm.get_pm_region_ref(), start, num_bytes, crc_addr)
    }
}

}

