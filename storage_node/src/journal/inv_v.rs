use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::{pmcopy_t::*, pmemspec_t::*, pmemutil_v::*, traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe}};
use crate::common::subrange_v::*;
use crate::common::util_v::*;
use crate::common::align_v::*;
use crate::pmem::wrpm_t::*;
use super::entry_v::*;
use super::journal_v::*;
use super::recover_v::*;
use super::setup_v::*;
use super::spec_v::*;

verus! {

impl <Perm, PM> Journal<Perm, PM>
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
{
    pub(super) open spec fn journal_entries_matches(self, read_state: Seq<u8>) -> bool
    {
        &&& 0 <= self.sm.journal_entries_start
        &&& self.sm.journal_entries_start + self.constants.journal_capacity <= self.sm.journal_entries_end
        &&& recover_journal_entries(read_state, self.sm, self.journal_length) == Some(self.entries@)
    }

    pub(super) open spec fn inv_journaled_addrs_complete(self) -> bool
    {
        journaled_addrs_complete(self.entries@, self.journaled_addrs@)
    }

    pub(super) open spec fn inv_constants_match(self) -> bool
    {
        &&& self.constants.app_version_number == self.sm.app_version_number
        &&& self.constants.app_program_guid == self.sm.app_program_guid
        &&& self.constants.journal_capacity == self.sm.journal_entries_end - self.sm.journal_entries_start
        &&& self.constants.app_area_start == self.sm.app_area_start
        &&& self.constants.app_area_end == self.sm.app_area_end
    }

    pub(super) open spec fn inv(self) -> bool
    {
        let pmv = self.wrpm.view();
        &&& self.wrpm.inv()
        &&& pmv.valid()
        &&& self.inv_constants_match()
        &&& self.constants.app_area_end == pmv.len()
        &&& recover_version_metadata(pmv.durable_state) == Some(self.vm@)
        &&& recover_static_metadata(pmv.durable_state, self.vm@) == Some(self.sm)
        &&& recover_committed_cdb(pmv.durable_state, self.sm) matches Some(committed)
        &&& self.status is Quiescent ==> !committed
        &&& apply_journal_entries(pmv.read_state, self.entries@, 0, self.sm) == Some(self@.commit_state)
        &&& self.inv_journaled_addrs_complete()
    }

    pub(super) open spec fn valid_internal(self) -> bool
    {
        &&& self.inv()
        &&& self.status is Quiescent
    }
}

}
