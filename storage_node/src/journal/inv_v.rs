use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::pmemspec_t::*;
use crate::common::subrange_v::*;
use crate::pmem::power_t::*;
use super::entry_v::*;
use super::impl_v::*;
use super::recover_v::*;

verus! {

pub(super) enum JournalStatus {
    Quiescent,
    WritingJournal,
    Committed,
}

impl <Perm, PermFactory, PM> Journal<Perm, PermFactory, PM>
where
    PM: PersistentMemoryRegion,
    Perm: CheckPermission<Seq<u8>>,
    PermFactory: PermissionFactory<Seq<u8>, Perm>,
{
    pub(super) open spec fn inv_constants_match(self) -> bool
    {
        &&& self.constants.app_version_number == self.sm.app_version_number
        &&& self.constants.app_program_guid == self.sm.app_program_guid
        &&& self.constants.journal_capacity == self.sm.journal_entries_end - self.sm.journal_entries_start
        &&& self.constants.app_area_start == self.sm.app_area_start
        &&& self.constants.app_area_end == self.sm.app_area_end
    }

    pub(super) open spec fn inv_perm_factory_allows_app_equivalent_changes(self) -> bool
    {
        &&& self.perm_factory@.id() == self.powerpm.id()
        &&& forall|s1: Seq<u8>, s2: Seq<u8>| Self::recovery_equivalent_for_app(s1, s2) ==>
            #[trigger] self.perm_factory@.check_permission(s1, s2)
    }

    pub(super) open spec fn inv(self) -> bool
    {
        let pmv = self.powerpm.view();
        &&& self.powerpm.inv()
        &&& self@.valid()
        &&& pmv.valid()
        &&& self.inv_constants_match()
        &&& self.inv_perm_factory_allows_app_equivalent_changes()
        &&& self.constants.app_area_end == pmv.len()
        &&& recover_version_metadata(pmv.durable_state) == Some(self.vm@)
        &&& recover_static_metadata(pmv.durable_state, self.vm@) == Some(self.sm)
        &&& recover_committed_cdb(pmv.durable_state, self.sm) matches Some(committed)
        &&& match self.status@ {
            JournalStatus::Quiescent => {
                &&& !committed
                &&& seqs_match_except_in_range(pmv.durable_state, pmv.read_state, self.sm.app_area_start as int,
                                              self.sm.app_area_end as int)
            },
            JournalStatus::WritingJournal => !committed,
            JournalStatus::Committed => committed,
        }
        &&& journal_entries_valid(self.entries@, self.sm)
        &&& journaled_addrs_complete(self.entries@, self.journaled_addrs@)
        &&& self.journal_length <= self.constants.journal_capacity
        &&& self.journal_length == space_needed_for_journal_entries_list(self.entries@)
    }
}

}
