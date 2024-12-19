use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::{pmcopy_t::*, pmemspec_t::*, pmemutil_v::*, traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe}};
use crate::common::subrange_v::*;
use crate::common::util_v::*;
use super::layout_v::*;
use super::spec_v::*;
use deps_hack::PmCopy;

verus! {

enum JournalStatus {
    Quiescent
}

struct Journal {
    vm: Ghost<JournalVersionMetadata>,
    sm: JournalStaticMetadata,
    status: JournalStatus,
    constants: JournalConstants,
    static_area: Ghost<Seq<u8>>,
    dynamic_area_on_crash: Ghost<Seq<u8>>,
    dynamic_area_on_read: Ghost<Seq<u8>>,
    dynamic_area_on_commit: Ghost<Seq<u8>>,
    committed: bool,
    journal_length: u64,
    journaled_addrs: Ghost<Set<int>>,
    entries: Ghost<Seq<JournalEntry>>,
}

impl View for Journal {
    type V = JournalView;
    
    closed spec fn view(&self) -> JournalView
    {
        JournalView{
            constants: self.constants,
            static_area: self.static_area@,
            dynamic_area_on_crash: self.dynamic_area_on_crash@,
            dynamic_area_on_read: self.dynamic_area_on_read@,
            dynamic_area_on_commit: self.dynamic_area_on_commit@,
            remaining_capacity: self.constants.journal_capacity - self.journal_length,
            journaled_addrs: self.journaled_addrs@,
        }
    }
}

impl Journal {
    
    pub closed spec fn journal_entries_matches(self, read_state: Seq<u8>) -> bool
    {
        &&& 0 <= self.sm.journal_entries_start
        &&& self.sm.journal_entries_start + self.constants.journal_capacity <= self.sm.journal_entries_end
        &&& recover_journal_entries(read_state, self.sm.journal_entries_start as int, self.sm.journal_entries_end as int) == Some(self.entries@)
    }

    pub closed spec fn inv_journaled_addrs_complete(self) -> bool
    {
        forall|entry, addr| #![trigger self.entries@.contains(entry), self.journaled_addrs@.contains(addr)]
            self.entries@.contains(entry) && entry.addr <= addr < entry.addr + entry.bytes.len() ==>
            self.journaled_addrs@.contains(addr)
    }

    pub closed spec fn inv(self, pmv: PersistentMemoryRegionView) -> bool
    {
        &&& recover_version_metadata(pmv.durable_state) == Some(self.vm@)
        &&& recover_static_metadata(pmv.durable_state, self.vm@) == Some(self.sm)
        &&& recover_cdb(pmv.durable_state, self.sm.committed_cdb_start as int) == Some(self.committed)
        &&& self.committed ==> recover_app_dynamic_area_case_committed(pmv.durable_state, self.sm) == Some(self@.dynamic_area_on_commit)
        &&& self@.dynamic_area_on_crash == opaque_subrange(pmv.durable_state, self.sm.app_dynamic_area_start as int, self.sm.app_dynamic_area_end as int)
        &&& self@.dynamic_area_on_read == opaque_subrange(pmv.read_state, self.sm.app_dynamic_area_start as int, self.sm.app_dynamic_area_end as int)
        &&& Some(self@.dynamic_area_on_commit) == apply_journal_entries(self@.dynamic_area_on_read, self.entries@, 0, self.sm)
        &&& self.inv_journaled_addrs_complete()
    }

    pub closed spec fn valid_closed(self, pmv: PersistentMemoryRegionView) -> bool
    {
        &&& self.inv(pmv)
        &&& self.status is Quiescent
    }

    pub open spec fn valid(self, pmv: PersistentMemoryRegionView) -> bool
    {
        &&& self.valid_closed(pmv)
    }
}

}
