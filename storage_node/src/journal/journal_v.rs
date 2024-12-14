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
    current: Ghost<JournalState>,
    committed: bool,
    entries: Ghost<Seq<JournalEntry>>,
    num_journal_bytes: u64,
}

impl View for Journal {
    type V = JournalState;
    
    closed spec fn view(&self) -> JournalState
    {
        self.current@
    }
}

impl Journal {
    pub closed spec fn journal_data_matches(self, read_state: Seq<u8>) -> bool
    {
        &&& 0 <= self.sm.journal_data_start
        &&& self.sm.journal_data_start + self.num_journal_bytes + u64::spec_size_of() <= self.sm.journal_data_end
        &&& self.sm.journal_data_end <= read_state.len()
        &&& {
            let journal_bytes = opaque_section(read_state, self.sm.journal_data_start as int,
                                               self.num_journal_bytes as nat);
            parse_journal_data(journal_bytes, 0) == Some(self.entries@)
        }
    }

    pub closed spec fn inv_journaled_addrs_complete(self) -> bool
    {
        forall|entry, addr| #![trigger self.entries@.contains(entry), self.current@.journaled_addrs.contains(addr)]
            self.entries@.contains(entry) && entry.addr <= addr < entry.addr + entry.bytes.len() ==>
            self.current@.journaled_addrs.contains(addr)
    }

    pub closed spec fn inv(self, pmv: PersistentMemoryRegionView) -> bool
    {
        &&& recover_version_metadata(pmv.durable_state) == Some(self.vm@)
        &&& recover_static_metadata(pmv.durable_state, self.vm@.static_metadata_addr as int) == Some(self.sm)
        &&& recover_cdb(pmv.durable_state, self.sm.committed_cdb_addr as int) == Some(self.committed)
        &&& self.committed ==> recover_journal_case_committed(pmv.durable_state, self.sm) == Some(self@.commit)
        &&& self@.abort == opaque_subrange(pmv.durable_state, self.sm.app_area_start as int, self.sm.app_area_end as int)
        &&& self@.read == opaque_subrange(pmv.read_state, self.sm.app_area_start as int, self.sm.app_area_end as int)
        &&& Some(self@.commit) == apply_journal_entries(self@.abort, self.entries@, 0, self.sm)
        &&& self.inv_journaled_addrs_complete()
    }

    pub closed spec fn valid(self, pmv: PersistentMemoryRegionView) -> bool
    {
        &&& self.inv(pmv)
        &&& self.status is Quiescent
    }
}

}
