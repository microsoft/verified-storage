use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::common::subrange_v::*;

verus! {

#[verifier::ext_equal]
pub struct JournalConstants {
    pub app_version_number: u64,
    pub app_program_guid: u128,
    pub journal_capacity: u64,
    pub app_area_start: u64,
    pub app_area_end: u64,
}

impl JournalConstants {
    pub open spec fn valid(self) -> bool
    {
        0 <= self.app_area_start <= self.app_area_end
    }

    pub exec fn clone(&self) -> (result: Self)
        ensures
            result == self
    {
        Self{
            app_version_number: self.app_version_number,
            app_program_guid: self.app_program_guid,
            journal_capacity: self.journal_capacity,
            app_area_start: self.app_area_start,
            app_area_end: self.app_area_end,
        }
    }
}

#[verifier::ext_equal]
pub struct JournalView {
    pub constants: JournalConstants,
    pub pm_constants: PersistentMemoryConstants,
    pub durable_state: Seq<u8>,
    pub read_state: Seq<u8>,
    pub commit_state: Seq<u8>,
    pub remaining_capacity: int,
    pub journaled_addrs: Set<int>,
}

impl JournalView {
    pub open spec fn valid(&self) -> bool
    {
        &&& self.constants.valid()
        &&& self.pm_constants.valid()
        &&& self.durable_state.len() == self.read_state.len()
        &&& self.read_state.len() == self.commit_state.len()
        &&& self.remaining_capacity >= 0
    }

    pub open spec fn len(&self) -> nat
    {
        self.durable_state.len()
    }

    pub open spec fn matches_in_range(self, other: JournalView, start: int, end: int) -> bool
    {
        &&& self.valid()
        &&& other.valid()
        &&& self.constants.app_area_start <= start <= end <= self.constants.app_area_end
        &&& seqs_match_in_range(self.durable_state, other.durable_state, start, end)
        &&& seqs_match_in_range(self.read_state, other.read_state, start, end)
        &&& seqs_match_in_range(self.commit_state, other.commit_state, start, end)
        &&& forall|addr: int| start <= addr && addr < end ==>
               self.journaled_addrs.contains(addr) == #[trigger] other.journaled_addrs.contains(addr)
    }

    pub open spec fn matches_except_in_range(self, other: JournalView, start: int, end: int) -> bool
    {
        &&& self.valid()
        &&& other.valid()
        &&& self.constants.app_area_start <= start <= end <= self.constants.app_area_end
        &&& seqs_match_in_range(self.durable_state, other.durable_state, self.constants.app_area_start as int, start)
        &&& seqs_match_in_range(self.durable_state, other.durable_state, end, self.constants.app_area_end as int)
        &&& seqs_match_in_range(self.read_state, other.read_state, self.constants.app_area_start as int, start)
        &&& seqs_match_in_range(self.read_state, other.read_state, end, self.constants.app_area_end as int)
        &&& seqs_match_in_range(self.commit_state, other.commit_state, self.constants.app_area_start as int, start)
        &&& seqs_match_in_range(self.commit_state, other.commit_state, end, self.constants.app_area_end as int)
        &&& forall|addr: int| self.constants.app_area_start <= addr < start || end <= addr < self.constants.app_area_end ==>
               self.journaled_addrs.contains(addr) == #[trigger] other.journaled_addrs.contains(addr)
    }
}

pub broadcast proof fn broadcast_journal_view_matches_in_range_can_narrow_range(
    jv1: JournalView,
    jv2: JournalView,
    outer_start: int,
    outer_end: int,
    inner_start: int,
    inner_end: int,
)
    requires
        #[trigger] jv1.matches_in_range(jv2, outer_start, outer_end),
        0 <= outer_start <= inner_start <= inner_end <= outer_end <= jv1.len(),
    ensures
        #[trigger] jv1.matches_in_range(jv2, inner_start, inner_end),
{
    broadcast use broadcast_seqs_match_in_range_can_narrow_range;
}

pub enum JournalError {
    CRCError,
    InvalidSetupParameters,
    NotEnoughSpace,
}

#[verifier::ext_equal]
pub struct RecoveredJournal {
    pub constants: JournalConstants,
    pub state: Seq<u8>,
}

}
