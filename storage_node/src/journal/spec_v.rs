use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::common::nonlinear_v::*;
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
        &&& 0 <= start <= end <= self.len()
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
        &&& 0 <= start <= end <= self.len()
        &&& self.matches_in_range(other, 0, start)
        &&& self.matches_in_range(other, end, self.len() as int)
    }
}

pub broadcast proof fn broadcast_journal_view_matches_in_range_effect_on_subranges(
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
    broadcast use broadcast_seqs_match_in_range_effect_on_subranges;
}

pub broadcast proof fn broadcast_journal_view_matches_in_range_can_narrow_range(
    jv1: JournalView,
    jv2: JournalView,
    start: int,
    end: int,
    new_start: int,
    new_end: int,
)
    requires
        #[trigger] jv1.matches_in_range(jv2, start, end),
        0 <= start <= new_start <= new_end <= end <= jv1.len(),
    ensures
        #[trigger] jv1.matches_in_range(jv2, new_start, new_end),
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

pub broadcast group broadcast_journal_view_matches_in_range {
    broadcast_journal_view_matches_in_range_can_narrow_range,
    broadcast_journal_view_matches_in_range_effect_on_subranges,
}

}
