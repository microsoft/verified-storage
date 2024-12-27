use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::{pmcopy_t::*, pmemspec_t::*, pmemutil_v::*, traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe}};
use crate::common::util_v::*;
use deps_hack::PmCopy;

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
    pub num_journal_entries: int,
}

pub enum JournalError {
    CRCError,
    InvalidAlignment,
    NotEnoughSpace,
}

#[verifier::ext_equal]
pub struct RecoveredJournal {
    pub constants: JournalConstants,
    pub state: Seq<u8>,
}

#[verifier::ext_equal]
pub struct JournalSetupParameters {
    pub app_version_number: u64,
    pub app_program_guid: u128,
    pub max_journal_entries: u64,
    pub max_journaled_bytes: u64,
    pub app_area_size: u64,
    pub app_area_alignment: u64,
}

impl JournalSetupParameters {
    pub open spec fn valid(&self) -> bool
    {
        0 < self.app_area_alignment
    }
}
    
}
