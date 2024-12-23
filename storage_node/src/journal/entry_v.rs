use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::{pmcopy_t::*, pmemspec_t::*, pmemutil_v::*, traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe}};
use crate::common::subrange_v::*;
use crate::common::util_v::*;
use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::pmem::wrpm_t::*;
use super::layout_v::*;
use super::setup_v::*;
use super::spec_v::*;
use super::util_v::*;

verus! {

pub open spec fn spec_space_needed_for_journal_entry(num_bytes: nat) -> int
{
    num_bytes + u64::spec_size_of() as int + u64::spec_size_of() as int
}

#[inline]
pub(super) exec fn get_space_needed_for_journal_entry(num_bytes: usize) -> (result: OverflowingU64)
    ensures
        0 <= result@,
        result@ == spec_space_needed_for_journal_entry(num_bytes as nat),
{
    let journal_entry_size = OverflowingU64::new(size_of::<u64>() as u64).add_usize(size_of::<u64>());
    journal_entry_size.add_usize(num_bytes)
}

#[verifier::ext_equal]
pub struct JournalEntry
{
    pub start: int,
    pub bytes_to_write: Seq<u8>,
}

impl JournalEntry
{
    pub(super) open spec fn end(self) -> int
    {
        self.start + self.bytes_to_write.len()
    }

    pub(super) open spec fn addrs(self) -> Set<int>
    {
        Set::<int>::new(|i| self.start <= i < self.end())
    }

    pub(super) open spec fn fits(self, sm: JournalStaticMetadata) -> bool
    {
        &&& 0 <= sm.app_area_start <= self.start
        &&& self.end() <= sm.app_area_end
    }
}

pub struct ConcreteJournalEntry
{
    pub start: u64,
    pub bytes_to_write: Vec<u8>,
}

impl View for ConcreteJournalEntry
{
    type V = JournalEntry;

    open spec fn view(&self) -> JournalEntry
    {
        JournalEntry{ start: self.start as int, bytes_to_write: self.bytes_to_write@ }
    }
}

impl DeepView for ConcreteJournalEntry
{
    type V = JournalEntry;

    open spec fn deep_view(&self) -> JournalEntry
    {
        self@
    }
}

impl ConcreteJournalEntry
{
    #[inline]
    pub exec fn new(start: u64, bytes_to_write: Vec<u8>) -> Self
    {
        Self{ start, bytes_to_write }
    }
}

pub struct ConcreteJournalEntries
{
    pub entries: Vec<ConcreteJournalEntry>,
}

impl View for ConcreteJournalEntries
{
    type V = Seq<JournalEntry>;

    open spec fn view(&self) -> Seq<JournalEntry>
    {
        self.entries.deep_view()
    }
}

impl ConcreteJournalEntries
{
    #[inline]
    pub exec fn new() -> (result: Self)
        ensures
            result@ == Seq::<JournalEntry>::empty(),
    {
        let result = Self{ entries: Vec::<ConcreteJournalEntry>::new() };
        assert(result@ =~= Seq::<JournalEntry>::empty());
        result
    }

    #[inline]
    pub exec fn push(&mut self, e: ConcreteJournalEntry)
        ensures
            self@ == old(self)@.push(e@)
    {
        self.entries.push(e);
        assert(self@ =~= old(self)@.push(e@));
    }
}

}
