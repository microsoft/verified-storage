use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::{pmcopy_t::*, pmemspec_t::*, pmemutil_v::*, traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe}};
use crate::common::subrange_v::*;
use crate::common::util_v::*;
use crate::common::align_v::*;
use crate::pmem::wrpm_t::*;
use super::layout_v::*;
use super::setup_v::*;
use super::spec_v::*;
use super::util_v::*;

verus! {

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
        pub exec fn new() -> (result: Self)
            ensures
                result@ == Seq::<JournalEntry>::empty(),
        {
            let result = Self{ entries: Vec::<ConcreteJournalEntry>::new() };
            assert(result@ =~= Seq::<JournalEntry>::empty());
            result
        }
    }

}
