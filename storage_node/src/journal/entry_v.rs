use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::size_of;
use crate::common::subrange_v::*;
use crate::common::util_v::*;
use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::pmem::wrpm_t::*;
use super::recover_v::*;
use super::setup_v::*;
use super::spec_v::*;

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

    pub(super) open spec fn space_needed(self) -> int
    {
        spec_space_needed_for_journal_entry(self.bytes_to_write.len())
    }
}

pub(super) open spec fn apply_journal_entry(bytes: Seq<u8>, entry: JournalEntry, sm: JournalStaticMetadata)
                                     -> Option<Seq<u8>>
{
    if entry.fits(sm) {
        Some(opaque_update_bytes(bytes, entry.start, entry.bytes_to_write))
    }
    else {
        None
    }
}

pub(super) open spec fn apply_journal_entries(bytes: Seq<u8>, entries: Seq<JournalEntry>,
                                              sm: JournalStaticMetadata) -> Option<Seq<u8>>
    decreases
        entries.len()
{
    if entries.len() == 0 {
        Some(bytes)
    }
    else {
        match apply_journal_entry(bytes, entries[0], sm) {
            None => None,
            Some(updated_bytes) => apply_journal_entries(updated_bytes, entries.skip(1), sm),
        }
    }
}

pub(super) open spec fn journal_entries_valid(entries: Seq<JournalEntry>, sm: JournalStaticMetadata) -> bool
    decreases
        entries.len()
{
    if entries.len() == 0 {
        true
    }
    else {
        entries[0].fits(sm) && journal_entries_valid(entries.skip(1), sm)
    }
}

pub(super) proof fn lemma_journal_entries_valid_implies_one_valid(
    entries: Seq<JournalEntry>,
    sm: JournalStaticMetadata,
    which_entry: int
)
    requires
        0 <= which_entry < entries.len(),
        journal_entries_valid(entries, sm),
    ensures
        entries[which_entry].fits(sm),
    decreases
        entries.len(),
{
    if which_entry > 0 {
        lemma_journal_entries_valid_implies_one_valid(entries.skip(1), sm, which_entry - 1);
        assert(entries[which_entry] =~= entries.skip(1)[which_entry - 1]);
    }
}

pub(super) open spec fn space_needed_for_journal_entries(entries: Seq<JournalEntry>) -> int
    decreases
        entries.len()
{
    if entries.len() == 0 {
        0
    }
    else {
        entries.last().space_needed() + space_needed_for_journal_entries(entries.drop_last())
    }
}

pub(super) open spec fn journaled_addrs_complete(entries: Seq<JournalEntry>, journaled_addrs: Set<int>) -> bool
{
    forall|entry, addr| #![trigger entries.contains(entry), journaled_addrs.contains(addr)]
        entries.contains(entry) && entry.start <= addr < entry.end() ==> journaled_addrs.contains(addr)
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
    pub exec fn new(start: u64, bytes_to_write: Vec<u8>) -> (result: Self)
        ensures
            result@ == (JournalEntry{ start: start as int, bytes_to_write: bytes_to_write@ }),
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

pub(super) proof fn lemma_apply_journal_entries_only_affects_dynamic_area_inductive_step(
    state: Seq<u8>,
    vm: JournalVersionMetadata,
    sm: JournalStaticMetadata,
    entries: Seq<JournalEntry>,
)
    requires
        validate_metadata(vm, sm, state.len()),
        apply_journal_entries(state, entries, sm) is Some,
    ensures ({
        let state2 = apply_journal_entries(state, entries, sm).unwrap();
        opaque_subrange(state2, 0, sm.app_area_start as int) == opaque_subrange(state, 0, sm.app_area_start as int)
    }),
    decreases
        entries.len()
{
    if 0 < entries.len() {
        reveal(opaque_update_bytes);
        reveal(opaque_subrange);
        let state_next = apply_journal_entry(state, entries[0], sm).unwrap();
        assert(opaque_subrange(state_next, 0, sm.app_area_start as int) =~=
               opaque_subrange(state, 0, sm.app_area_start as int));
        lemma_apply_journal_entries_only_affects_dynamic_area_inductive_step(
            state_next, vm, sm, entries.skip(1)
        );
    }
}

pub(super) proof fn lemma_addresses_in_entry_dont_affect_apply_journal_entries_inductive_step(
    state1: Seq<u8>,
    state2: Seq<u8>,
    vm: JournalVersionMetadata,
    sm: JournalStaticMetadata,
    entries: Seq<JournalEntry>,
    which_entry: int,
)
    requires
        validate_metadata(vm, sm, state1.len()),
        state1.len() == state2.len(),
        journal_entries_valid(entries, sm),
        0 <= which_entry < entries.len(),
        forall|other_addr: int| #![trigger state2[other_addr]] {
            &&& 0 <= other_addr < state1.len()
            &&& !entries[which_entry].addrs().contains(other_addr)
        } ==> state1[other_addr] == state2[other_addr],
    ensures
        apply_journal_entries(state2, entries, sm) == apply_journal_entries(state1, entries, sm),
    decreases
        entries.len()
{
    reveal(opaque_update_bytes);
    let state1_next = apply_journal_entry(state1, entries[0], sm).unwrap();
    let state2_next = apply_journal_entry(state2, entries[0], sm).unwrap();
    if which_entry == 0 {
        assert(state1_next =~= state2_next);
    }
    else {
        lemma_addresses_in_entry_dont_affect_apply_journal_entries_inductive_step(
            state1_next, state2_next, vm, sm, entries.skip(1), which_entry - 1
        );
    }
}

pub(super) proof fn lemma_addresses_in_entry_dont_affect_apply_journal_entries(
    state1: Seq<u8>,
    state2: Seq<u8>,
    vm: JournalVersionMetadata,
    sm: JournalStaticMetadata,
    entries: Seq<JournalEntry>,
    which_entry: int,
)
    requires
        validate_metadata(vm, sm, state1.len()),
        state1.len() == state2.len(),
        journal_entries_valid(entries, sm),
        0 <= which_entry < entries.len(),
        forall|other_addr: int| #![trigger state2[other_addr]] {
            &&& 0 <= other_addr < state1.len()
            &&& !entries[which_entry].addrs().contains(other_addr)
        } ==> state1[other_addr] == state2[other_addr],
    ensures
        apply_journal_entries(state2, entries, sm) == apply_journal_entries(state1, entries, sm),
{
    lemma_addresses_in_entry_dont_affect_apply_journal_entries_inductive_step(
        state1, state2, vm, sm, entries, which_entry);
}

pub(super) proof fn lemma_apply_journal_entry_doesnt_change_size(
    state: Seq<u8>,
    entry: JournalEntry,
    sm: JournalStaticMetadata,
)
    requires
        apply_journal_entry(state, entry, sm) is Some,
    ensures
        state.len() == apply_journal_entry(state, entry, sm).unwrap().len(),
{
    reveal(opaque_update_bytes);
}

pub(super) proof fn lemma_apply_journal_entries_doesnt_change_size(
    state: Seq<u8>,
    entries: Seq<JournalEntry>,
    sm: JournalStaticMetadata,
)
    requires
        apply_journal_entries(state, entries, sm) is Some,
    ensures
        state.len() == apply_journal_entries(state, entries, sm).unwrap().len(),
    decreases
        entries.len()
{
    if entries.len() > 0 {
        let next_state = apply_journal_entry(state, entries[0], sm).unwrap();
        lemma_apply_journal_entry_doesnt_change_size(state, entries[0], sm);
        lemma_apply_journal_entries_doesnt_change_size(next_state, entries.skip(1), sm);
    }
}

pub(super) proof fn lemma_addresses_in_entry_dont_affect_recovery(
    state: Seq<u8>,
    vm: JournalVersionMetadata,
    sm: JournalStaticMetadata,
    entries_bytes: Seq<u8>,
    entries: Seq<JournalEntry>,
    which_entry: int,
)
    requires
        recover_version_metadata(state) == Some(vm),
        recover_static_metadata(state, vm) == Some(sm),
        recover_committed_cdb(state, sm) == Some(true),
        recover_journal_length(state, sm) == Some(entries_bytes.len() as u64),
        recover_journal_entries_bytes(state, sm, entries_bytes.len() as u64)
            == Some(entries_bytes),
        parse_journal_entries(entries_bytes) == Some(entries),
        journal_entries_valid(entries, sm),
        recover_journal(state) is Some,
        0 <= which_entry < entries.len(),
    ensures
        addresses_not_accessed_by_recovery(
            state,
            entries[which_entry].addrs(),
            |s| recover_journal(s),
        )
{
    let addrs = entries[which_entry].addrs();
    assert forall|s2: Seq<u8>| {
        &&& s2.len() == state.len()
        &&& forall|i: int| #![trigger s2[i]] 0 <= i < state.len() && !addrs.contains(i) ==> state[i] == s2[i]
    } implies #[trigger] recover_journal(s2) == recover_journal(state) by {
        lemma_addresses_in_entry_dont_affect_apply_journal_entries_inductive_step(
            state, s2, vm, sm, entries, which_entry
        );
        reveal(opaque_subrange);
        lemma_apply_journal_entries_success_implies_bounded_addrs_for_entry(sm, state, entries, which_entry);
        assert(forall|i| 0 <= i < sm.app_area_start ==> !addrs.contains(i));
        assert(opaque_subrange(state, 0, sm.app_area_start as int) =~=
               opaque_subrange(s2, 0, sm.app_area_start as int));
        lemma_auto_opaque_subrange_subrange(state, 0, sm.app_area_start as int);
        lemma_auto_opaque_subrange_subrange(s2, 0, sm.app_area_start as int);
    }
}

pub(super) proof fn lemma_apply_journal_entries_success_implies_bounded_addrs_for_entry(
    sm: JournalStaticMetadata,
    state: Seq<u8>,
    entries: Seq<JournalEntry>,
    which_entry: int,
)
    requires
        apply_journal_entries(state, entries, sm) is Some,
        0 <= which_entry < entries.len(),
    ensures
        entries[which_entry].fits(sm),
    decreases
        entries.len()
{
    if 0 < which_entry {
        let next_state = apply_journal_entry(state, entries[0], sm).unwrap();
        lemma_apply_journal_entries_success_implies_bounded_addrs_for_entry(sm, next_state, entries.skip(1),
                                                                            which_entry - 1);
    }
}

pub(super) proof fn lemma_parse_journal_entry_relation_to_next(entries_bytes: Seq<u8>, start: int)
    requires
        parse_journal_entries(entries_bytes.skip(start)) is Some,
        parse_journal_entry(entries_bytes.skip(start)) is Some,
        0 <= start < entries_bytes.len(),
    ensures
        ({
            let (entry, num_bytes) = parse_journal_entry(entries_bytes.skip(start)).unwrap();
            &&& parse_journal_entries(entries_bytes.skip(start)).unwrap().len() > 0
            &&& 0 <= num_bytes
            &&& start + num_bytes <= entries_bytes.len()
            &&& parse_journal_entries(entries_bytes.skip(start + num_bytes)) is Some
            &&& parse_journal_entries(entries_bytes.skip(start)).unwrap()[0] == entry
            &&& parse_journal_entries(entries_bytes.skip(start + num_bytes)).unwrap() ==
                   parse_journal_entries(entries_bytes.skip(start)).unwrap().skip(1)
            &&& start + num_bytes == entries_bytes.len()
                  <==> parse_journal_entries(entries_bytes.skip(start)).unwrap().len() == 1
        }),
{
    let (entry, num_bytes) = parse_journal_entry(entries_bytes.skip(start)).unwrap();
    assert(entries_bytes.skip(start + num_bytes) =~= entries_bytes.skip(start).skip(num_bytes));
    assert(parse_journal_entries(entries_bytes.skip(start + num_bytes)).unwrap() =~=
           parse_journal_entries(entries_bytes.skip(start)).unwrap().skip(1));
}

pub(super) proof fn lemma_parse_journal_entry_implications(
    entries_bytes: Seq<u8>,
    entries: Seq<JournalEntry>,
    current_pos: int,
    num_entries_read: int,
)
    requires
        parse_journal_entries(entries_bytes) == Some(entries),
        0 <= num_entries_read < entries.len(),
        0 <= current_pos < entries_bytes.len(),
        parse_journal_entries(entries_bytes.skip(current_pos)) == Some(entries.skip(num_entries_read)),
        parse_journal_entry(entries_bytes.skip(current_pos)) is Some
    ensures ({
        let (entry, num_bytes) = parse_journal_entry(entries_bytes.skip(current_pos)).unwrap();
        &&& num_entries_read + 1 == entries.len() <==> current_pos + num_bytes == entries_bytes.len()
        &&& entries[num_entries_read] == entry
        &&& parse_journal_entries(entries_bytes.skip(current_pos + num_bytes))
               == Some(entries.skip(num_entries_read + 1))
    }),
{
    lemma_parse_journal_entry_relation_to_next(entries_bytes, current_pos);
    assert(entries.skip(num_entries_read + 1) =~= entries.skip(num_entries_read).skip(1));
}

pub(super) proof fn lemma_parse_journal_entries_append(
    entries_bytes: Seq<u8>,
    entries: Seq<JournalEntry>,
    new_entry: JournalEntry,
)
    requires
        parse_journal_entries(entries_bytes) == Some(entries),
        0 <= new_entry.start <= u64::MAX,
        new_entry.bytes_to_write.len() <= u64::MAX,
    ensures ({
        let new_entries_bytes = entries_bytes
                              + (new_entry.start as u64).spec_to_bytes()
                              + (new_entry.bytes_to_write.len() as u64).spec_to_bytes()
                              + new_entry.bytes_to_write;
        parse_journal_entries(new_entries_bytes) == Some(entries.push(new_entry))
    }),
    decreases
        entries.len(),
{
    reveal(opaque_subrange);
    broadcast use pmcopy_axioms;
    let new_entries_bytes = entries_bytes
                          + (new_entry.start as u64).spec_to_bytes()
                          + (new_entry.bytes_to_write.len() as u64).spec_to_bytes()
                          + new_entry.bytes_to_write;
    if entries_bytes.len() == 0 {
        let addr_bytes = opaque_section(new_entries_bytes, 0, u64::spec_size_of());
        assert(addr_bytes =~= (new_entry.start as u64).spec_to_bytes());
        let length_bytes = opaque_section(new_entries_bytes, u64::spec_size_of() as int, u64::spec_size_of());
        assert(length_bytes =~= (new_entry.bytes_to_write.len() as u64).spec_to_bytes());
        let data_offset = u64::spec_size_of() + u64::spec_size_of();
        assert(opaque_section(new_entries_bytes, data_offset as int, new_entry.bytes_to_write.len())
               =~= new_entry.bytes_to_write);
        assert(parse_journal_entry(new_entries_bytes) == Some((new_entry, new_entries_bytes.len() as int)));
        assert(entries =~= Seq::<JournalEntry>::empty());
        assert(parse_journal_entries(new_entries_bytes.skip(new_entries_bytes.len() as int))
               == Some(Seq::<JournalEntry>::empty()));
        assert(Seq::<JournalEntry>::empty().push(new_entry) =~= seq![new_entry] + Seq::<JournalEntry>::empty());
    }
    else {
        let (entry, num_bytes) = parse_journal_entry(entries_bytes).unwrap();
        let remaining_entries = parse_journal_entries(entries_bytes.skip(num_bytes)).unwrap();

        let (alt_entry, alt_num_bytes) = parse_journal_entry(new_entries_bytes).unwrap();
        let addr_bytes = opaque_section(new_entries_bytes, 0, u64::spec_size_of());
        assert(addr_bytes =~= opaque_section(entries_bytes, 0, u64::spec_size_of()));
        let length_bytes = opaque_section(new_entries_bytes, u64::spec_size_of() as int, u64::spec_size_of());
        assert(length_bytes =~= opaque_section(entries_bytes, u64::spec_size_of() as int, u64::spec_size_of()));
        let length = u64::spec_from_bytes(length_bytes);
        let data_offset = u64::spec_size_of() + u64::spec_size_of();
        assert(opaque_section(new_entries_bytes, data_offset as int, length as nat) =~=
               opaque_section(entries_bytes, data_offset as int, length as nat));
        assert(alt_entry == entry);
        assert(alt_num_bytes == num_bytes);

        lemma_parse_journal_entries_append(entries_bytes.skip(num_bytes), remaining_entries, new_entry);
        assert(entries_bytes.skip(num_bytes)
               + (new_entry.start as u64).spec_to_bytes()
               + (new_entry.bytes_to_write.len() as u64).spec_to_bytes()
               + new_entry.bytes_to_write
               =~= new_entries_bytes.skip(num_bytes));
    }
}

pub(super) proof fn lemma_apply_journal_entries_some_iff_journal_entries_valid(
    bytes: Seq<u8>,
    entries: Seq<JournalEntry>,
    sm: JournalStaticMetadata
)
    ensures
        apply_journal_entries(bytes, entries, sm) is Some <==> journal_entries_valid(entries, sm)
    decreases
        entries.len(),
{
    if entries.len() == 0 {
        return;
    }
    else {
        if entries[0].fits(sm) {
            let next_bytes = apply_journal_entry(bytes, entries[0], sm).unwrap();
            lemma_apply_journal_entries_some_iff_journal_entries_valid(next_bytes, entries.skip(1), sm);
        }
    }
}

pub(super) proof fn lemma_apply_journal_entries_commutes_with_update_bytes(
    s: Seq<u8>,
    entries: Seq<JournalEntry>,
    journaled_addrs: Set<int>,
    addr: int,
    bytes_to_write: Seq<u8>,
    sm: JournalStaticMetadata,
)
    requires
        journal_entries_valid(entries, sm),
        sm.app_area_start <= sm.app_area_end == s.len(),
        journaled_addrs_complete(entries, journaled_addrs),
        forall|i: int| #![trigger journaled_addrs.contains(i)] addr <= i < addr + bytes_to_write.len()
            ==> !journaled_addrs.contains(i),
    ensures ({
        &&& apply_journal_entries(s, entries, sm) matches Some(s2)
        &&& apply_journal_entries(opaque_update_bytes(s, addr, bytes_to_write), entries, sm) ==
               Some(opaque_update_bytes(s2, addr, bytes_to_write))
    }),
    decreases
        entries.len(),
{
    reveal(opaque_update_bytes);
    if 0 < entries.len() {
        let next_state = apply_journal_entry(s, entries[0], sm).unwrap();
        assert (journaled_addrs_complete(entries.skip(1), journaled_addrs)) by {
            assert forall|entry, addr| #![trigger entries.skip(1).contains(entry), journaled_addrs.contains(addr)]
                entries.skip(1).contains(entry) && entry.start <= addr < entry.end()
                implies journaled_addrs.contains(addr) by {
                assert(entries.contains(entry));
            }
        }
        lemma_apply_journal_entries_commutes_with_update_bytes(next_state, entries.skip(1), journaled_addrs,
                                                               addr, bytes_to_write, sm);
        vstd::assert_seqs_equal!(
            apply_journal_entry(opaque_update_bytes(s, addr, bytes_to_write), entries[0], sm).unwrap() ==
            opaque_update_bytes(next_state, addr, bytes_to_write),
            i => {
                assert(entries.contains(entries[0])); // triggers journaled_addrs_complete
                if addr <= i < addr + bytes_to_write.len() {
                    assert(!journaled_addrs.contains(i)); // triggers quantifier in this function's precondition
                }
            }
        );
    }
}

pub(super) proof fn lemma_updating_journal_area_doesnt_affect_apply_journal_entries(
    s1: Seq<u8>,
    s2: Seq<u8>,
    entries: Seq<JournalEntry>,
    vm: JournalVersionMetadata,
    sm: JournalStaticMetadata,
)
    requires
        validate_metadata(vm, sm, s1.len()),
        s1.len() == s2.len(),
        apply_journal_entries(s1, entries, sm) is Some,
        opaque_subrange(s1, sm.app_area_start as int, sm.app_area_end as int)
            == opaque_subrange(s2, sm.app_area_start as int, sm.app_area_end as int),
    ensures ({
        let s1_updated = apply_journal_entries(s1, entries, sm);
        let s2_updated = apply_journal_entries(s2, entries, sm);
        &&& s2_updated is Some
        &&& opaque_subrange(s1_updated.unwrap(), sm.app_area_start as int, sm.app_area_end as int)
            == opaque_subrange(s2_updated.unwrap(), sm.app_area_start as int, sm.app_area_end as int)
    }),
    decreases
        entries.len(),
{
    if 0 < entries.len() {
        let entry = entries[0];
        let s1_next = apply_journal_entry(s1, entry, sm).unwrap();
        let s2_next = apply_journal_entry(s2, entry, sm).unwrap();
        lemma_auto_effect_of_opaque_update_bytes_on_opaque_subranges();
        lemma_auto_opaque_subrange_subrange(s1, sm.app_area_start as int, sm.app_area_end as int);
        lemma_auto_opaque_subrange_subrange(s2, sm.app_area_start as int, sm.app_area_end as int);
        assert(opaque_subrange(s1_next, sm.app_area_start as int, sm.app_area_end as int)
               == opaque_subrange(s2_next, sm.app_area_start as int, sm.app_area_end as int)) by {
            lemma_concatenate_three_opaque_subranges(s1_next, sm.app_area_start as int, entry.start as int,
                                                     entry.end(), sm.app_area_end as int);
            lemma_concatenate_three_opaque_subranges(s2_next, sm.app_area_start as int, entry.start as int,
                                                     entry.end(), sm.app_area_end as int);
        }
        lemma_updating_journal_area_doesnt_affect_apply_journal_entries(
            s1_next, s2_next, entries.skip(1), vm, sm);
    }

}

pub(super) proof fn lemma_space_needed_for_journal_entries_monotonic(entries: Seq<JournalEntry>, i: int, j: int)
    requires
        0 <= i <= j <= entries.len(),
    ensures
        space_needed_for_journal_entries(entries.take(i)) <= space_needed_for_journal_entries(entries.take(j)),
    decreases
        j - i
{
    if i < j {
        lemma_space_needed_for_journal_entries_monotonic(entries, i + 1, j);
        assert(entries.take(i + 1).drop_last() =~= entries.take(i));
        assert(entries.take(i + 1).last() =~= entries[i]);
    }
}

pub(super) proof fn lemma_space_needed_for_journal_entries_increases(entries: Seq<JournalEntry>, i: int)
    requires
        0 <= i < entries.len(),
    ensures
        space_needed_for_journal_entries(entries.take(i + 1))
           == space_needed_for_journal_entries(entries.take(i)) + entries[i].space_needed()
{
    assert(entries.take(i + 1).drop_last() =~= entries.take(i));
    assert(entries.take(i + 1).last() =~= entries[i]);
}

pub(super) proof fn lemma_space_needed_for_journal_entries_nonnegative(entries: Seq<JournalEntry>)
    ensures
        0 <= space_needed_for_journal_entries(entries),
    decreases
        entries.len()
{
    if entries.len() > 0 {
        lemma_space_needed_for_journal_entries_nonnegative(entries.drop_last());
    }
}

pub(super) proof fn lemma_effect_of_append_on_apply_journal_entries(
    s: Seq<u8>,
    entries: Seq<JournalEntry>,
    new_entry: JournalEntry,
    sm: JournalStaticMetadata
)
    requires
        apply_journal_entries(s, entries, sm) is Some,
        apply_journal_entry(apply_journal_entries(s, entries, sm).unwrap(), new_entry, sm) is Some,
        sm.app_area_start <= sm.app_area_end == s.len(),
    ensures
        apply_journal_entries(s, entries.push(new_entry), sm) ==
            apply_journal_entry(apply_journal_entries(s, entries, sm).unwrap(), new_entry, sm),
    decreases
        entries.len(),
{
    if entries.len() == 0 {
        let s_next = apply_journal_entry(s, new_entry, sm).unwrap();
        assert(entries.push(new_entry)[0] == new_entry);
        assert(apply_journal_entry(s, entries.push(new_entry)[0], sm) == Some(s_next));
        assert(apply_journal_entries(s_next, entries.push(new_entry).skip(1), sm) == Some(s_next));
    }
    else {
        reveal(opaque_update_bytes);
        assert(entries.push(new_entry)[0] == entries[0]);
        let s_next = apply_journal_entry(s, entries[0], sm).unwrap();
        assert(apply_journal_entry(s, entries.push(new_entry)[0], sm) == Some(s_next));
        lemma_effect_of_append_on_apply_journal_entries(s_next, entries.skip(1), new_entry, sm);
        assert(entries.push(new_entry).skip(1) =~= entries.skip(1).push(new_entry));
    }
}

}
