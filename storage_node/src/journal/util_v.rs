use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::{size_of, align_of};
use crate::pmem::wrpm_t::*;
use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
use crate::common::util_v::*;
use super::journal_v::*;
use super::layout_v::*;
use super::spec_v::*;

verus! {

pub(super) proof fn lemma_apply_journal_entries_only_affects_dynamic_area_inductive_step(
    state: Seq<u8>,
    vm: JournalVersionMetadata,
    sm: JournalStaticMetadata,
    entries: Seq<JournalEntry>,
    entries_checked_so_far: int,
)
    requires
        validate_metadata(vm, sm, state.len()),
        apply_journal_entries(state, entries, entries_checked_so_far, sm) is Some,
        0 <= entries_checked_so_far <= entries.len(),
    ensures ({
        let state2 = apply_journal_entries(state, entries, entries_checked_so_far, sm).unwrap();
        opaque_subrange(state2, 0, sm.app_area_start as int) == opaque_subrange(state, 0, sm.app_area_start as int)
    }),
    decreases
        entries.len() - entries_checked_so_far
{
    if entries_checked_so_far < entries.len() {
        reveal(opaque_update_bytes);
        reveal(opaque_subrange);
        let state_next = apply_journal_entry(state, entries[entries_checked_so_far], sm).unwrap();
        assert(opaque_subrange(state_next, 0, sm.app_area_start as int) =~=
               opaque_subrange(state, 0, sm.app_area_start as int));
        lemma_apply_journal_entries_only_affects_dynamic_area_inductive_step(
            state_next, vm, sm, entries, entries_checked_so_far + 1
        );
    }
}

pub(super) proof fn lemma_addresses_in_entry_dont_affect_apply_journal_entries_inductive_step(
    state1: Seq<u8>,
    state2: Seq<u8>,
    vm: JournalVersionMetadata,
    sm: JournalStaticMetadata,
    entries: Seq<JournalEntry>,
    entries_checked_so_far: int,
    which_entry: int,
)
    requires
        validate_metadata(vm, sm, state1.len()),
        state1.len() == state2.len(),
        journal_entries_valid(entries, entries_checked_so_far, sm),
        0 <= entries_checked_so_far <= which_entry < entries.len(),
        forall|other_addr: int| #![trigger state2[other_addr]] {
            &&& 0 <= other_addr < state1.len()
            &&& !entries[which_entry].addrs().contains(other_addr)
        } ==> state1[other_addr] == state2[other_addr],
    ensures
        apply_journal_entries(state2, entries, entries_checked_so_far, sm) ==
            apply_journal_entries(state1, entries, entries_checked_so_far, sm),
    decreases
        entries.len() - entries_checked_so_far
{
    reveal(opaque_update_bytes);
    let state1_next = apply_journal_entry(state1, entries[entries_checked_so_far], sm).unwrap();
    let state2_next = apply_journal_entry(state2, entries[entries_checked_so_far], sm).unwrap();
    if which_entry == entries_checked_so_far {
        assert(state1_next =~= state2_next);
    }
    else {
        lemma_addresses_in_entry_dont_affect_apply_journal_entries_inductive_step(
            state1_next, state2_next, vm, sm, entries,
            entries_checked_so_far + 1, which_entry
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
        journal_entries_valid(entries, 0, sm),
        0 <= which_entry < entries.len(),
        forall|other_addr: int| #![trigger state2[other_addr]] {
            &&& 0 <= other_addr < state1.len()
            &&& !entries[which_entry].addrs().contains(other_addr)
        } ==> state1[other_addr] == state2[other_addr],
    ensures
        apply_journal_entries(state2, entries, 0, sm) == apply_journal_entries(state1, entries, 0, sm),
{
    lemma_addresses_in_entry_dont_affect_apply_journal_entries_inductive_step(
        state1, state2, vm, sm, entries, 0, which_entry);
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
        parse_journal_entries(entries_bytes, 0) == Some(entries),
        journal_entries_valid(entries, 0, sm),
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
            state, s2, vm, sm, entries, 0, which_entry
        );
        reveal(opaque_subrange);
        lemma_apply_journal_entries_success_implies_bounded_addrs_for_entry(sm, state, entries, 0, which_entry);
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
    start: int,
    which_entry: int,
)
    requires
        apply_journal_entries(state, entries, start, sm) is Some,
        0 <= start <= which_entry < entries.len(),
    ensures
        entries[which_entry].fits(sm),
    decreases
        entries.len() - start,
{
    if start < which_entry {
        let next_state = apply_journal_entry(state, entries[start], sm).unwrap();
        lemma_apply_journal_entries_success_implies_bounded_addrs_for_entry(sm, next_state, entries, start + 1,
                                                                            which_entry);
    }
}

pub(super) proof fn lemma_parse_journal_entry_relation_to_next(entries_bytes: Seq<u8>, start: int)
    requires
        parse_journal_entries(entries_bytes, start) is Some,
        parse_journal_entry(entries_bytes, start) is Some,
    ensures
        ({
            let (entry, next) = parse_journal_entry(entries_bytes, start).unwrap();
            &&& parse_journal_entries(entries_bytes, start).unwrap().len() > 0
            &&& parse_journal_entries(entries_bytes, next) is Some
            &&& parse_journal_entries(entries_bytes, start).unwrap()[0] == entry
            &&& parse_journal_entries(entries_bytes, next).unwrap() ==
                parse_journal_entries(entries_bytes, start).unwrap().skip(1)
        }),
{
    let (entry, next) = parse_journal_entry(entries_bytes, start).unwrap();
    assert(parse_journal_entries(entries_bytes, next).unwrap() =~=
           parse_journal_entries(entries_bytes, start).unwrap().skip(1));
}

pub(super) proof fn lemma_parse_journal_entry_implications(
    entries_bytes: Seq<u8>,
    entries: Seq<JournalEntry>,
    num_entries_read: int,
    current_pos: int,
)
    requires
        parse_journal_entries(entries_bytes, 0) == Some(entries),
        0 <= num_entries_read < entries.len(),
        0 <= current_pos < entries_bytes.len(),
        parse_journal_entries(entries_bytes, current_pos) == Some(entries.skip(num_entries_read)),
        parse_journal_entry(entries_bytes, current_pos) is Some
    ensures ({
        let (entry, next_pos) = parse_journal_entry(entries_bytes, current_pos).unwrap();
        &&& num_entries_read + 1 == entries.len() <==> next_pos == entries_bytes.len()
        &&& entries[num_entries_read] == entry
        &&& parse_journal_entries(entries_bytes, next_pos) == Some(entries.skip(num_entries_read + 1))
    }),
{
    lemma_parse_journal_entry_relation_to_next(entries_bytes, current_pos);
    assert(entries.skip(num_entries_read + 1) =~= entries.skip(num_entries_read).skip(1));
}

pub(super) open spec fn journal_entries_valid(entries: Seq<JournalEntry>, starting_entry: int, sm: JournalStaticMetadata) -> bool
    decreases
        entries.len() - starting_entry
{
    if starting_entry < 0 || starting_entry > entries.len() {
        false
    }
    else if entries.len() == starting_entry {
        true
    }
    else {
        entries[starting_entry].fits(sm) && journal_entries_valid(entries, starting_entry + 1, sm)
    }
}

pub(super) proof fn lemma_apply_journal_entries_some_iff_journal_entries_valid(
    bytes: Seq<u8>,
    entries: Seq<JournalEntry>,
    starting_entry: int,
    sm: JournalStaticMetadata
)
    ensures
        apply_journal_entries(bytes, entries, starting_entry, sm) is Some
        <==> journal_entries_valid(entries, starting_entry, sm)
    decreases
        entries.len() - starting_entry,
{
    if starting_entry < 0 || starting_entry > entries.len() {
        return;
    }
    else if entries.len() == starting_entry {
        return;
    }
    else {
        if entries[starting_entry].fits(sm) {
            let next_bytes = apply_journal_entry(bytes, entries[starting_entry], sm).unwrap();
            lemma_apply_journal_entries_some_iff_journal_entries_valid(next_bytes, entries, starting_entry + 1, sm);
        }
    }
}

pub(super) open spec fn spec_recovery_equivalent_for_app(state1: Seq<u8>, state2: Seq<u8>) -> bool
{
    &&& recover_journal(state1) matches Some(j1)
    &&& recover_journal(state2) matches Some(j2)
    &&& j1.constants == j2.constants
    &&& opaque_subrange(j1.state, j1.constants.app_area_start as int, j1.constants.app_area_end as int)
           == opaque_subrange(j2.state, j2.constants.app_area_start as int, j2.constants.app_area_end as int)
}

}
