#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use super::impl_v::*;
use super::inv_v::*;
use super::super::spec_t::*;

verus! {

pub(super) proof fn lemma_writing_element_and_next_effect_on_recovery<L>(
    s1: Seq<u8>,
    s5: Seq<u8>,
    row_addr: u64,
    element: L,
    next: u64,
    sm: ListTableStaticMetadata,
)
    where 
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
    requires
        sm.valid::<L>(),
        0 < sm.start(),
        sm.end() <= s1.len(),
        sm.table.validate_row_addr(row_addr),
        ({
            let s2 = update_bytes(s1, row_addr + sm.row_element_start, element.spec_to_bytes());
            let s3 = update_bytes(s2, row_addr + sm.row_element_crc_start,
                                  spec_crc_bytes(element.spec_to_bytes()));
            let s4 = update_bytes(s3, row_addr + sm.row_next_start, next.spec_to_bytes());
            s5 == update_bytes(s4, row_addr + sm.row_next_start + u64::spec_size_of(),
                               spec_crc_bytes(next.spec_to_bytes()))
        }),
    ensures
        forall|other_row_addr: u64| {
            &&& sm.table.validate_row_addr(other_row_addr)
            &&& other_row_addr != row_addr
        } ==> {
            &&& recover_object::<L>(s5, other_row_addr + sm.row_element_start,
                                    other_row_addr + sm.row_element_crc_start)
                == recover_object::<L>(s1, other_row_addr + sm.row_element_start,
                                       other_row_addr + sm.row_element_crc_start)
            &&& recover_object::<u64>(s5, other_row_addr + sm.row_next_start,
                                      other_row_addr + sm.row_next_start + u64::spec_size_of())
                == recover_object::<u64>(s1, other_row_addr + sm.row_next_start,
                                         other_row_addr + sm.row_next_start + u64::spec_size_of())
        },
        recover_object::<L>(s5, row_addr + sm.row_element_start, row_addr + sm.row_element_crc_start)
            == Some(element),
        recover_object::<u64>(s5, row_addr + sm.row_next_start, row_addr + sm.row_next_start + u64::spec_size_of())
            == Some(next),
{
    broadcast use group_update_bytes_effect;
    broadcast use pmcopy_axioms;
    broadcast use broadcast_seqs_match_in_range_can_narrow_range;
    broadcast use group_validate_row_addr;
}

pub(super) proof fn lemma_writing_next_and_crc_together_effect_on_recovery<L>(
    s1: Seq<u8>,
    s2: Seq<u8>,
    row_addr: u64,
    next: u64,
    sm: ListTableStaticMetadata,
)
    where 
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
    requires
        sm.valid::<L>(),
        0 < sm.start(),
        sm.end() <= s1.len(),
        sm.table.validate_row_addr(row_addr),
        s2 == update_bytes(s1, row_addr + sm.row_next_start,
                           next.spec_to_bytes() + spec_crc_bytes(next.spec_to_bytes())),
    ensures
        recover_object::<u64>(s2, row_addr + sm.row_next_start, row_addr + sm.row_next_start + u64::spec_size_of())
            == Some(next),
        forall|other_row_addr: u64| {
            &&& sm.table.validate_row_addr(other_row_addr)
            &&& other_row_addr != row_addr
        } ==>
            recover_object::<u64>(s2, other_row_addr + sm.row_next_start,
                                  other_row_addr + sm.row_next_start + u64::spec_size_of())
                == recover_object::<u64>(s1, other_row_addr + sm.row_next_start,
                                        other_row_addr + sm.row_next_start + u64::spec_size_of()),
        forall|any_row_addr: u64| sm.table.validate_row_addr(any_row_addr) ==>
            recover_object::<L>(s2, any_row_addr + sm.row_element_start,
                                any_row_addr + sm.row_element_crc_start)
                == recover_object::<L>(s1, any_row_addr + sm.row_element_start,
                                       any_row_addr + sm.row_element_crc_start),
{
    broadcast use group_update_bytes_effect;
    broadcast use pmcopy_axioms;
    broadcast use broadcast_seqs_match_in_range_can_narrow_range;
    broadcast use group_validate_row_addr;

    let next_addr = row_addr + sm.row_next_start;
    let bytes_written = next.spec_to_bytes() + spec_crc_bytes(next.spec_to_bytes());
    lemma_subrange_subrange(s2,
                            next_addr as int, next_addr + u64::spec_size_of() + u64::spec_size_of(),
                            next_addr as int, next_addr + u64::spec_size_of());
    lemma_subrange_subrange(s2,
                            next_addr as int, next_addr + u64::spec_size_of() + u64::spec_size_of(),
                            next_addr + u64::spec_size_of(),
                            next_addr + u64::spec_size_of() + u64::spec_size_of());
    assert(bytes_written.subrange(0, u64::spec_size_of() as int) =~= next.spec_to_bytes());
    assert(bytes_written.subrange(u64::spec_size_of() as int, (u64::spec_size_of() + u64::spec_size_of()) as int)
           =~= spec_crc_bytes(next.spec_to_bytes()));
    assert(recover_object::<u64>(s2, next_addr, next_addr + u64::spec_size_of()) =~= Some(next));
}

impl<PM, L> ListTable<PM, L>
where
    PM: PersistentMemoryRegion,
    L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) proof fn lemma_writing_to_free_slot_doesnt_change_recovery(
        iv: ListTableInternalView<L>,
        s1: Seq<u8>,
        s2: Seq<u8>,
        sm: ListTableStaticMetadata,
        free_list_pos: int,
        row_addr: u64,
        start: int,
        end: int,
    )
        requires
            sm.valid::<L>(),
            iv.valid(sm),
            iv.corresponds_to_durable_state(s1, sm),
            0 <= free_list_pos < iv.free_list.len(),
            iv.free_list[free_list_pos] == row_addr,
            sm.table.validate_row_addr(row_addr),
            row_addr <= start <= end <= row_addr + sm.table.row_size,
            seqs_match_except_in_range(s1, s2, start, end),
        ensures
            iv.corresponds_to_durable_state(s2, sm),
            Self::recover(s2, iv.durable_mapping.list_elements.dom(), sm) ==
                Self::recover(s1, iv.durable_mapping.list_elements.dom(), sm),
    {
        broadcast use group_validate_row_addr;
        broadcast use broadcast_seqs_match_in_range_can_narrow_range;

        assert(iv.row_info[row_addr] is InFreeList);
        assert(iv.corresponds_to_durable_state(s2, sm));

        let list_addrs = iv.durable_mapping.list_elements.dom();
        iv.durable_mapping.lemma_corresponds_implies_equals_new(s1, list_addrs, sm);
        iv.durable_mapping.lemma_corresponds_implies_equals_new(s2, list_addrs, sm);
        assert(Self::recover(s2, list_addrs, sm) =~= Self::recover(s1, list_addrs, sm));
    }

    pub(super) proof fn lemma_writing_to_free_slot_has_permission_later_forall<PermFactory>(
        iv: ListTableInternalView<L>,
        initial_jv: JournalView,
        sm: ListTableStaticMetadata,
        free_list_pos: int,
        row_addr: u64,
        perm_factory: PermFactory,
    )
        where
            PermFactory: PermissionFactory<Seq<u8>>,
        requires
            sm.valid::<L>(),
            iv.valid(sm),
            iv.corresponds_to_durable_state(initial_jv.durable_state, sm),
            iv.corresponds_to_durable_state(initial_jv.read_state, sm),
            Journal::<PM>::state_recovery_idempotent(initial_jv.durable_state, initial_jv.constants),
            0 <= free_list_pos < iv.free_list.len(),
            iv.free_list[free_list_pos] == row_addr,
            sm.table.validate_row_addr(row_addr),
            sm.table.end <= initial_jv.durable_state.len(),
            forall|s1: Seq<u8>, s2: Seq<u8>| {
                &&& Self::state_equivalent_for_me(s1, initial_jv.durable_state, iv.durable_mapping.list_elements.dom(),
                                                 initial_jv.constants, sm)
                &&& Self::state_equivalent_for_me(s2, initial_jv.durable_state, iv.durable_mapping.list_elements.dom(),
                                                 initial_jv.constants, sm)
            } ==> #[trigger] perm_factory.permits(s1, s2),
        ensures
            forall|current_durable_state: Seq<u8>, new_durable_state: Seq<u8>, start: int, end: int|
                #![trigger seqs_match_except_in_range(current_durable_state, new_durable_state, start, end)]
            {
                &&& seqs_match_except_in_range(current_durable_state, new_durable_state, start, end)
                &&& Self::state_equivalent_for_me(current_durable_state, initial_jv.durable_state,
                                                iv.durable_mapping.list_elements.dom(), initial_jv.constants, sm)
                &&& iv.corresponds_to_durable_state(current_durable_state, sm)
                &&& row_addr <= start <= end <= row_addr + sm.table.row_size
                &&& Journal::<PM>::state_recovery_idempotent(new_durable_state, initial_jv.constants)
            } ==> {
                &&& Self::state_equivalent_for_me(new_durable_state, initial_jv.durable_state,
                                                iv.durable_mapping.list_elements.dom(), initial_jv.constants, sm)
                &&& iv.corresponds_to_durable_state(new_durable_state, sm)
                &&& perm_factory.permits(current_durable_state, new_durable_state)
            },

            forall|current_read_state: Seq<u8>, start: int, bytes: Seq<u8>|
                #![trigger update_bytes(current_read_state, start, bytes)]
            {
                let new_read_state = update_bytes(current_read_state, start, bytes);
                &&& seqs_match_except_in_range(initial_jv.read_state, current_read_state, sm.start() as int,
                                             sm.end() as int)
                &&& iv.corresponds_to_durable_state(current_read_state, sm)
                &&& row_addr <= start
                &&& start + bytes.len() <= row_addr + sm.table.row_size
            } ==> {
                let new_read_state = update_bytes(current_read_state, start, bytes);
                &&& iv.corresponds_to_durable_state(new_read_state, sm)
                &&& seqs_match_except_in_range(initial_jv.read_state, new_read_state, sm.start() as int, sm.end() as int)
            },
    {
        assert forall|current_durable_state: Seq<u8>, new_durable_state: Seq<u8>, start: int, end: int|
                #![trigger seqs_match_except_in_range(current_durable_state, new_durable_state, start, end)]
            {
                &&& seqs_match_except_in_range(current_durable_state, new_durable_state, start, end)
                &&& Self::state_equivalent_for_me(current_durable_state, initial_jv.durable_state,
                                                iv.durable_mapping.list_elements.dom(), initial_jv.constants, sm)
                &&& iv.corresponds_to_durable_state(current_durable_state, sm)
                &&& row_addr <= start <= end <= row_addr + sm.table.row_size
                &&& Journal::<PM>::state_recovery_idempotent(new_durable_state, initial_jv.constants)
            } implies {
                &&& Self::state_equivalent_for_me(new_durable_state, initial_jv.durable_state,
                                                iv.durable_mapping.list_elements.dom(), initial_jv.constants, sm)
                &&& iv.corresponds_to_durable_state(new_durable_state, sm)
                &&& perm_factory.permits(current_durable_state, new_durable_state)
            } by {
            broadcast use group_validate_row_addr;
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            Self::lemma_writing_to_free_slot_doesnt_change_recovery(
                iv, current_durable_state, new_durable_state, sm, free_list_pos, row_addr, start, end
            );
        }

        assert forall|current_read_state: Seq<u8>, start: int, bytes: Seq<u8>|
                #![trigger update_bytes(current_read_state, start, bytes)]
            {
                let new_read_state = update_bytes(current_read_state, start, bytes);
                &&& seqs_match_except_in_range(initial_jv.read_state, current_read_state, sm.start() as int,
                                             sm.end() as int)
                &&& iv.corresponds_to_durable_state(current_read_state, sm)
                &&& row_addr <= start
                &&& start + bytes.len() <= row_addr + sm.table.row_size
            } implies {
                let new_read_state = update_bytes(current_read_state, start, bytes);
                &&& iv.corresponds_to_durable_state(new_read_state, sm)
                &&& seqs_match_except_in_range(initial_jv.read_state, new_read_state, sm.start() as int, sm.end() as int)
            } by
        {
            broadcast use group_validate_row_addr;
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            broadcast use broadcast_update_bytes_effect;
            let new_read_state = update_bytes(current_read_state, start, bytes);
            Self::lemma_writing_to_free_slot_doesnt_change_recovery(
                iv, current_read_state, new_read_state, sm, free_list_pos, row_addr, start, start + bytes.len()
            );
        }
    }
}

impl ListSummary
{
    pub(super) exec fn default() -> Self
    {
        Self{ head: 0, tail: 0, length: 0, end_of_logical_range: 0 }
    }
}

impl<L> ListTableEntry<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) exec fn default() -> Self
    {
        Self::Durable{ summary: ListSummary::default() }
    }

    pub(super) exec fn unwrap_durable(self) -> (result: ListSummary)
        requires
            self is Durable,
        ensures
            self == (Self::Durable{ summary: result }),
    {
        match self {
            ListTableEntry::Durable{ summary } => summary,
            _ => { assert(false); ListSummary::default() },
        }
    }
}

pub(super) proof fn lemma_push_commutes_with_skip<T>(s: Seq<T>, skip_amount: int, pushed_element: T)
    requires
        0 <= skip_amount <= s.len(),
    ensures
        s.skip(skip_amount).push(pushed_element) == s.push(pushed_element).skip(skip_amount),
{
    assert(s.skip(skip_amount).push(pushed_element) =~= s.push(pushed_element).skip(skip_amount));
}

}

