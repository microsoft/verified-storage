#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use deps_hack::PmCopy;
use std::collections::HashMap;
use std::hash::Hash;
use super::*;
use super::recover_v::*;
use super::super::impl_t::*;
use super::super::spec_t::*;
use vstd::std_specs::hash::*;

verus! {

pub(super) proof fn lemma_writing_next_and_crc_together_enables_recovery(
    s1: Seq<u8>,
    s2: Seq<u8>,
    next: u64,
    next_addr: int,
    bytes_written: Seq<u8>
)
    requires
        0 <= next_addr,
        next_addr + bytes_written.len() <= s1.len(),
        bytes_written.len() == u64::spec_size_of() + u64::spec_size_of(),
        s2 == update_bytes(s1, next_addr, bytes_written),
        bytes_written == next.spec_to_bytes() + spec_crc_bytes(next.spec_to_bytes()),
    ensures
        recover_object::<u64>(s2, next_addr, next_addr + u64::spec_size_of()) == Some(next),
{
    broadcast use group_update_bytes_effect;
    broadcast use pmcopy_axioms;

    let next_crc = spec_crc_bytes(next.spec_to_bytes());
    lemma_subrange_subrange(s2,
                            next_addr as int, next_addr + u64::spec_size_of() + u64::spec_size_of(),
                            next_addr as int, next_addr + u64::spec_size_of());
    lemma_subrange_subrange(s2,
                            next_addr as int, next_addr + u64::spec_size_of() + u64::spec_size_of(),
                            next_addr + u64::spec_size_of(),
                            next_addr + u64::spec_size_of() + u64::spec_size_of());
    assert(bytes_written.subrange(0, u64::spec_size_of() as int) =~= next.spec_to_bytes());
    assert(bytes_written.subrange(u64::spec_size_of() as int, (u64::spec_size_of() + u64::spec_size_of()) as int)
           =~= next_crc);
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
            Self::recover(s2, iv.durable_list_addrs, sm) == Self::recover(s1, iv.durable_list_addrs, sm),
    {
        broadcast use group_validate_row_addr;
        broadcast use broadcast_seqs_match_in_range_can_narrow_range;

        assert(iv.row_info[row_addr] is InFreeList);
        assert(iv.corresponds_to_durable_state(s2, sm));
        iv.durable_mapping.lemma_corresponds_implies_equals_new(s1, iv.durable_list_addrs, sm);
        iv.durable_mapping.lemma_corresponds_implies_equals_new(s2, iv.durable_list_addrs, sm);
        assert(Self::recover(s2, iv.durable_list_addrs, sm) =~= Self::recover(s1, iv.durable_list_addrs, sm));
    }

    pub(super) proof fn lemma_writing_to_free_slot_has_permission_later_forall(
        iv: ListTableInternalView<L>,
        initial_jv: JournalView,
        sm: ListTableStaticMetadata,
        free_list_pos: int,
        row_addr: u64,
        tracked perm: &TrustedKvPermission,
    )
        requires
            sm.valid::<L>(),
            iv.valid(sm),
            iv.corresponds_to_durable_state(initial_jv.durable_state, sm),
            iv.corresponds_to_durable_state(initial_jv.read_state, sm),
            Journal::<TrustedKvPermission, PM>::state_recovery_idempotent(initial_jv.durable_state,
                                                                          initial_jv.constants),
            0 <= free_list_pos < iv.free_list.len(),
            iv.free_list[free_list_pos] == row_addr,
            sm.table.validate_row_addr(row_addr),
            sm.table.end <= initial_jv.durable_state.len(),
            forall|s: Seq<u8>| Self::state_equivalent_for_me_specific(s, iv.durable_list_addrs,
                                                                 initial_jv.durable_state, initial_jv.constants, sm)
                ==> #[trigger] perm.check_permission(s),
        ensures
            forall|current_durable_state: Seq<u8>, new_durable_state: Seq<u8>, start: int, end: int|
                #![trigger seqs_match_except_in_range(current_durable_state, new_durable_state, start, end)]
            {
                &&& seqs_match_except_in_range(current_durable_state, new_durable_state, start, end)
                &&& Self::state_equivalent_for_me_specific(current_durable_state, iv.durable_list_addrs,
                                                         initial_jv.durable_state, initial_jv.constants, sm)
                &&& iv.corresponds_to_durable_state(current_durable_state, sm)
                &&& row_addr <= start <= end <= row_addr + sm.table.row_size
                &&& Journal::<TrustedKvPermission, PM>::state_recovery_idempotent(new_durable_state,
                                                                                initial_jv.constants)
            } ==> {
                &&& Self::state_equivalent_for_me_specific(new_durable_state, iv.durable_list_addrs,
                                                         initial_jv.durable_state, initial_jv.constants, sm)
                &&& iv.corresponds_to_durable_state(new_durable_state, sm)
                &&& perm.check_permission(new_durable_state)
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
                &&& Self::state_equivalent_for_me_specific(current_durable_state, iv.durable_list_addrs,
                                                         initial_jv.durable_state, initial_jv.constants, sm)
                &&& iv.corresponds_to_durable_state(current_durable_state, sm)
                &&& row_addr <= start <= end <= row_addr + sm.table.row_size
                &&& Journal::<TrustedKvPermission, PM>::state_recovery_idempotent(new_durable_state,
                                                                                initial_jv.constants)
            } implies {
                &&& Self::state_equivalent_for_me_specific(new_durable_state, iv.durable_list_addrs,
                                                         initial_jv.durable_state, initial_jv.constants, sm)
                &&& iv.corresponds_to_durable_state(new_durable_state, sm)
                &&& perm.check_permission(new_durable_state)
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
            } by {
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

impl ListTableDurableEntry
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
        Self::Durable{ entry: ListTableDurableEntry::default() }
    }

    pub(super) exec fn unwrap_durable(self) -> (result: ListTableDurableEntry)
        requires
            self is Durable,
        ensures
            self == (Self::Durable{ entry: result }),
    {
        match self {
            ListTableEntry::Durable{ entry } => entry,
            _ => { assert(false); ListTableDurableEntry::default() },
        }
    }
}

}

