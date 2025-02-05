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

impl<L> ListTableInternalView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn create_singleton(self, new_element: L) -> Self
    {
        let row_addr = self.free_list.last();
        let disposition = ListRowDisposition::InPendingAllocationList{ pos: self.pending_allocations.len() as nat };
        let which_create = self.creates.len();
        let entry = ListTableEntryView::<L>::Created{
            which_create,
            tentative_addrs: seq![row_addr],
            tentative_elements: seq![new_element],
        };

        Self{
            tentative_list_addrs: self.tentative_list_addrs.insert(row_addr),
            tentative_mapping: self.tentative_mapping.create_singleton(row_addr, new_element),
            row_info: self.row_info.insert(row_addr, disposition),
            creates: self.creates.push(Some(row_addr)),
            free_list: self.free_list.drop_last(),
            pending_allocations: self.pending_allocations.push(row_addr),
            m: self.m.insert(row_addr, entry),
            ..self
        }
    }

    pub(super) proof fn lemma_create_singleton_works(self, new_element: L, sm: ListTableStaticMetadata)
        requires
            sm.valid::<L>(),
            self.valid(sm),
            self.durable_mapping.internally_consistent(),
            self.tentative_mapping.internally_consistent(),
            self.free_list.len() > 0,
        ensures
            self.create_singleton(new_element).valid(sm),
            self.create_singleton(new_element).tentative_mapping.as_snapshot() ==
                self.tentative_mapping.as_snapshot().create_singleton(self.free_list.last(), new_element),
    {
        let new_self = self.create_singleton(new_element);
        let old_snapshot = self.tentative_mapping.as_snapshot();
        let new_snapshot = new_self.tentative_mapping.as_snapshot();
        let row_addr = self.free_list.last();
        let tentative_addrs = seq![row_addr];
        let tentative_elements = seq![new_element];
        let which_create = self.creates.len();

        assert(tentative_elements =~=
               tentative_addrs.map(|_i, addr| new_self.tentative_mapping.row_info[addr].element));

        assert(forall|list_addr: u64| #[trigger] new_self.m.contains_key(list_addr) ==>
               list_addr == row_addr || self.m.contains_key(list_addr));

        assert(forall|list_addr: u64| #[trigger] new_self.m.contains_key(list_addr) ==>
               match new_self.m[list_addr] {
                   ListTableEntryView::Durable{ entry } => true,
                   ListTableEntryView::Updated{ which_update, durable, tentative, num_trimmed,
                                                appended_addrs, appended_elements } => {
                       let addrs = new_self.tentative_mapping.list_info[list_addr];
                       let elements = addrs.map(|_i, addr| new_self.tentative_mapping.row_info[addr].element);
                       &&& addrs == self.tentative_mapping.list_info[list_addr]
                       &&& elements =~= addrs.map(|_i, addr| self.tentative_mapping.row_info[addr].element)
                   },
                   ListTableEntryView::Created{ which_create, tentative_addrs, tentative_elements } => {
                       let addrs = new_self.tentative_mapping.list_info[list_addr];
                       let elements = addrs.map(|_i, addr| new_self.tentative_mapping.row_info[addr].element);
                       if which_create == self.creates.len() {
                           &&& addrs == tentative_addrs
                           &&& elements =~= tentative_elements
                       } else {
                           &&& addrs == self.tentative_mapping.list_info[list_addr]
                           &&& elements =~= addrs.map(|_i, addr| self.tentative_mapping.row_info[addr].element)
                       }
                   },
               });

        assert forall|list_addr: u64| #[trigger] new_snapshot.m.contains_key(list_addr) implies {
                &&& old_snapshot.create_singleton(row_addr, new_element).m.contains_key(list_addr)
                &&& new_snapshot.m[list_addr] == old_snapshot.create_singleton(row_addr, new_element).m[list_addr]
            } by {
            assert(list_addr != row_addr ==> old_snapshot.m.contains_key(list_addr));
            assert(old_snapshot.create_singleton(row_addr, new_element).m.contains_key(list_addr));
            assert(new_snapshot.m[list_addr] =~= old_snapshot.create_singleton(row_addr, new_element).m[list_addr]);
        }

        assert(new_snapshot =~= old_snapshot.create_singleton(row_addr, new_element));
    }
}

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    proof fn lemma_writing_to_free_slot_doesnt_change_recovery(
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

    proof fn lemma_writing_to_free_slot_has_permission_later_forall(
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

    pub exec fn append(
        &mut self,
        row_addr: u64,
        new_element: L,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<u64, KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().m.contains_key(row_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(new_row_addr) => {
                    &&& new_row_addr != 0
                    &&& new_row_addr == row_addr || !old(self)@.tentative.unwrap().m.contains_key(new_row_addr)
                    &&& match self@.logical_range_gaps_policy {
                        LogicalRangeGapsPolicy::LogicalRangeGapsPermitted =>
                            new_element.start() >= end_of_range(old(self)@.tentative.unwrap().m[row_addr]),
                        LogicalRangeGapsPolicy::LogicalRangeGapsForbidden =>
                            new_element.start() == end_of_range(old(self)@.tentative.unwrap().m[row_addr]),
                    }
                    &&& self@ == (ListTableView {
                        tentative: Some(old(self)@.tentative.unwrap().append(row_addr, new_row_addr, new_element)),
                        ..old(self)@
                    })
                    &&& self.validate_list_addr(new_row_addr)
                },
                Err(KvError::PageLeavesLogicalRangeGap{ end_of_valid_range }) => {
                    &&& self@ == old(self)@
                    &&& self@.logical_range_gaps_policy is LogicalRangeGapsForbidden
                    &&& new_element.start() > end_of_range(old(self)@.tentative.unwrap().m[row_addr])
                    &&& end_of_valid_range == end_of_range(old(self)@.tentative.unwrap().m[row_addr])
                },
                Err(KvError::PageOutOfLogicalRangeOrder{ end_of_valid_range }) => {
                    &&& self@ == old(self)@
                    &&& new_element.start() < end_of_range(old(self)@.tentative.unwrap().m[row_addr])
                    &&& end_of_valid_range == end_of_range(old(self)@.tentative.unwrap().m[row_addr])
                }
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (ListTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                Err(KvError::CRCMismatch) => {
                    &&& !journal@.pm_constants.impervious_to_corruption()
                    &&& self@ == (ListTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                _ => false,
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn create_singleton(
        &mut self,
        new_element: L,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<u64, KvError>)
        requires
            old(self).valid(old(journal)@),
            old(self)@.tentative is Some,
            old(journal).valid(),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(new_row_addr) => {
                    &&& new_row_addr != 0
                    &&& self@.logical_range_gaps_policy is LogicalRangeGapsForbidden ==>
                        new_element.start() == 0
                    &&& !old(self)@.tentative.unwrap().m.contains_key(new_row_addr)
                    &&& self@ == (ListTableView {
                        tentative: Some(old(self)@.tentative.unwrap().create_singleton(new_row_addr, new_element)),
                        ..old(self)@
                    })
                    &&& self.validate_list_addr(new_row_addr)
                },
                Err(KvError::PageLeavesLogicalRangeGap{ end_of_valid_range }) => {
                    &&& self@ == old(self)@
                    &&& self@.logical_range_gaps_policy is LogicalRangeGapsForbidden
                    &&& new_element.start() != 0
                    &&& end_of_valid_range == 0
                }
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (ListTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                Err(KvError::CRCMismatch) => {
                    &&& !journal@.pm_constants.impervious_to_corruption()
                    &&& self@ == (ListTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                _ => false,
            }
    {
        proof {
            self.lemma_valid_implications(journal@);
            journal.lemma_valid_implications();
            assert(self@.durable.m.dom() =~= self.internal_view().durable_list_addrs);
            if self.free_list@.len() > 0 {
                Self::lemma_writing_to_free_slot_has_permission_later_forall(
                    self.internal_view(),
                    journal@,
                    self.sm,
                    self.free_list@.len() - 1,
                    self.free_list@.last(),
                    perm
                );
            }

            broadcast use group_validate_row_addr;
            broadcast use pmcopy_axioms;
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            broadcast use group_update_bytes_effect;
            broadcast use group_hash_axioms;
        }

        match self.logical_range_gaps_policy {
            LogicalRangeGapsPolicy::LogicalRangeGapsForbidden =>
                if new_element.start() != 0 {
                    return Err(KvError::PageLeavesLogicalRangeGap{ end_of_valid_range: 0 });
                },
            _ => {},
        }

        let row_addr = match self.free_list.pop() {
            None => {
                self.must_abort = Ghost(true);
                return Err(KvError::OutOfSpace);
            },
            Some(a) => a,
        };
        assert(old(self).free_list@[self.free_list@.len() as int] == row_addr);

        let element_addr = row_addr + self.sm.row_element_start;
        let element_crc_addr = row_addr + self.sm.row_element_crc_start;
        let element_crc = calculate_crc(&new_element);

        journal.write_object::<L>(element_addr, &new_element, Tracked(perm));
        journal.write_object::<u64>(element_crc_addr, &element_crc, Tracked(perm));

        let next_addr = row_addr + self.sm.row_next_start;
        let next_crc_addr = row_addr + self.sm.row_next_crc_start;
        let next: u64 = 0;
        let next_crc = calculate_crc(&next);

        journal.write_object::<u64>(next_addr, &next, Tracked(perm));
        journal.write_object::<u64>(next_crc_addr, &next_crc, Tracked(perm));

        // Leverage postcondition of `lemma_writing_to_free_slot_has_permission_later_forall`
        // to conclude that `self` is still consistent with both the durable and read state
        // of the journal.
        assert(self.internal_view().corresponds_to_durable_state(journal@.durable_state, self.sm));
        assert(self.internal_view().corresponds_to_durable_state(journal@.read_state, self.sm));

        self.tentative_list_addrs = Ghost(self.tentative_list_addrs@.insert(row_addr));
        self.tentative_mapping = Ghost(self.tentative_mapping@.create_singleton(row_addr, new_element));

        let ghost disposition =
            ListRowDisposition::InPendingAllocationList{ pos: self.pending_allocations.len() as nat };
        self.row_info = Ghost(self.row_info@.insert(row_addr, disposition));

        let which_create = self.creates.len();
        self.creates.push(Some(row_addr));

        self.pending_allocations.push(row_addr);

        let tentative_addrs = vec![row_addr];
        let tentative_elements = vec![new_element];
        assert(tentative_addrs@ =~= seq![row_addr]);
        assert(tentative_elements@ =~= seq![new_element]);
        let entry = ListTableEntry::<L>::Created{
            which_create,
            tentative_addrs,
            tentative_elements,
        };
        self.m.insert(row_addr, entry);

        assert(self.internal_view() =~= old(self).internal_view().create_singleton(new_element));
        proof {
            old(self).internal_view().lemma_create_singleton_works(new_element, self.sm);
        }

        assert(self@ == (ListTableView {
                        tentative: Some(old(self)@.tentative.unwrap().create_singleton(row_addr, new_element)),
                        ..old(self)@
                    }));
        assert(self.valid(journal@));

        Ok(row_addr)
    }
}

}

