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

verus! {

#[verifier::ext_equal]
pub(super) enum ListTableStatus {
    Quiescent,
}

#[verifier::ext_equal]
#[derive(PmCopy, Copy)]
#[repr(C)]
pub(super) struct ListTableDurableEntry
{
    pub head: u64,
    pub tail: u64,
    pub length: usize,
    pub end_of_logical_range: usize,
}

#[verifier::ext_equal]
pub(super) enum ListTableEntryView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    Durable{
        entry: ListTableDurableEntry
    },
    Updated{
        which_update: nat,
        durable: ListTableDurableEntry,
        tentative: ListTableDurableEntry,
        num_trimmed: int,
        appended_addrs: Seq<u64>,
        appended_elements: Seq<L>,
    },
    Created{
        which_create: nat,
        tentative_addrs: Seq<u64>,
        tentative_elements: Seq<L>
    }
}

#[verifier::ext_equal]
pub(super) enum ListTableEntry<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    Durable{
        entry: ListTableDurableEntry
    },
    Updated{
        which_update: usize,
        durable: ListTableDurableEntry,
        tentative: ListTableDurableEntry,
        num_trimmed: usize,
        appended_addrs: Vec<u64>,
        appended_elements: Vec<L>,
    },
    Created{
        which_create: usize,
        tentative_addrs: Vec<u64>,
        tentative_elements: Vec<L>,
    },
}

impl<L> ListTableEntry<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn view(self) -> ListTableEntryView<L>
    {
        match self {
            ListTableEntry::Durable{ entry } => ListTableEntryView::Durable{ entry },
            ListTableEntry::Updated{ which_update, durable, tentative, num_trimmed,
                                     appended_addrs, appended_elements } =>
                ListTableEntryView::Updated{ which_update: which_update as nat,
                                             durable, tentative, num_trimmed: num_trimmed as int,
                                             appended_addrs: appended_addrs@,
                                             appended_elements: appended_elements@ },
            ListTableEntry::Created{ which_create, tentative_addrs, tentative_elements } =>
                ListTableEntryView::Created{ which_create: which_create as nat,
                                             tentative_addrs: tentative_addrs@,
                                             tentative_elements: tentative_elements@ },
        }
    }
}

impl<L> ListTableEntryView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn commit(self) -> Self
    {
        match self {
            ListTableEntryView::Durable{ entry } => ListTableEntryView::Durable{ entry },
            ListTableEntryView::Updated{ tentative, .. } => ListTableEntryView::Durable{ entry: tentative },
            ListTableEntryView::Created{ tentative_addrs, tentative_elements, .. } =>
                ListTableEntryView::Durable{
                    entry: ListTableDurableEntry{
                        head: tentative_addrs[0],
                        tail: tentative_addrs.last(),
                        length: tentative_addrs.len() as usize,
                        end_of_logical_range: end_of_range(tentative_elements),
                    }
                },
        }
    }
}

#[verifier::ext_equal]
pub(super) enum ListRowDisposition
{
    NowhereFree,
    InFreeList{ pos: nat },
    InPendingDeallocationList{ pos: nat },
    InPendingAllocationList{ pos: nat },
    InBothPendingLists{ alloc_pos: nat, dealloc_pos: nat },
}

#[verifier::ext_equal]
#[verifier::reject_recursive_types(L)]
pub(super) struct ListTableInternalView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub durable_list_addrs: Set<u64>,
    pub tentative_list_addrs: Set<u64>,
    pub durable_mapping: ListRecoveryMapping<L>,
    pub tentative_mapping: ListRecoveryMapping<L>,
    pub row_info: Map<u64, ListRowDisposition>,
    pub m: Map<u64, ListTableEntryView<L>>,
    pub deletes_inverse: Map<u64, nat>,
    pub deletes: Seq<ListTableDurableEntry>,
    pub updates: Seq<Option<u64>>,
    pub creates: Seq<Option<u64>>,
    pub free_list: Seq<u64>,
    pub pending_allocations: Seq<u64>,
    pub pending_deallocations: Seq<u64>,
}

impl<L> ListTableInternalView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn valid(self, sm: ListTableStaticMetadata) -> bool
    {
        &&& self.durable_mapping_reflected_in_changes_or_m()
        &&& self.durable_mapping_corresponds_to_row_info()
        &&& self.tentative_mapping_corresponds_to_row_info()
        &&& self.updates_reflected_in_m()
        &&& self.creates_reflected_in_m()
        &&& forall|list_addr: u64| #[trigger] self.tentative_mapping.list_info.contains_key(list_addr) ==>
                self.m.contains_key(list_addr)
        &&& self.m_consistent_with_durable_recovery_mapping()
        &&& self.m_consistent_with_tentative_recovery_mapping()
        &&& self.deletes_consistent_with_durable_recovery_mapping()
        &&& self.deletes_inverse_is_inverse_of_deletes()
        &&& self.row_info_complete(sm)
        &&& self.per_row_info_consistent(sm)
    }

    pub(super) open spec fn durable_mapping_reflected_in_changes_or_m(self) -> bool
    {
        &&& forall|list_addr: u64| #[trigger] self.durable_mapping.list_info.contains_key(list_addr) ==> {
            if self.deletes_inverse.contains_key(list_addr) {
                let which_delete = self.deletes_inverse[list_addr];
                &&& which_delete < self.deletes.len()
                &&& self.deletes[which_delete as int].head == list_addr
            }
            else {
                &&& self.m.contains_key(list_addr)
                &&& self.m[list_addr] is Durable
            }
        }
    }

    pub(super) open spec fn durable_mapping_corresponds_to_row_info(self) -> bool
    {
        &&& forall|row_addr: u64| #[trigger] self.durable_mapping.row_info.contains_key(row_addr) ==> {
               &&& self.row_info.contains_key(row_addr)
               &&& self.row_info[row_addr] is NowhereFree ||
                  self.row_info[row_addr] is InPendingDeallocationList
           }
    }

    pub(super) open spec fn tentative_mapping_corresponds_to_row_info(self) -> bool
    {
        &&& forall|row_addr: u64| #[trigger] self.tentative_mapping.row_info.contains_key(row_addr) ==> {
               &&& self.row_info.contains_key(row_addr)
               &&& self.row_info[row_addr] is NowhereFree ||
                  self.row_info[row_addr] is InPendingAllocationList
           }
    }

    pub(super) open spec fn updates_reflected_in_m(self) -> bool
    {
        &&& forall|which_update: int| 0 <= which_update < self.updates.len() ==>
               (#[trigger] self.updates[which_update] matches Some(tentative_list_addr) ==> {
                   &&& self.m.contains_key(tentative_list_addr)
                   &&& self.m[tentative_list_addr] matches ListTableEntryView::Updated{ which_update: wu, .. }
                   &&& wu == which_update
               })
    }

    pub(super) open spec fn creates_reflected_in_m(self) -> bool
    {
        &&& forall|which_create: int| 0 <= which_create < self.creates.len() ==>
               (#[trigger] self.creates[which_create] matches Some(tentative_list_addr) ==> {
                   &&& self.m.contains_key(tentative_list_addr)
                   &&& self.m[tentative_list_addr] matches ListTableEntryView::Created{ which_create: wc, .. }
                   &&& wc == which_create
               })
    }

    pub(super) open spec fn m_consistent_with_durable_recovery_mapping(self) -> bool
    {
        &&& forall|list_addr: u64| #[trigger] self.m.contains_key(list_addr) ==>
               (self.m[list_addr] matches ListTableEntryView::Durable{ entry } ==> {
                   let addrs = self.durable_mapping.list_info[list_addr];
                   let elements = addrs.map(|_i, addr| self.durable_mapping.row_info[addr].element);
                   &&& 0 < addrs.len()
                   &&& self.durable_mapping.list_info.contains_key(list_addr)
                   &&& self.durable_mapping.row_info.contains_key(addrs.last())
                   &&& entry.head == addrs[0] == list_addr
                   &&& entry.tail == addrs.last()
                   &&& entry.length == addrs.len()
                   &&& entry.end_of_logical_range == end_of_range(elements)
                   &&& addrs.len() == elements.len()
                   &&& addrs.len() <= usize::MAX
               })
    }

    pub(super) open spec fn deletes_consistent_with_durable_recovery_mapping(self) -> bool
    {
        &&& forall|i: int| #![trigger self.deletes[i]] 0 <= i < self.deletes.len() ==> {
               let entry = self.deletes[i];
               let list_addr = entry.head;
               let addrs = self.durable_mapping.list_info[list_addr];
               let elements = addrs.map(|_i, addr| self.durable_mapping.row_info[addr].element);
               &&& entry.head == addrs[0]
               &&& entry.tail == addrs.last()
               &&& entry.length == addrs.len()
               &&& entry.end_of_logical_range == end_of_range(elements)
               &&& self.deletes_inverse.contains_key(list_addr)
               &&& self.deletes_inverse[list_addr] == i
               &&& 0 < addrs.len()
               &&& self.durable_mapping.list_info.contains_key(list_addr)
               &&& self.durable_mapping.row_info.contains_key(addrs.last())
               &&& addrs.len() == elements.len()
               &&& addrs.len() <= usize::MAX
        }
    }

    pub(super) open spec fn m_consistent_with_tentative_recovery_mapping(self) -> bool
    {
        &&& forall|list_addr: u64| #[trigger] self.m.contains_key(list_addr) ==>
               match self.m[list_addr] {
                   ListTableEntryView::Durable{ entry } => {
                       let addrs = self.tentative_mapping.list_info[list_addr];
                       let elements = addrs.map(|_i, addr| self.tentative_mapping.row_info[addr].element);
                       &&& 0 < addrs.len()
                       &&& self.tentative_mapping.list_info.contains_key(list_addr)
                       &&& entry.head == list_addr == addrs[0]
                       &&& entry.tail == addrs.last()
                       &&& entry.length == addrs.len()
                       &&& entry.end_of_logical_range == end_of_range(elements)
                       &&& addrs.len() == elements.len()
                       &&& addrs.len() <= usize::MAX
                   },
                   ListTableEntryView::Updated{ which_update, durable, tentative, num_trimmed,
                                                appended_addrs, appended_elements } => {
                       let addrs = self.tentative_mapping.list_info[list_addr];
                       let elements = addrs.map(|_i, addr| self.tentative_mapping.row_info[addr].element);
                       &&& 0 <= which_update < self.updates.len()
                       &&& self.updates[which_update as int] == Some(list_addr)
                       &&& self.tentative_mapping.list_info.contains_key(list_addr)
                       &&& tentative.head == list_addr
                       &&& 0 < addrs.len()
                       &&& tentative.head == addrs[0]
                       &&& tentative.tail == addrs.last()
                       &&& tentative.length == addrs.len()
                       &&& addrs.len() == elements.len()
                       &&& addrs.len() <= usize::MAX
                       &&& tentative.end_of_logical_range == end_of_range(elements)
                       &&& num_trimmed < durable.length
                       &&& durable.tail == addrs[durable.length - num_trimmed - 1]
                       &&& durable.end_of_logical_range == elements[durable.length - num_trimmed - 1].end()
                       &&& appended_addrs.len() == appended_elements.len()
                       &&& durable.length + appended_elements.len() - num_trimmed == tentative.length
                       &&& elements.skip(elements.len() - appended_elements.len()) == appended_elements
                       &&& addrs.skip(addrs.len() - appended_addrs.len()) == appended_addrs
                   },
                   ListTableEntryView::Created{ which_create, tentative_addrs, tentative_elements } => {
                       let addrs = self.tentative_mapping.list_info[list_addr];
                       let elements = addrs.map(|_i, addr| self.tentative_mapping.row_info[addr].element);
                       &&& 0 <= which_create < self.creates.len()
                       &&& self.creates[which_create as int] == Some(list_addr)
                       &&& 0 < tentative_addrs.len()
                       &&& tentative_addrs[0] == list_addr
                       &&& self.tentative_mapping.list_info.contains_key(list_addr)
                       &&& tentative_addrs == addrs
                       &&& tentative_elements == elements
                       &&& addrs.len() == elements.len()
                       &&& addrs.len() <= usize::MAX
                   },
               }
    }

    pub(super) open spec fn deletes_inverse_is_inverse_of_deletes(self) -> bool
    {
        &&& forall|list_addr: u64| #[trigger] self.deletes_inverse.contains_key(list_addr) ==> {
            let which_delete = self.deletes_inverse[list_addr];
            &&& 0 <= which_delete < self.deletes.len()
            &&& self.deletes[which_delete as int].head == list_addr
        }
    }

    pub(super) open spec fn corresponds_to_durable_state(self, s: Seq<u8>, sm: ListTableStaticMetadata) -> bool
    {
        &&& self.durable_mapping.corresponds(s, self.durable_list_addrs, sm)
    }

    pub(super) open spec fn corresponds_to_tentative_state(self, s: Seq<u8>, sm: ListTableStaticMetadata) -> bool
    {
        &&& self.tentative_mapping.corresponds(s, self.tentative_list_addrs, sm)
    }

    pub(super) open spec fn consistent_with_journaled_addrs(
        self,
        journaled_addrs: Set<int>,
        sm: ListTableStaticMetadata
    ) -> bool
    {
        &&& forall|i: int, addr: int| #![trigger self.free_list[i], journaled_addrs.contains(addr)] {
            let row_addr = self.free_list[i];
            &&& 0 <= i < self.free_list.len()
            &&& row_addr <= addr < row_addr + sm.table.row_size
        } ==> !journaled_addrs.contains(addr)
    }

    pub(super) open spec fn row_info_complete(self, sm: ListTableStaticMetadata) -> bool
    {
        &&& forall|row_addr: u64| #[trigger] sm.table.validate_row_addr(row_addr) ==> self.row_info.contains_key(row_addr)
    }

    pub(super) open spec fn row_info_consistent(self, sm: ListTableStaticMetadata) -> bool
    {
        forall|row_addr: u64| #[trigger] self.row_info.contains_key(row_addr) ==> {
            &&& sm.table.validate_row_addr(row_addr)
            &&& match self.row_info[row_addr] {
                  ListRowDisposition::NowhereFree => true,
                  ListRowDisposition::InFreeList{ pos } => {
                      &&& 0 <= pos < self.free_list.len()
                      &&& self.free_list[pos as int] == row_addr
                  },
                  ListRowDisposition::InPendingAllocationList{ pos } => {
                      &&& 0 <= pos < self.pending_allocations.len()
                      &&& self.pending_allocations[pos as int] == row_addr
                  },
                  ListRowDisposition::InPendingDeallocationList{ pos } => {
                      &&& 0 <= pos < self.pending_deallocations.len()
                      &&& self.pending_deallocations[pos as int] == row_addr
                  },
                  ListRowDisposition::InBothPendingLists{ alloc_pos, dealloc_pos } => {
                      &&& 0 <= alloc_pos < self.pending_allocations.len()
                      &&& self.pending_allocations[alloc_pos as int] == row_addr
                      &&& 0 <= dealloc_pos < self.pending_deallocations.len()
                      &&& self.pending_deallocations[dealloc_pos as int] == row_addr
                  },
              }
        }
    }

    pub(super) open spec fn free_list_consistent(self, sm: ListTableStaticMetadata) -> bool
    {
        &&& forall|i: int| 0 <= i < self.free_list.len() ==> {
            &&& self.row_info.contains_key(#[trigger] self.free_list[i])
            &&& self.row_info[self.free_list[i]] matches ListRowDisposition::InFreeList{ pos }
            &&& pos == i
        }
    }

    pub(super) open spec fn pending_allocations_consistent(self, sm: ListTableStaticMetadata) -> bool
    {
        &&& forall|i: int| 0 <= i < self.pending_allocations.len() ==> {
            &&& self.row_info.contains_key(#[trigger] self.pending_allocations[i])
            &&& match self.row_info[self.pending_allocations[i]] {
                ListRowDisposition::InPendingAllocationList{ pos } => pos == i,
                ListRowDisposition::InBothPendingLists{ alloc_pos, dealloc_pos } => alloc_pos == i,
                _ => false,
            }
        }
    }

    pub(super) open spec fn pending_deallocations_consistent(self, sm: ListTableStaticMetadata) -> bool
    {
        &&& forall|i: int| 0 <= i < self.pending_deallocations.len() ==> {
            &&& self.row_info.contains_key(#[trigger] self.pending_deallocations[i])
            &&& match self.row_info[self.pending_deallocations[i]] {
                ListRowDisposition::InPendingDeallocationList{ pos } => pos == i,
                ListRowDisposition::InBothPendingLists{ alloc_pos, dealloc_pos } => dealloc_pos == i,
                _ => false,
            }
        }
    }

    pub(super) open spec fn per_row_info_consistent(self, sm: ListTableStaticMetadata) -> bool
    {
        &&& self.row_info_consistent(sm)
        &&& self.free_list_consistent(sm)
        &&& self.pending_allocations_consistent(sm)
        &&& self.pending_deallocations_consistent(sm)
    }
}

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn inv(self, jv: JournalView) -> bool
    {
        &&& 0 < self.sm.start()
        &&& jv.constants.app_area_start <= self.sm.start()
        &&& self.sm.end() <= jv.constants.app_area_end
        &&& self.sm.valid::<L>()
        &&& self.internal_view().valid(self.sm)
        &&& self.internal_view().corresponds_to_durable_state(jv.durable_state, self.sm)
        &&& self.internal_view().corresponds_to_durable_state(jv.read_state, self.sm)
        &&& self.internal_view().corresponds_to_tentative_state(jv.commit_state, self.sm)
        &&& self.internal_view().consistent_with_journaled_addrs(jv.journaled_addrs, self.sm)
    }

    pub(super) open spec fn internal_view(self) -> ListTableInternalView<L>
    {
        ListTableInternalView{
            durable_list_addrs: self.durable_list_addrs@,
            tentative_list_addrs: self.tentative_list_addrs@,
            durable_mapping: self.durable_mapping@,
            tentative_mapping: self.tentative_mapping@,
            row_info: self.row_info@,
            m: self.m@.map_values(|e: ListTableEntry<L>| e@),
            deletes_inverse: self.deletes_inverse@,
            deletes: self.deletes@,
            updates: self.updates@,
            creates: self.creates@,
            free_list: self.free_list@,
            pending_allocations: self.pending_allocations@,
            pending_deallocations: self.pending_deallocations@,
        }
    }

    pub proof fn lemma_valid_implications(self, jv: JournalView)
        requires
            self.valid(jv),
        ensures
            Self::recover(jv.durable_state, self@.durable.m.dom(), self@.sm) == Some(self@.durable),
            self@.tentative is Some ==>
                Self::recover(jv.commit_state, self@.tentative.unwrap().m.dom(), self@.sm) == self@.tentative,
    {
        self.durable_mapping@.lemma_corresponds_implies_equals_new(jv.durable_state, self@.durable.m.dom(), self@.sm);
        if !self.must_abort@ {
            self.tentative_mapping@.lemma_corresponds_implies_equals_new(jv.commit_state,
                                                                         self@.tentative.unwrap().m.dom(), self@.sm);
        }
    }

    pub proof fn lemma_valid_depends_only_on_my_area(&self, old_jv: JournalView, new_jv: JournalView)
        requires
            self.valid(old_jv),
            old_jv.matches_in_range(new_jv, self@.sm.start() as int, self@.sm.end() as int),
            old_jv.constants == new_jv.constants,
        ensures
            self.valid(new_jv),
    {
        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        broadcast use group_validate_row_addr;

        assert(self.valid(new_jv));
    }
}

}

