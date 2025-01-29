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
pub(super) struct ListTableDurableEntry
{
    pub head: u64,
    pub tail: u64,
    pub length: usize,
    pub end_of_logical_range: u64,
}

impl ListTableDurableEntry
{
    pub(super) open spec fn consistent_with_recovery_state<L>(self, mapping: ListRecoveryMapping<L>) -> bool
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
    {
        let addrs = mapping.list_info[self.head];
        let last_element = mapping.row_info[addrs.last()].element;
        &&& 0 < addrs.len()
        &&& mapping.list_info.contains_key(self.head)
        &&& mapping.row_info.contains_key(addrs.last())
        &&& self.head == addrs[0]
        &&& self.tail == addrs.last()
        &&& self.length == addrs.len()
        &&& self.end_of_logical_range == last_element.end()
    }
}

#[verifier::ext_equal]
pub(super) enum ListTableEntryView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    Durable{
        entry: ListTableDurableEntry
    },
    TrimmedAndOrAppended{
        durable: ListTableDurableEntry,
        tentative: ListTableDurableEntry,
        num_trimmed: usize,
        appended_addrs: Seq<u64>,
        appended_elements: Seq<L>,
    },
    Updated{
        durable: ListTableDurableEntry,
        tentative_addrs: Seq<u64>,
        tentative_elements: Seq<L>
    },
}

#[verifier::ext_equal]
pub(super) enum ListTableEntry<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    Durable{
        entry: ListTableDurableEntry
    },
    TrimmedAndOrAppended{
        durable: ListTableDurableEntry,
        tentative: ListTableDurableEntry,
        num_trimmed: usize,
        appended_addrs: Vec<u64>,
        appended_elements: Vec<L>,
    },
    Updated{
        durable: ListTableDurableEntry,
        tentative_addrs: Vec<u64>,
        tentative_elements: Vec<L>
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
            ListTableEntry::TrimmedAndOrAppended{ durable, tentative, num_trimmed, appended_addrs, appended_elements } =>
                ListTableEntryView::TrimmedAndOrAppended{ durable, tentative, num_trimmed, appended_addrs: appended_addrs@, appended_elements: appended_elements@ },
            ListTableEntry::Updated{ durable, tentative_addrs, tentative_elements } =>
                ListTableEntryView::Updated{ durable, tentative_addrs: tentative_addrs@, tentative_elements: tentative_elements@ },
        }
    }
}

impl<L> ListTableEntryView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn durable_entry(self) -> ListTableDurableEntry
    {
        match self {
            ListTableEntryView::Durable{ entry } => entry,
            ListTableEntryView::TrimmedAndOrAppended{ durable, .. } => durable,
            ListTableEntryView::Updated{ durable, .. } => durable,
        }
    }

    pub(super) open spec fn consistent_with_tentative_recovery_state(self, mapping: ListRecoveryMapping<L>) -> bool
    {
        match self {
            ListTableEntryView::Durable{ entry } => entry.consistent_with_recovery_state(mapping),
            ListTableEntryView::TrimmedAndOrAppended{ durable, tentative, num_trimmed, appended_addrs, appended_elements } => {
                let addrs = mapping.list_info[tentative.head];
                let elements = addrs.map(|_i, addr| mapping.row_info[addr].element);
                &&& mapping.list_info.contains_key(tentative.head)
                &&& tentative.consistent_with_recovery_state(mapping)
                &&& 0 < addrs.len()
                &&& appended_addrs.len() == appended_elements.len()
                &&& durable.length + appended_elements.len() - num_trimmed == tentative.length
                &&& if elements.len() >= appended_elements.len() {
                    &&& elements.skip(elements.len() - appended_elements.len()) == appended_elements
                    &&& addrs.skip(addrs.len() - appended_addrs.len()) == appended_addrs
                }
                else {
                    &&& addrs == appended_addrs.skip(appended_addrs.len() - addrs.len())
                    &&& elements == appended_elements.skip(appended_elements.len() - elements.len())
                }
            },
            ListTableEntryView::Updated{ durable, tentative_addrs, tentative_elements } => {
                let addrs = mapping.list_info[tentative_addrs[0]];
                let elements = addrs.map(|_i, addr| mapping.row_info[addr].element);
                &&& 0 < tentative_addrs.len()
                &&& mapping.list_info.contains_key(tentative_addrs[0])
                &&& tentative_addrs == addrs
                &&& tentative_elements == elements
                &&& tentative_addrs.len() == tentative_elements.len()
            },
        }
    }    
}

#[verifier::ext_equal]
pub(super) enum ListTableTentativeChange
{
    Updated{ tentative_list_addr: u64 },
    Created{ tentative_list_addr: u64 },
    Deleted{ durable_list_addr: u64, entry: ListTableDurableEntry },
}

#[verifier::ext_equal]
pub(super) enum ListRowDisposition<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    NowhereFree{ element: L },
    InFreeList{ pos: nat },
    InPendingDeallocationList{ pos: nat, element: L },
    InPendingAllocationList{ pos: nat, element: L },
    InBothPendingLists{ alloc_pos: nat, dealloc_pos: nat, element: L },
}

#[verifier::ext_equal]
#[verifier::reject_recursive_types(L)]
pub(super) struct ListInternalView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub durable_list_addrs: Set<u64>,
    pub tentative_list_addrs: Set<u64>,
    pub durable_mapping: ListRecoveryMapping<L>,
    pub tentative_mapping: ListRecoveryMapping<L>,
    pub row_info: Map<u64, ListRowDisposition<L>>,
    pub durable_changes: Map<u64, usize>,
    pub m: Map<u64, ListTableEntryView<L>>,
    pub changes: Seq<ListTableTentativeChange>,
    pub free_list: Seq<u64>,
    pub pending_allocations: Seq<u64>,
    pub pending_deallocations: Seq<u64>,
}

impl<L> ListInternalView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn resolve_change(self, change: ListTableTentativeChange) -> Option<ListTableDurableEntry>
    {
        match change {
            ListTableTentativeChange::Updated{ tentative_list_addr } => {
                if self.m.contains_key(tentative_list_addr) {
                    Some(self.m[tentative_list_addr].durable_entry())
                }
                else {
                    None
                }
            },
            ListTableTentativeChange::Created{ tentative_list_addr } => {
                if self.m.contains_key(tentative_list_addr) {
                    Some(self.m[tentative_list_addr].durable_entry())
                }
                else {
                    None
                }
            },
            ListTableTentativeChange::Deleted{ durable_list_addr, entry } =>
                Some(entry),
        }
    }

    pub(super) open spec fn valid(self, sm: ListTableStaticMetadata) -> bool
    {
        &&& forall|list_addr: u64| #[trigger] self.durable_mapping.list_info.contains_key(list_addr) ==> {
            if self.durable_changes.contains_key(list_addr) {
                let which_change = self.durable_changes[list_addr];
                &&& 0 <= which_change < self.changes.len()
                &&& self.resolve_change(self.changes[which_change as int]) matches Some(entry)
                &&& entry.head == list_addr
            }
            else {
                &&& self.m.contains_key(list_addr)
                &&& self.m[list_addr] is Durable
            }
        }
        &&& forall|list_addr: u64| #[trigger] self.tentative_mapping.list_info.contains_key(list_addr) ==>
                self.m.contains_key(list_addr)
        &&& self.m_consistent_with_durable_recovery_state()        
        &&& self.m_consistent_with_tentative_recovery_state()
        &&& self.deletions_consistent_with_durable_recovery_state()
        &&& self.row_info_complete(sm)
        &&& self.per_row_info_consistent(sm)
    }

    pub(super) open spec fn m_consistent_with_durable_recovery_state(self) -> bool
    {
        &&& forall|list_addr: u64| #[trigger] self.m.contains_key(list_addr) ==>
                self.m[list_addr].durable_entry().consistent_with_recovery_state(self.durable_mapping)
    }

    pub(super) open spec fn m_consistent_with_tentative_recovery_state(self) -> bool
    {
        &&& forall|list_addr: u64| #[trigger] self.m.contains_key(list_addr) ==>
                self.m[list_addr].consistent_with_tentative_recovery_state(self.tentative_mapping)
    }

    pub(super) open spec fn deletions_consistent_with_durable_recovery_state(self) -> bool
    {
        &&& forall|i: int| 0 <= i < self.changes.len() ==>
            (#[trigger] self.changes[i] matches ListTableTentativeChange::Deleted{ durable_list_addr, entry } ==>
             entry.consistent_with_recovery_state(self.durable_mapping))
    }

    pub(super) open spec fn corresponds_to_durable_state(self, s: Seq<u8>, sm: ListTableStaticMetadata) -> bool
    {
        &&& self.durable_mapping.corresponds(s, self.durable_list_addrs, sm)
    }

    pub(super) open spec fn corresponds_to_tentative_state(self, s: Seq<u8>, sm: ListTableStaticMetadata) -> bool
    {
        &&& self.tentative_mapping.corresponds(s, self.tentative_list_addrs, sm)
    }

    pub(super) open spec fn consistent_with_journaled_addrs(self, journaled_addrs: Set<int>, sm: ListTableStaticMetadata) -> bool
    {
        &&& forall|i: int, addr: int| #![trigger self.free_list[i], journaled_addrs.contains(addr)] {
            let row_addr = self.free_list[i];
            &&& 0 <= i < self.free_list.len()
            &&& row_addr <= addr < row_addr + sm.table.row_size
        } ==> !journaled_addrs.contains(addr)
    }

    pub(super) open spec fn row_info_complete(self, sm: ListTableStaticMetadata) -> bool
    {
        &&& forall|row_addr: u64|
            #![trigger sm.table.validate_row_addr(row_addr)]
            #![trigger self.row_info.contains_key(row_addr)]
            sm.table.validate_row_addr(row_addr) ==> self.row_info.contains_key(row_addr)
    }

    pub(super) open spec fn row_info_consistent(self, sm: ListTableStaticMetadata) -> bool
    {
        forall|row_addr: u64| #[trigger] self.row_info.contains_key(row_addr) ==> {
            &&& sm.table.validate_row_addr(row_addr)
            &&& match self.row_info[row_addr] {
                  ListRowDisposition::NowhereFree{ element } => true,
                  ListRowDisposition::InFreeList{ pos } => {
                      &&& 0 <= pos < self.free_list.len()
                      &&& self.free_list[pos as int] == row_addr
                  },
                  ListRowDisposition::InPendingAllocationList{ pos, element } => {
                      &&& 0 <= pos < self.pending_allocations.len()
                      &&& self.pending_allocations[pos as int] == row_addr
                  },
                  ListRowDisposition::InPendingDeallocationList{ pos, element } => {
                      &&& 0 <= pos < self.pending_deallocations.len()
                      &&& self.pending_deallocations[pos as int] == row_addr
                  },
                  ListRowDisposition::InBothPendingLists{ alloc_pos, dealloc_pos, element } => {
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
        &&& forall|i: int| #![trigger self.free_list[i]]
            0 <= i < self.free_list.len() ==> {
            &&& self.row_info.contains_key(self.free_list[i])
            &&& #[trigger] self.row_info[self.free_list[i]] matches ListRowDisposition::InFreeList{ pos }
            &&& pos == i
        }
    }

    pub(super) open spec fn pending_allocations_consistent(self, sm: ListTableStaticMetadata) -> bool
    {
        &&& forall|i: int| #![trigger self.pending_allocations[i]] 0 <= i < self.pending_allocations.len() ==> {
            &&& self.row_info.contains_key(self.pending_allocations[i])
            &&& match self.row_info[self.pending_allocations[i]] {
                ListRowDisposition::InPendingAllocationList{ pos, element } => pos == i,
                ListRowDisposition::InBothPendingLists{ alloc_pos, dealloc_pos, element } => alloc_pos == i,
                _ => false,
            }
        }
    }

    pub(super) open spec fn pending_deallocations_consistent(self, sm: ListTableStaticMetadata) -> bool
    {
        &&& forall|i: int| #![trigger self.pending_deallocations[i]] 0 <= i < self.pending_deallocations.len() ==> {
            &&& self.row_info.contains_key(self.pending_deallocations[i])
            &&& match self.row_info[self.pending_deallocations[i]] {
                ListRowDisposition::InPendingDeallocationList{ pos, element } => pos == i,
                ListRowDisposition::InBothPendingLists{ alloc_pos, dealloc_pos, element } => dealloc_pos == i,
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
        &&& self.sm.valid::<L>()
        &&& self.internal_view().valid(self.sm)
        &&& self.internal_view().corresponds_to_durable_state(jv.durable_state, self.sm)
        &&& self.internal_view().corresponds_to_durable_state(jv.read_state, self.sm)
        &&& self.internal_view().corresponds_to_tentative_state(jv.commit_state, self.sm)
        &&& self.internal_view().consistent_with_journaled_addrs(jv.journaled_addrs, self.sm)
    }

    pub(super) open spec fn internal_view(self) -> ListInternalView<L>
    {
        ListInternalView{
            durable_list_addrs: self.durable_list_addrs@,
            tentative_list_addrs: self.tentative_list_addrs@,
            durable_mapping: self.durable_mapping@,
            tentative_mapping: self.tentative_mapping@,
            row_info: self.row_info@,
            durable_changes: self.durable_changes@,
            m: self.m@.map_values(|e: ListTableEntry<L>| e@),
            changes: self.changes@,
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
            self.tentative_mapping@.lemma_corresponds_implies_equals_new(jv.commit_state, self@.tentative.unwrap().m.dom(), self@.sm);
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
        assume(false);
    }
}

}

