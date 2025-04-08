#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::power_t::*;
use deps_hack::PmCopy;
use super::impl_v::*;
use super::recover_v::*;
use super::super::spec_t::*;

verus! {

#[verifier::ext_equal]
pub(super) enum ListTableStatus {
    Quiescent,
    PoppedEntry,
}

#[verifier::ext_equal]
#[derive(PmCopy, Copy)]
#[repr(C)]
pub(super) struct ListSummary
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
        summary: ListSummary
    },
    Modified{
        which_modification: nat,
        durable_head: u64,
        summary: ListSummary,
        addrs: Seq<u64>,
        elements: Seq<L>
    }
}

#[verifier::ext_equal]
pub(super) enum ListTableEntry<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    Durable{
        summary: ListSummary
    },
    Modified{
        which_modification: usize,
        durable_head: Ghost<u64>,
        summary: ListSummary,
        addrs: Vec<u64>,
        elements: Vec<L>,
    },
}

impl<L> ListTableEntry<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn view(self) -> ListTableEntryView<L>
    {
        match self {
            ListTableEntry::Durable{ summary } => ListTableEntryView::Durable{ summary },
            ListTableEntry::Modified{ which_modification, durable_head, summary, addrs, elements } =>
                ListTableEntryView::Modified{ which_modification: which_modification as nat,
                                              durable_head: durable_head@, summary,
                                              addrs: addrs@, elements: elements@ },
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
            ListTableEntryView::Durable{ summary } => ListTableEntryView::Durable{ summary },
            ListTableEntryView::Modified{ summary, .. } => ListTableEntryView::Durable{ summary },
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

impl ListTableStaticMetadata
{
    pub(super) open spec fn corresponds_to_journal(self, jv: JournalView) -> bool
    {
        &&& jv.constants.app_area_start <= self.start()
        &&& self.end() <= jv.constants.app_area_end
    }
}

#[verifier::ext_equal]
#[verifier::reject_recursive_types(L)]
pub(super) struct ListTableInternalView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub status: ListTableStatus,
    pub durable_mapping: ListRecoveryMapping<L>,
    pub tentative_mapping: ListRecoveryMapping<L>,
    pub row_info: Map<u64, ListRowDisposition>,
    pub m: Map<u64, ListTableEntryView<L>>,
    pub deletes_inverse: Map<u64, nat>,
    pub deletes: Seq<ListSummary>,
    pub modifications: Seq<Option<u64>>,
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
        &&& self.durable_mapping.internally_consistent(sm)
        &&& self.tentative_mapping.internally_consistent(sm)
        &&& self.durable_mapping_reflected_in_changes_or_m()
        &&& self.modifications_reflected_in_m()
        &&& forall|list_addr: u64| #[trigger] self.tentative_mapping.list_info.contains_key(list_addr) ==>
                self.m.contains_key(list_addr)
        &&& self.m_consistent_with_recovery_mappings()
        &&& self.deletes_arent_durable_in_m()
        &&& self.deletes_consistent_with_durable_recovery_mapping()
        &&& self.deletes_inverse_is_inverse_of_deletes()
        &&& self.row_info_complete(sm)
        &&& self.per_row_info_consistent(sm)
    }

    pub(super) open spec fn corresponds_to_journal(self, jv: JournalView, sm: ListTableStaticMetadata) -> bool
    {
        &&& self.valid(sm)
        &&& self.corresponds_to_durable_state(jv.durable_state, sm)
        &&& self.corresponds_to_durable_state(jv.read_state, sm)
        &&& self.corresponds_to_tentative_state(jv.commit_state, sm)
        &&& self.consistent_with_journaled_addrs(jv.journaled_addrs, sm)
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

    pub(super) open spec fn modifications_reflected_in_m(self) -> bool
    {
        &&& forall|which_modification: int| 0 <= which_modification < self.modifications.len() ==>
               (#[trigger] self.modifications[which_modification] matches Some(tentative_list_addr) ==> {
                   &&& self.m.contains_key(tentative_list_addr)
                   &&& match self.m[tentative_list_addr] {
                          ListTableEntryView::Modified{ which_modification: wm, .. } => which_modification == wm,
                          _ => false,
                      }
               })
    }

    pub(super) open spec fn m_consistent_with_recovery_mappings(self) -> bool
    {
        &&& forall|list_addr: u64| #[trigger] self.m.contains_key(list_addr) ==>
               match self.m[list_addr] {
                   ListTableEntryView::Durable{ summary } => {
                       let durable_addrs = self.durable_mapping.list_info[list_addr];
                       let durable_elements = self.durable_mapping.list_elements[list_addr];
                       let tentative_addrs = self.tentative_mapping.list_info[list_addr];
                       let tentative_elements = self.tentative_mapping.list_elements[list_addr];
                       &&& durable_addrs == tentative_addrs
                       &&& durable_elements == tentative_elements
                       &&& 0 < tentative_addrs.len()
                       &&& self.durable_mapping.list_info.contains_key(list_addr)
                       &&& self.durable_mapping.row_info.contains_key(durable_addrs.last())
                       &&& self.tentative_mapping.list_info.contains_key(list_addr)
                       &&& summary.head == list_addr == tentative_addrs[0]
                       &&& summary.tail == tentative_addrs.last()
                       &&& summary.length == tentative_addrs.len()
                       &&& summary.end_of_logical_range == end_of_range(tentative_elements)
                       &&& tentative_addrs.len() == tentative_elements.len()
                       &&& tentative_addrs.len() <= usize::MAX
                   },
                   ListTableEntryView::Modified{ which_modification, durable_head, summary, addrs, elements } => {
                       let tentative_addrs = self.tentative_mapping.list_info[list_addr];
                       let tentative_elements = self.tentative_mapping.list_elements[list_addr];
                       &&& 0 <= which_modification < self.modifications.len()
                       &&& self.modifications[which_modification as int] == Some(list_addr)
                       &&& self.tentative_mapping.list_info.contains_key(list_addr)
                       &&& summary.head == list_addr
                       &&& 0 < tentative_addrs.len()
                       &&& summary.head == tentative_addrs[0]
                       &&& summary.tail == tentative_addrs.last()
                       &&& summary.length == tentative_addrs.len()
                       &&& tentative_addrs.len() == tentative_elements.len()
                       &&& tentative_addrs.len() <= usize::MAX
                       &&& summary.end_of_logical_range == end_of_range(tentative_elements)
                       &&& addrs.len() == elements.len()
                       &&& if addrs.len() == summary.length {
                              &&& durable_head == 0
                              &&& tentative_addrs == addrs
                              &&& tentative_elements == elements
                          } else {
                              let durable_addrs = self.durable_mapping.list_info[durable_head];
                              let durable_elements = self.durable_mapping.list_elements[durable_head];
                              &&& self.durable_mapping.list_info.contains_key(durable_head)
                              &&& 0 < durable_addrs.len()
                              &&& addrs.len() < summary.length
                              &&& summary.length - addrs.len() <= durable_addrs.len()
                              &&& durable_addrs.len() == durable_elements.len()
                              &&& tentative_addrs ==
                                  durable_addrs.skip(durable_addrs.len() - (summary.length - addrs.len())) + addrs
                              &&& tentative_elements ==
                                 durable_elements.skip(durable_elements.len() - (summary.length - elements.len())) +
                                  elements
                              &&& addrs.len() == elements.len()
                          }
                   },
               }
    }

    pub(super) open spec fn deletes_arent_durable_in_m(self) -> bool
    {
        &&& forall|i: int| #![trigger self.deletes[i]] 0 <= i < self.deletes.len() ==> {
               let summary = self.deletes[i];
               let list_addr = summary.head;
               self.m.contains_key(list_addr) ==> !(self.m[list_addr] is Durable)
           }
    }

    pub(super) open spec fn deletes_consistent_with_durable_recovery_mapping(self) -> bool
    {
        &&& forall|i: int| #![trigger self.deletes[i]] 0 <= i < self.deletes.len() ==> {
               let summary = self.deletes[i];
               let list_addr = summary.head;
               let addrs = self.durable_mapping.list_info[list_addr];
               let elements = self.durable_mapping.list_elements[list_addr];
               &&& summary.head == addrs[0]
               &&& summary.tail == addrs.last()
               &&& summary.length == addrs.len()
               &&& summary.end_of_logical_range == end_of_range(elements)
               &&& self.deletes_inverse.contains_key(list_addr)
               &&& self.deletes_inverse[list_addr] == i
               &&& 0 < addrs.len()
               &&& self.durable_mapping.list_info.contains_key(list_addr)
               &&& self.durable_mapping.row_info.contains_key(addrs.last())
               &&& addrs.len() == elements.len()
               &&& addrs.len() <= usize::MAX
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
        &&& self.durable_mapping.corresponds(s, self.durable_mapping.list_elements.dom(), sm)
    }

    pub(super) open spec fn corresponds_to_tentative_state(self, s: Seq<u8>, sm: ListTableStaticMetadata) -> bool
    {
        &&& self.tentative_mapping.corresponds(s, self.tentative_mapping.list_elements.dom(), sm)
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
                  ListRowDisposition::NowhereFree => {
                      &&& self.durable_mapping.row_info.contains_key(row_addr)
                      &&& self.tentative_mapping.row_info.contains_key(row_addr)
                  },
                  ListRowDisposition::InFreeList{ pos } => {
                      &&& 0 <= pos < self.free_list.len()
                      &&& self.free_list[pos as int] == row_addr
                      &&& !self.durable_mapping.row_info.contains_key(row_addr)
                      &&& !self.tentative_mapping.row_info.contains_key(row_addr)
                  },
                  ListRowDisposition::InPendingAllocationList{ pos } => {
                      &&& 0 <= pos < self.pending_allocations.len()
                      &&& self.pending_allocations[pos as int] == row_addr
                      &&& !self.durable_mapping.row_info.contains_key(row_addr)
                      &&& self.tentative_mapping.row_info.contains_key(row_addr)
                  },
                  ListRowDisposition::InPendingDeallocationList{ pos } => {
                      &&& 0 <= pos < self.pending_deallocations.len()
                      &&& self.pending_deallocations[pos as int] == row_addr
                      &&& self.durable_mapping.row_info.contains_key(row_addr)
                      &&& !self.tentative_mapping.row_info.contains_key(row_addr)
                  },
                  ListRowDisposition::InBothPendingLists{ alloc_pos, dealloc_pos } => {
                      &&& 0 <= alloc_pos < self.pending_allocations.len()
                      &&& self.pending_allocations[alloc_pos as int] == row_addr
                      &&& 0 <= dealloc_pos < self.pending_deallocations.len()
                      &&& self.pending_deallocations[dealloc_pos as int] == row_addr
                      &&& !self.durable_mapping.row_info.contains_key(row_addr)
                      &&& !self.tentative_mapping.row_info.contains_key(row_addr)
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

    pub(super) open spec fn add_entry(self, list_addr: u64, entry: ListTableEntryView<L>) -> Self
    {
        Self{
            m: self.m.insert(list_addr, entry),
            ..self
        }
    }

    pub(super) open spec fn push_to_free_list(self, row_addr: u64) -> Self
    {
        Self{
            free_list: self.free_list.push(row_addr),
            ..self
        }
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
        &&& 0 < self.sm.start()
        &&& self.sm.corresponds_to_journal(jv)
        &&& self.space_needed_to_journal_next ==
            spec_journal_entry_overhead() +
            u64::spec_size_of() + u64::spec_size_of()
        &&& self.status@ is Quiescent ==> self.internal_view().corresponds_to_journal(jv, self.sm)
    }

    pub(super) open spec fn internal_view(self) -> ListTableInternalView<L>
    {
        ListTableInternalView{
            status: self.status@,
            durable_mapping: self.durable_mapping@,
            tentative_mapping: self.tentative_mapping@,
            row_info: self.row_info@,
            m: self.m@.map_values(|e: ListTableEntry<L>| e@),
            deletes_inverse: self.deletes_inverse@,
            deletes: self.deletes@,
            modifications: self.modifications@,
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

