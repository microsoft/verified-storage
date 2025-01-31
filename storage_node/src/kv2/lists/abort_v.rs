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
use super::spec_v::*;
use super::super::impl_t::*;
use super::super::spec_t::*;

verus! {

#[verifier::ext_equal]
pub(super) enum ListTableStatus {
    Quiescent,
}

impl<L> ListTableInternalView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn abort_m(self) -> Map<u64, ListTableEntryView<L>>
    {
        Map::<u64, ListTableEntryView<L>>::new(
            |list_addr: u64| {
                ||| self.deletions_inverse.contains_key(list_addr)
                ||| {
                       &&& self.m.contains_key(list_addr)
                       &&& self.m[list_addr] is Durable
                   }
            },
            |list_addr: u64| {
                if self.deletions_inverse.contains_key(list_addr) {
                    ListTableEntryView::Durable{ entry: self.deletions[self.deletions_inverse[list_addr] as int] }
                }
                else {
                    self.m[list_addr]
                }
            }
        )
    }

    pub(super) open spec fn abort_row_info(self) -> Map<u64, ListRowDisposition<L>>
    {
        Map::<u64, ListRowDisposition<L>>::new(
            |row_addr: u64| self.row_info.contains_key(row_addr),
            |row_addr: u64| match self.row_info[row_addr] {
                ListRowDisposition::<L>::InPendingAllocationList{ pos, element } =>
                    ListRowDisposition::<L>::InFreeList{ pos: self.free_list.len() + pos },
                ListRowDisposition::<L>::InPendingDeallocationList{ pos, element } =>
                    ListRowDisposition::<L>::NowhereFree{ element },
                ListRowDisposition::<L>::InBothPendingLists{ alloc_pos, dealloc_pos, element } =>
                    ListRowDisposition::<L>::InFreeList{ pos: self.free_list.len() + alloc_pos },
                _ => self.row_info[row_addr],
            },
        )
    }

    pub(super) open spec fn abort(self) -> Self
    {
        Self {
            durable_list_addrs: self.durable_list_addrs,
            tentative_list_addrs: self.durable_list_addrs,
            durable_mapping: self.durable_mapping,
            tentative_mapping: self.durable_mapping,
            row_info: self.abort_row_info(),
            m: self.abort_m(),
            deletions_inverse: Map::<u64, usize>::empty(),
            deletions: Seq::<ListTableDurableEntry>::empty(),
            updates: Seq::<Option<u64>>::empty(),
            creates: Seq::<Option<u64>>::empty(),
            free_list: self.free_list + self.pending_allocations,
            pending_allocations: Seq::<u64>::empty(),
            pending_deallocations: Seq::<u64>::empty(),
        }
    }

    pub(super) proof fn lemma_abort_works(self, s: Seq<u8>, sm: ListTableStaticMetadata)
        requires
            self.valid(sm),
            self.corresponds_to_durable_state(s, sm),
        ensures
            self.abort().valid(sm),
            self.abort().corresponds_to_durable_state(s, sm),
    {
    }
}

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub exec fn abort(
        &mut self,
        jv_before_abort: Ghost<JournalView>,
        jv_after_abort: Ghost<JournalView>,
    )
        requires
            old(self).valid(jv_before_abort@),
            jv_before_abort@.valid(),
            jv_after_abort@.valid(),
            jv_after_abort == jv_before_abort@.abort(),
        ensures
            self.valid(jv_after_abort@),
            self@ == (ListTableView{ tentative: Some(old(self)@.durable), ..old(self)@ }),
    {
        // Play back the undo list from back to front
        self.must_abort = Ghost(false);
        assume(false); // unimplemented
    }
}

}

