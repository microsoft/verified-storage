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

    /*
#[verifier::ext_equal]
pub(super) enum ListTableStatus {
    Quiescent,
}
impl<L> ListInternalView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub open spec fn apply_last_durable_change(self) -> Self
        recommends
            0 < self.changes.len(),
    {
        let changed_self = match self.changes.last() {
            ListTableTentativeChange::Updated{ tentative_list_addr } =>
                self.apply_updated_change(tentative_list_addr),
            ListTableTentativeChange::Created{ tentative_list_addr } =>
                self.apply_create_change(tentative_list_addr),
        }
    }
}
    */

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub exec fn commit(
        &mut self,
        Ghost(jv_before_commit): Ghost<JournalView>,
        Ghost(jv_after_commit): Ghost<JournalView>,
    )
        requires
            old(self).valid(jv_before_commit),
            old(self)@.tentative is Some,
            jv_before_commit.valid(),
            jv_after_commit.valid(),
            jv_after_commit.committed_from(jv_before_commit),
        ensures
            self.valid(jv_after_commit),
            self@ == (ListTableView{ durable: old(self)@.tentative.unwrap(), ..old(self)@ }),
    {
        assume(false);
        /*
        let ghost new_row_info =
            Map::<u64, ListRowDisposition<L>>::new(
                |row_addr: u64| self.row_info@.contains_key(row_addr),
                |row_addr: u64| match self.row_info@[row_addr] {
                    ListRowDisposition::<L>::InPendingAllocationList{ pos, element } =>
                        ListRowDisposition::<L>::NowhereFree{ element },
                    ListRowDisposition::<L>::InPendingDeallocationList{ pos, element } =>
                        ListRowDisposition::<L>::InFreeList{ pos: self.free_list@.len() + pos },
                    ListRowDisposition::<L>::InBothPendingLists{ alloc_pos, dealloc_pos, element } =>
                        ListRowDisposition::<L>::InFreeList{ pos: self.free_list@.len() + dealloc_pos },
                    _ => self.row_info@[row_addr],
                },
            );
        self.row_info = Ghost(new_row_info);
        self.free_list.append(&mut self.pending_deallocations);
        self.pending_allocations.clear();
        self.durable_list_addrs = self.tentative_list_addrs;
        self.durable_mapping = self.tentative_mapping;

        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        broadcast use group_validate_row_addr;

        assert(self.valid(jv_after_commit)) by {
            assume(false);
            assert(self.sm.valid::<L>());
            assert(self.internal_view().valid(self.sm));
            assume(self.internal_view().corresponds_to_durable_state(jv_after_commit.durable_state, self.sm));
            assume(self.internal_view().corresponds_to_durable_state(jv_after_commit.read_state, self.sm));
            assume(self.internal_view().corresponds_to_tentative_state(jv_after_commit.commit_state, self.sm));
            assume(self.internal_view().consistent_with_journaled_addrs(jv_after_commit.journaled_addrs, self.sm));
        }
        assert(self@ =~= (ListTableView{ durable: old(self)@.tentative.unwrap(), ..old(self)@ }));
        */
    }
}

}

