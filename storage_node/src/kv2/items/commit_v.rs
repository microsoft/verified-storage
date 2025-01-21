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

verus! {

#[verifier::ext_equal]
pub(super) enum ItemTableStatus {
    Quiescent,
}

impl<PM, I> ItemTable<PM, I>
    where
        PM: PersistentMemoryRegion,
        I: PmCopy + Sized + std::fmt::Debug,
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
            self@ == (ItemTableView{ durable: old(self)@.tentative.unwrap(), ..old(self)@ }),
    {
        let ghost new_row_info =
            Map::<u64, ItemRowDisposition<I>>::new(
                |row_addr: u64| self.row_info@.contains_key(row_addr),
                |row_addr: u64| match self.row_info@[row_addr] {
                    ItemRowDisposition::<I>::InPendingAllocationList{ pos, item } =>
                        ItemRowDisposition::<I>::NowhereFree{ item },
                    ItemRowDisposition::<I>::InPendingDeallocationList{ pos, item } =>
                        ItemRowDisposition::<I>::InFreeList{ pos: self.free_list@.len() + pos },
                    _ => self.row_info@[row_addr],
                },
            );
        self.row_info = Ghost(new_row_info);
        self.free_list.append(&mut self.pending_deallocations);
        self.pending_allocations.clear();

        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        broadcast use group_validate_row_addr;

        assert(self.valid(jv_after_commit));
        assert(self@ =~= (ItemTableView{ durable: old(self)@.tentative.unwrap(), ..old(self)@ }));
    }
}

}

