#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use super::super::impl_t::*;
use super::super::spec_t::*;
use super::recover_v::*;
use super::*;
use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use deps_hack::PmCopy;
use std::collections::HashMap;
use std::hash::Hash;

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
    pub(super) open spec fn inv(self, jv: JournalView) -> bool
    {
        // no rows are both free and pending deallocation
        &&& self.free_list@.to_set().intersect(self.pending_deallocations@.to_set()) == Set::<u64>::empty()

        // TODO @hayley fix invariant

        // // durable and tentative views correspond to free list.
        // // in the durable state, pending deallocations have not yet been deallocated;
        // // in the tentative state they have
        // &&& self.free_list@.to_set().intersect(self@.durable.m.dom()) == Set::<u64>::empty()
        // &&& (self.free_list@.to_set() + self.pending_deallocations@.to_set()).intersect(self@.tentative.m.dom()) == Set::<u64>::empty()

        // // free list and pending dealloc list only contain addresses for valid rows
        // &&& forall |i: int| 0 <= i < self.free_list@.len() ==> #[trigger] self.sm.table.validate_row_addr(self.free_list@[i])
        // &&& forall |i: int| 0 <= i < self.pending_deallocations@.len() ==> #[trigger] self.sm.table.validate_row_addr(self.free_list@[i])

        // // all addresses are either free, pending deallocation, or valid
        // &&& ({
        //         let all_addrs = Set::new(|addr: u64| self.sm.table.validate_row_addr(addr));
        //         // free list + durable view dom == all valid addresses
        //         &&& self.free_list@.to_set() + self@.durable_snapshot.dom() == all_addrs
        //         // free list + pending deallocs + tentative view dom == all valid addresses
        //         &&& self.free_list@.to_set() + self.pending_deallocations@.to_set() + self@.tentative_snapshot.dom() == all_addrs
        //     })
    }

    pub proof fn lemma_valid_implications(self, jv: JournalView)
        requires
            self.valid(jv),
        ensures
            Self::recover(jv.durable_state, self@.durable.m.dom(), self@.sm) == Some(self@.durable),
            self@.tentative is Some ==>
                Self::recover(jv.commit_state, self@.tentative.unwrap().m.dom(), self@.sm) == self@.tentative,
    {
        assume(false);
    }
}

}
