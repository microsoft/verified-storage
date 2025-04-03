#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::journal::JournalView;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use std::hash::Hash;
use super::impl_v::*;
use super::spec_v::*;

verus! {

impl<Perm, PermFactory, PM, K> KeyTable<Perm, PermFactory, PM, K>
where
    Perm: CheckPermission<Seq<u8>>,
    PermFactory: PermissionFactory<Seq<u8>, Perm>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
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
            self@ == (KeyTableView{ durable: old(self)@.tentative.unwrap(), used_slots: self@.used_slots, ..old(self)@ }),
            self@.durable.key_info.dom().finite(),
            self@.used_slots == self@.durable.key_info.dom().len(),
    {
        // Delete all the undo records, and move everything in the pending deallocations
        // list to the free list.

        self.undo_records.clear();
        self.memory_mapping =
            Ghost(self.memory_mapping@.move_pending_deallocations_to_free_list(self.free_list@.len()));
        self.free_list.append(&mut self.pending_deallocations);

        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        broadcast use group_validate_row_addr;

        assert(self.valid(jv_after_commit));

        proof {
            self.memory_mapping@.lemma_corresponds_implication_for_free_list_length(self.free_list@, self.sm);
        }

        assert(self@ =~= (KeyTableView{ durable: old(self)@.tentative.unwrap(), used_slots: self@.used_slots,
                                        ..old(self)@ }));
    }
}

}

