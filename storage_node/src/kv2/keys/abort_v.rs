#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::journal::JournalView;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use std::hash::Hash;
use super::impl_v::*;
use super::inv_v::*;
use super::spec_v::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::hash::*;

verus! {

impl<PM, K> KeyTable<PM, K>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    exec fn apply_last_undo_record(
        &mut self,
        Ghost(jv): Ghost<JournalView>,
    )
        requires
            old(self).inv(jv),
            old(self).status@ is Inconsistent,
            old(self).undo_records@.len() > 0,
            old(self).internal_view().apply_undo_record(old(self).undo_records@.last()).unwrap().valid(old(self).sm),
        ensures
            self.inv(jv),
            self.status == old(self).status,
            self.must_abort == old(self).must_abort,
            self.sm == old(self).sm,
            self.undo_records@ == old(self).undo_records@.drop_last(),    
    {
        broadcast use group_hash_axioms;

        let undo_record = self.undo_records.pop().unwrap();
        match undo_record {
            KeyUndoRecord::UndoCreate{ row_addr, k } => {
                let ghost rm = self.memory_mapping@.row_info[row_addr]->rm;
                self.memory_mapping =
                    Ghost(self.memory_mapping@.undo_create(row_addr, k, rm, self.free_list@.len()).unwrap());
                self.m.remove(&k);
                self.free_list.push(row_addr);
            },
            KeyUndoRecord::UndoUpdate{ row_addr, k, former_rm } => {
                self.memory_mapping =
                    Ghost(self.memory_mapping@.undo_update(row_addr, k, former_rm).unwrap());
                self.m.insert(k, ConcreteKeyInfo{ row_addr, rm: former_rm });
            },
            KeyUndoRecord::UndoDelete{ row_addr, k, rm } => {
                self.memory_mapping =
                    Ghost(self.memory_mapping@.undo_delete(row_addr, k, rm).unwrap());
                self.m.insert(k, ConcreteKeyInfo{ row_addr, rm });
                let _ = self.pending_deallocations.pop();
            },
        };

        assert(old(self).internal_view().apply_undo_record(undo_record) =~= Some(self.internal_view()));
        assert(self.internal_view().apply_undo_records(self.undo_records@, self.sm) ==
               old(self).internal_view().apply_undo_records(old(self).undo_records@, self.sm));
    }
        
    exec fn apply_all_undo_records(
        &mut self,
        Ghost(jv): Ghost<JournalView>,
    )
        requires
            old(self).inv(jv),
            old(self).status@ is Inconsistent,
        ensures
            self.inv(jv),
            self.status == old(self).status,
            self.must_abort == old(self).must_abort,
            self.sm == old(self).sm,
            self.undo_records@.len() == 0,
    {
        while self.undo_records.len() > 0
            invariant
                self.inv(jv),
                self.status@ is Inconsistent,
                self.must_abort == old(self).must_abort,
                self.sm == old(self).sm,
        {
            self.apply_last_undo_record(Ghost(jv));
        }
    }
    
    pub exec fn abort(
        &mut self,
        Ghost(jv_before_abort): Ghost<JournalView>,
        Ghost(jv_after_abort): Ghost<JournalView>,
    )
        requires
            old(self).valid(jv_before_abort),
            jv_before_abort.valid(),
            jv_after_abort.valid(),
            jv_after_abort == jv_before_abort.abort(),
            jv_before_abort.durable_state == jv_before_abort.read_state,
        ensures
            self.valid(jv_after_abort),
            self@ == (KeyTableView{ tentative: Some(old(self)@.durable), used_slots: self@.used_slots, ..old(self)@ }),
            self@.durable.key_info.dom().finite(),
            self@.used_slots == self@.durable.key_info.dom().len(),
    {
        self.status = Ghost(KeyTableStatus::Inconsistent);
        self.apply_all_undo_records(Ghost(jv_before_abort));
        self.status = Ghost(KeyTableStatus::Quiescent);
        self.must_abort = Ghost(false);

        // There's no need to empty the pending deallocations list because
        // applying the undo records emptied it.
        assert(self.pending_deallocations@ == Seq::<u64>::empty());

        proof {
            self.memory_mapping@.lemma_corresponds_implication_for_free_list_length(self.free_list@, self.sm);
        }

        assert(self@ =~= (KeyTableView{ tentative: Some(old(self)@.durable), used_slots: self@.used_slots,
                                        ..old(self)@ }));
    }
}

}

