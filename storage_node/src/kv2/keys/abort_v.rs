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
use vstd::std_specs::hash::*;

verus! {

impl<PM, K> KeyTable<PM, K>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    exec fn apply_last_undo_record(
        &mut self,
        Ghos(jv): Ghost<JournalView>,
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
            self@ == (KeyTableView{ tentative: Some(old(self)@.durable), ..old(self)@ }),
    {
        self.status = Ghost(KeyTableStatus::Inconsistent);
        self.apply_all_undo_records(Ghost(jv_before_abort));
        self.status = Ghost(KeyTableStatus::Quiescent);
        self.must_abort = Ghost(false);

        // There's no need to empty the pending deallocations list because
        // applying the undo records emptied it.
        assert(self.pending_deallocations@ == Seq::<u64>::empty());

        assert(self@.durable == old(self)@.durable) by {
            let old_mapping =
                old(self).internal_view()
                        .apply_undo_records(old(self).undo_records@, old(self).sm)
                        .unwrap().memory_mapping;
            let mapping = self.internal_view().memory_mapping;
        
            assert(self@.durable.key_info =~= old(self)@.durable.key_info) by {
                assert(forall|k: K| #[trigger] old(self)@.durable.key_info.contains_key(k) ==>
                       old_mapping.row_info.contains_key(old_mapping.key_info[k]));
                assert(forall|k: K| #[trigger] self@.durable.key_info.contains_key(k) ==>
                       mapping.row_info.contains_key(mapping.key_info[k]));
            }
            assert(self@.durable.item_info =~= old(self)@.durable.item_info) by {
                assert(forall|item_addr: u64| #[trigger] old(self)@.durable.item_info.contains_key(item_addr) ==>
                       old_mapping.row_info.contains_key(old_mapping.item_info[item_addr]));
                assert(forall|item_addr: u64| #[trigger] self@.durable.item_info.contains_key(item_addr) ==>
                       mapping.row_info.contains_key(mapping.item_info[item_addr]));
            }
            assert(self@.durable.list_info =~= old(self)@.durable.list_info) by {
                assert(forall|list_addr: u64| #[trigger] old(self)@.durable.list_info.contains_key(list_addr) ==>
                       old_mapping.row_info.contains_key(old_mapping.list_info[list_addr]));
                assert(forall|list_addr: u64| #[trigger] self@.durable.list_info.contains_key(list_addr) ==>
                       mapping.row_info.contains_key(mapping.list_info[list_addr]));
            }
        }
        assert(self@ =~= (KeyTableView{ tentative: Some(old(self)@.durable), ..old(self)@ }));
    }
}

}

