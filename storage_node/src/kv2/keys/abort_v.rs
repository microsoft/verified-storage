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
            old(self).status@ is Undoing,
            old(self).undo_records@.len() > 0,
        ensures
            self.inv(jv),
            self.status == old(self).status,
            self.must_abort == old(self).must_abort,
            self.sm == old(self).sm,
            self.undo_records@ == old(self).undo_records@.drop_last(),    
    {
        broadcast use broadcast_undo_records_preserves_sm;

        let undo_record = self.undo_records.pop().unwrap();
        assert(self.internal_view().apply_undo_record(undo_record) is Some);
        broadcast use group_hash_axioms;
        match undo_record {
            KeyUndoRecord::UndoCreate{ row_addr, k } => {
                let ghost rm = self.memory_mapping@.row_info[row_addr]->rm;
                self.memory_mapping =
                    Ghost(self.memory_mapping@.undo_create(row_addr, k, rm, self.free_list@.len()).unwrap());
                self.m.remove(&k);
                self.free_list.push(row_addr);
            },
            KeyUndoRecord::UndoUpdate{ row_addr, former_rm } => { assume(false); }, // TODO @jay
            KeyUndoRecord::UndoDelete{ row_addr, k, rm } => { assume(false); }, // TODO @jay
        };

        assert(old(self).internal_view().apply_undo_record(undo_record) == Some(self.internal_view()));
        assert(self.internal_view().apply_undo_records(self.undo_records@) ==
               old(self).internal_view().apply_undo_records(old(self).undo_records@));
    }
        
    exec fn apply_all_undo_records(
        &mut self,
        Ghost(jv): Ghost<JournalView>,
    )
        requires
            old(self).inv(jv),
            old(self).status@ is Undoing,
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
                self.status@ is Undoing,
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
        ensures
            self.valid(jv_after_abort),
            self@ == (KeyTableView{ tentative: Some(old(self)@.durable), ..old(self)@ }),
    {
        self.status = Ghost(KeyTableStatus::Undoing);
        self.apply_all_undo_records(Ghost(jv_before_abort));
        // Play back the undo list from back to front
        assume(false); // unimplemented
    }
}

}

