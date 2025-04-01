#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::subrange_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use std::hash::Hash;
use super::impl_v::*;
use super::recover_v::*;
use super::spec_t::*;

verus! {

impl<Perm, PM, K, I, L> UntrustedKvStoreImpl<Perm, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub exec fn commit(
        &mut self, 
        Tracked(perm): Tracked<&Perm>
    ) -> (result: Result<(), KvError>)
        requires 
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <== {
                ||| Self::recover(s) == Some(RecoveredKvStore::<K, I, L>{ ps: old(self)@.ps, kv: old(self)@.durable })
                ||| Self::recover(s) == Some(RecoveredKvStore::<K, I, L>{ ps: old(self)@.ps, kv: old(self)@.tentative })
            },
        ensures 
            self.valid(),
            match result {
                Ok(()) => self@ == old(self)@.commit(),
                Err(_) => false,
            }
    {
        let ghost jv_before_commit = self.journal@;

        proof {
            self.lemma_establish_recovery_equivalent_for_app(perm);
            self.lemma_establish_recovery_equivalent_for_app_after_commit(perm);
        }

        self.journal.commit(Tracked(perm));

        proof {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(
                old(self).journal@.durable_state, self.journal@.commit_state, self.sm@, jv_before_commit.constants
            );
        }

        self.keys.commit(Ghost(jv_before_commit), Ghost(self.journal@));
        self.items.commit(Ghost(jv_before_commit), Ghost(self.journal@));
        self.lists.commit(Ghost(jv_before_commit), Ghost(self.journal@));

        self.used_key_slots = Ghost(self@.durable.num_keys());
        self.used_list_element_slots = Ghost(self@.durable.num_list_elements());
        self.used_transaction_operation_slots = Ghost(0);

        proof {
            self.lemma_used_slots_correspond();
        }

        Ok(())
    }
}

}
