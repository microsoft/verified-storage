#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::pcm::frac::*;

use crate::common::subrange_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use std::hash::Hash;
use super::impl_v::*;
use super::recover_v::*;
use super::spec_t::*;

verus! {

impl<PermFactory, PM, K, I, L> UntrustedKvStoreImpl<PermFactory, PM, K, I, L>
where
    PermFactory: PermissionFactory<Seq<u8>>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub exec fn commit<Perm>(
        &mut self, 
        Tracked(perm): Tracked<Perm>
    ) -> (result: Result<Tracked<Perm::Completion>, KvError>)
        where
            Perm: CheckPermission<Seq<u8>>,
        requires 
            old(self).valid(),
            perm.id() == old(self)@.powerpm_id,
            forall|s1: Seq<u8>, s2: Seq<u8>| ({
                &&& Self::recover(s1) == Some(RecoveredKvStore::<K, I, L>{ ps: old(self)@.ps, kv: old(self)@.durable })
                &&& Self::recover(s2) == Some(RecoveredKvStore::<K, I, L>{ ps: old(self)@.ps, kv: old(self)@.tentative })
            } || {
                &&& Self::recover(s1) == Some(RecoveredKvStore::<K, I, L>{ ps: old(self)@.ps, kv: old(self)@.durable })
                &&& Self::recover(s2) == Some(RecoveredKvStore::<K, I, L>{ ps: old(self)@.ps, kv: old(self)@.durable })
            }) ==> #[trigger] perm.check_permission(s1, s2),
        ensures 
            self.valid(),
            match result {
                Ok(complete) => {
                    &&& self@ == old(self)@.commit()
                    &&& perm.completed(complete@)
                },
                Err(_) => false,
            }
    {
        let ghost jv_before_commit = self.journal@;

        proof {
            Self::lemma_establish_recovery_equivalent_for_app(self.perm_factory@);
            self.lemma_establish_recovery_equivalent_for_app_on_commit(perm);
        }

        let complete = self.journal.commit::<PermFactory, Perm>(Tracked(self.perm_factory.borrow()), Tracked(perm));

        proof {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(
                old(self).journal@.durable_state, self.journal@.commit_state, jv_before_commit.constants
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

        Ok(complete)
    }

    #[inline(always)]
    pub exec fn agree(&self, Tracked(r): Tracked<&GhostVar<Seq<u8>>>)
        requires
            self.valid(),
            r.id() == self@.powerpm_id,
        ensures
            Self::recover(r@) == Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })
    {
        self.journal.agree(Tracked(r));

        proof {
            self.lemma_recover_to_durable_state();
        }
    }
}

}
