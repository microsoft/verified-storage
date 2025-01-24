#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::seq::*;

use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use std::hash::Hash;
use super::*;
use super::impl_t::*;
use super::items::*;
use super::keys::*;
use super::lists::*;
use super::recover_v::*;
use super::setup_v::*;
use super::spec_t::*;

verus! {

impl<PM, K, I, L> UntrustedKvStoreImpl<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub exec fn untrusted_commit(
        &mut self, 
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError>)
        requires 
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> {
                ||| Self::untrusted_recover(s) == Some(old(self)@.durable)
                ||| Self::untrusted_recover(s) == Some(old(self)@.tentative)
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

        Ok(())
    }
}

}
