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
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> {
                ||| Self::untrusted_recover(s) == Some(old(self)@.durable)
                ||| Self::untrusted_recover(s) == Some(old(self)@.tentative)
            },
        ensures 
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => self@ == old(self)@.commit(),
                Err(_) => false,
            }
    {
        let ghost jv_before_commit = self.journal@;
        let ghost jc = jv_before_commit.constants;
        let ghost js = jv_before_commit.durable_state;
        let ghost sm = self.sm@;

        proof {
            self.lemma_establish_recovery_equivalent_for_app(perm);
        }
        assert forall|s: Seq<u8>| Journal::<TrustedKvPermission, PM>::recovery_equivalent_for_app(
            s, jv_before_commit.commit_state
        ) implies #[trigger] perm.check_permission(s) by {
            assume(false);
        }
        self.journal.commit(Tracked(perm));
        assume(false);
        self.keys.commit(Ghost(jv_before_commit), Ghost(self.journal@));
        self.items.commit(Ghost(jv_before_commit), Ghost(self.journal@));
        self.lists.commit(Ghost(jv_before_commit), Ghost(self.journal@));
        Ok(())
    }
}

}
