#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::seq::*;

use crate::common::align_v::*;
use crate::common::overflow_v::*;
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
    pub exec fn abort(
        &mut self,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError>)
        requires 
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::recover(s) == Some(old(self)@.durable),
        ensures 
            self.valid(),
            match result {
                Ok(()) => self@ == old(self)@.abort(),
                Err(_) => false,
            }
    {
        self.status = Ghost(KvStoreStatus::MustAbort);
        self.internal_abort(Tracked(perm));
        Ok(())
    }

    pub(super) exec fn internal_abort(
        &mut self,
        Tracked(perm): Tracked<&TrustedKvPermission>
    )
        requires 
            old(self).inv(),
            old(self).status@ is MustAbort,
            forall |s| #[trigger] perm.check_permission(s) <==> Self::recover(s) == Some(old(self)@.durable),
        ensures 
            self.valid(),
            self@ == old(self)@.abort(),
            self.journal@.durable_state == self.journal@.read_state,
    {
        let ghost jv_before_abort = self.journal@;
        self.journal.abort();

        // Calling flush simplifies the reasoning that each component
        // has to do. It has to keep track of its relation to the
        // durable state anyway because of the possibility of a crash.
        // But it might be lazy (from a proof perspective) and not
        // keep track of its relation to the read state. By flushing,
        // we let it know that the durable state and the read state
        // are the same thing. TODO - We could save some performance
        // by not doing this flush, at the cost of trickier reasoning.
        // But since aborts are rare, removing this flush is
        // low-priority for now.

        self.journal.flush();
        
        self.keys.abort(Ghost(jv_before_abort), Ghost(self.journal@));
        self.items.abort(Ghost(jv_before_abort), Ghost(self.journal@));
        self.lists.abort(Ghost(jv_before_abort), Ghost(self.journal@));
        self.status = Ghost(KvStoreStatus::Quiescent);
    }
}

}
