#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use std::hash::Hash;
use super::impl_v::*;
use super::spec_t::*;

verus! {

impl<Perm, PermFactory, PM, K, I, L> UntrustedKvStoreImpl<Perm, PermFactory, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PermFactory: PermissionFactory<Seq<u8>, Perm>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub exec fn abort(&mut self) -> (result: Result<(), KvError>)
        requires 
            old(self).valid(),
        ensures 
            self.valid(),
            match result {
                Ok(()) => self@ == old(self)@.abort(),
                Err(_) => false,
            }
    {
        self.status = Ghost(KvStoreStatus::MustAbort);
        assert(self.perm_factory == old(self).perm_factory);
        self.internal_abort();
        Ok(())
    }

    pub(super) exec fn internal_abort(&mut self)
        requires 
            old(self).inv(),
            old(self).status@ is MustAbort,
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

        self.used_key_slots = Ghost(self@.durable.num_keys());
        self.used_list_element_slots = Ghost(self@.durable.num_list_elements());
        self.used_transaction_operation_slots = Ghost(0);
        self.status = Ghost(KvStoreStatus::Quiescent);

        proof {
            self.lemma_used_slots_correspond();
        }
    }
}

}
