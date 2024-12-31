//! This file contains the verified implementation of the KV store. The methods
//! defined here are meant to be called by methods in kvimpl_t.rs with `Perm`
//! arguments that have been audited along with the rest of that file.
//!
//! The UntrustedKvStoreImpl is split into two key components: a volatile index
//! and a durable store. Each of these may be further split into separate components,
//! but having a high-level split between volatile and durable should make the
//! distinction between updates that require crash-consistency proofs, and updates
//! that don't, clear. The view of an UntrustedKvStoreImpl is obtained using the contents
//! of its current volatile and durable components.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::seq::*;

use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use std::hash::Hash;
use super::kvimpl_t::*;
use super::kvspec_t::*;

verus! {

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
pub struct UntrustedKvStoreImpl<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + std::fmt::Debug,
    I: PmCopy + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug + Copy,
{
    id: u128,
    phantom_pm: core::marker::PhantomData<PM>,
    phantom_k: core::marker::PhantomData<K>,
    phantom_i: core::marker::PhantomData<I>,
    phantom_l: core::marker::PhantomData<L>,
}

pub open spec fn untrusted_recover<K, I, L>(mem: Seq<u8>) -> Option<AbstractKvStoreState<K, I, L>>
{
    None
}

impl<PM, K, I, L> UntrustedKvStoreImpl<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug + Copy,
{
    pub closed spec fn pm_constants(self) -> PersistentMemoryConstants
    {
        arbitrary()
    }

    pub closed spec fn view(&self) -> AbstractKvState<K, I, L>
    {
        arbitrary()
    }

    pub closed spec fn valid(self) -> bool
    {
        true
    }

    pub exec fn untrusted_setup(
        pm: &mut PM,
        kvstore_id: u128,
        num_keys: u64, 
        num_list_entries_per_node: u32,
        num_list_nodes: u64,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(pm).inv(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            match result {
                Ok(()) => {
                    &&& pm@.flush_predicted()
                    &&& untrusted_recover::<K, I, L>(pm@.durable_state)
                        == Some(AbstractKvStoreState::<K, I, L>::init(kvstore_id))
                },
                Err(_) => true,
            }
    {
        // 1. flush the pm to ensure there are no outstanding writes
        pm.flush();
        assume(false);
        Ok(())
    }

    pub fn untrusted_start(
        wrpm: WriteRestrictedPersistentMemoryRegion<TrustedKvPermission, PM>,
        kvstore_id: u128,
        Ghost(state): Ghost<AbstractKvStoreState<K, I, L>>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<Self, KvError<K>>)
        requires 
            wrpm.inv(),
            wrpm@.flush_predicted(),
            untrusted_recover::<K, I, L>(wrpm@.durable_state) == Some(state),
            forall |s| #[trigger] perm.check_permission(s) <==> untrusted_recover::<K, I, L>(s) == Some(state),
        ensures
            match result {
                Ok(kv) => {
                    &&& kv.valid()
                    &&& kv.pm_constants() == wrpm.constants()
                    &&& kv@.valid()
                    &&& kv@.id() == state.id == kvstore_id
                    &&& kv@.durable == state
                    &&& kv@.tentative == state
                }
                Err(KvError::CRCMismatch) => !wrpm.constants().impervious_to_corruption(),
                Err(KvError::WrongKvStoreId{ requested_id, actual_id }) => {
                   &&& requested_id == kvstore_id
                   &&& actual_id == state.id
                },
                Err(_) => false,
            }
    {        
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_read_item(
        &self,
        key: &K,
    ) -> (result: Result<&I, KvError<K>>)
        requires 
            self.valid(),
        ensures
            match result {
                Ok(item) => {
                    &&& self@.tentative.read_item(*key) matches Ok(i)
                    &&& item == i
                },
                Err(KvError::CRCMismatch) => !self.pm_constants().impervious_to_corruption(),
                Err(e) => {
                    &&& self@.tentative.read_item(*key) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    // This function performs a tentative update to the item of the specified key 
    // as part of an ongoing transaction.
    pub exec fn untrusted_update_item(
        &mut self,
        key: &K,
        new_item: &I,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> untrusted_recover::<K, I, L>(s) == Some(old(self)@.durable),
        ensures 
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.update_item(*key, *new_item) matches Ok(new_self)
                    &&& self@.tentative == new_self
                    &&& self@.durable == old(self)@.durable
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self.pm_constants().impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    // TODO
                },
                Err(e) => {
                    &&& old(self)@.tentative.update_item(*key, *new_item) matches Err(e_spec)
                    &&& e_spec == e
                    &&& self@ == old(self)@
                },
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_commit(
        &mut self, 
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> {
                ||| untrusted_recover::<K, I, L>(s) == Some(old(self)@.durable)
                ||| untrusted_recover::<K, I, L>(s) == Some(old(self)@.tentative)
            },
        ensures 
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => self@ == old(self)@.commit(),
                Err(_) => false,
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_create(
        &mut self,
        key: &K,
        item: &I,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> untrusted_recover::<K, I, L>(s) == Some(old(self)@.durable),
        ensures 
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.create(*key, *item) matches Ok(new_self)
                    &&& self@.tentative == new_self
                    &&& self@.durable == old(self)@.durable
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self.pm_constants().impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    // TODO
                }
                Err(e) => {
                    &&& old(self)@.tentative.create(*key, *item) matches Err(e_spec)
                    &&& e == e_spec
                    &&& self@ == old(self)@
                },
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_delete(
        &mut self,
        key: &K,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> untrusted_recover::<K, I, L>(s) == Some(old(self)@.durable),
        ensures 
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.delete(*key) matches Ok(new_self)
                    &&& self@.tentative == new_self
                    &&& self@.durable == old(self)@.durable
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self.pm_constants().impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    // TODO
                }
                Err(e) => {
                    &&& old(self)@.tentative.delete(*key) matches Err(e_spec)
                    &&& e == e_spec
                    &&& self@ == old(self)@
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub fn untrusted_read_item_and_list(&self, key: &K) -> (result: Result<(&I, &Vec<L>), KvError<K>>)
        requires
            self.valid(),
        ensures
            match result {
                Ok((item, lst)) => {
                    &&& self@.tentative.read_item_and_list(*key) matches Ok((i, l))
                    &&& item == i
                    &&& lst@ == l
                },
                Err(KvError::CRCMismatch) => !self.pm_constants().impervious_to_corruption(),
                Err(e) => {
                    &&& self@.tentative.read_item_and_list(*key) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub fn untrusted_read_list(&self, key: &K) -> (result: Result<&Vec<L>, KvError<K>>)
        requires
            self.valid(),
        ensures
            match result {
                Ok(lst) => {
                    &&& self@.tentative.read_item_and_list(*key) matches Ok((i, l))
                    &&& lst@ == l
                },
                Err(KvError::CRCMismatch) => !self.pm_constants().impervious_to_corruption(),
                Err(e) => {
                    &&& self@.tentative.read_item_and_list(*key) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub fn untrusted_read_list_entry_at_index(&self, key: &K, idx: u64) -> (result: Result<&L, KvError<K>>)
        requires
            self.valid()
        ensures
            match result {
                Ok(element) => {
                    &&& self@.tentative.read_list_entry_at_index(*key, idx as nat) matches Ok((e))
                    &&& *element == e
                },
                Err(KvError::CRCMismatch) => !self.pm_constants().impervious_to_corruption(),
                Err(e) => {
                    &&& self@.tentative.read_list_entry_at_index(*key, idx as nat) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub fn untrusted_append_to_list(
        &mut self,
        key: &K,
        new_list_entry: L,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> untrusted_recover::<K, I, L>(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.append_to_list(*key, new_list_entry) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => !self.pm_constants().impervious_to_corruption(),
                Err(e) => {
                    &&& old(self)@.tentative.append_to_list(*key, new_list_entry) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub fn untrusted_append_to_list_and_update_item(
        &mut self,
        key: &K,
        new_list_entry: L,
        new_item: I,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> untrusted_recover::<K, I, L>(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.append_to_list_and_update_item(*key, new_list_entry, new_item)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => !self.pm_constants().impervious_to_corruption(),
                Err(e) => {
                    &&& old(self)@.tentative.append_to_list_and_update_item(*key, new_list_entry, new_item)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub fn untrusted_update_list_entry_at_index(
        &mut self,
        key: &K,
        idx: usize,
        new_list_entry: L,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> untrusted_recover::<K, I, L>(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.update_list_entry_at_index(*key, idx as nat, new_list_entry)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => !self.pm_constants().impervious_to_corruption(),
                Err(e) => {
                    &&& old(self)@.tentative.update_list_entry_at_index(*key, idx as nat, new_list_entry)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub fn untrusted_update_list_entry_at_index_and_item(
        &mut self,
        key: &K,
        idx: usize,
        new_list_entry: L,
        new_item: I,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> untrusted_recover::<K, I, L>(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.update_list_entry_at_index_and_item(*key, idx as nat, new_list_entry, new_item)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => !self.pm_constants().impervious_to_corruption(),
                Err(e) => {
                    &&& old(self)@.tentative.update_list_entry_at_index_and_item(*key, idx as nat, new_list_entry, new_item)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub fn untrusted_trim_list(
        &mut self,
        key: &K,
        trim_length: usize,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> untrusted_recover::<K, I, L>(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.trim_list(*key, trim_length as nat) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => !self.pm_constants().impervious_to_corruption(),
                Err(e) => {
                    &&& old(self)@.tentative.trim_list(*key, trim_length as nat) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub fn untrusted_trim_list_and_update_item(
        &mut self,
        key: &K,
        trim_length: usize,
        new_item: I,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> untrusted_recover::<K, I, L>(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.trim_list_and_update_item(*key, trim_length as nat, new_item)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => !self.pm_constants().impervious_to_corruption(),
                Err(e) => {
                    &&& old(self)@.tentative.trim_list_and_update_item(*key, trim_length as nat, new_item)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    // pub fn untrusted_get_keys(&self) -> (result: Vec<K>)
    //     requires
    //         self.valid()
    //     ensures
    //         result@.to_set() == self@.get_keys()
    // {
    //     assume(false);
    //     self.volatile_index.get_keys()
    // }

    // pub fn untrusted_contains_key(&self, key: &K) -> (result: bool)
    //     requires
    //         self.valid(),
    //     ensures
    //         match result {
    //             true => self@[*key] is Some,
    //             false => self@[*key] is None
    //         }
    // {
    //     assume(false);
    //     self.volatile_index.get(key).is_some()
    // }

}

}
