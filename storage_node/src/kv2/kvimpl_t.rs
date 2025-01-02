//! This file contains the public interface of the paged key-value store.
//! The methods offered by this file should match the mocks.
//! The key-value store itself should be as generic as possible, not
//! restricted to particular data structures.
//! We define legal crash states at this level and pass them
//! to the untrusted implementation, which passes them along
//! to untrusted components.
//!
//! This file is unverified and should be tested/audited for correctness.

#![allow(unused_imports)]
// #![verus::trusted]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use std::hash::Hash;
use super::kvimpl_v::*;
use super::kvspec_t::*;

verus! {

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
pub struct KvStore<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    untrusted_kv_impl: UntrustedKvStoreImpl<PM, K, I, L>,
}

pub struct TrustedKvPermission
{
    ghost is_state_allowable: spec_fn(Seq<u8>) -> bool,
}

impl CheckPermission<Seq<u8>> for TrustedKvPermission
{
    closed spec fn check_permission(&self, state: Seq<u8>) -> bool
    {
        (self.is_state_allowable)(state)
    }
}

impl TrustedKvPermission
{
    // This is one of two constructors for `TrustedKvPermission`.
    // It conveys permission to do any update as long as a
    // subsequent crash and recovery can only lead to given
    // abstract state `state`.
    proof fn new_one_possibility<PM, K, I, L>(state: AbstractKvStoreState<K, I, L>) -> (tracked perm: Self)
        where
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
            I: PmCopy + std::fmt::Debug,
            L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        ensures
            forall |s| #[trigger] perm.check_permission(s) <==>
                UntrustedKvStoreImpl::<PM, K, I, L>::untrusted_recover(s) == Some(state),
    {
        Self {
            is_state_allowable: |s| UntrustedKvStoreImpl::<PM, K, I, L>::untrusted_recover(s) == Some(state),
        }
    }

    // This is the second of two constructors for
    // `TrustedKvPermission`.  It conveys permission to do any
    // update as long as a subsequent crash and recovery can only
    // lead to one of two given abstract states `state1` and
    // `state2`.
    proof fn new_two_possibilities<PM, K, I, L>(
        state1: AbstractKvStoreState<K, I, L>,
        state2: AbstractKvStoreState<K, I, L>
    ) -> (tracked perm: Self)
        where
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
            I: PmCopy + std::fmt::Debug,
            L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        ensures
            forall |s| #[trigger] perm.check_permission(s) <==> {
                ||| UntrustedKvStoreImpl::<PM, K, I, L>::untrusted_recover(s) == Some(state1)
                ||| UntrustedKvStoreImpl::<PM, K, I, L>::untrusted_recover(s) == Some(state2)
            }
    {
        Self {
            is_state_allowable: |s| {
                ||| UntrustedKvStoreImpl::<PM, K, I, L>::untrusted_recover(s) == Some(state1)
                ||| UntrustedKvStoreImpl::<PM, K, I, L>::untrusted_recover(s) == Some(state2)
            },
        }
    }
}

impl<PM, K, I, L> View for KvStore<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type V = AbstractKvState<K, I, L>;

    closed spec fn view(&self) -> AbstractKvState<K, I, L>
    {
        self.untrusted_kv_impl@
    }
}

impl<PM, K, I, L> KvStore<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub closed spec fn valid(self) -> bool
    {
        &&& self.untrusted_kv_impl.valid()
    }

    pub closed spec fn pm_constants(self) -> PersistentMemoryConstants
    {
        self.untrusted_kv_impl.pm_constants()
    }

    pub exec fn setup(pm: &mut PM, ps: &SetupParameters) -> (result: Result<(), KvError<K>>)
        requires 
            old(pm).inv(),
        ensures
            pm.inv(),
            match result {
                Ok(()) => {
                    &&& pm@.flush_predicted()
                    &&& UntrustedKvStoreImpl::<PM, K, I, L>::untrusted_recover(pm@.durable_state)
                        == Some(AbstractKvStoreState::<K, I, L>::init(ps.kvstore_id, ps.logical_range_gaps_policy))
                }
                Err(_) => true
            }
    {
        UntrustedKvStoreImpl::<PM, K, I, L>::untrusted_setup(pm, ps)?;
        Ok(())
    }

    pub exec fn start(mut pm: PM, kvstore_id: u128) -> (result: Result<Self, KvError<K>>)
        requires 
            pm.inv(),
            UntrustedKvStoreImpl::<PM, K, I, L>::untrusted_recover(pm@.read_state) is Some,
            vstd::std_specs::hash::obeys_key_model::<K>(),
        ensures
        ({
            let state = UntrustedKvStoreImpl::<PM, K, I, L>::untrusted_recover(pm@.read_state).unwrap();
            match result {
                Ok(kv) => {
                    &&& kv.valid()
                    &&& kv.pm_constants() == pm.constants()
                    &&& kv@.valid()
                    &&& kv@.id() == state.id == kvstore_id
                    &&& kv@.durable == state
                    &&& kv@.tentative == state
                },
                Err(KvError::CRCMismatch) => !pm.constants().impervious_to_corruption(),
                Err(KvError::WrongKvStoreId{ requested_id, actual_id }) => {
                   &&& requested_id == kvstore_id
                   &&& actual_id == state.id
                },
                Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
                Err(_) => false,
            }
        }),
    {
        let mut wrpm = WriteRestrictedPersistentMemoryRegion::new(pm);
        wrpm.flush(); // ensure there are no outstanding writes
        let ghost state = UntrustedKvStoreImpl::<PM, K, I, L>::untrusted_recover(wrpm@.durable_state).unwrap();
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(state);
        let untrusted_kv_impl = UntrustedKvStoreImpl::<PM, K, I, L>::untrusted_start(
            wrpm, kvstore_id, Ghost(state), Tracked(&perm))?;

        Ok(Self { untrusted_kv_impl })
    }

    pub exec fn read_item(
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
        self.untrusted_kv_impl.untrusted_read_item(key)
    }

    pub exec fn create(
        &mut self,
        key: &K,
        item: &I,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
        ensures 
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.create(*key, *item) matches Ok(new_self)
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
                }
                Err(e) => {
                    &&& old(self)@.tentative.create(*key, *item) matches Err(e_spec)
                    &&& e == e_spec
                    &&& self@ == old(self)@
                },
            }
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.untrusted_create(key, item, Tracked(&perm))
    }

    pub exec fn update_item(
        &mut self,
        key: &K,
        item: &I,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
        ensures 
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.update_item(*key, *item) matches Ok(new_self)
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
                    &&& old(self)@.tentative.update_item(*key, *item) matches Err(e_spec)
                    &&& e_spec == e
                    &&& self@ == old(self)@
                },
            }
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.untrusted_update_item(key, item, Tracked(&perm))
    }

    pub exec fn delete(
        &mut self,
        key: &K,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
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
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.untrusted_delete(key, Tracked(&perm))
    }

    pub exec fn commit(&mut self) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
        ensures 
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => self@ == old(self)@.commit(),
                Err(_) => false,
            },
    {
        let tracked perm = TrustedKvPermission::new_two_possibilities::<PM, K, I, L>(self@.durable, self@.tentative);
        self.untrusted_kv_impl.untrusted_commit(Tracked(&perm))
    }

    pub exec fn get_keys(&self) -> (result: Result<Vec<K>, KvError<K>>)
        requires 
            self.valid(),
        ensures 
            match result {
                Ok(keys) => {
                    &&& keys@.to_set() == self@.tentative.get_keys()
                    &&& keys@.no_duplicates()
                },
                Err(KvError::CRCMismatch) => !self.pm_constants().impervious_to_corruption(),
                Err(_) => false,
            },
    {
        self.untrusted_kv_impl.untrusted_get_keys()
    }

    pub exec fn read_item_and_list(
        &self,
        key: &K,
    ) -> (result: Result<(&I, &Vec<L>), KvError<K>>)
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
        self.untrusted_kv_impl.untrusted_read_item_and_list(key)
    }

    pub exec fn read_list(&self, key: &K) -> (result: Result<&Vec<L>, KvError<K>>)
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
        self.untrusted_kv_impl.untrusted_read_list(key)
    }

    pub exec fn read_list_entry_at_index(&self, key: &K, idx: u64) -> (result: Result<&L, KvError<K>>)
        requires
            self.valid(),
        ensures
            match result {
                Ok(list_entry) => {
                    &&& self@.tentative.read_list_entry_at_index(*key, idx as nat) matches Ok((e))
                    &&& *list_entry == e
                },
                Err(KvError::CRCMismatch) => !self.pm_constants().impervious_to_corruption(),
                Err(e) => {
                    &&& self@.tentative.read_list_entry_at_index(*key, idx as nat) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        self.untrusted_kv_impl.untrusted_read_list_entry_at_index(key, idx)
    }

    pub exec fn append_to_list(
        &mut self,
        key: &K,
        new_list_entry: L,
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
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
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.untrusted_append_to_list(key, new_list_entry, Tracked(&perm))
    }

    pub exec fn append_to_list_and_update_item(
        &mut self,
        key: &K,
        new_list_entry: L,
        new_item: I,
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
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
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.untrusted_append_to_list_and_update_item(key, new_list_entry, new_item, Tracked(&perm))
    }

    pub exec fn update_list_entry_at_index(
        &mut self,
        key: &K,
        idx: usize,
        new_list_entry: L,
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
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
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.untrusted_update_list_entry_at_index(key, idx, new_list_entry, Tracked(&perm))
    }

    pub exec fn update_list_entry_at_index_and_item(
        &mut self,
        key: &K,
        idx: usize,
        new_list_entry: L,
        new_item: I,
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
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
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.untrusted_update_list_entry_at_index_and_item(key, idx, new_list_entry, new_item,
                                                                             Tracked(&perm))
    }

    pub exec fn trim_list(
        &mut self,
        key: &K,
        trim_length: usize,
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
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
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.untrusted_trim_list(key, trim_length, Tracked(&perm))
    }

    pub exec fn trim_list_and_update_item(
        &mut self,
        key: &K,
        trim_length: usize,
        new_item: I,
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
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
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.untrusted_trim_list_and_update_item(key, trim_length, new_item, Tracked(&perm))
    }

}

}
