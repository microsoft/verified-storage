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
use super::*;
use super::spec_t::*;

verus! {

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
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
    proof fn new_one_possibility<PM, K, I, L>(state: AtomicKvStore<K, I, L>) -> (tracked perm: Self)
        where
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
            I: PmCopy + std::fmt::Debug,
            L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        ensures
            forall |s| #[trigger] perm.check_permission(s) <==>
                UntrustedKvStoreImpl::<PM, K, I, L>::recover(s) == Some(state),
    {
        Self {
            is_state_allowable: |s| UntrustedKvStoreImpl::<PM, K, I, L>::recover(s) == Some(state),
        }
    }

    // This is the second of two constructors for
    // `TrustedKvPermission`.  It conveys permission to do any
    // update as long as a subsequent crash and recovery can only
    // lead to one of two given abstract states `state1` and
    // `state2`.
    proof fn new_two_possibilities<PM, K, I, L>(
        state1: AtomicKvStore<K, I, L>,
        state2: AtomicKvStore<K, I, L>
    ) -> (tracked perm: Self)
        where
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
            I: PmCopy + std::fmt::Debug,
            L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        ensures
            forall |s| #[trigger] perm.check_permission(s) <==> {
                ||| UntrustedKvStoreImpl::<PM, K, I, L>::recover(s) == Some(state1)
                ||| UntrustedKvStoreImpl::<PM, K, I, L>::recover(s) == Some(state2)
            }
    {
        Self {
            is_state_allowable: |s| {
                ||| UntrustedKvStoreImpl::<PM, K, I, L>::recover(s) == Some(state1)
                ||| UntrustedKvStoreImpl::<PM, K, I, L>::recover(s) == Some(state2)
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
    type V = KvStoreView<K, I, L>;

    closed spec fn view(&self) -> KvStoreView<K, I, L>
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

    pub closed spec fn spec_space_needed_for_setup(ps: SetupParameters) -> nat
    {
        UntrustedKvStoreImpl::<PM, K, I, L>::spec_space_needed_for_setup(ps)
    }

    pub exec fn space_needed_for_setup(ps: &SetupParameters) -> (result: Result<u64, KvError>)
        ensures
            match result {
                Ok(v) => v == Self::spec_space_needed_for_setup(*ps),
                Err(KvError::InvalidParameter) => !ps.valid(),
                Err(KvError::OutOfSpace) => Self::spec_space_needed_for_setup(*ps) > u64::MAX,
                Err(_) => false,
            },
    {
        UntrustedKvStoreImpl::<PM, K, I, L>::space_needed_for_setup(ps)
    }

    pub exec fn setup(pm: &mut PM, ps: &SetupParameters) -> (result: Result<(), KvError>)
        requires 
            old(pm).inv(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            match result {
                Ok(()) => {
                    &&& pm@.flush_predicted()
                    &&& UntrustedKvStoreImpl::<PM, K, I, L>::recover(pm@.durable_state)
                        == Some(AtomicKvStore::<K, I, L>::init(ps.kvstore_id, ps.logical_range_gaps_policy))
                }
                Err(KvError::InvalidParameter) => !ps.valid(),
                Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
                Err(KvError::OutOfSpace) => pm@.len() < Self::spec_space_needed_for_setup(*ps),
                Err(_) => false,
            }
    {
        UntrustedKvStoreImpl::<PM, K, I, L>::setup(pm, ps)
    }

    pub exec fn start(mut pm: PM, kvstore_id: u128) -> (result: Result<Self, KvError>)
        requires 
            pm.inv(),
            UntrustedKvStoreImpl::<PM, K, I, L>::recover(pm@.read_state) is Some,
            vstd::std_specs::hash::obeys_key_model::<K>(),
        ensures
        ({
            let state = UntrustedKvStoreImpl::<PM, K, I, L>::recover(pm@.read_state).unwrap();
            match result {
                Ok(kv) => {
                    &&& kv.valid()
                    &&& kv@.valid()
                    &&& kv@.id == state.id == kvstore_id
                    &&& kv@.logical_range_gaps_policy == state.logical_range_gaps_policy
                    &&& kv@.pm_constants == pm.constants()
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
        let ghost state = UntrustedKvStoreImpl::<PM, K, I, L>::recover(wrpm@.durable_state).unwrap();
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(state);
        let untrusted_kv_impl = UntrustedKvStoreImpl::<PM, K, I, L>::start(
            wrpm, kvstore_id, Ghost(state), Tracked(&perm))?;

        Ok(Self { untrusted_kv_impl })
    }

    pub exec fn read_item(
        &self,
        key: &K,
    ) -> (result: Result<I, KvError>)
        requires 
            self.valid(),
        ensures 
            match result {
                Ok(item) => {
                    &&& self@.tentative.read_item(*key) matches Ok(i)
                    &&& item == i
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(e) => {
                    &&& self@.tentative.read_item(*key) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        self.untrusted_kv_impl.read_item(key)
    }

    pub exec fn tentatively_create(
        &mut self,
        key: &K,
        item: &I,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures 
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
                    &&& old(self)@.tentative.create(*key, *item) matches Ok(new_self)
                    &&& self@.tentative == new_self
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    // TODO - Whenever we return OutOfSpace, we should establish why
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.create(*key, *item) matches Err(e_spec)
                    &&& e == e_spec
                },
            }
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.tentatively_create(key, item, Tracked(&perm))
    }

    pub exec fn tentatively_update_item(
        &mut self,
        key: &K,
        item: &I,
    ) -> (result: Result<(), KvError>)
        requires 
            old(self).valid(),
        ensures 
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
                    &&& old(self)@.tentative.update_item(*key, *item) matches Ok(new_self)
                    &&& self@.tentative == new_self
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.update_item(*key, *item) matches Err(e_spec)
                    &&& e_spec == e
                },
            }
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.tentatively_update_item(key, item, Tracked(&perm))
    }

    pub exec fn tentatively_delete(
        &mut self,
        key: &K,
    ) -> (result: Result<(), KvError>)
        requires 
            old(self).valid(),
        ensures 
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
                    &&& old(self)@.tentative.delete(*key) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.delete(*key) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.tentatively_delete(key, Tracked(&perm))
    }

    pub exec fn abort(&mut self) -> (result: Result<(), KvError>)
        requires 
            old(self).valid(),
        ensures 
            self.valid(),
            match result {
                Ok(()) => self@ == old(self)@.abort(),
                Err(_) => false,
            },
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.abort(Tracked(&perm))
    }

    pub exec fn commit(&mut self) -> (result: Result<(), KvError>)
        requires 
            old(self).valid(),
        ensures 
            self.valid(),
            match result {
                Ok(()) => self@ == old(self)@.commit(),
                Err(_) => false,
            },
    {
        let tracked perm = TrustedKvPermission::new_two_possibilities::<PM, K, I, L>(self@.durable, self@.tentative);
        self.untrusted_kv_impl.commit(Tracked(&perm))
    }

    pub exec fn get_keys(&self) -> (result: Result<Vec<K>, KvError>)
        requires 
            self.valid(),
        ensures 
            match result {
                Ok(keys) => {
                    &&& keys@.to_set() == self@.tentative.get_keys()
                    &&& keys@.no_duplicates()
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(_) => false,
            },
    {
        self.untrusted_kv_impl.get_keys()
    }

    pub exec fn read_item_and_list(
        &mut self,
        key: &K,
    ) -> (result: Result<(I, Vec<L>), KvError>)
        requires 
            old(self).valid(),
        ensures
            self.valid(),
            self@ == old(self)@,
            match result {
                Ok((item, lst)) => {
                    &&& self@.tentative.read_item_and_list(*key) matches Ok((i, l))
                    &&& item == i
                    &&& lst@ == l
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(e) => {
                    &&& self@.tentative.read_item_and_list(*key) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        self.untrusted_kv_impl.read_item_and_list(key)
    }

    pub exec fn read_list(&mut self, key: &K) -> (result: Result<Vec<L>, KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            self@ == old(self)@,
            match result {
                Ok(lst) => {
                    &&& self@.tentative.read_item_and_list(*key) matches Ok((i, l))
                    &&& lst@ == l
                },
                Err(KvError::CRCMismatch) => {
                    &&& !self@.pm_constants.impervious_to_corruption()
                },
                Err(e) => {
                    &&& self@.tentative.read_item_and_list(*key) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        self.untrusted_kv_impl.read_list(key)
    }

    pub exec fn tentatively_append_to_list(
        &mut self,
        key: &K,
        new_list_entry: L,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
                    &&& old(self)@.tentative.append_to_list(*key, new_list_entry) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.append_to_list(*key, new_list_entry) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.tentatively_append_to_list(key, new_list_entry, Tracked(&perm))
    }

    pub exec fn tentatively_append_to_list_and_update_item(
        &mut self,
        key: &K,
        new_list_entry: L,
        new_item: &I,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
                    &&& old(self)@.tentative.append_to_list_and_update_item(*key, new_list_entry, *new_item)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.append_to_list_and_update_item(*key, new_list_entry, *new_item)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.tentatively_append_to_list_and_update_item(key, new_list_entry, new_item, Tracked(&perm))
    }

    pub exec fn tentatively_update_list_entry_at_index(
        &mut self,
        key: &K,
        idx: usize,
        new_list_entry: L,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
                    &&& old(self)@.tentative.update_list_entry_at_index(*key, idx as nat, new_list_entry)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.update_list_entry_at_index(*key, idx as nat, new_list_entry)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.tentatively_update_list_entry_at_index(key, idx, new_list_entry, Tracked(&perm))
    }

    pub exec fn tentatively_update_list_entry_at_index_and_item(
        &mut self,
        key: &K,
        idx: usize,
        new_list_entry: L,
        new_item: &I,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
                    &&& old(self)@.tentative.update_list_entry_at_index_and_item(*key, idx as nat, new_list_entry,
                                                                             *new_item) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.update_list_entry_at_index_and_item(*key, idx as nat, new_list_entry,
                                                                              *new_item) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.tentatively_update_list_entry_at_index_and_item(key, idx, new_list_entry, new_item,
                                                                               Tracked(&perm))
    }

    pub exec fn tentatively_trim_list(
        &mut self,
        key: &K,
        trim_length: usize,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
                    &&& old(self)@.tentative.trim_list(*key, trim_length as nat) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.trim_list(*key, trim_length as nat) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.tentatively_trim_list(key, trim_length, Tracked(&perm))
    }

    pub exec fn tentatively_trim_list_and_update_item(
        &mut self,
        key: &K,
        trim_length: usize,
        new_item: &I,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
                    &&& old(self)@.tentative.trim_list_and_update_item(*key, trim_length as nat, *new_item)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.trim_list_and_update_item(*key, trim_length as nat, *new_item)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.durable);
        self.untrusted_kv_impl.tentatively_trim_list_and_update_item(key, trim_length, new_item, Tracked(&perm))
    }

}

}
