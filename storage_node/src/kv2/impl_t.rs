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

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use std::hash::Hash;
use super::impl_v::*;
use super::inv_v::*;
use super::spec_t::*;

verus! {

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
    untrusted_kv_impl: UntrustedKvStoreImpl<TrustedKvPermission, PM, K, I, L>,
}

impl TrustedKvPermission
{
    // This is one of two constructors for `TrustedKvPermission`.
    // It conveys permission to do any update as long as a
    // subsequent crash and recovery can only lead to given
    // abstract state `state`.
    proof fn new_one_possibility<PM, K, I, L>(ps: SetupParameters, kv: AtomicKvStore<K, I, L>) -> (tracked perm: Self)
        where
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
            I: PmCopy + std::fmt::Debug,
            L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        ensures
            forall |s| #[trigger] perm.check_permission(s) <==
                UntrustedKvStoreImpl::<TrustedKvPermission, PM, K, I, L>::recover(s) ==
                Some(RecoveredKvStore::<K, I, L>{ ps, kv }),
    {
        Self {
            is_state_allowable:
                |s| UntrustedKvStoreImpl::<TrustedKvPermission, PM, K, I, L>::recover(s) ==
                    Some(RecoveredKvStore::<K, I, L>{ ps, kv }),
        }
    }

    // This is the second of two constructors for
    // `TrustedKvPermission`.  It conveys permission to do any
    // update as long as a subsequent crash and recovery can only
    // lead to one of two given abstract states `state1` and
    // `state2`.
    proof fn new_two_possibilities<PM, K, I, L>(
        ps: SetupParameters,
        kv1: AtomicKvStore<K, I, L>,
        kv2: AtomicKvStore<K, I, L>
    ) -> (tracked perm: Self)
        where
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
            I: PmCopy + std::fmt::Debug,
            L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        ensures
            forall |s| #[trigger] perm.check_permission(s) <== {
                ||| UntrustedKvStoreImpl::<TrustedKvPermission, PM, K, I, L>::recover(s) ==
                   Some(RecoveredKvStore::<K, I, L>{ ps, kv: kv1 })
                ||| UntrustedKvStoreImpl::<TrustedKvPermission, PM, K, I, L>::recover(s) ==
                   Some(RecoveredKvStore::<K, I, L>{ ps, kv: kv2 })
            }
    {
        Self {
            is_state_allowable: |s| {
                ||| UntrustedKvStoreImpl::<TrustedKvPermission, PM, K, I, L>::recover(s) ==
                   Some(RecoveredKvStore::<K, I, L>{ ps, kv: kv1 })
                ||| UntrustedKvStoreImpl::<TrustedKvPermission, PM, K, I, L>::recover(s) ==
                   Some(RecoveredKvStore::<K, I, L>{ ps, kv: kv2 })
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

    pub closed spec fn recover(s: Seq<u8>) -> Option<RecoveredKvStore::<K, I, L>>
    {
        UntrustedKvStoreImpl::<TrustedKvPermission, PM, K, I, L>::recover(s)
    }

    pub closed spec fn spec_space_needed_for_setup(ps: SetupParameters) -> nat
    {
        UntrustedKvStoreImpl::<TrustedKvPermission, PM, K, I, L>::spec_space_needed_for_setup(ps)
    }

    pub closed spec fn spec_space_needed_for_transaction_operation() -> nat
    {
        UntrustedKvStoreImpl::<TrustedKvPermission, PM, K, I, L>::spec_space_needed_for_transaction_operation()
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
        UntrustedKvStoreImpl::<TrustedKvPermission, PM, K, I, L>::space_needed_for_setup(ps)
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
                    &&& ps.valid()
                    &&& Self::recover(pm@.durable_state) == Some(RecoveredKvStore::<K, I, L>::init(*ps))
                }
                Err(KvError::InvalidParameter) => !ps.valid(),
                Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
                Err(KvError::OutOfSpace) => pm@.len() < Self::spec_space_needed_for_setup(*ps),
                Err(_) => false,
            }
    {
        UntrustedKvStoreImpl::<TrustedKvPermission, PM, K, I, L>::setup(pm, ps)
    }

    pub exec fn start(pm: PM, kvstore_id: u128) -> (result: Result<Self, KvError>)
        requires 
            pm.inv(),
            Self::recover(pm@.read_state) is Some,
            vstd::std_specs::hash::obeys_key_model::<K>(),
        ensures
        ({
            let state = Self::recover(pm@.read_state).unwrap();
            match result {
                Ok(kv) => {
                    &&& kv.valid()
                    &&& kv@.valid()
                    &&& kv@.ps == state.ps
                    &&& kv@.ps.valid()
                    &&& kv@.used_key_slots == state.kv.m.dom().len()
                    &&& kv@.used_list_element_slots == state.kv.num_list_elements()
                    &&& kv@.used_transaction_operation_slots == 0
                    &&& kv@.pm_constants == pm.constants()
                    &&& kv@.durable == state.kv
                    &&& kv@.tentative == state.kv
                },
                Err(KvError::CRCMismatch) => !pm.constants().impervious_to_corruption(),
                Err(KvError::WrongKvStoreId{ requested_id, actual_id }) => {
                   &&& requested_id == kvstore_id
                   &&& actual_id == state.ps.kvstore_id
                },
                Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
                Err(_) => false,
            }
        }),
    {
        let mut powerpm = PoWERPersistentMemoryRegion::new(pm);
        powerpm.flush(); // ensure there are no outstanding writes
        let ghost state = UntrustedKvStoreImpl::<TrustedKvPermission, PM, K, I, L>::recover(powerpm@.durable_state).unwrap();
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(state.ps, state.kv);
        let untrusted_kv_impl = UntrustedKvStoreImpl::<TrustedKvPermission, PM, K, I, L>::start(
            powerpm, kvstore_id, Ghost(state), Tracked(&perm))?;

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
                    &&& self@ == KvStoreView{
                        tentative: self@.tentative,
                        used_key_slots: old(self)@.used_key_slots + 1,
                        used_transaction_operation_slots: old(self)@.used_transaction_operation_slots + 1,
                        ..old(self)@
                    }
                    &&& old(self)@.tentative.create(*key, *item) matches Ok(new_self)
                    &&& self@.tentative == new_self
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    &&& {
                        ||| old(self)@.used_key_slots >= old(self)@.ps.max_keys
                        ||| old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                    }
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.create(*key, *item) matches Err(e_spec)
                    &&& e == e_spec
                },
            }
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.ps, self@.durable);
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
                    &&& self@ == KvStoreView{
                        tentative: self@.tentative,
                        used_key_slots: old(self)@.used_key_slots + 1,
                        used_transaction_operation_slots: old(self)@.used_transaction_operation_slots + 1,
                        ..old(self)@
                    }
                    &&& old(self)@.tentative.update_item(*key, *item) matches Ok(new_self)
                    &&& self@.tentative == new_self
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    &&& {
                        ||| old(self)@.used_key_slots >= old(self)@.ps.max_keys
                        ||| old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                    }
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.update_item(*key, *item) matches Err(e_spec)
                    &&& e_spec == e
                },
            }
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.ps, self@.durable);
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
                    &&& self@ == KvStoreView{
                        tentative: self@.tentative,
                        used_transaction_operation_slots: old(self)@.used_transaction_operation_slots + 1,
                        ..old(self)@
                    }
                    &&& old(self)@.tentative.delete(*key) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    &&& old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.delete(*key) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.ps, self@.durable);
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
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.ps, self@.durable);
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
        let tracked perm = TrustedKvPermission::new_two_possibilities::<PM, K, I, L>(self@.ps, self@.durable,
                                                                                     self@.tentative);
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
        &self,
        key: &K,
    ) -> (result: Result<(I, Vec<L>), KvError>)
        requires 
            self.valid(),
        ensures
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

    pub exec fn read_list(&self, key: &K) -> (result: Result<Vec<L>, KvError>)
        requires
            self.valid(),
        ensures
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

    pub exec fn get_list_length(&self, key: &K) -> (result: Result<usize, KvError>)
        requires
            self.valid(),
        ensures
            match result {
                Ok(num_elements) => {
                    &&& self@.tentative.get_list_length(*key) matches Ok(n)
                    &&& num_elements == n
                },
                Err(KvError::CRCMismatch) => {
                    &&& !self@.pm_constants.impervious_to_corruption()
                },
                Err(e) => {
                    &&& self@.tentative.get_list_length(*key) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        self.untrusted_kv_impl.get_list_length(key)
    }

    pub exec fn tentatively_append_to_list(
        &mut self,
        key: &K,
        new_list_element: L,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{
                        tentative: self@.tentative,
                        used_key_slots: old(self)@.used_key_slots + 1,
                        used_list_element_slots: old(self)@.used_list_element_slots + 1,
                        used_transaction_operation_slots: old(self)@.used_transaction_operation_slots + 1,
                        ..old(self)@
                    }
                    &&& old(self)@.tentative.append_to_list(*key, new_list_element) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    &&& {
                        ||| old(self)@.used_key_slots >= old(self)@.ps.max_keys
                        ||| old(self)@.used_list_element_slots >= old(self)@.ps.max_list_elements
                        ||| old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                    }
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.append_to_list(*key, new_list_element) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.ps, self@.durable);
        self.untrusted_kv_impl.tentatively_append_to_list(key, new_list_element, Tracked(&perm))
    }

    pub exec fn tentatively_append_to_list_and_update_item(
        &mut self,
        key: &K,
        new_list_element: L,
        new_item: &I,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{
                        tentative: self@.tentative,
                        used_key_slots: old(self)@.used_key_slots + 1,
                        used_list_element_slots: old(self)@.used_list_element_slots + 1,
                        used_transaction_operation_slots: old(self)@.used_transaction_operation_slots + 1,
                        ..old(self)@
                    }
                    &&& old(self)@.tentative.append_to_list_and_update_item(*key, new_list_element, *new_item)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    &&& {
                        ||| old(self)@.used_key_slots >= old(self)@.ps.max_keys
                        ||| old(self)@.used_list_element_slots >= old(self)@.ps.max_list_elements
                        ||| old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                    }
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.append_to_list_and_update_item(*key, new_list_element, *new_item)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.ps, self@.durable);
        self.untrusted_kv_impl.tentatively_append_to_list_and_update_item(key, new_list_element, new_item, Tracked(&perm))
    }

    pub exec fn tentatively_update_list_element_at_index(
        &mut self,
        key: &K,
        idx: usize,
        new_list_element: L,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{
                        tentative: self@.tentative,
                        used_key_slots: old(self)@.used_key_slots + 1,
                        used_list_element_slots: old(self)@.used_list_element_slots + 1,
                        used_transaction_operation_slots: old(self)@.used_transaction_operation_slots + 1,
                        ..old(self)@
                    }
                    &&& old(self)@.tentative.update_list_element_at_index(*key, idx as nat, new_list_element)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    &&& {
                        ||| old(self)@.used_key_slots >= old(self)@.ps.max_keys
                        ||| old(self)@.used_list_element_slots >= old(self)@.ps.max_list_elements
                        ||| old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                    }
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.update_list_element_at_index(*key, idx as nat, new_list_element)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.ps, self@.durable);
        self.untrusted_kv_impl.tentatively_update_list_element_at_index(key, idx, new_list_element, Tracked(&perm))
    }

    pub exec fn tentatively_update_list_element_at_index_and_item(
        &mut self,
        key: &K,
        idx: usize,
        new_list_element: L,
        new_item: &I,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{
                        tentative: self@.tentative,
                        used_key_slots: old(self)@.used_key_slots + 1,
                        used_list_element_slots: old(self)@.used_list_element_slots + 1,
                        used_transaction_operation_slots: old(self)@.used_transaction_operation_slots + 1,
                        ..old(self)@
                    }
                    &&& old(self)@.tentative.update_list_element_at_index_and_item(*key, idx as nat, new_list_element,
                                                                             *new_item) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    &&& {
                        ||| old(self)@.used_key_slots >= old(self)@.ps.max_keys
                        ||| old(self)@.used_list_element_slots >= old(self)@.ps.max_list_elements
                        ||| old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                    }
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.update_list_element_at_index_and_item(*key, idx as nat, new_list_element,
                                                                              *new_item) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.ps, self@.durable);
        self.untrusted_kv_impl.tentatively_update_list_element_at_index_and_item(key, idx, new_list_element, new_item,
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
                    &&& self@ == KvStoreView{
                        tentative: self@.tentative,
                        used_key_slots: old(self)@.used_key_slots + 1,
                        used_transaction_operation_slots: old(self)@.used_transaction_operation_slots + 1,
                        ..old(self)@
                    }
                    &&& old(self)@.tentative.trim_list(*key, trim_length as nat) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    &&& {
                        ||| old(self)@.used_key_slots >= old(self)@.ps.max_keys
                        ||| old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                    }
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.trim_list(*key, trim_length as nat) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.ps, self@.durable);
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
                    &&& self@ == KvStoreView{
                        tentative: self@.tentative,
                        used_key_slots: old(self)@.used_key_slots + 1,
                        used_transaction_operation_slots: old(self)@.used_transaction_operation_slots + 1,
                        ..old(self)@
                    }
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
                    &&& {
                        ||| old(self)@.used_key_slots >= old(self)@.ps.max_keys
                        ||| old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                    }
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.trim_list_and_update_item(*key, trim_length as nat, *new_item)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        let tracked perm = TrustedKvPermission::new_one_possibility::<PM, K, I, L>(self@.ps, self@.durable);
        self.untrusted_kv_impl.tentatively_trim_list_and_update_item(key, trim_length, new_item, Tracked(&perm))
    }

}

}
