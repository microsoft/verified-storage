//! This file implements `KvStoreImpl`, a single-threaded key-value
//! store also known as CapybaraKV. It uses PoWER to enforce crash
//! consistency, by limiting the set of allowable crash states in the
//! middle of operations.
//!
//! The implementation of `KvStoreImpl` relies on an untrusted KV
//! store `UntrustedKvStoreImpl` to do the actual work of maintaining
//! KV state in memory and on disk. Because that code is verified, we
//! know that its operations are functionally correct. Because this
//! file wraps calls to that store in PoWER wrappers, we know that it
//! must be crash-consistent as well.
//!
//! This file is unverified and should be tested/audited for
//! correctness, most notably to verify that the PoWER wrappers indeed
//! enforce crash consistency.
//!
//! The API for `KvStoreImpl` is transactional. That is, all mutating
//! operations are tentative in that they are applied only to the
//! current tentative state and are undone in the event of a crash.
//! The only way to make the tentative state durable is by calling
//! `commit`. One can undo all the tentative operations since the last
//! commit by calling `abort`. Read-only operations read from the
//! current tentative state.
//!
//! A `KvStoreImpl<K, I, L>` maps each key of type `K` to a value
//! consisting of an item of type `I` and an append-only list of
//! elements of type `L`. Thus, while key, item, and element types are
//! fixed-size, lists can grow arbitrarily long, permitting
//! arbitrary-sized values. Each of the types `K`, `I`, and `L` must
//! implement `PmCopy`, permitting their storage on persistent memory;
//! one can do this with `#[repr(C)]` and `#[derive(PmCopy, Copy)]`.
//!
//! Supported read-only operations are as follows:
//!
//! * `read_item`
//! * `read_item_and_list`
//! * `read_list_element_at_index`
//! * `get_list_length`
//! * `get_keys`
//!
//! Supported mutating operations are as follows. To make clear that
//! these operations are all tentative, the functions invoking them
//! all start with `tentatively_`, e.g., `tentatively_create`:
//!
//! * `create`
//! * `update_item`
//! * `delete`
//! * `append_to_list`
//! * `append_to_list_and_update_item`
//! * `update_list_element_at_index`
//! * `update_list_element_at_index_and_item`
//! * `trim_list`
//! * `trim_list_and_update_item`
//!
//! To create a new KV store on persistent memory, overwriting
//! whatever is already there, one uses `setup`. To create a
//! `KvStoreImpl` using the state on persistent memory (either
//! immediately after setup or after running for a while then
//! crashing), one uses `start`.
//!

#![allow(unused_imports)]
#![cfg_attr(verus_keep_ghost, verus::trusted)]
use vstd::prelude::*;
use vstd::tokens::frac::*;

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use std::hash::Hash;
use super::impl_v::*;
use super::inv_v::*;
use super::spec_t::*;

verus! {

// This structure represents a permission to transition the state of
// the persistent storage from one state (represented as a sequence of
// `u8`) to another. Its fields aren't `pub`, so no code outside this
// trusted file can create such a permission.

pub struct TrustedKvPermission
{
    ghost is_transition_allowable: spec_fn(Seq<u8>, Seq<u8>) -> bool,
    ghost powerpm_id: int,
}

impl CheckPermission<Seq<u8>> for TrustedKvPermission
{
    type Completion = ();

    closed spec fn permits(&self, s1: Seq<u8>, s2: Seq<u8>) -> bool
    {
        (self.is_transition_allowable)(s1, s2)
    }

    closed spec fn id(&self) -> int
    {
        self.powerpm_id
    }

    closed spec fn completed(&self, c: Self::Completion) -> bool
    {
        true
    }

    // The trait `CheckPermission` is general enough to support two
    // scenarios: (1) Audited, trusted code creates the permission,
    // and we rely on the auditor to ensure that this permission
    // implies that the transition is permissible. That is, we rely on
    // someone reading this file carefully to decide whether the
    // permission is reasonable to grant. (2) The permission does
    // something useful when code uses it to effect a write by calling
    // its `apply` function. In this file, we use scenario (1), so we
    // can just have `apply` be an assumed-correct function.

    proof fn apply(tracked self, tracked credit: vstd::invariant::OpenInvariantCredit, tracked r: &mut GhostVarAuth<Seq<u8>>, new_state: Seq<u8>) -> (tracked result: Self::Completion)
    {
        admit();
        ()
    }
}

// This structure is a factory that can generate an arbitrary number
// of copies of a certain transition permission. We use it to give the
// untrusted code blanket permission to perform any storage
// transitions that are functionally idempotent.

pub struct TrustedKvPermissionFactory
{
    ghost is_transition_allowable: spec_fn(Seq<u8>, Seq<u8>) -> bool,
    ghost powerpm_id: int
}

impl PermissionFactory<Seq<u8>> for TrustedKvPermissionFactory
{
    type Perm = TrustedKvPermission;

    closed spec fn permits(&self, s1: Seq<u8>, s2: Seq<u8>) -> bool
    {
        (self.is_transition_allowable)(s1, s2)
    }

    proof fn grant_permission(tracked &self) -> (tracked perm: TrustedKvPermission)
        ensures
            forall|s1, s2| self.permits(s1, s2) ==> #[trigger] perm.permits(s1, s2)
    {
        TrustedKvPermission{
            is_transition_allowable: |s1: Seq<u8>, s2: Seq<u8>| (self.is_transition_allowable)(s1, s2),
            powerpm_id: self.powerpm_id,
        }
    }

    proof fn clone(tracked &self) -> (tracked other: Self)
        ensures
            forall|s1, s2| self.permits(s1, s2) ==> #[trigger] other.permits(s1, s2)
    {
        Self{
            is_transition_allowable: self.is_transition_allowable,
            powerpm_id: self.powerpm_id,
        }
    }

    closed spec fn id(&self) -> int
    {
        self.powerpm_id
    }
}

// This is the trusted structure that exposes the KV store API.
// Internally, it uses `UntrustedKvStoreImpl` for its functionality
// and uses PoWER-based permissions to restrict how that untrusted KV
// store can crash.

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
    untrusted_kv_impl: UntrustedKvStoreImpl<TrustedKvPermissionFactory, PM, K, I, L>,
    powerpm_id: Ghost<int>,
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
    PM: PersistentMemoryRegion, K: Hash + PmCopy + Sized +
    std::fmt::Debug, I: PmCopy + Sized + std::fmt::Debug, L: PmCopy +
    LogicalRange + std::fmt::Debug + Copy,
{
    pub closed spec fn valid(self) -> bool {
        &&& self.untrusted_kv_impl.valid() &&& self.powerpm_id@ ==
        self.untrusted_kv_impl@.powerpm_id
    }

    pub closed spec fn recover(s: Seq<u8>) -> Option<RecoveredKvStore::<K, I, L>>
    {
        UntrustedKvStoreImpl::<TrustedKvPermissionFactory, PM, K, I, L>::recover(s)
    }

    pub closed spec fn spec_space_needed_for_setup(ps: SetupParameters) -> nat
    {
        UntrustedKvStoreImpl::<TrustedKvPermissionFactory, PM, K, I, L>::spec_space_needed_for_setup(ps)
    }

    pub closed spec fn spec_space_needed_for_transaction_operation() -> nat
    {
        spec_space_needed_for_transaction_operation()
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
        UntrustedKvStoreImpl::<TrustedKvPermissionFactory, PM, K, I, L>::space_needed_for_setup(ps)
    }

    // This function sets up a persistent-memory (PM) region to serve
    // as storage for a KV store. It writes initial contents there
    // representing an empty KV store.

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
        UntrustedKvStoreImpl::<TrustedKvPermissionFactory, PM, K, I, L>::setup(pm, ps)
    }

    // This function restores the in-memory state of a KV store from
    // PM after a crash, or immediately after setup. It assumes the
    // state is recoverable because every other function ensures
    // that's the case even during crashes.

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
        let (mut powerpm, _) = PoWERPersistentMemoryRegion::new(pm);
        powerpm.flush(); // ensure there are no outstanding writes

        // At startup, we grant a blanket permission for as long as
        // the program runs, represented by a factory that can
        // generate the same permission an arbitrary number of times.
        // That permission allows any write to storage as long as it
        // can't change the post-recovery state, even if that write
        // only completes partially due to a crash. In other words, a
        // transition from state `s1` to `s2` is allowable only if
        // both those recover to the same abstract state according to
        // the untrusted recovery specification.

        let ghost state = UntrustedKvStoreImpl::<TrustedKvPermissionFactory,
                                                 PM, K, I, L>::recover(powerpm@.durable_state).unwrap();
        let ghost is_transition_allowable: spec_fn(Seq<u8>, Seq<u8>) -> bool = |s1: Seq<u8>, s2: Seq<u8>| {
            UntrustedKvStoreImpl::<TrustedKvPermissionFactory, PM, K, I, L>::recover(s1) ==
            UntrustedKvStoreImpl::<TrustedKvPermissionFactory, PM, K, I, L>::recover(s2)
        };
        let tracked perm_factory = TrustedKvPermissionFactory{
            is_transition_allowable,
            powerpm_id: powerpm.id(),
        };
        let untrusted_kv_impl =
            UntrustedKvStoreImpl::<TrustedKvPermissionFactory, PM, K, I, L>::start(
                powerpm, kvstore_id, Ghost(state), Tracked(perm_factory)
            )?;

        Ok(Self {
            untrusted_kv_impl,
            powerpm_id: Ghost(powerpm.id()),
        })
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
        self.untrusted_kv_impl.tentatively_create(key, item)
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
        self.untrusted_kv_impl.tentatively_update_item(key, item)
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
        self.untrusted_kv_impl.tentatively_delete(key)
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
        self.untrusted_kv_impl.abort()
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
        // To effect commit, we need to pass the untrusted code
        // permission to make a transition from one storage state to
        // another. Specifically, we give it permission to make a
        // single transition from the durable state (the one that
        // would result from a crash right now) to the tentative state
        // (the one that should result from this commit). We also need
        // to give it permission to stay in the durable state, to
        // allow for the possibility that the committing write crashes
        // before anything changes on the storage.

        let ghost is_transition_allowable: spec_fn(Seq<u8>, Seq<u8>) -> bool = |s1: Seq<u8>, s2: Seq<u8>| ({
            &&& UntrustedKvStoreImpl::<TrustedKvPermissionFactory, PM, K, I, L>::recover(s1) ==
                Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })
            &&& UntrustedKvStoreImpl::<TrustedKvPermissionFactory, PM, K, I, L>::recover(s2) ==
                Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.tentative })
        } || {
            &&& UntrustedKvStoreImpl::<TrustedKvPermissionFactory, PM, K, I, L>::recover(s1) ==
                Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })
            &&& UntrustedKvStoreImpl::<TrustedKvPermissionFactory, PM, K, I, L>::recover(s2) ==
                Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })
        });
        let tracked perm = TrustedKvPermission{
            is_transition_allowable,
            powerpm_id: self.powerpm_id@
        };
        self.untrusted_kv_impl.commit::<TrustedKvPermission>(Tracked(perm))?;
        Ok(())
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
        self.untrusted_kv_impl.tentatively_append_to_list(key, new_list_element)
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
        self.untrusted_kv_impl.tentatively_append_to_list_and_update_item(key, new_list_element, new_item)
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
        self.untrusted_kv_impl.tentatively_update_list_element_at_index(key, idx, new_list_element)
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
        self.untrusted_kv_impl.tentatively_update_list_element_at_index_and_item(key, idx, new_list_element, new_item)
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
        self.untrusted_kv_impl.tentatively_trim_list(key, trim_length)
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
        self.untrusted_kv_impl.tentatively_trim_list_and_update_item(key, trim_length, new_item)
    }

}

}
