#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::tokens::frac::*;
use vstd::invariant::*;

use std::sync::Arc;
use std::hash::Hash;

use crate::pmem::crashinv_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;

use super::concurrentspec_t::*;
use super::spec_t::*;
use super::rwkv_v::*;
use super::impl_v::*;
use super::recover_v::*;

verus! {

// TODO: this is probably not correct or safe to do
// This can't live in rwkv_t.rs because lock is private, but it does something
// that Verus doesn't like, so it has to be external.
#[verus::trusted]
#[verifier::external]
impl<PM, K, I, L> Drop for ConcurrentKvStore<PM, K, I, L> 
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    fn drop(&mut self) 
        opens_invariants none 
        no_unwind
    {
        self.lock.acquire_write();
    }
}


#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
pub struct ConcurrentKvStoreInvState<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub(super) rwlock_auth: GhostVarAuth<ConcurrentKvStoreView<K, I, L>>,
    pub(super) caller_auth: GhostVarAuth<ConcurrentKvStoreView<K, I, L>>,
    pub(super) durable_res: GhostVar<Seq<u8>>,
    pub(super) ghost _pm: core::marker::PhantomData<PM>,
}

pub struct ConcurrentKvStoreInvPred {
    pub rwlock_id: int,
    pub caller_id: int,
    pub durable_id: int,
    pub pm_constants: PersistentMemoryConstants,
    pub ps: SetupParameters,
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
impl<PM, K, I, L> InvariantPredicate<ConcurrentKvStoreInvPred, ConcurrentKvStoreInvState<PM, K, I, L>> for ConcurrentKvStoreInvPred
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    open(super) spec fn inv(k: ConcurrentKvStoreInvPred, inner: ConcurrentKvStoreInvState<PM, K, I, L>) -> bool {
        &&& inner.rwlock_auth.id() == k.rwlock_id
        &&& inner.caller_auth.id() == k.caller_id
        &&& inner.durable_res.id() == k.durable_id
        &&& inner.rwlock_auth@ == inner.caller_auth@
        &&& k.pm_constants == inner.caller_auth@.pm_constants
        &&& k.ps == inner.caller_auth@.ps
        &&& recover_journal_then_kv::<PM, K, I, L>(inner.durable_res@) ==
            Some(RecoveredKvStore::<K, I, L>{
                ps: inner.caller_auth@.ps,
                kv: inner.caller_auth@.kv,
            })
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
pub trait ConcurrentKvStoreTrait<PM, K, I, L> : Sized
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    spec fn id(self) -> int;
    spec fn namespace(self) -> int;
    spec fn spec_space_needed_for_setup(ps: SetupParameters) -> nat;

    exec fn space_needed_for_setup(ps: &SetupParameters) -> (result: Result<u64, KvError>)
        ensures
            match result {
                Ok(v) => v == Self::spec_space_needed_for_setup(*ps),
                Err(KvError::InvalidParameter) => !ps.valid(),
                Err(KvError::OutOfSpace) => Self::spec_space_needed_for_setup(*ps) > u64::MAX,
                Err(_) => false,
            };

    exec fn start_with_resource(
        atomicpm: PersistentMemoryRegionAtomic<PM>,
        kvstore_id: u128,
        Tracked(inv): Tracked<Arc<AtomicInvariant::<ConcurrentKvStoreInvPred, ConcurrentKvStoreInvState<PM, K, I, L>, ConcurrentKvStoreInvPred>>>,
        Tracked(rwlock_res): Tracked<GhostVar<ConcurrentKvStoreView<K, I, L>>>,
    ) -> (result: Result<Self, KvError>)
        requires
            atomicpm.inv(),
            atomicpm.id() == inv.constant().durable_id,
            atomicpm.constants() == inv.constant().pm_constants,
            rwlock_res.id() == inv.constant().rwlock_id,
            vstd::std_specs::hash::obeys_key_model::<K>(),
        ensures
            match result {
                Ok(kv) => {
                    &&& kv.id() == inv.constant().caller_id
                    &&& kv.namespace() == inv.namespace()
                },
                Err(KvError::CRCMismatch) => !atomicpm.constants().impervious_to_corruption(),
                Err(KvError::WrongKvStoreId{ requested_id, actual_id }) => {
                   &&& requested_id == kvstore_id
                   &&& actual_id == inv.constant().ps.kvstore_id
                   &&& requested_id != actual_id
                },
                Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
                Err(_) => false,
            };

    exec fn read_item<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<I, KvError>, Tracked<CB::Completion>))
        where
            CB: ReadLinearizer<K, I, L, ReadItemOp<K>>,
        requires 
            cb.pre(self.id(), ReadItemOp{ key: *key }),
            !cb.namespaces().contains(self.namespace()),
        ensures
            cb.post(result.1@, self.id(), ReadItemOp{ key: *key }, result.0);

    exec fn get_keys<CB: ReadLinearizer<K, I, L, GetKeysOp>>(
        &self,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<Vec<K>, KvError>, Tracked<CB::Completion>))
        requires 
            cb.pre(self.id(), GetKeysOp{ }),
            !cb.namespaces().contains(self.namespace()),
        ensures
            cb.post(result.1@, self.id(), GetKeysOp{ }, result.0);

    exec fn read_item_and_list<CB: ReadLinearizer<K, I, L, ReadItemAndListOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(I, Vec<L>), KvError>, Tracked<CB::Completion>))
        requires 
            cb.pre(self.id(), ReadItemAndListOp{ key: *key }),
            !cb.namespaces().contains(self.namespace()),
        ensures
            cb.post(result.1@, self.id(), ReadItemAndListOp{ key: *key }, result.0);

    exec fn read_list<CB: ReadLinearizer<K, I, L, ReadListOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<Vec<L>, KvError>, Tracked<CB::Completion>))
        requires 
            cb.pre(self.id(), ReadListOp{ key: *key }),
            !cb.namespaces().contains(self.namespace()),
        ensures
            cb.post(result.1@, self.id(), ReadListOp{ key: *key }, result.0);

    exec fn get_list_length<CB: ReadLinearizer<K, I, L, GetListLengthOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<usize, KvError>, Tracked<CB::Completion>))
        requires 
            cb.pre(self.id(), GetListLengthOp{ key: *key }),
            !cb.namespaces().contains(self.namespace()),
        ensures
            cb.post(result.1@, self.id(), GetListLengthOp{ key: *key }, result.0);

    exec fn create<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, CreateOp<K, I, STRICT_SPACE>>,
        requires
            cb.pre(self.id(), CreateOp{ key: *key, item: *item }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), CreateOp{ key: *key, item: *item }, result.0);

    exec fn update_item<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, UpdateItemOp<K, I, STRICT_SPACE>>,
        requires
            cb.pre(self.id(), UpdateItemOp{ key: *key, item: *item }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), UpdateItemOp{ key: *key, item: *item }, result.0);

    exec fn delete<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, DeleteOp<K>>,
        requires
            cb.pre(self.id(), DeleteOp{ key: *key }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), DeleteOp{ key: *key }, result.0);

    exec fn append_to_list<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        new_list_element: L,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, AppendToListOp<K, L, STRICT_SPACE>>,
        requires
            cb.pre(self.id(), AppendToListOp{ key: *key, new_list_element }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), AppendToListOp{ key: *key, new_list_element }, result.0);

    exec fn append_to_list_and_update_item<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        new_list_element: L,
        new_item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, AppendToListAndUpdateItemOp<K, I, L, STRICT_SPACE>>,
        requires
            cb.pre(self.id(), AppendToListAndUpdateItemOp{ key: *key, new_list_element, new_item: *new_item }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), AppendToListAndUpdateItemOp{ key: *key, new_list_element, new_item: *new_item }, result.0);

    exec fn update_list_element_at_index<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        idx: usize,
        new_list_element: L,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, UpdateListElementAtIndexOp<K, L, STRICT_SPACE>>,
        requires
            cb.pre(self.id(), UpdateListElementAtIndexOp{ key: *key, idx, new_list_element }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), UpdateListElementAtIndexOp{ key: *key, idx, new_list_element }, result.0);

    exec fn update_list_element_at_index_and_item<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        idx: usize,
        new_list_element: L,
        new_item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, UpdateListElementAtIndexAndItemOp<K, I, L, STRICT_SPACE>>,
        requires
            cb.pre(self.id(), UpdateListElementAtIndexAndItemOp{ key: *key, idx, new_list_element, new_item: *new_item }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), UpdateListElementAtIndexAndItemOp{ key: *key, idx, new_list_element, new_item: *new_item }, result.0);

    exec fn trim_list<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        trim_length: usize,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, TrimListOp<K, STRICT_SPACE>>,
        requires
            cb.pre(self.id(), TrimListOp{ key : *key, trim_length }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), TrimListOp{ key: *key, trim_length }, result.0);

    exec fn trim_list_and_update_item<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        trim_length: usize,
        new_item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, TrimListAndUpdateItemOp<K, I, STRICT_SPACE>>,
        requires
            cb.pre(self.id(), TrimListAndUpdateItemOp{ key : *key, trim_length, new_item: *new_item }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), TrimListAndUpdateItemOp{ key: *key, trim_length, new_item: *new_item }, result.0);
}

// This function is expected to be called after a crash.
//
// The caller must be sure that the CKV atomic invariant held before the crash
// for this PM region.
//
// This might be true because in the previous execution before the crash, one
// of these two was true:
//
// - The PM region was given to setup(), which returned.
//
// - The PM region was given to recover().
// 
// The underlying property is that both of the above call hold_until_crash()
// to ensure that the invariant keeps holding until the system crashes.
pub exec fn recover<PM, K, I, L>(
    mut pm: PM,
    kvstore_id: u128,
    Ghost(id): Ghost<int>,
    Ghost(namespace): Ghost<int>,
) -> (result: Result<ConcurrentKvStore::<PM, K, I, L>, KvError>)
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
    requires
        pm.inv(),
        vstd::std_specs::hash::obeys_key_model::<K>(),
    ensures
        match result {
            Ok(kv) => {
                &&& kv.id() == id
                &&& kv.namespace() == namespace
            },
            Err(KvError::CRCMismatch) => !pm.constants().impervious_to_corruption(),
            Err(KvError::WrongKvStoreId{ requested_id, actual_id }) => {
               &&& requested_id == kvstore_id
            },
            Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
            Err(_) => false,
        },
{
    let (atomicpm, durable_res) = PersistentMemoryRegionAtomic::new(pm);
    let tracked crashinv = InvariantRecoverer::new(ConcurrentKvStoreInvPred{
        rwlock_id: arbitrary(),
        caller_id: id,
        durable_id: durable_res@.id(),
        pm_constants: pm.constants(),
        ps: arbitrary(),
    }, namespace);
    assume(crashinv.held_before_crash());
    start_with_inv(atomicpm, kvstore_id, Tracked(crashinv.get()))
}

exec fn start_with_inv<PM, K, I, L>(
    atomicpm: PersistentMemoryRegionAtomic<PM>,
    kvstore_id: u128,
    Tracked(inv): Tracked<AtomicInvariant::<ConcurrentKvStoreInvPred, ConcurrentKvStoreInvState<PM, K, I, L>, ConcurrentKvStoreInvPred>>,
) -> (result: Result<ConcurrentKvStore::<PM, K, I, L>, KvError>)
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
    requires
        atomicpm.inv(),
        atomicpm.id() == inv.constant().durable_id,
        atomicpm.constants() == inv.constant().pm_constants,
        vstd::std_specs::hash::obeys_key_model::<K>(),
    ensures
        match result {
            Ok(kv) => {
                &&& kv.id() == inv.constant().caller_id
                &&& kv.namespace() == inv.namespace()
            },
            Err(KvError::CRCMismatch) => !atomicpm.constants().impervious_to_corruption(),
            Err(KvError::WrongKvStoreId{ requested_id, actual_id }) => {
               &&& requested_id == kvstore_id
               &&& actual_id == inv.constant().ps.kvstore_id
               &&& requested_id != actual_id
            },
            Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
            Err(_) => false,
        },
{
    let tracked inv_old = inv.into_inner();
    let tracked (rwlock_auth, rwlock_res) = GhostVarAuth::<ConcurrentKvStoreView::<K, I, L>>::new(inv_old.caller_auth@);

    let ghost inv_pred = ConcurrentKvStoreInvPred{
        rwlock_id: rwlock_auth.id(),
        .. inv.constant()
    };

    let ghost namespace = inv.namespace();
    let tracked inv_state = ConcurrentKvStoreInvState::<PM, K, I, L>{
        rwlock_auth: rwlock_auth,
        .. inv_old
    };


    let tracked inv = AtomicInvariant::<_, _, ConcurrentKvStoreInvPred>::new(inv_pred, inv_state, inv.namespace());
    let tracked inv = Arc::new(inv);

    proof {
        hold_until_crash(inv.clone());
    }

    ConcurrentKvStore::<PM, K, I, L>::start_with_resource(
        atomicpm, kvstore_id, Tracked(inv), Tracked(rwlock_res)
    )
}

pub exec fn setup<PM, K, I, L>(
    mut pm: PM,
    ps: &SetupParameters,
    Ghost(namespace): Ghost<int>,
) -> (result: Result<(ConcurrentKvStore::<PM, K, I, L>,
                      Tracked<GhostVar<ConcurrentKvStoreView::<K, I, L>>>),
                     KvError>)
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
    requires
        pm.inv(),
        vstd::std_specs::hash::obeys_key_model::<K>(),
    ensures
        match result {
            Ok((kv, res)) => {
                &&& kv.id() == res@.id()
                &&& kv.namespace() == namespace
                &&& res@@ == ConcurrentKvStoreView::<K, I, L>{
                        ps: *ps,
                        pm_constants: pm.constants(),
                        kv: RecoveredKvStore::<K, I, L>::init(*ps).kv,
                    }
            },
            Err(KvError::InvalidParameter) => !ps.valid(),
            Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
            Err(KvError::OutOfSpace) => pm@.len() < ConcurrentKvStore::<PM, K, I, L>::spec_space_needed_for_setup(*ps),
            Err(KvError::CRCMismatch) => !pm.constants().impervious_to_corruption(),
            Err(_) => false,
        },
{
    match UntrustedKvStoreImpl::<NoopPermFactory<PM, K, I, L>, PM, K, I, L>::setup(&mut pm, ps) {
        Err(e) => Err(e),
        Ok(v) => {
            let (atomicpm, durable_res) = PersistentMemoryRegionAtomic::new(pm);
            let ghost ckv = ConcurrentKvStoreView::<K, I, L>{
                ps: *ps,
                pm_constants: pm.constants(),
                kv: RecoveredKvStore::<K, I, L>::init(*ps).kv,
            };

            let tracked (caller_auth, caller_res) = GhostVarAuth::<ConcurrentKvStoreView::<K, I, L>>::new(ckv);
            let tracked (rwlock_auth, _) = GhostVarAuth::<ConcurrentKvStoreView::<K, I, L>>::new(ckv);

            let ghost inv_pred = ConcurrentKvStoreInvPred{
                rwlock_id: rwlock_auth.id(),
                caller_id: caller_auth.id(),
                durable_id: durable_res@.id(),
                pm_constants: pm.constants(),
                ps: *ps,
            };
            let tracked inv_state = ConcurrentKvStoreInvState::<PM, K, I, L>{
                rwlock_auth: rwlock_auth,
                caller_auth: caller_auth,
                durable_res: durable_res.get(),
                _pm: core::marker::PhantomData,
            };
            let tracked inv = AtomicInvariant::<_, _, ConcurrentKvStoreInvPred>::new(inv_pred, inv_state, namespace);

            match start_with_inv(atomicpm, ps.kvstore_id, Tracked(inv)) {
                Ok(ckv) => Ok((ckv, Tracked(caller_res))),
                Err(e) => Err(e),
            }
        },
    }
}

}
