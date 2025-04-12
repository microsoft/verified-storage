#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use std::hash::Hash;
use super::concurrentspec_t::*;
use super::impl_v::*;
use super::spec_t::*;
use super::recover_v::*;
use vstd::pcm::frac::*;
use vstd::rwlock::{RwLock, RwLockPredicate};
use vstd::invariant::*;
use vstd::modes::*;
use std::sync::Arc;

verus! {

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
struct ConcurrentKvStoreInternal<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    invariant_resource: Tracked<GhostVar<ConcurrentKvStoreView<K, I, L>>>,
    kv: UntrustedKvStoreImpl<NoopPermFactory<PM, K, I, L>, PM, K, I, L>,
}

struct ConcurrentKvStorePredicate
{
    id: int,
    powerpm_id: int,
}

impl<PM, K, I, L> RwLockPredicate<ConcurrentKvStoreInternal<PM, K, I, L>> for ConcurrentKvStorePredicate
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    closed spec fn inv(self, v: ConcurrentKvStoreInternal<PM, K, I, L>) -> bool
    {
        &&& v.kv.valid()
        &&& v.kv@.ps.valid()
        &&& v.kv@.used_key_slots == v.kv@.durable.num_keys()
        &&& v.kv@.used_list_element_slots == v.kv@.durable.num_list_elements()
        &&& v.kv@.used_transaction_operation_slots == 0
        &&& v.kv@.durable == v.kv@.tentative
        &&& v.kv@.ps.logical_range_gaps_policy == v.kv@.durable.logical_range_gaps_policy
        &&& self.id == v.invariant_resource@.id()
        &&& self.powerpm_id == v.kv@.powerpm_id
        &&& v.invariant_resource@@ == ConcurrentKvStoreView::from_kvstore_view(v.kv@)
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
    rwlock_auth: GhostVarAuth<ConcurrentKvStoreView<K, I, L>>,
    caller_auth: GhostVarAuth<ConcurrentKvStoreView<K, I, L>>,
    durable_res: GhostVar<Seq<u8>>,
    ghost _pm: core::marker::PhantomData<PM>,
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
    closed spec fn inv(k: ConcurrentKvStoreInvPred, inner: ConcurrentKvStoreInvState<PM, K, I, L>) -> bool {
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
pub struct ConcurrentKvStore<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    lock: RwLock<ConcurrentKvStoreInternal<PM, K, I, L>, ConcurrentKvStorePredicate>,
    inv: Tracked<Arc<AtomicInvariant<ConcurrentKvStoreInvPred,
                                     ConcurrentKvStoreInvState<PM, K, I, L>,
                                     ConcurrentKvStoreInvPred>>>,
}

impl<PM, K, I, L> CanRecover<K, I, L> for ConcurrentKvStore<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    closed spec fn recover(s: Seq<u8>) -> Option<RecoveredKvStore<K, I, L>> {
        recover_journal_then_kv::<PM, K, I, L>(s)
    }
}

impl<PM, K, I, L> ConcurrentKvStore<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub closed spec fn valid(self) -> bool
    {
        &&& self.inv@.constant().rwlock_id == self.lock.pred().id
        &&& self.inv@.constant().durable_id == self.lock.pred().powerpm_id
    }

    pub closed spec fn id(self) -> int
    {
        self.inv@.constant().caller_id
    }

    pub closed spec fn namespace(self) -> int
    {
        self.inv@.namespace()
    }

    pub closed spec fn spec_space_needed_for_setup(ps: SetupParameters) -> nat
    {
        UntrustedKvStoreImpl::<NoopPermFactory<PM, K, I, L>, PM, K, I, L>::spec_space_needed_for_setup(ps)
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
        UntrustedKvStoreImpl::<NoopPermFactory<PM, K, I, L>, PM, K, I, L>::space_needed_for_setup(ps)
    }

    // This function is expected to be called after a crash.
    //
    // The caller must be sure that the CKV atomic invariant held before the crash
    // for this PM region.
    //
    // This might be true because in the previous execution before the crash, one
    // of these two was true:
    //
    // - The PM region was given to setup(), which returned, and the only thing
    //   done with the resulting invariant was to possibly pass it to start().
    //
    // - The PM region was given to recover_inv(), and the only thing done with
    //   the resulting invariant (if any, due to possibly a crash in recover_inv)
    //   was to possibly pass it to start().
    pub exec fn recover_inv_checked(
        mut pm: PM,
        Ghost(id): Ghost<int>,
    ) -> (result: (PersistentMemoryRegionAtomic<PM>,
                   Tracked<AtomicInvariant::<ConcurrentKvStoreInvPred,
                                             ConcurrentKvStoreInvState<PM, K, I, L>,
                                             ConcurrentKvStoreInvPred>>))
        requires
            pm.inv(),
        ensures
            result.0.inv(),
            result.1@.constant().durable_id == result.0.id(),
            result.1@.constant().caller_id == id,
    {
        let (atomicpm, durable_res) = PersistentMemoryRegionAtomic::new(pm);
        (atomicpm, Tracked(Self::invariant_recovery_axiom(id, durable_res@.id())))
    }

    #[verifier::external_body]
    proof fn invariant_recovery_axiom(
        caller_id: int,
        durable_id: int
    ) -> (tracked result: AtomicInvariant::<ConcurrentKvStoreInvPred,
                                            ConcurrentKvStoreInvState<PM, K, I, L>,
                                            ConcurrentKvStoreInvPred>)
        ensures
            result.constant().durable_id == durable_id,
            result.constant().caller_id == caller_id,
    {
        unimplemented!()
    }

    pub exec fn setup(
        mut pm: PM,
        ps: &SetupParameters,
        Ghost(namespace): Ghost<int>,
    ) -> (result: Result<(PersistentMemoryRegionAtomic<PM>,
                          Tracked<AtomicInvariant::<ConcurrentKvStoreInvPred, ConcurrentKvStoreInvState<PM, K, I, L>, ConcurrentKvStoreInvPred>>,
                          Tracked<GhostVar<ConcurrentKvStoreView::<K, I, L>>>),
                         (KvError, PM)>)
        requires
            pm.inv(),
        ensures
            match result {
                Ok((atomicpm, inv, res)) => {
                    &&& atomicpm.inv()
                    &&& atomicpm.constants() == pm.constants()
                    &&& atomicpm.id() == inv@.constant().durable_id
                    &&& inv@.namespace() == namespace
                    &&& inv@.constant().ps == ps
                    &&& inv@.constant().pm_constants == pm.constants()
                    &&& res@.id() == inv@.constant().caller_id
                    &&& res@@ == ConcurrentKvStoreView::<K, I, L>{
                            ps: *ps,
                            pm_constants: pm.constants(),
                            kv: RecoveredKvStore::<K, I, L>::init(*ps).kv,
                        }
                }
                Err((KvError::InvalidParameter, _)) => !ps.valid(),
                Err((KvError::KeySizeTooSmall, _)) => K::spec_size_of() == 0,
                Err((KvError::OutOfSpace, _)) => pm@.len() < Self::spec_space_needed_for_setup(*ps),
                Err(_) => false,
            },
            match result {
                Ok(_) => true,
                Err((_, err_pm)) => {
                    &&& err_pm.inv()
                    &&& err_pm.constants() == pm.constants()
                    &&& err_pm@.len() == pm@.len()
                },
            },
    {
        match UntrustedKvStoreImpl::<NoopPermFactory<PM, K, I, L>, PM, K, I, L>::setup(&mut pm, ps) {
            Err(e) => Err((e, pm)),
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

                Ok((atomicpm, Tracked(inv), Tracked(caller_res)))
            },
        }
    }

    pub exec fn start(
        atomicpm: PersistentMemoryRegionAtomic<PM>,
        kvstore_id: u128,
        Tracked(inv): Tracked<AtomicInvariant::<ConcurrentKvStoreInvPred, ConcurrentKvStoreInvState<PM, K, I, L>, ConcurrentKvStoreInvPred>>,
    ) -> (result: Result<Self, KvError>)
        requires
            atomicpm.inv(),
            atomicpm.id() == inv.constant().durable_id,
            atomicpm.constants() == inv.constant().pm_constants,
            vstd::std_specs::hash::obeys_key_model::<K>(),
        ensures
            match result {
                Ok(kv) => {
                    &&& kv.valid()
                    &&& kv.id() == inv.constant().caller_id
                    &&& kv.namespace() == inv.namespace()
                },
                Err(KvError::CRCMismatch) => !atomicpm.constants().impervious_to_corruption(),
                Err(KvError::WrongKvStoreId{ requested_id, actual_id }) => {
                   &&& requested_id == kvstore_id
                   &&& actual_id == inv.constant().ps.kvstore_id
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

        atomicpm.agree(Tracked(&inv_state.durable_res));

        let tracked inv = AtomicInvariant::<_, _, ConcurrentKvStoreInvPred>::new(inv_pred, inv_state, namespace);
        let tracked inv = Arc::new(inv);

        let tracked perm_factory = NoopPermFactory::<PM, K, I, L>{
            inv: inv.clone(),
        };

        let ghost recovered_state = RecoveredKvStore::<K, I, L>{
            ps: inv_old.caller_auth@.ps,
            kv: inv_old.caller_auth@.kv,
        };

        let powerpm = PoWERPersistentMemoryRegion::new_atomic(atomicpm);
        let kv = match UntrustedKvStoreImpl::<NoopPermFactory<PM, K, I, L>, PM, K, I, L>::start(
            powerpm, kvstore_id, Ghost(recovered_state), Tracked(perm_factory)
        ) {
            Ok(kv) => kv,
            Err(e) => { return Err(e); },
        };

        let ghost pred = ConcurrentKvStorePredicate{
            id: rwlock_auth.id(),
            powerpm_id: powerpm.id(),
        };
        let kv_internal = ConcurrentKvStoreInternal::<PM, K, I, L>{
            invariant_resource: Tracked(rwlock_res),
            kv: kv,
        };
        let lock = RwLock::<ConcurrentKvStoreInternal<PM, K, I, L>, ConcurrentKvStorePredicate>::new(
            kv_internal, Ghost(pred)
        );
        let selfish = Self{
            lock: lock,
            inv: Tracked(inv),
        };
        Ok(selfish)
    }

    pub exec fn read_item<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<I, KvError>, Tracked<CB::Completion>))
        where
            CB: ReadLinearizer<K, I, L, ReadItemOp<K>>,
        requires 
            self.valid(),
            cb.pre(self.id(), ReadItemOp{ key: *key }),
            !cb.namespaces().contains(self.namespace()),
        ensures
            self.valid(),
            cb.post(result.1@, self.id(), ReadItemOp{ key: *key }, result.0),
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = ReadItemOp{ key: *key };
        let kv_internal = read_handle.borrow();
        let result = kv_internal.kv.read_item(key);
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        let tracked mut completion;
        open_atomic_invariant!(self.inv.borrow() => inner => {
            proof {
                inner.rwlock_auth.agree(kv_internal.invariant_resource.borrow());
                completion = cb.apply(op, result, &inner.caller_auth);
            };
        });
        read_handle.release_read();
        (result, Tracked(completion))
    }

    pub exec fn get_keys<CB: ReadLinearizer<K, I, L, GetKeysOp>>(
        &self,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<Vec<K>, KvError>, Tracked<CB::Completion>))
        requires 
            self.valid(),
            cb.pre(self.id(), GetKeysOp{ }),
            !cb.namespaces().contains(self.namespace()),
        ensures
            self.valid(),
            cb.post(result.1@, self.id(), GetKeysOp{ }, result.0),
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = GetKeysOp{ };
        let kv_internal = read_handle.borrow();
        let result = kv_internal.kv.get_keys();
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        let tracked mut completion;
        open_atomic_invariant!(self.inv.borrow() => inner => {
            proof {
                inner.rwlock_auth.agree(kv_internal.invariant_resource.borrow());
                completion = cb.apply(op, result, &inner.caller_auth);
            }
        });
        read_handle.release_read();
        (result, Tracked(completion))
    }

    pub exec fn read_item_and_list<CB: ReadLinearizer<K, I, L, ReadItemAndListOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(I, Vec<L>), KvError>, Tracked<CB::Completion>))
        requires 
            self.valid(),
            cb.pre(self.id(), ReadItemAndListOp{ key: *key }),
            !cb.namespaces().contains(self.namespace()),
        ensures
            self.valid(),
            cb.post(result.1@, self.id(), ReadItemAndListOp{ key: *key }, result.0),
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = ReadItemAndListOp{ key: *key };
        let kv_internal = read_handle.borrow();
        let result = kv_internal.kv.read_item_and_list(key);
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        let tracked mut completion;
        open_atomic_invariant!(self.inv.borrow() => inner => {
            proof {
                inner.rwlock_auth.agree(kv_internal.invariant_resource.borrow());
                completion = cb.apply(op, result, &inner.caller_auth);
            }
        });
        read_handle.release_read();
        (result, Tracked(completion))
    }

    pub exec fn read_list<CB: ReadLinearizer<K, I, L, ReadListOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<Vec<L>, KvError>, Tracked<CB::Completion>))
        requires 
            self.valid(),
            cb.pre(self.id(), ReadListOp{ key: *key }),
            !cb.namespaces().contains(self.namespace()),
        ensures
            self.valid(),
            cb.post(result.1@, self.id(), ReadListOp{ key: *key }, result.0),
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = ReadListOp{ key: *key };
        let kv_internal = read_handle.borrow();
        let result = kv_internal.kv.read_list(key);
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        let tracked mut completion;
        open_atomic_invariant!(self.inv.borrow() => inner => {
            proof {
                inner.rwlock_auth.agree(kv_internal.invariant_resource.borrow());
                completion = cb.apply(op, result, &inner.caller_auth);
            }
        });
        read_handle.release_read();
        (result, Tracked(completion))
    }

    pub exec fn get_list_length<CB: ReadLinearizer<K, I, L, GetListLengthOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<usize, KvError>, Tracked<CB::Completion>))
        requires 
            self.valid(),
            cb.pre(self.id(), GetListLengthOp{ key: *key }),
            !cb.namespaces().contains(self.namespace()),
        ensures
            self.valid(),
            cb.post(result.1@, self.id(), GetListLengthOp{ key: *key }, result.0),
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = GetListLengthOp{ key: *key };
        let kv_internal = read_handle.borrow();
        let result = kv_internal.kv.get_list_length(key);
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        let tracked mut completion;
        open_atomic_invariant!(self.inv.borrow() => inner => {
            proof {
                inner.rwlock_auth.agree(kv_internal.invariant_resource.borrow());
                completion = cb.apply(op, result, &inner.caller_auth);
            }
        });
        read_handle.release_read();
        (result, Tracked(completion))
    }

    proof fn linearize_nop<Op, CB>(
        tracked credit: OpenInvariantCredit,
        tracked inv: Arc<AtomicInvariant<ConcurrentKvStoreInvPred,
                                         ConcurrentKvStoreInvState<PM, K, I, L>,
                                         ConcurrentKvStoreInvPred>>,
        tracked ckv_res: &GhostVar<ConcurrentKvStoreView<K, I, L>>,
        op: Op,
        exec_result: Result<Op::KvResult, KvError>,
        tracked cb: CB,
    ) -> (tracked complete: CB::Completion)
        where
            Op: MutatingOperation<K, I, L>,
            CB: MutatingLinearizer<K, I, L, Op>,
        requires
            ckv_res.id() == inv.constant().rwlock_id,
            cb.pre(inv.constant().caller_id, op),
            !cb.namespaces().contains(inv.namespace()),
            op.result_valid(ckv_res@, ckv_res@, exec_result),
        ensures
            cb.post(complete, inv.constant().caller_id, op, exec_result),
        opens_invariants
            cb.namespaces().insert(inv.namespace())
    {
        let tracked mut completion;
        open_atomic_invariant_in_proof!(credit => &inv => inner => {
            inner.rwlock_auth.agree(ckv_res);
            completion = cb.apply(op, ckv_res@, exec_result, &mut inner.caller_auth);
        });
        completion
    }

    exec fn maybe_commit<Op, CB>(
        &self,
        tentative_result: Result<Op::KvResult, KvError>,
        kv_internal: &mut ConcurrentKvStoreInternal<PM, K, I, L>,
        Ghost(op): Ghost<Op>,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<Op::KvResult, KvError>, Tracked<CB::Completion>))
        where
            Op: MutatingOperation<K, I, L>,
            CB: MutatingLinearizer<K, I, L, Op>,
        requires
            self.valid(),
            old(kv_internal).kv.valid(),
            old(kv_internal).kv@.ps.valid(),
            old(kv_internal).kv@.ps.logical_range_gaps_policy ==
                old(kv_internal).kv@.durable.logical_range_gaps_policy,
            old(kv_internal).kv@.powerpm_id == self.inv@.constant().durable_id,
            old(kv_internal).invariant_resource@.id() == self.inv@.constant().rwlock_id,
            old(kv_internal).invariant_resource@@ == ConcurrentKvStoreView::from_kvstore_view(old(kv_internal).kv@),
            cb.pre(self.inv@.constant().caller_id, op),
            !cb.namespaces().contains(self.inv@.namespace()),
            forall |ckv_old, ckv_new, result|
                #[trigger] op.result_valid(ckv_old, ckv_new, result) ==> {
                    &&& ckv_old.pm_constants == ckv_new.pm_constants
                    &&& ckv_old.ps == ckv_new.ps
                },
            op.result_valid(old(kv_internal).invariant_resource@@,
                            ConcurrentKvStoreView::<K, I, L>{
                                ps: old(kv_internal).kv@.ps,
                                pm_constants: old(kv_internal).kv@.pm_constants,
                                kv: old(kv_internal).kv@.tentative,
                            },
                            tentative_result),
            match tentative_result {
                Ok(_) => true,
                Err(_) => {
                    &&& old(kv_internal).kv@.used_key_slots == old(kv_internal).kv@.durable.num_keys()
                    &&& old(kv_internal).kv@.used_list_element_slots == old(kv_internal).kv@.durable.num_list_elements()
                    &&& old(kv_internal).kv@.used_transaction_operation_slots == 0
                    &&& old(kv_internal).kv@.tentative == old(kv_internal).kv@.durable
                },
            },
        ensures
            self.lock.pred().inv(*kv_internal),
            cb.post(result.1@, self.id(), op, result.0),
    {
        match tentative_result {
            Err(e) => {
                let credit = create_open_invariant_credit();
                let completion = Tracked(Self::linearize_nop::<Op, CB>(
                    credit.get(), self.inv.borrow().clone(), kv_internal.invariant_resource.borrow(), op, Err(e), cb)
                );
                (Err(e), completion)
            },
            Ok(v) => {
                let tracked mut completion;
                let result = Ok(v);
                let tracked mut inv_res;
                proof {
                    inv_res = GhostVarAuth::<ConcurrentKvStoreView<K, I, L>>::new(kv_internal.invariant_resource@@).1;
                    tracked_swap(kv_internal.invariant_resource.borrow_mut(), &mut inv_res);
                }

                let tracked perm = OpPerm{
                    inv: self.inv.borrow().clone(),
                    lin: cb,
                    rwlock_res: inv_res,
                    op: op,
                    result: result,
                };

                let perm_complete = kv_internal.kv.commit::<OpPerm::<PM, K, I, L, Op, CB>>(Tracked(perm));
                let perm_complete = perm_complete.unwrap();
                let tracked perm_complete = perm_complete.get();

                kv_internal.invariant_resource = Tracked(perm_complete.rwlock_res);
                let ghost ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);

                open_atomic_invariant!(self.inv.borrow() => inner => {
                    kv_internal.kv.agree(Tracked(&inner.durable_res));

                    proof {
                        inner.rwlock_auth.agree(kv_internal.invariant_resource.borrow());
                        completion = match perm_complete.lin_or_complete {
                            Either::A(lin) => lin.apply(op, ckv, result, &mut inner.caller_auth),
                            Either::B(complete) => complete,
                        }
                    }
                });

                (result, Tracked(completion))
            },
        }
    }

    pub exec fn create<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, CreateOp<K, I, STRICT_SPACE>>,
        requires
            self.valid(),
            cb.pre(self.id(), CreateOp{ key: *key, item: *item }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), CreateOp{ key: *key, item: *item }, result.0),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = CreateOp::<K, I, STRICT_SPACE>{ key: *key, item: *item };
        let result = kv_internal.kv.tentatively_create(key, item);
        let result = self.maybe_commit::<CreateOp<K, I, STRICT_SPACE>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn update_item<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, UpdateItemOp<K, I, STRICT_SPACE>>,
        requires
            self.valid(),
            cb.pre(self.id(), UpdateItemOp{ key: *key, item: *item }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), UpdateItemOp{ key: *key, item: *item }, result.0),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = UpdateItemOp::<K, I, STRICT_SPACE>{ key: *key, item: *item };
        let result = kv_internal.kv.tentatively_update_item(key, item);
        let result = self.maybe_commit::<UpdateItemOp<K, I, STRICT_SPACE>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn delete<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, DeleteOp<K>>,
        requires
            self.valid(),
            cb.pre(self.id(), DeleteOp{ key: *key }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), DeleteOp{ key: *key }, result.0),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = DeleteOp::<K>{ key: *key };
        let result = kv_internal.kv.tentatively_delete(key);
        let result = self.maybe_commit::<DeleteOp::<K>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn append_to_list<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        new_list_element: L,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, AppendToListOp<K, L, STRICT_SPACE>>,
        requires
            self.valid(),
            cb.pre(self.id(), AppendToListOp{ key: *key, new_list_element }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), AppendToListOp{ key: *key, new_list_element }, result.0),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = AppendToListOp::<K, L, STRICT_SPACE>{ key: *key, new_list_element };
        let result = kv_internal.kv.tentatively_append_to_list(key, new_list_element);
        let result = self.maybe_commit::<AppendToListOp::<K, L, STRICT_SPACE>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn append_to_list_and_update_item<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        new_list_element: L,
        new_item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, AppendToListAndUpdateItemOp<K, I, L, STRICT_SPACE>>,
        requires
            self.valid(),
            cb.pre(self.id(), AppendToListAndUpdateItemOp{ key: *key, new_list_element, new_item: *new_item }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), AppendToListAndUpdateItemOp{ key: *key, new_list_element, new_item: *new_item }, result.0),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = AppendToListAndUpdateItemOp::<K, I, L, STRICT_SPACE>{ key: *key, new_list_element, new_item: *new_item };
        let result = kv_internal.kv.tentatively_append_to_list_and_update_item(key, new_list_element, new_item);
        let result = self.maybe_commit::<AppendToListAndUpdateItemOp<K, I, L, STRICT_SPACE>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn update_list_element_at_index<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        idx: usize,
        new_list_element: L,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, UpdateListElementAtIndexOp<K, L, STRICT_SPACE>>,
        requires
            self.valid(),
            cb.pre(self.id(), UpdateListElementAtIndexOp{ key: *key, idx, new_list_element }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), UpdateListElementAtIndexOp{ key: *key, idx, new_list_element }, result.0),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = UpdateListElementAtIndexOp::<K, L, STRICT_SPACE>{ key: *key, idx, new_list_element };
        let result = kv_internal.kv.tentatively_update_list_element_at_index(key, idx, new_list_element);
        let result = self.maybe_commit::<UpdateListElementAtIndexOp<K, L, STRICT_SPACE>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn update_list_element_at_index_and_item<CB, const STRICT_SPACE: bool>(
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
            self.valid(),
            cb.pre(self.id(), UpdateListElementAtIndexAndItemOp{ key: *key, idx, new_list_element, new_item: *new_item }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), UpdateListElementAtIndexAndItemOp{ key: *key, idx, new_list_element, new_item: *new_item }, result.0),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = UpdateListElementAtIndexAndItemOp::<K, I, L, STRICT_SPACE>{ key: *key, idx, new_list_element,
                                                                     new_item: *new_item };
        let result = kv_internal.kv.tentatively_update_list_element_at_index_and_item(
            key, idx, new_list_element, new_item
        );
        let result = self.maybe_commit::<UpdateListElementAtIndexAndItemOp<K, I, L, STRICT_SPACE>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn trim_list<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        trim_length: usize,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, TrimListOp<K, STRICT_SPACE>>,
        requires
            self.valid(),
            cb.pre(self.id(), TrimListOp{ key : *key, trim_length }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), TrimListOp{ key: *key, trim_length }, result.0),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = TrimListOp::<K, STRICT_SPACE>{ key: *key, trim_length };
        let result = kv_internal.kv.tentatively_trim_list(key, trim_length);
        let result = self.maybe_commit::<TrimListOp<K, STRICT_SPACE>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn trim_list_and_update_item<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        trim_length: usize,
        new_item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, TrimListAndUpdateItemOp<K, I, STRICT_SPACE>>,
        requires
            self.valid(),
            cb.pre(self.id(), TrimListAndUpdateItemOp{ key : *key, trim_length, new_item: *new_item }),
            !cb.namespaces().contains(self.namespace()),
        ensures 
            cb.post(result.1@, self.id(), TrimListAndUpdateItemOp{ key: *key, trim_length, new_item: *new_item }, result.0),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = TrimListAndUpdateItemOp::<K, I, STRICT_SPACE>{ key: *key, trim_length, new_item: *new_item };
        let result = kv_internal.kv.tentatively_trim_list_and_update_item(key, trim_length, new_item);
        let result = self.maybe_commit::<TrimListAndUpdateItemOp<K, I, STRICT_SPACE>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
struct OpPerm<PM, K, I, L, Op, Lin>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        Op: MutatingOperation<K, I, L>,
        Lin: MutatingLinearizer<K, I, L, Op>,
{
    inv: Arc<AtomicInvariant<ConcurrentKvStoreInvPred,
                             ConcurrentKvStoreInvState<PM, K, I, L>,
                             ConcurrentKvStoreInvPred>>,
    lin: Lin,
    rwlock_res: GhostVar<ConcurrentKvStoreView<K, I, L>>,
    ghost op: Op,
    ghost result: Result<Op::KvResult, KvError>,
}

impl<PM, K, I, L, Op, Lin> OpPerm<PM, K, I, L, Op, Lin>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        Op: MutatingOperation<K, I, L>,
        Lin: MutatingLinearizer<K, I, L, Op>,
{
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.rwlock_res.id() == self.inv.constant().rwlock_id
        &&& !self.lin.namespaces().contains(self.inv.namespace())
        &&& self.lin.pre(self.inv.constant().caller_id, self.op)
        &&& forall |old_state, new_state, result| #[trigger] self.op.result_valid(old_state, new_state, result) ==> {
            &&& old_state.ps == new_state.ps
            &&& old_state.pm_constants == new_state.pm_constants
        }
    }
}

enum Either<A, B> {
    A(A),
    B(B),
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
struct OpPermComplete<K, I, L, Op, Lin>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        Op: MutatingOperation<K, I, L>,
        Lin: MutatingLinearizer<K, I, L, Op>,
{
    rwlock_res: GhostVar<ConcurrentKvStoreView<K, I, L>>,
    lin_or_complete: Either<Lin, Lin::Completion>,
}

impl<PM, K, I, L, Op, Lin> CheckPermission<Seq<u8>> for OpPerm<PM, K, I, L, Op, Lin>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        Op: MutatingOperation<K, I, L>,
        Lin: MutatingLinearizer<K, I, L, Op>,
{
    type Completion = OpPermComplete<K, I, L, Op, Lin>;

    closed spec fn check_permission(&self, old_state: Seq<u8>, new_state: Seq<u8>) -> bool {
        &&& recover_journal_then_kv::<PM, K, I, L>(old_state) matches Some(old_rkv)
        &&& recover_journal_then_kv::<PM, K, I, L>(new_state) matches Some(new_rkv)
        &&& {
            ||| self.op.result_valid(
                    ConcurrentKvStoreView::<K, I, L>{ ps: old_rkv.ps, pm_constants: self.rwlock_res@.pm_constants, kv: old_rkv.kv },
                    ConcurrentKvStoreView::<K, I, L>{ ps: new_rkv.ps, pm_constants: self.rwlock_res@.pm_constants, kv: new_rkv.kv },
                    self.result)
            ||| old_rkv == new_rkv
        }
    }

    closed spec fn id(&self) -> int {
        self.inv.constant().durable_id
    }

    closed spec fn completed(&self, c: Self::Completion) -> bool {
        &&& c.rwlock_res.id() == self.rwlock_res.id()
        &&& match c.lin_or_complete {
            Either::A(lin) => {
                &&& c.rwlock_res@ == self.rwlock_res@
                &&& lin == self.lin
            },
            Either::B(complete) => {
                &&& self.op.result_valid(self.rwlock_res@, c.rwlock_res@, self.result)
                &&& self.lin.post(complete, self.inv.constant().caller_id, self.op, self.result)
            },
        }
    }

    proof fn apply(tracked self, tracked credit: OpenInvariantCredit, tracked r: &mut GhostVarAuth<Seq<u8>>, new_state: Seq<u8>) -> (tracked result: Self::Completion) {
        use_type_invariant(&self);

        let tracked mut rwlock_res = self.rwlock_res;
        let tracked mut lin_or_complete;

        open_atomic_invariant_in_proof!(credit => &self.inv => inner => {
            inner.rwlock_auth.agree(&rwlock_res);
            r.agree(&inner.durable_res);

            let ghost old_rkv = recover_journal_then_kv::<PM, K, I, L>(r@).unwrap();
            let ghost new_rkv = recover_journal_then_kv::<PM, K, I, L>(new_state).unwrap();

            if old_rkv == new_rkv {
                // No change to durable state on disk, can't call linearizer yet.  Keep it.
                lin_or_complete = Either::A(self.lin);
            } else {
                // Committed on disk, can invoke linearizer, save completion.
                let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>{
                    ps: new_rkv.ps,
                    pm_constants: rwlock_res@.pm_constants,
                    kv: new_rkv.kv,
                };

                let tracked lin_complete = self.lin.apply(self.op, new_ckv, self.result, &mut inner.caller_auth);
                inner.rwlock_auth.update(&mut rwlock_res, new_ckv);
                lin_or_complete = Either::B(lin_complete);
            }

            r.update(&mut inner.durable_res, new_state);
        });

        OpPermComplete::<K, I, L, Op, Lin>{
            rwlock_res: rwlock_res,
            lin_or_complete: lin_or_complete,
        }
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
struct NoopPerm<PM, K, I, L>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    inv: Arc<AtomicInvariant<ConcurrentKvStoreInvPred,
                             ConcurrentKvStoreInvState<PM, K, I, L>,
                             ConcurrentKvStoreInvPred>>,
}

impl<PM, K, I, L> CheckPermission<Seq<u8>> for NoopPerm<PM, K, I, L>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type Completion = ();

    closed spec fn check_permission(&self, old_state: Seq<u8>, new_state: Seq<u8>) -> bool {
        recover_journal_then_kv::<PM, K, I, L>(old_state) == recover_journal_then_kv::<PM, K, I, L>(new_state)
    }

    closed spec fn id(&self) -> int {
        self.inv.constant().durable_id
    }

    closed spec fn completed(&self, c: Self::Completion) -> bool {
        true
    }

    proof fn apply(tracked self, tracked credit: OpenInvariantCredit, tracked r: &mut GhostVarAuth<Seq<u8>>, new_state: Seq<u8>) -> (tracked result: Self::Completion) {
        open_atomic_invariant_in_proof!(credit => &self.inv => inner => {
            r.update(&mut inner.durable_res, new_state);
        });
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
struct NoopPermFactory<PM, K, I, L>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    inv: Arc<AtomicInvariant<ConcurrentKvStoreInvPred,
                             ConcurrentKvStoreInvState<PM, K, I, L>,
                             ConcurrentKvStoreInvPred>>,
}

impl<PM, K, I, L> PermissionFactory<Seq<u8>> for NoopPermFactory<PM, K, I, L>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type Perm = NoopPerm<PM, K, I, L>;

    closed spec fn check_permission(&self, old_state: Seq<u8>, new_state: Seq<u8>) -> bool {
        NoopPerm{
            inv: self.inv.clone(),
        }.check_permission(old_state, new_state)
    }

    closed spec fn id(&self) -> int {
        NoopPerm{
            inv: self.inv.clone(),
        }.id()
    }

    proof fn grant_permission(tracked &self) -> (tracked perm: NoopPerm<PM, K, I, L>) {
        NoopPerm{
            inv: self.inv.clone(),
        }
    }

    proof fn clone(tracked &self) -> (tracked other: Self) {
        Self{
            inv: self.inv.clone(),
        }
    }
}

}
