#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::crashinv_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use std::hash::Hash;
use super::concurrentspec_t::*;
use super::impl_v::*;
use super::spec_t::*;
use super::recover_v::*;
use super::rwkv_t::*;
use vstd::tokens::frac::*;
use super::rwlock_t::{RwLockReadGuardWithPredicate, RwLockPredicate, RwLockWithPredicate, RwLockWriter};
use vstd::invariant::*;
use vstd::modes::*;
use std::sync::Arc;

verus! {

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
pub(super) struct ConcurrentKvStoreInternal<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    invariant_resource: Tracked<GhostVar<ConcurrentKvStoreView<K, I, L>>>,
    kv: UntrustedKvStoreImpl<NoopPermFactory<PM, K, I, L>, PM, K, I, L>,
}

pub(super) struct ConcurrentKvStorePredicate
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

proof fn linearize_nop<PM, K, I, L, Op, CB>(
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
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
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

exec fn maybe_commit<PM, K, I, L, Op, CB>(
    inv: Tracked<Arc<AtomicInvariant<ConcurrentKvStoreInvPred,
                                     ConcurrentKvStoreInvState<PM, K, I, L>,
                                     ConcurrentKvStoreInvPred>>>,
    pred: Ghost<ConcurrentKvStorePredicate>,
    tentative_result: Result<Op::KvResult, KvError>,
    kv_internal: &mut ConcurrentKvStoreInternal<PM, K, I, L>,
    Ghost(op): Ghost<Op>,
    Tracked(cb): Tracked<CB>,
) -> (result: (Result<Op::KvResult, KvError>, Tracked<CB::Completion>))
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        Op: MutatingOperation<K, I, L>,
        CB: MutatingLinearizer<K, I, L, Op>,
    requires
        old(kv_internal).kv.valid(),
        old(kv_internal).kv@.ps.valid(),
        old(kv_internal).kv@.ps.logical_range_gaps_policy ==
            old(kv_internal).kv@.durable.logical_range_gaps_policy,
        old(kv_internal).kv@.powerpm_id == inv@.constant().durable_id,
        old(kv_internal).invariant_resource@.id() == inv@.constant().rwlock_id,
        old(kv_internal).invariant_resource@@ == ConcurrentKvStoreView::from_kvstore_view(old(kv_internal).kv@),
        cb.pre(inv@.constant().caller_id, op),
        !cb.namespaces().contains(inv@.namespace()),
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
        inv@.constant().rwlock_id == pred@.id,
        inv@.constant().durable_id == pred@.powerpm_id,
    ensures
        pred@.inv(*kv_internal),
        cb.post(result.1@, inv@.constant().caller_id, op, result.0),
{
    match tentative_result {
        Err(e) => {
            let credit = create_open_invariant_credit();
            let completion = Tracked(linearize_nop::<PM, K, I, L, Op, CB>(
                credit.get(), inv.borrow().clone(), kv_internal.invariant_resource.borrow(), op, Err(e), cb)
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
                inv: inv.borrow().clone(),
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

            open_atomic_invariant!(inv.borrow() => inner => {
                kv_internal.kv.agree(Tracked(&inner.durable_res));

                proof {
                    inner.rwlock_auth.agree(kv_internal.invariant_resource.borrow());

                    // We can provably unwrap, because if it was None, that means
                    // the committing write predicted a crash and didn't update the
                    // durable state to linearize at the write call.  But at this
                    // point, we now know the flush succeeded and the resulting state
                    // does satisfy result_valid().
                    completion = perm_complete.complete.tracked_unwrap();
                }
            });

            (result, Tracked(completion))
        },
    }
}

trait OpParameters<K, I, L, Op>: Sized
    where
        Op: MutatingOperation<K, I, L>,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    spec fn op(self) -> Op;

    proof fn lemma_result_valid_implies_constants_unchanged(self)
        ensures
            forall |ckv_old, ckv_new, result|
                #[trigger] self.op().result_valid(ckv_old, ckv_new, result) ==> {
                    &&& ckv_old.pm_constants == ckv_new.pm_constants
                    &&& ckv_old.ps == ckv_new.ps
                },
    ;

    exec fn execute<PM>(&self, kv: &mut UntrustedKvStoreImpl<NoopPermFactory<PM, K, I, L>, PM, K, I, L>)
                        -> (result: Result<Op::KvResult, KvError>)
        where
            PM: PersistentMemoryRegion,
        requires
            old(kv).valid(),
            old(kv)@.ps.valid(),
            old(kv)@.used_key_slots == old(kv)@.durable.num_keys(),
            old(kv)@.used_list_element_slots == old(kv)@.durable.num_list_elements(),
            old(kv)@.used_transaction_operation_slots == 0,
            old(kv)@.durable == old(kv)@.tentative,
            old(kv)@.ps.logical_range_gaps_policy == old(kv)@.durable.logical_range_gaps_policy,
        ensures
            kv.valid(),
            kv@.ps == old(kv)@.ps,
            kv@.pm_constants == old(kv)@.pm_constants,
            kv@.durable == old(kv)@.durable,
            kv@.powerpm_id == old(kv)@.powerpm_id,
            ({
                let old_ckv = ConcurrentKvStoreView::<K, I, L>{ ps: old(kv)@.ps, pm_constants: old(kv)@.pm_constants,
                                                                kv: old(kv)@.tentative };
                let new_ckv = ConcurrentKvStoreView::<K, I, L>{ ps: kv@.ps, pm_constants: kv@.pm_constants,
                                                                kv: kv@.tentative };
                self.op().result_valid(old_ckv, new_ckv, result)
            }),
            match result {
                Ok(_) => true,
                Err(_) => {
                    &&& kv@.used_key_slots == kv@.durable.num_keys()
                    &&& kv@.used_list_element_slots == kv@.durable.num_list_elements()
                    &&& kv@.used_transaction_operation_slots == 0
                    &&& kv@.tentative == kv@.durable
                },
            },
    ;
}

struct CreateParameters<'a, K, I>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
{
    key: &'a K,
    item: &'a I,
}

impl<'a, K, I, L, const STRICT_SPACE: bool> OpParameters<K, I, L, CreateOp<K, I, STRICT_SPACE>>
        for CreateParameters<'a, K, I>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    spec fn op(self) -> CreateOp<K, I, STRICT_SPACE>
    {
        CreateOp::<K, I, STRICT_SPACE>{ key: *self.key, item: *self.item }
    }

    proof fn lemma_result_valid_implies_constants_unchanged(self)
    {
    }

    exec fn execute<PM>(&self, kv: &mut UntrustedKvStoreImpl<NoopPermFactory<PM, K, I, L>, PM, K, I, L>)
                        -> (result: Result<(), KvError>)
        where
            PM: PersistentMemoryRegion,
    {
        kv.tentatively_create(self.key, self.item)
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
struct ConcurrentKvStoreWriter<PM, K, I, L, Op, Params, CB>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        Op: MutatingOperation<K, I, L>,
        Params: OpParameters<K, I, L, Op>,
        CB: MutatingLinearizer<K, I, L, Op>,
{
    params: Params,
    cb: Tracked<CB>,
    pred: Ghost<ConcurrentKvStorePredicate>,
    inv: Tracked<Arc<AtomicInvariant<ConcurrentKvStoreInvPred,
                                     ConcurrentKvStoreInvState<PM, K, I, L>,
                                     ConcurrentKvStoreInvPred>>>,
    op: Ghost<core::marker::PhantomData<Op>>,
}

impl<PM, K, I, L, Op, Params, CB> ConcurrentKvStoreWriter<PM, K, I, L, Op, Params, CB>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        Op: MutatingOperation<K, I, L>,
        Params: OpParameters<K, I, L, Op>,
        CB: MutatingLinearizer<K, I, L, Op>,
{
    exec fn new(params: Params, cb: Tracked<CB>, pred: Ghost<ConcurrentKvStorePredicate>,
                inv: &Tracked<Arc<AtomicInvariant<ConcurrentKvStoreInvPred,
                                                  ConcurrentKvStoreInvState<PM, K, I, L>,
                                                  ConcurrentKvStoreInvPred>>>) -> (result: Self)
        ensures
            result.params == params,
            result.cb == cb,
            result.pred == pred,
            result.inv@ == inv@,
    {
        let tracked inv_clone = inv.borrow().clone();
        Self{ params, cb, pred, inv: Tracked(inv_clone), op: Ghost(core::marker::PhantomData) }
    }
}

impl<PM, K, I, L, Op, Params, CB>
        RwLockWriter<ConcurrentKvStoreInternal<PM, K, I, L>,
                     (Result<Op::KvResult, KvError>, Tracked<CB::Completion>),
                     ConcurrentKvStorePredicate>
        for ConcurrentKvStoreWriter<PM, K, I, L, Op, Params, CB>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        Op: MutatingOperation<K, I, L>,
        Params: OpParameters<K, I, L, Op>,
        CB: MutatingLinearizer<K, I, L, Op>,
{
    closed spec fn pred(self) -> ConcurrentKvStorePredicate
    {
        self.pred@
    }

    closed spec fn pre(self) -> bool
    {
        &&& self.cb@.pre(self.inv@.constant().caller_id, self.params.op())
        &&& !self.cb@.namespaces().contains(self.inv@.namespace())
        &&& self.inv@.constant().rwlock_id == self.pred@.id
        &&& self.inv@.constant().durable_id == self.pred@.powerpm_id
    }

    closed spec fn post(self, completion: (Result<Op::KvResult, KvError>, Tracked<CB::Completion>)) -> bool
    {
        let (exec_result, cb_completion) = completion;
        self.cb@.post(cb_completion@, self.inv@.constant().caller_id, self.params.op(), exec_result)
    }

    exec fn write(self, kv_internal: &mut ConcurrentKvStoreInternal<PM, K, I, L>)
                  -> (result_and_completion: (Result<Op::KvResult, KvError>, Tracked<CB::Completion>))
     {
        let exec_result = self.params.execute(&mut kv_internal.kv);
        proof { self.params.lemma_result_valid_implies_constants_unchanged(); }
        maybe_commit::<PM, K, I, L, Op, CB>(self.inv, self.pred, exec_result, kv_internal,
                                            Ghost(self.params.op()), self.cb)
     }
}

#[verifier::reject_recursive_types(PM)]
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
    pub(super) lock: RwLockWithPredicate<ConcurrentKvStoreInternal<PM, K, I, L>, ConcurrentKvStorePredicate>,
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
    #[verifier::type_invariant]
    spec fn typeinv(self) -> bool
    {
        &&& self.inv@.constant().rwlock_id == self.lock.pred().id
        &&& self.inv@.constant().durable_id == self.lock.pred().powerpm_id
    }
}

impl<PM, K, I, L> ConcurrentKvStoreTrait<PM, K, I, L> for ConcurrentKvStore<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    closed spec fn id(self) -> int
    {
        self.inv@.constant().caller_id
    }

    closed spec fn namespace(self) -> int
    {
        self.inv@.namespace()
    }

    open(super) spec fn spec_space_needed_for_setup(ps: SetupParameters) -> nat
    {
        UntrustedKvStoreImpl::<NoopPermFactory<PM, K, I, L>, PM, K, I, L>::spec_space_needed_for_setup(ps)
    }

    exec fn space_needed_for_setup(ps: &SetupParameters) -> (result: Result<u64, KvError>)
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

    exec fn start_with_resource(
        atomicpm: PersistentMemoryRegionAtomic<PM>,
        kvstore_id: u128,
        Tracked(inv): Tracked<Arc<AtomicInvariant::<ConcurrentKvStoreInvPred, ConcurrentKvStoreInvState<PM, K, I, L>, ConcurrentKvStoreInvPred>>>,
        Tracked(rwlock_res): Tracked<GhostVar<ConcurrentKvStoreView<K, I, L>>>,
    ) -> (result: Result<Self, KvError>)
    {
        let tracked mut rwlock_res = rwlock_res;

        open_atomic_invariant!(&inv => inner => {
            atomicpm.agree(Tracked(&inner.durable_res));

            proof {
                inner.rwlock_auth.update(&mut rwlock_res, inner.caller_auth@);
            }
        });

        let ghost mut recovered_state = RecoveredKvStore::<K, I, L>{
            ps: rwlock_res@.ps,
            kv: rwlock_res@.kv,
        };

        let tracked perm_factory = NoopPermFactory::<PM, K, I, L>{
            inv: inv.clone(),
        };

        let powerpm = PoWERPersistentMemoryRegion::new_atomic(atomicpm);
        let kv = match UntrustedKvStoreImpl::<NoopPermFactory<PM, K, I, L>, PM, K, I, L>::start(
            powerpm, kvstore_id, Ghost(recovered_state), Tracked(perm_factory)
        ) {
            Ok(kv) => kv,
            Err(e) => { return Err(e); },
        };

        let ghost pred = ConcurrentKvStorePredicate{
            id: rwlock_res.id(),
            powerpm_id: powerpm.id(),
        };
        let kv_internal = ConcurrentKvStoreInternal::<PM, K, I, L>{
            invariant_resource: Tracked(rwlock_res),
            kv: kv,
        };
        assert(pred.inv(kv_internal));
        let lock = RwLockWithPredicate::<ConcurrentKvStoreInternal<PM, K, I, L>, ConcurrentKvStorePredicate>::new(
            kv_internal, Ghost(pred)
        );
        let selfish = Self{
            lock: lock,
            inv: Tracked(inv),
        };
        Ok(selfish)
    }

    exec fn read_item<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<I, KvError>, Tracked<CB::Completion>))
        where
            CB: ReadLinearizer<K, I, L, ReadItemOp<K>>,
    {
        proof { use_type_invariant(self); }
        let read_handle = self.lock.read();
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
        (result, Tracked(completion))
    }

    exec fn get_keys<CB: ReadLinearizer<K, I, L, GetKeysOp>>(
        &self,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<Vec<K>, KvError>, Tracked<CB::Completion>))
    {
        proof { use_type_invariant(self); }
        let read_handle = self.lock.read();
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
        (result, Tracked(completion))
    }

    exec fn read_item_and_list<CB: ReadLinearizer<K, I, L, ReadItemAndListOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(I, Vec<L>), KvError>, Tracked<CB::Completion>))
    {
        proof { use_type_invariant(self); }
        let read_handle = self.lock.read();
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
        (result, Tracked(completion))
    }

    exec fn read_list<CB: ReadLinearizer<K, I, L, ReadListOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<Vec<L>, KvError>, Tracked<CB::Completion>))
    {
        proof { use_type_invariant(self); }
        let read_handle = self.lock.read();
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
        (result, Tracked(completion))
    }

    exec fn get_list_length<CB: ReadLinearizer<K, I, L, GetListLengthOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<usize, KvError>, Tracked<CB::Completion>))
    {
        proof { use_type_invariant(self); }
        let read_handle = self.lock.read();
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
        (result, Tracked(completion))
    }

    exec fn create<'a, CB, const STRICT_SPACE: bool>(
        &self,
        key: &'a K,
        item: &'a I,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, CreateOp<K, I, STRICT_SPACE>>,
    {
        proof { use_type_invariant(self); }
        let mut writer =
            ConcurrentKvStoreWriter::<PM, K, I, L, CreateOp<K, I, STRICT_SPACE>, CreateParameters<'a, K, I>, CB>::new(
                CreateParameters::<'a, K, I>{ key, item },
                Tracked(cb),
                Ghost(self.lock.pred()),
                &self.inv
            );
        self.lock.write(writer)
    }

    #[verifier::external_body]
    exec fn update_item<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, UpdateItemOp<K, I, STRICT_SPACE>>,
    {
        assume(false);
        unimplemented!()
            /*
        proof { use_type_invariant(self); }
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = UpdateItemOp::<K, I, STRICT_SPACE>{ key: *key, item: *item };
        let result = kv_internal.kv.tentatively_update_item(key, item);
        let result = self.maybe_commit::<UpdateItemOp<K, I, STRICT_SPACE>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
            */
    }

    #[verifier::external_body]
    exec fn delete<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, DeleteOp<K>>,
    {
        assume(false);
        unimplemented!()
            /*
        proof { use_type_invariant(self); }
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = DeleteOp::<K>{ key: *key };
        let result = kv_internal.kv.tentatively_delete(key);
        let result = self.maybe_commit::<DeleteOp::<K>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
        assume(false);
        unimplemented!()
            */
    }

    #[verifier::external_body]
    exec fn append_to_list<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        new_list_element: L,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, AppendToListOp<K, L, STRICT_SPACE>>,
    {
        assume(false);
        unimplemented!()
            /*
        proof { use_type_invariant(self); }
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = AppendToListOp::<K, L, STRICT_SPACE>{ key: *key, new_list_element };
        let result = kv_internal.kv.tentatively_append_to_list(key, new_list_element);
        let result = self.maybe_commit::<AppendToListOp::<K, L, STRICT_SPACE>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
         */
    }

    #[verifier::external_body]
    exec fn append_to_list_and_update_item<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        new_list_element: L,
        new_item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, AppendToListAndUpdateItemOp<K, I, L, STRICT_SPACE>>,
    {
        assume(false);
        unimplemented!()
            /*
        proof { use_type_invariant(self); }
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = AppendToListAndUpdateItemOp::<K, I, L, STRICT_SPACE>{ key: *key, new_list_element, new_item: *new_item };
        let result = kv_internal.kv.tentatively_append_to_list_and_update_item(key, new_list_element, new_item);
        let result = self.maybe_commit::<AppendToListAndUpdateItemOp<K, I, L, STRICT_SPACE>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
         */
    }

    #[verifier::external_body]
    exec fn update_list_element_at_index<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        idx: usize,
        new_list_element: L,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, UpdateListElementAtIndexOp<K, L, STRICT_SPACE>>,
    {
        assume(false);
        unimplemented!()
            /*
        proof { use_type_invariant(self); }
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = UpdateListElementAtIndexOp::<K, L, STRICT_SPACE>{ key: *key, idx, new_list_element };
        let result = kv_internal.kv.tentatively_update_list_element_at_index(key, idx, new_list_element);
        let result = self.maybe_commit::<UpdateListElementAtIndexOp<K, L, STRICT_SPACE>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
         */
    }

    #[verifier::external_body]
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
    {
        assume(false);
        unimplemented!()
            /*
        proof { use_type_invariant(self); }
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = UpdateListElementAtIndexAndItemOp::<K, I, L, STRICT_SPACE>{ key: *key, idx, new_list_element,
                                                                     new_item: *new_item };
        let result = kv_internal.kv.tentatively_update_list_element_at_index_and_item(
            key, idx, new_list_element, new_item
        );
        let result = self.maybe_commit::<UpdateListElementAtIndexAndItemOp<K, I, L, STRICT_SPACE>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
         */
    }

    #[verifier::external_body]
    exec fn trim_list<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        trim_length: usize,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, TrimListOp<K, STRICT_SPACE>>,
    {
        assume(false);
        unimplemented!()
            /*
        proof { use_type_invariant(self); }
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = TrimListOp::<K, STRICT_SPACE>{ key: *key, trim_length };
        let result = kv_internal.kv.tentatively_trim_list(key, trim_length);
        let result = self.maybe_commit::<TrimListOp<K, STRICT_SPACE>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
         */
    }

    #[verifier::external_body]
    exec fn trim_list_and_update_item<CB, const STRICT_SPACE: bool>(
        &self,
        key: &K,
        trim_length: usize,
        new_item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, TrimListAndUpdateItemOp<K, I, STRICT_SPACE>>,
    {
        assume(false);
        unimplemented!()
            /*
        proof { use_type_invariant(self); }
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = TrimListAndUpdateItemOp::<K, I, STRICT_SPACE>{ key: *key, trim_length, new_item: *new_item };
        let result = kv_internal.kv.tentatively_trim_list_and_update_item(key, trim_length, new_item);
        let result = self.maybe_commit::<TrimListAndUpdateItemOp<K, I, STRICT_SPACE>, CB>(result, &mut kv_internal, Ghost(op), Tracked(cb));
        write_handle.release_write(kv_internal);
        result
         */
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
    complete: Option<Lin::Completion>,
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

    closed spec fn permits(&self, old_state: Seq<u8>, new_state: Seq<u8>) -> bool {
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
        &&& match c.complete {
            None => {
                &&& c.rwlock_res@ == self.rwlock_res@
                &&& !self.op.result_valid(self.rwlock_res@, c.rwlock_res@, self.result)
            },
            Some(complete) => {
                &&& self.op.result_valid(self.rwlock_res@, c.rwlock_res@, self.result)
                &&& self.lin.post(complete, self.inv.constant().caller_id, self.op, self.result)
            },
        }
    }

    proof fn apply(tracked self, tracked credit: OpenInvariantCredit, tracked r: &mut GhostVarAuth<Seq<u8>>, new_state: Seq<u8>) -> (tracked result: Self::Completion) {
        use_type_invariant(&self);

        let tracked mut rwlock_res = self.rwlock_res;
        let tracked mut complete = None;

        open_atomic_invariant_in_proof!(credit => &self.inv => inner => {
            inner.rwlock_auth.agree(&rwlock_res);
            r.agree(&inner.durable_res);

            let ghost old_rkv = recover_journal_then_kv::<PM, K, I, L>(r@).unwrap();
            let ghost new_rkv = recover_journal_then_kv::<PM, K, I, L>(new_state).unwrap();

            let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>{
                ps: new_rkv.ps,
                pm_constants: rwlock_res@.pm_constants,
                kv: new_rkv.kv,
            };

            if !self.op.result_valid( rwlock_res@, new_ckv, self.result) {
                // No change to durable state on disk, and moreover, no change
                // is not valid for this op.  Can't call linearizer, but this
                // case corresponds to a predicted crash; if we get all the way
                // to flush() in commit, we can turn this into a contradiction.
            } else {
                complete = Some(self.lin.apply(self.op, new_ckv, self.result, &mut inner.caller_auth));
                inner.rwlock_auth.update(&mut rwlock_res, new_ckv);
            }

            r.update(&mut inner.durable_res, new_state);
        });

        OpPermComplete::<K, I, L, Op, Lin>{
            rwlock_res: rwlock_res,
            complete: complete,
        }
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
pub(super) struct NoopPerm<PM, K, I, L>
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

    closed spec fn permits(&self, old_state: Seq<u8>, new_state: Seq<u8>) -> bool {
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
            assert(self.inv.inv(inner));
            r.update(&mut inner.durable_res, new_state);
        });
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
pub(super) struct NoopPermFactory<PM, K, I, L>
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

    closed spec fn permits(&self, old_state: Seq<u8>, new_state: Seq<u8>) -> bool {
        NoopPerm{
            inv: self.inv.clone(),
        }.permits(old_state, new_state)
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
