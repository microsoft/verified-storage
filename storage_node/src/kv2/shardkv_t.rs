#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::tokens::frac::*;
use vstd::invariant::*;

use std::sync::Arc;
use std::marker::PhantomData;
use std::hash::{Hash, Hasher, DefaultHasher};
use std::collections::VecDeque;

use crate::pmem::crashinv_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;

use super::concurrentspec_t::*;
use super::spec_t::*;
use super::rwkv_t;
use super::rwkv_t::*;
use super::rwkv_v::*;
use super::shardkv_v::*;

verus! {

pub uninterp spec fn default_hash_of_key<K: Hash>(k: K) -> u64;

#[verifier::external_body]
pub exec fn hash_key<K: Hash>(k: &K) -> (result: u64)
    ensures
        result == default_hash_of_key(*k)
{
    let mut hasher = DefaultHasher::new();
    k.hash(&mut hasher);
    hasher.finish()
}

pub trait ShardedKvStoreTrait<PM, K, I, L> : Sized
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    spec fn namespaces(self) -> Set<int>;
    spec fn id(self) -> int;

    exec fn setup(
        nshards: usize,
        Tracked(shard_res): Tracked<Map<int, GhostVar<ConcurrentKvStoreView::<K, I, L>>>>,
        Ghost(ps): Ghost<SetupParameters>,
        Ghost(pm_constants): Ghost<PersistentMemoryConstants>,
        Ghost(namespace): Ghost<int>,
    ) -> (result: (Tracked<AtomicInvariant::<ShardingPredicate, ShardStates<K, I, L>, ShardingPredicate>>,
                   Tracked<GhostVar<ConcurrentKvStoreView::<K, I, L>>>))
        requires
            nshards >= 1,
            forall |shard| 0 <= shard < nshards ==> #[trigger] shard_res.contains_key(shard),
            forall |shard| #[trigger] shard_res.contains_key(shard) ==> {
                &&& shard_res[shard]@.ps == ps
                &&& shard_res[shard]@.pm_constants == pm_constants
                &&& shard_res[shard]@.kv == RecoveredKvStore::<K, I, L>::init(ps).kv
            }
        ensures
            result.0@.namespace() == namespace,
            result.0@.constant().nshard() == nshards,
            forall |shard| 0 <= shard < nshards ==>
                #[trigger] result.0@.constant().shard_ids[shard] == shard_res[shard].id(),
            result.1@.id() == result.0@.constant().combined_id,
            result.1@@ == (ConcurrentKvStoreView::<K, I, L>{
                ps: ps,
                pm_constants: pm_constants,
                kv: RecoveredKvStore::<K, I, L>::init(ps).kv,
            });

    exec fn start(
        shard_kvs: Vec<ConcurrentKvStore<PM, K, I, L>>,
        Tracked(inv): Tracked<Arc<AtomicInvariant::<ShardingPredicate, ShardStates<K, I, L>, ShardingPredicate>>>,
        Ghost(shard_namespace): Ghost<int>,
    ) -> (result: Self)
        requires
            shard_kvs@.len() >= 1,
            shard_kvs@.len() == inv.constant().nshard(),
            forall |shard: int| #![all_triggers] 0 <= shard < shard_kvs@.len() ==> {
                &&& shard_kvs@[shard].namespace() == shard_namespace
                &&& shard_kvs@[shard].id() == inv.constant().shard_ids[shard]
            },
            vstd::std_specs::hash::obeys_key_model::<K>(),
            shard_namespace != inv.namespace(),
        ensures
            result.id() == inv.constant().combined_id,
            result.namespaces() == set![inv.namespace(), shard_namespace];

    exec fn read_item<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<I, KvError>, Tracked<CB::Completion>))
        where
            CB: ReadLinearizer<K, I, L, ReadItemOp<K>>,
        requires
            cb.pre(self.id(), ReadItemOp{ key: *key }),
            cb.namespaces().disjoint(self.namespaces()),
        ensures
            cb.post(result.1@, self.id(), ReadItemOp{ key: *key }, result.0);

    exec fn read_item_and_list<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(I, Vec<L>), KvError>, Tracked<CB::Completion>))
        where
            CB: ReadLinearizer<K, I, L, ReadItemAndListOp<K>>,
        requires
            cb.pre(self.id(), ReadItemAndListOp{ key: *key }),
            cb.namespaces().disjoint(self.namespaces()),
        ensures
            cb.post(result.1@, self.id(), ReadItemAndListOp{ key: *key }, result.0);

    exec fn read_list<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<Vec<L>, KvError>, Tracked<CB::Completion>))
        where
            CB: ReadLinearizer<K, I, L, ReadListOp<K>>,
        requires
            cb.pre(self.id(), ReadListOp{ key: *key }),
            cb.namespaces().disjoint(self.namespaces()),
        ensures
            cb.post(result.1@, self.id(), ReadListOp{ key: *key }, result.0);

    exec fn get_list_length<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<usize, KvError>, Tracked<CB::Completion>))
        where
            CB: ReadLinearizer<K, I, L, GetListLengthOp<K>>,
        requires
            cb.pre(self.id(), GetListLengthOp{ key: *key }),
            cb.namespaces().disjoint(self.namespaces()),
        ensures
            cb.post(result.1@, self.id(), GetListLengthOp{ key: *key }, result.0);

    exec fn create<CB>(
        &self,
        key: &K,
        item: &I,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, CreateOp<K, I, false>>,
        requires
            cb.pre(self.id(), CreateOp{ key: *key, item: *item }),
            cb.namespaces().disjoint(self.namespaces()),
        ensures
            cb.post(result.1@, self.id(), CreateOp{ key: *key, item: *item }, result.0);

    exec fn update_item<CB>(
        &self,
        key: &K,
        item: &I,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, UpdateItemOp<K, I, false>>,
        requires
            cb.pre(self.id(), UpdateItemOp{ key: *key, item: *item }),
            cb.namespaces().disjoint(self.namespaces()),
        ensures
            cb.post(result.1@, self.id(), UpdateItemOp{ key: *key, item: *item }, result.0);

    exec fn delete<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, DeleteOp<K>>,
        requires
            cb.pre(self.id(), DeleteOp{ key: *key }),
            cb.namespaces().disjoint(self.namespaces()),
        ensures
            cb.post(result.1@, self.id(), DeleteOp{ key: *key }, result.0);

    exec fn append_to_list<CB>(
        &self,
        key: &K,
        new_list_element: L,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, AppendToListOp<K, L, false>>,
        requires
            cb.pre(self.id(), AppendToListOp{ key: *key, new_list_element }),
            cb.namespaces().disjoint(self.namespaces()),
        ensures
            cb.post(result.1@, self.id(), AppendToListOp{ key: *key, new_list_element }, result.0);

    exec fn append_to_list_and_update_item<CB>(
        &self,
        key: &K,
        new_list_element: L,
        new_item: &I,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, AppendToListAndUpdateItemOp<K, I, L, false>>,
        requires
            cb.pre(self.id(), AppendToListAndUpdateItemOp{ key: *key, new_list_element, new_item: *new_item }),
            cb.namespaces().disjoint(self.namespaces()),
        ensures
            cb.post(result.1@, self.id(), AppendToListAndUpdateItemOp{ key: *key, new_list_element, new_item: *new_item }, result.0);

    exec fn update_list_element_at_index<CB>(
        &self,
        key: &K,
        idx: usize,
        new_list_element: L,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, UpdateListElementAtIndexOp<K, L, false>>,
        requires
            cb.pre(self.id(), UpdateListElementAtIndexOp{ key: *key, idx, new_list_element }),
            cb.namespaces().disjoint(self.namespaces()),
        ensures
            cb.post(result.1@, self.id(), UpdateListElementAtIndexOp{ key: *key, idx, new_list_element }, result.0);

    exec fn update_list_element_at_index_and_item<CB>(
        &self,
        key: &K,
        idx: usize,
        new_list_element: L,
        new_item: &I,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, UpdateListElementAtIndexAndItemOp<K, I, L, false>>,
        requires
            cb.pre(self.id(), UpdateListElementAtIndexAndItemOp{ key: *key, idx, new_list_element, new_item: *new_item }),
            cb.namespaces().disjoint(self.namespaces()),
        ensures
            cb.post(result.1@, self.id(), UpdateListElementAtIndexAndItemOp{ key: *key, idx, new_list_element, new_item: *new_item }, result.0);

    exec fn trim_list<CB>(
        &self,
        key: &K,
        trim_length: usize,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, TrimListOp<K, false>>,
        requires
            cb.pre(self.id(), TrimListOp{ key: *key, trim_length }),
            cb.namespaces().disjoint(self.namespaces()),
        ensures
            cb.post(result.1@, self.id(), TrimListOp{ key: *key, trim_length }, result.0);

    exec fn trim_list_and_update_item<CB>(
        &self,
        key: &K,
        trim_length: usize,
        new_item: &I,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, TrimListAndUpdateItemOp<K, I, false>>,
        requires
            cb.pre(self.id(), TrimListAndUpdateItemOp{ key: *key, trim_length, new_item: *new_item }),
            cb.namespaces().disjoint(self.namespaces()),
        ensures
            cb.post(result.1@, self.id(), TrimListAndUpdateItemOp{ key: *key, trim_length, new_item: *new_item }, result.0);
}

pub exec fn setup<PM, K, I, L>(
    pms: VecDeque<PM>,
    ps: &SetupParameters,
    Ghost(pm_constants): Ghost<PersistentMemoryConstants>,
    Ghost(namespace): Ghost<int>,
    Ghost(shard_namespace): Ghost<int>,
) -> (result: Result<(ShardedKvStore::<PM, K, I, L>,
                      Tracked<GhostVar<ConcurrentKvStoreView::<K, I, L>>>),
                     KvError>)
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
    requires
        pms@.len() > 0,
        forall |i| 0 <= i < pms@.len() ==> {
            &&& #[trigger] pms@[i].inv()
            &&& pms@[i].constants() == pm_constants
        },
        namespace != shard_namespace,
        vstd::std_specs::hash::obeys_key_model::<K>(),
    ensures
        match result {
            Ok((kv, res)) => {
                &&& kv.id() == res@.id()
                &&& kv.namespaces() == set![namespace, shard_namespace]
                &&& res@@ == ConcurrentKvStoreView::<K, I, L>{
                        ps: *ps,
                        pm_constants: pm_constants,
                        kv: RecoveredKvStore::<K, I, L>::init(*ps).kv,
                    }
            },
            Err(KvError::InvalidParameter) => !ps.valid(),
            Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
            Err(KvError::OutOfSpace) => exists |i| 0 <= i < pms@.len() && #[trigger] pms@[i]@.len() < ConcurrentKvStore::<PM, K, I, L>::spec_space_needed_for_setup(*ps),
            Err(KvError::CRCMismatch) => !pm_constants.impervious_to_corruption(),
            Err(_) => false,
        },
{
    broadcast use vstd::std_specs::vecdeque::group_vec_dequeue_axioms;

    let nshards = pms.len();
    let mut pms_mut = pms;
    let mut shard_kvs: Vec<ConcurrentKvStore::<PM, K, I, L>> = Vec::new();
    let tracked mut shard_res = Map::<int, GhostVar<ConcurrentKvStoreView::<K, I, L>>>::tracked_empty();

    for idx in 0..nshards
        invariant
            nshards > 0,
            pms@.len() == nshards,
            pms_mut@ =~= pms@.subrange(idx as int, pms@.len() as int),
            forall |i| #![all_triggers] 0 <= i < pms@.len() ==> {
                &&& pms@[i].inv()
                &&& pms@[i].constants() == pm_constants
            },
            forall |shard| 0 <= shard < idx ==> #[trigger] shard_res.contains_key(shard),
            forall |shard| #[trigger] shard_res.contains_key(shard) ==> {
                &&& shard_res[shard]@.ps == *ps
                &&& shard_res[shard]@.pm_constants == pm_constants
                &&& shard_res[shard]@.kv == RecoveredKvStore::<K, I, L>::init(*ps).kv
            },
            shard_kvs@.len() == idx,
            forall |shard| #![all_triggers] 0 <= shard < shard_kvs@.len() ==> {
                &&& shard_kvs@[shard].namespace() == shard_namespace
                &&& shard_kvs@[shard].id() == shard_res[shard].id()
            },
            vstd::std_specs::hash::obeys_key_model::<K>(),
    {
        // Force trigger.
        assert(pms@[idx as int].inv());
        let pm = pms_mut.pop_front().unwrap();

        match rwkv_t::setup::<PM, K, I, L>(pm, ps, Ghost(shard_namespace)) {
            Err(e) => return Err(e),
            Ok((ckv, gvar)) => {
                shard_kvs.push(ckv);
                proof {
                    shard_res.tracked_insert(idx as int, gvar.get());
                }
            },
        }
    }

    let (Tracked(inv), Tracked(gvar)) = ShardedKvStore::<PM, K, I, L>::setup(
        nshards, Tracked(shard_res), Ghost(*ps), Ghost(pm_constants), Ghost(namespace)
    );
    let tracked inv: Arc<AtomicInvariant::<ShardingPredicate, ShardStates<K, I, L>, ShardingPredicate>> = Arc::new(inv);

    proof {
        hold_until_crash(inv.clone());
    }

    Ok((ShardedKvStore::<PM, K, I, L>::start(shard_kvs, Tracked(inv), Ghost(shard_namespace)),
        Tracked(gvar)))
}

pub exec fn recover<PM, K, I, L>(
    pms: VecDeque<PM>,
    kvstore_id: u128,
    Ghost(pm_constants): Ghost<PersistentMemoryConstants>,
    Ghost(id): Ghost<int>,
    Ghost(namespace): Ghost<int>,
    Ghost(shard_namespace): Ghost<int>,
) -> (result: Result<ShardedKvStore::<PM, K, I, L>, KvError>)
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
    requires
        pms@.len() > 0,
        forall |i| #![all_triggers] 0 <= i < pms@.len() ==> {
            &&& pms@[i].inv()
            &&& pms@[i].constants() == pm_constants
        },
        vstd::std_specs::hash::obeys_key_model::<K>(),
        namespace != shard_namespace,
    ensures
        match result {
            Ok(kv) => {
                &&& kv.id() == id
                &&& kv.namespaces() == set![namespace, shard_namespace]
            },
            Err(KvError::CRCMismatch) => !pm_constants.impervious_to_corruption(),
            Err(KvError::WrongKvStoreId{ requested_id, actual_id }) => {
               &&& requested_id == kvstore_id
            },
            Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
            Err(_) => false,
        },
{
    broadcast use vstd::std_specs::vecdeque::group_vec_dequeue_axioms;

    let nshards = pms.len();
    let mut pms_mut = pms;
    let mut shard_kvs: Vec<ConcurrentKvStore::<PM, K, I, L>> = Vec::new();
    let ghost mut shard_ids = Seq::empty();

    for idx in 0..nshards
        invariant
            nshards > 0,
            pms@.len() == nshards,
            pms_mut@ =~= pms@.subrange(idx as int, pms@.len() as int),
            forall |i| #![all_triggers] 0 <= i < pms@.len() ==> {
                &&& pms@[i].inv()
                &&& pms@[i].constants() == pm_constants
            },
            shard_ids.len() == idx,
            shard_kvs@.len() == idx,
            forall |shard| #![all_triggers] 0 <= shard < shard_kvs@.len() ==> {
                &&& shard_kvs@[shard].namespace() == shard_namespace
                &&& shard_kvs@[shard].id() == shard_ids[shard]
            },
            vstd::std_specs::hash::obeys_key_model::<K>(),
            namespace != shard_namespace,
    {
        // Force trigger.
        assert(pms@[idx as int].inv());
        let pm = pms_mut.pop_front().unwrap();

        // There was some shard ID before crash; it doesn't matter what it was.
        let ghost shard_id: int = arbitrary();

        match rwkv_t::recover(pm, kvstore_id, Ghost(shard_id), Ghost(shard_namespace)) {
            Err(e) => return Err(e),
            Ok(ckv) => {
                shard_kvs.push(ckv);
                proof {
                    shard_ids = shard_ids.push(shard_id);
                }
            },
        }
    }

    let tracked crashinv = InvariantRecoverer::new(ShardingPredicate{
        shard_ids: shard_ids,
        combined_id: id,
        pm_constants: pm_constants,
    }, namespace);

    assume(crashinv.held_before_crash());
    let tracked inv = crashinv.get();
    let tracked inv: Arc<AtomicInvariant::<ShardingPredicate, ShardStates<K, I, L>, ShardingPredicate>> = Arc::new(inv);

    proof {
        hold_until_crash(inv.clone());
    }

    Ok(ShardedKvStore::<PM, K, I, L>::start(shard_kvs, Tracked(inv), Ghost(shard_namespace)))
}

}
