#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use std::hash::{Hash, Hasher, DefaultHasher};
use super::concurrentspec_t::*;
use super::impl_v::*;
use super::spec_t::*;
use super::rwkv_t::*;
use super::rwkv_v::*;
use super::shardkv_t::*;
use vstd::invariant::*;
use vstd::pcm::frac::*;
use std::sync::Arc;
use std::marker::PhantomData;
use vstd::modes::*;
use std::collections::VecDeque;
use super::recover_v::*;

verus! {

spec fn shard_of_key<K: Hash>(k: K, nshards: int) -> int {
    default_hash_of_key(k) as int % nshards
}

spec fn keys_match_shard<K: Hash, I, L>(kv: AtomicKvStore<K, I, L>, shard: int, nshards: int) -> bool
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    forall |k| #[trigger] kv.m.contains_key(k) ==> shard_of_key(k, nshards) == shard
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
struct ShardState<K, I, L>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    kv_state: GhostVar<ConcurrentKvStoreView::<K, I, L>>,
}

impl<K, I, L> ShardState<K, I, L>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    spec fn valid(self, kv_id: int, shard: int, nshards: int, combined: ConcurrentKvStoreView<K, I, L>) -> bool {
        &&& self.kv_state.id() == kv_id
        &&& keys_match_shard(self.kv_state@.kv, shard, nshards)
        &&& self.kv_state@.ps == combined.ps
        &&& self.kv_state@.pm_constants == combined.pm_constants
        &&& self.kv_state@.kv.logical_range_gaps_policy == combined.kv.logical_range_gaps_policy
        &&& forall |k| #[trigger] shard_of_key(k, nshards) == shard ==> self.kv_state@.kv[k] == #[trigger] combined.kv[k]
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
pub struct ShardStates<K, I, L>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    shards: Map<int, ShardState<K, I, L>>,
    combined: GhostVarAuth<ConcurrentKvStoreView::<K, I, L>>,
}

pub struct ShardingPredicate
{
    pub shard_ids: Seq<int>,
    pub combined_id: int,
    pub pm_constants: PersistentMemoryConstants,
}

impl ShardingPredicate {
    pub open spec fn nshard(self) -> int {
        self.shard_ids.len() as int
    }
}

impl<K, I, L> InvariantPredicate<ShardingPredicate, ShardStates<K, I, L>> for ShardingPredicate
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    closed spec fn inv(k: ShardingPredicate, inner: ShardStates<K, I, L>) -> bool {
        &&& k.nshard() >= 1
        &&& inner.combined.id() == k.combined_id
        &&& inner.combined@.pm_constants == k.pm_constants
        &&& forall |shard| 0 <= shard < k.nshard() ==> #[trigger] inner.shards.contains_key(shard)
        &&& forall |shard| #[trigger] inner.shards.contains_key(shard) ==> {
            &&& 0 <= shard < k.nshard()
            &&& inner.shards[shard].valid(k.shard_ids[shard], shard, k.nshard(), inner.combined@)
        }
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
pub struct ShardedKvStore<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    nshard: u64,
    kv: Vec<ConcurrentKvStore<PM, K, I, L>>,
    inv: Tracked<Arc<AtomicInvariant<ShardingPredicate, ShardStates<K, I, L>, ShardingPredicate>>>,
    shard_namespace: Ghost<int>,
}

impl<PM, K, I, L> ShardedKvStore<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    #[verifier::type_invariant]
    pub closed spec fn typeinv(self) -> bool {
        &&& self.inv@.constant().nshard() == self.nshard as int
        &&& self.nshard as int == self.kv.len()
        &&& self.nshard >= 1
        &&& forall |shard| 0 <= shard < self.kv.len() ==>
                #[trigger] self.kv[shard].id() == self.inv@.constant().shard_ids[shard]
        &&& forall |shard| 0 <= shard < self.kv.len() ==>
                #[trigger] self.kv[shard].namespace() == self.shard_namespace@
        &&& vstd::std_specs::hash::obeys_key_model::<K>()
        &&& self.shard_namespace@ != self.inv@.namespace()
    }

    spec fn shard_of_key(self, k: K) -> int {
        shard_of_key(k, self.nshard as int)
    }

    exec fn key_to_shard(&self, k: &K) -> (result: usize)
        ensures
            result == self.shard_of_key(*k)
    {
        proof { use_type_invariant(self); }
        let h = hash_key(k);
        (h % self.nshard) as usize
    }

    exec fn read_linearizer<Op, CB>(
        &self,
        op: Op,
        Tracked(cb): Tracked<CB>,
    ) -> (shardcb: Tracked<ShardedReadLinearizer::<K, I, L, Op, CB>>)
        where
            Op: SingleKeyReadOnlyOperation<K, I, L>,
            CB: ReadLinearizer<K, I, L, Op>,
        requires
            cb.pre(self.id(), op),
            cb.namespaces().disjoint(self.namespaces()),
        ensures
            shardcb@.pre(self.kv[shard_of_key(op.key(), self.nshard as int)].id(), op),
            !shardcb@.namespaces().contains(self.shard_namespace@),
            forall |complete, id, result| #[trigger] shardcb@.post(complete, id, op, result)
                ==> cb.post(complete, self.inv@.constant().combined_id, op, result),
    {
        proof { use_type_invariant(self); }
        let Tracked(credit) = create_open_invariant_credit();
        let tracked shardcb = ShardedReadLinearizer::<K, I, L, Op, CB>{
            inv: self.inv.borrow().clone(),
            lin: cb,
            credit: credit,
            shard: self.shard_of_key(op.key()),
            __phantom: PhantomData,
        };
        Tracked(shardcb)
    }

    exec fn mut_linearizer<Op, CB>(
        &self,
        op: Op,
        Tracked(cb): Tracked<CB>,
    ) -> (shardcb: Tracked<ShardedMutatingLinearizer::<K, I, L, Op, CB>>)
        where
            Op: SingleKeyMutatingOperation<K, I, L>,
            CB: MutatingLinearizer<K, I, L, Op>,
        requires
            cb.pre(self.id(), op),
            cb.namespaces().disjoint(self.namespaces()),
            forall |old_state, new_state, result| #[trigger] op.result_valid(old_state, new_state, result) ==> {
                &&& old_state.ps == new_state.ps
                &&& old_state.pm_constants == new_state.pm_constants
                &&& old_state.kv.logical_range_gaps_policy == new_state.kv.logical_range_gaps_policy
                &&& forall |k| k != op.key() ==> old_state.kv[k] == #[trigger] new_state.kv[k]
            },
        ensures
            shardcb@.pre(self.kv[shard_of_key(op.key(), self.nshard as int)].id(), op),
            !shardcb@.namespaces().contains(self.shard_namespace@),
            forall |complete, id, result| #[trigger] shardcb@.post(complete, id, op, result)
                ==> cb.post(complete, self.inv@.constant().combined_id, op, result),
    {
        proof { use_type_invariant(self); }
        let Tracked(credit) = create_open_invariant_credit();
        let tracked shardcb = ShardedMutatingLinearizer::<K, I, L, Op, CB>{
            inv: self.inv.borrow().clone(),
            lin: cb,
            credit: credit,
            shard: self.shard_of_key(op.key()),
            __phantom: PhantomData,
        };
        Tracked(shardcb)
    }
}

impl<PM, K, I, L> ShardedKvStoreTrait<PM, K, I, L> for ShardedKvStore<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    closed spec fn namespaces(self) -> Set<int> {
        set![self.inv@.namespace(), self.shard_namespace@]
    }

    closed spec fn id(self) -> int {
        self.inv@.constant().combined_id
    }

    exec fn setup(
        nshards: usize,
        Tracked(shard_res): Tracked<Map<int, GhostVar<ConcurrentKvStoreView::<K, I, L>>>>,
        Ghost(ps): Ghost<SetupParameters>,
        Ghost(pm_constants): Ghost<PersistentMemoryConstants>,
        Ghost(namespace): Ghost<int>,
    ) -> (result: (Tracked<AtomicInvariant::<ShardingPredicate, ShardStates<K, I, L>, ShardingPredicate>>,
                   Tracked<GhostVar<ConcurrentKvStoreView::<K, I, L>>>))
    {
        let ghost shard_res_old = shard_res;
        let ghost combined_state = ConcurrentKvStoreView::<K, I, L>{
            ps: ps,
            pm_constants: pm_constants,
            kv: RecoveredKvStore::<K, I, L>::init(ps).kv,
        };

        let tracked (combined_auth, combined_res) = GhostVarAuth::new(combined_state);

        let ghost mut pred = ShardingPredicate{
            shard_ids: Seq::empty(),
            combined_id: combined_auth.id(),
            pm_constants: pm_constants,
        };

        let tracked mut shard_res = shard_res;
        let tracked mut shardstates = ShardStates::<K, I, L>{
            shards: Map::<int, ShardState<K, I, L>>::tracked_empty(),
            combined: combined_auth,
        };

        for idx in 0..nshards
            invariant
                pred.shard_ids.len() == idx,
                pred.combined_id == shardstates.combined.id(),
                pred.combined_id == combined_res.id(),
                pred.pm_constants == shardstates.combined@.pm_constants,
                forall |shard| 0 <= shard < idx ==>
                    #[trigger] pred.shard_ids[shard] == shard_res_old[shard].id(),
                shardstates.combined@ == (ConcurrentKvStoreView::<K, I, L>{
                    ps: ps,
                    pm_constants: pm_constants,
                    kv: RecoveredKvStore::<K, I, L>::init(ps).kv,
                }),
                forall |shard| idx <= shard < nshards ==> #[trigger] shard_res.contains_key(shard),
                forall |shard| #[trigger] shard_res.contains_key(shard) ==> {
                    &&& shard_res[shard] == shard_res_old[shard]
                    &&& shard_res[shard]@.ps == ps
                    &&& shard_res[shard]@.pm_constants == pm_constants
                    &&& shard_res[shard]@.kv == RecoveredKvStore::<K, I, L>::init(ps).kv
                },
                forall |shard| 0 <= shard < idx ==> #[trigger] shardstates.shards.contains_key(shard),
                forall |shard| #[trigger] shardstates.shards.contains_key(shard) ==> {
                    &&& 0 <= shard < idx
                    &&& shardstates.shards[shard].kv_state.id() == pred.shard_ids[shard]
                    &&& shardstates.shards[shard].kv_state@ == ConcurrentKvStoreView::<K, I, L>{
                        ps: ps,
                        pm_constants: pm_constants,
                        kv: RecoveredKvStore::<K, I, L>::init(ps).kv,
                    }
                },
        {
            proof {
                let tracked shardstate = ShardState::<K, I, L>{
                    kv_state: shard_res.tracked_remove(idx as int),
                };
                pred.shard_ids = pred.shard_ids.push(shardstate.kv_state.id());
                shardstates.shards.tracked_insert(idx as int, shardstate);
            }
        }

        assert(ShardingPredicate::inv(pred, shardstates));
        let tracked inv = AtomicInvariant::<_, _, ShardingPredicate>::new(pred, shardstates, namespace);

        (Tracked(inv), Tracked(combined_res))
    }

    exec fn start(
        shard_kvs: Vec<ConcurrentKvStore<PM, K, I, L>>,
        Tracked(inv): Tracked<Arc<AtomicInvariant::<ShardingPredicate, ShardStates<K, I, L>, ShardingPredicate>>>,
        Ghost(shard_namespace): Ghost<int>,
    ) -> (result: Self)
    {
        let nshards = shard_kvs.len() as u64;

        Self{
            nshard: nshards,
            kv: shard_kvs,
            inv: Tracked(inv),
            shard_namespace: Ghost(shard_namespace),
        }
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
        let shard = self.key_to_shard(key);
        let shardcb = self.read_linearizer(ReadItemOp{ key: *key }, Tracked(cb));
        self.kv[shard].read_item::<ShardedReadLinearizer::<K, I, L, ReadItemOp<K>, CB>>(key, shardcb)
    }

    exec fn read_item_and_list<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(I, Vec<L>), KvError>, Tracked<CB::Completion>))
        where
            CB: ReadLinearizer<K, I, L, ReadItemAndListOp<K>>,
    {
        proof { use_type_invariant(self); }
        let shard = self.key_to_shard(key);
        let shardcb = self.read_linearizer(ReadItemAndListOp{ key: *key }, Tracked(cb));
        self.kv[shard].read_item_and_list::<ShardedReadLinearizer::<K, I, L, ReadItemAndListOp<K>, CB>>(key, shardcb)
    }

    exec fn read_list<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<Vec<L>, KvError>, Tracked<CB::Completion>))
        where
            CB: ReadLinearizer<K, I, L, ReadListOp<K>>,
    {
        proof { use_type_invariant(self); }
        let shard = self.key_to_shard(key);
        let shardcb = self.read_linearizer(ReadListOp{ key: *key }, Tracked(cb));
        self.kv[shard].read_list::<ShardedReadLinearizer::<K, I, L, ReadListOp<K>, CB>>(key, shardcb)
    }

    exec fn get_list_length<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<usize, KvError>, Tracked<CB::Completion>))
        where
            CB: ReadLinearizer<K, I, L, GetListLengthOp<K>>,
    {
        proof { use_type_invariant(self); }
        let shard = self.key_to_shard(key);
        let shardcb = self.read_linearizer(GetListLengthOp{ key: *key }, Tracked(cb));
        self.kv[shard].get_list_length::<ShardedReadLinearizer::<K, I, L, GetListLengthOp<K>, CB>>(key, shardcb)
    }

    exec fn create<CB>(
        &self,
        key: &K,
        item: &I,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, CreateOp<K, I, false>>,
    {
        proof { use_type_invariant(self); }
        let shard = self.key_to_shard(key);
        let shardcb = self.mut_linearizer(CreateOp{ key: *key, item: *item }, Tracked(cb));
        self.kv[shard].create::<ShardedMutatingLinearizer::<K, I, L, CreateOp<K, I, false>, CB>, false>(key, item, shardcb)
    }

    exec fn update_item<CB>(
        &self,
        key: &K,
        item: &I,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, UpdateItemOp<K, I, false>>,
    {
        proof { use_type_invariant(self); }
        let shard = self.key_to_shard(key);
        let shardcb = self.mut_linearizer(UpdateItemOp{ key: *key, item: *item }, Tracked(cb));
        self.kv[shard].update_item::<ShardedMutatingLinearizer::<K, I, L, UpdateItemOp<K, I, false>, CB>, false>(key, item, shardcb)
    }

    exec fn delete<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, DeleteOp<K>>,
    {
        proof { use_type_invariant(self); }
        let shard = self.key_to_shard(key);
        let shardcb = self.mut_linearizer(DeleteOp{ key: *key }, Tracked(cb));
        self.kv[shard].delete::<ShardedMutatingLinearizer::<K, I, L, DeleteOp<K>, CB>>(key, shardcb)
    }

    exec fn append_to_list<CB>(
        &self,
        key: &K,
        new_list_element: L,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, AppendToListOp<K, L, false>>,
    {
        proof { use_type_invariant(self); }
        let shard = self.key_to_shard(key);
        let shardcb = self.mut_linearizer(AppendToListOp{ key: *key, new_list_element }, Tracked(cb));
        self.kv[shard].append_to_list::<ShardedMutatingLinearizer::<K, I, L, AppendToListOp<K, L, false>, CB>, false>(key, new_list_element, shardcb)
    }

    exec fn append_to_list_and_update_item<CB>(
        &self,
        key: &K,
        new_list_element: L,
        new_item: &I,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, AppendToListAndUpdateItemOp<K, I, L, false>>,
    {
        proof { use_type_invariant(self); }
        let shard = self.key_to_shard(key);
        let shardcb = self.mut_linearizer(AppendToListAndUpdateItemOp{ key: *key, new_list_element, new_item: *new_item }, Tracked(cb));
        self.kv[shard].append_to_list_and_update_item::<ShardedMutatingLinearizer::<K, I, L, AppendToListAndUpdateItemOp<K, I, L, false>, CB>, false>(key, new_list_element, new_item, shardcb)
    }

    exec fn update_list_element_at_index<CB>(
        &self,
        key: &K,
        idx: usize,
        new_list_element: L,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, UpdateListElementAtIndexOp<K, L, false>>,
    {
        proof { use_type_invariant(self); }
        let shard = self.key_to_shard(key);
        let shardcb = self.mut_linearizer(UpdateListElementAtIndexOp{ key: *key, idx, new_list_element }, Tracked(cb));
        self.kv[shard].update_list_element_at_index::<ShardedMutatingLinearizer::<K, I, L, UpdateListElementAtIndexOp<K, L, false>, CB>, false>(key, idx, new_list_element, shardcb)
    }

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
    {
        proof { use_type_invariant(self); }
        let shard = self.key_to_shard(key);
        let shardcb = self.mut_linearizer(UpdateListElementAtIndexAndItemOp{ key: *key, idx, new_list_element, new_item: *new_item }, Tracked(cb));
        self.kv[shard].update_list_element_at_index_and_item::<ShardedMutatingLinearizer::<K, I, L, UpdateListElementAtIndexAndItemOp<K, I, L, false>, CB>, false>(key, idx, new_list_element, new_item, shardcb)
    }

    exec fn trim_list<CB>(
        &self,
        key: &K,
        trim_length: usize,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, TrimListOp<K, false>>,
    {
        proof { use_type_invariant(self); }
        let shard = self.key_to_shard(key);
        let shardcb = self.mut_linearizer(TrimListOp{ key: *key, trim_length }, Tracked(cb));
        self.kv[shard].trim_list::<ShardedMutatingLinearizer::<K, I, L, TrimListOp<K, false>, CB>, false>(key, trim_length, shardcb)
    }

    exec fn trim_list_and_update_item<CB>(
        &self,
        key: &K,
        trim_length: usize,
        new_item: &I,
        Tracked(cb): Tracked<CB>
    ) -> (result: (Result<(), KvError>, Tracked<CB::Completion>))
        where
            CB: MutatingLinearizer<K, I, L, TrimListAndUpdateItemOp<K, I, false>>,
    {
        proof { use_type_invariant(self); }
        let shard = self.key_to_shard(key);
        let shardcb = self.mut_linearizer(TrimListAndUpdateItemOp{ key: *key, trim_length, new_item: *new_item }, Tracked(cb));
        self.kv[shard].trim_list_and_update_item::<ShardedMutatingLinearizer::<K, I, L, TrimListAndUpdateItemOp<K, I, false>, CB>, false>(key, trim_length, new_item, shardcb)
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
struct ShardedReadLinearizer<K, I, L, Op, Lin>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        Op: SingleKeyReadOnlyOperation<K, I, L>,
        Lin: ReadLinearizer<K, I, L, Op>,
{
    inv: Arc<AtomicInvariant<ShardingPredicate, ShardStates<K, I, L>, ShardingPredicate>>,
    lin: Lin,
    credit: OpenInvariantCredit,

    ghost shard: int,
    ghost __phantom: PhantomData<Op>,
}

impl<K, I, L, Op, Lin> ReadLinearizer<K, I, L, Op> for ShardedReadLinearizer<K, I, L, Op, Lin>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        Op: SingleKeyReadOnlyOperation<K, I, L>,
        Lin: ReadLinearizer<K, I, L, Op>,
{
    type Completion = Lin::Completion;

    closed spec fn namespaces(self) -> Set<int> {
        self.lin.namespaces().insert(self.inv.namespace())
    }

    closed spec fn pre(self, id: int, op: Op) -> bool {
        &&& 0 <= self.shard < self.inv.constant().nshard()
        &&& id == self.inv.constant().shard_ids[self.shard]
        &&& self.lin.pre(self.inv.constant().combined_id, op)
        &&& self.shard == shard_of_key(op.key(), self.inv.constant().nshard())
        &&& !self.lin.namespaces().contains(self.inv.namespace())
    }

    closed spec fn post(self, complete: Self::Completion, id: int, op: Op, result: Result<Op::KvResult, KvError>) -> bool {
        &&& self.lin.post(complete, self.inv.constant().combined_id, op, result)
    }

    proof fn apply(tracked self, op: Op, result: Result<Op::KvResult, KvError>, tracked r: &GhostVarAuth<ConcurrentKvStoreView<K, I, L>>) -> (tracked complete: Self::Completion) {
        let tracked mut completion;
        open_atomic_invariant_in_proof!(self.credit => &self.inv => inner => {
            assert(inner.shards.contains_key(self.shard));
            r.agree(&inner.shards.tracked_borrow(self.shard).kv_state);

            op.only_key_matters(r@, inner.combined@, result);

            assert(op.result_valid(inner.combined@, result));
            completion = self.lin.apply(op, result, &inner.combined);
            assert(self.lin.post(completion, self.inv.constant().combined_id, op, result));
        });
        assert(self.lin.post(completion, self.inv.constant().combined_id, op, result));
        assert(self.post(completion, r.id(), op, result));
        completion
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
struct ShardedMutatingLinearizer<K, I, L, Op, Lin>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        Op: SingleKeyMutatingOperation<K, I, L>,
        Lin: MutatingLinearizer<K, I, L, Op>,
{
    inv: Arc<AtomicInvariant<ShardingPredicate, ShardStates<K, I, L>, ShardingPredicate>>,
    lin: Lin,
    credit: OpenInvariantCredit,

    ghost shard: int,
    ghost __phantom: PhantomData<Op>,
}

impl<K, I, L, Op, Lin> MutatingLinearizer<K, I, L, Op> for ShardedMutatingLinearizer<K, I, L, Op, Lin>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        Op: SingleKeyMutatingOperation<K, I, L>,
        Lin: MutatingLinearizer<K, I, L, Op>,
{
    type Completion = Lin::Completion;

    closed spec fn namespaces(self) -> Set<int> {
        self.lin.namespaces().insert(self.inv.namespace())
    }

    closed spec fn pre(self, id: int, op: Op) -> bool {
        &&& 0 <= self.shard < self.inv.constant().nshard()
        &&& id == self.inv.constant().shard_ids[self.shard]
        &&& self.lin.pre(self.inv.constant().combined_id, op)
        &&& self.shard == shard_of_key(op.key(), self.inv.constant().nshard())
        &&& !self.lin.namespaces().contains(self.inv.namespace())
        &&& forall |old_state, new_state, result| #[trigger] op.result_valid(old_state, new_state, result) ==> {
            &&& old_state.ps == new_state.ps
            &&& old_state.pm_constants == new_state.pm_constants
            &&& old_state.kv.logical_range_gaps_policy == new_state.kv.logical_range_gaps_policy
            &&& forall |k| k != op.key() ==> old_state.kv[k] == #[trigger] new_state.kv[k]
        }
    }

    closed spec fn post(self, complete: Self::Completion, id: int, op: Op, result: Result<Op::KvResult, KvError>) -> bool {
        &&& self.lin.post(complete, self.inv.constant().combined_id, op, result)
    }

    proof fn apply(
        tracked self,
        op: Op,
        new_state: ConcurrentKvStoreView<K, I, L>,
        result: Result<Op::KvResult, KvError>,
        tracked r: &mut GhostVarAuth<ConcurrentKvStoreView<K, I, L>>,
    ) -> (tracked result: Self::Completion) {
        let ghost key = op.key();
        let tracked mut completion;
        open_atomic_invariant_in_proof!(self.credit => &self.inv => inner => {
            // Force trigger
            assert(inner.shards.contains_key(self.shard));

            // Force trigger
            assert(shard_of_key(key, self.inv.constant().nshard()) == self.shard);

            let tracked mut shard = inner.shards.tracked_remove(self.shard);
            r.agree(&shard.kv_state);

            let ghost old_shard_ckv = r@;
            let ghost old_combined_ckv = inner.combined@;
            let ghost new_shard_ckv = new_state;
            let ghost new_combined_ckv = ConcurrentKvStoreView::<K, I, L>{
                kv: AtomicKvStore::<K, I, L>{
                    m: map_optset(old_combined_ckv.kv.m, key, new_shard_ckv.kv[key]),
                    .. old_combined_ckv.kv
                },
                .. old_combined_ckv
            };

            // Force trigger
            assert(op.result_valid(old_shard_ckv, new_shard_ckv, result));

            assert forall |k| new_shard_ckv.kv.m.contains_key(k)
                implies #[trigger] shard_of_key(k, self.inv.constant().nshard()) == self.shard by
            {
                if k != key {
                    assert(old_shard_ckv.kv[k] == new_shard_ckv.kv[k]);
                }
            }

            r.update(&mut shard.kv_state, new_state);
            assert(keys_match_shard(shard.kv_state@.kv, self.shard, self.inv.constant().nshard()));

            op.only_key_matters(old_shard_ckv, old_combined_ckv,
                                new_shard_ckv, new_combined_ckv, result);

            completion = self.lin.apply(op, new_combined_ckv, result, &mut inner.combined);
            assert(self.lin.post(completion, self.inv.constant().combined_id, op, result));
            assert(shard.valid(self.inv.constant().shard_ids[self.shard],
                               self.shard,
                               self.inv.constant().nshard(),
                               inner.combined@));
            inner.shards.tracked_insert(self.shard, shard);

            assert(ShardingPredicate::inv(self.inv.constant(), inner));
        });
        assert(self.lin.post(completion, self.inv.constant().combined_id, op, result));
        assert(self.post(completion, r.id(), op, result));
        completion
    }
}

}
