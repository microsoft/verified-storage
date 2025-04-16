#![cfg_attr(verus_keep_ghost, verus::trusted)]
use builtin::*;
use builtin_macros::*;
use vstd::pervasive::*;
use vstd::prelude::*;
use vstd::pcm::frac::*;
use vstd::invariant::*;

use deps_hack::PmCopy;
use crate::kv2::spec_t::*;
use crate::kv2::shardkv_v::*;
use crate::kv2::rwkv_inv_v::*;
use crate::kv2::concurrentspec_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_v::*;
use crate::pmem::power_t::*;
use crate::pmem::mmap_pmemfile_t::*;

use std::hash::Hash;
use std::io::Read;


verus! {

pub const MAX_SHARDS: isize = isize::MAX;
pub const NAMESPACE: i32 = 6; // TODO: don't hardcode this as a constant -- what should it actually be?

// pub struct TrustedKvPermission 
// {
//     ghost is_transition_allowable: spec_fn(Seq<u8>, Seq<u8>) -> bool,
//     ghost powerpm_id: int,
// }

// impl TrustedKvPermission
// {
//     proof fn new<PM, K, I, L>(powerpm_id: int) -> (tracked perm: Self)
//         where
//             PM: PersistentMemoryRegion,
//             K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
//             I: PmCopy + std::fmt::Debug,
//             L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
//         ensures
//             perm.id() == powerpm_id,
//     {
//         Self {
//             is_transition_allowable:
//                    |s1: Seq<u8>, s2: Seq<u8>|
//                        ConcurrentKvStore::<PM, K, I, L>::recover(s1) ==
//                        ConcurrentKvStore::<PM, K, I, L>::recover(s2),
//             powerpm_id: powerpm_id,
//         }
//     }
// }

// impl CheckPermission<Seq<u8>> for TrustedKvPermission
// {
//     type Completion = ();

//     closed spec fn check_permission(&self, s1: Seq<u8>, s2: Seq<u8>) -> bool
//     {
//         (self.is_transition_allowable)(s1, s2)
//     }

//     closed spec fn id(&self) -> int
//     {
//         self.powerpm_id
//     }

//     closed spec fn completed(&self, c: Self::Completion) -> bool
//     {
//         true
//     }

//     proof fn apply(tracked self, tracked credit: vstd::invariant::OpenInvariantCredit, tracked r: &mut GhostVarAuth<Seq<u8>>, new_state: Seq<u8>) -> (tracked result: Self::Completion)
//     {
//         admit();
//         ()
//     }
// }

// pub struct TrustedPermissionFactory 
// {
//     ghost is_transition_allowable: spec_fn(Seq<u8>, Seq<u8>) -> bool,
//     ghost powerpm_id: int,
// }

// impl PermissionFactory<Seq<u8>> for TrustedPermissionFactory
// {
//     type Perm = TrustedKvPermission;

//     closed spec fn check_permission(&self, s1: Seq<u8>, s2: Seq<u8>) -> bool
//     {
//         (self.is_transition_allowable)(s1, s2)
//     }

//     proof fn grant_permission(tracked &self) -> (tracked perm: TrustedKvPermission)
//         ensures
//             forall|s1, s2| self.check_permission(s1, s2) ==> #[trigger] perm.check_permission(s1, s2)
//     {
//         TrustedKvPermission{
//             is_transition_allowable: |s1: Seq<u8>, s2: Seq<u8>| (self.is_transition_allowable)(s1, s2),
//             powerpm_id: self.powerpm_id,
//         }
//     }

//     proof fn clone(tracked &self) -> (tracked other: Self)
//         ensures
//             forall|s1, s2| self.check_permission(s1, s2) ==> #[trigger] other.check_permission(s1, s2)
//     {
//         Self{
//             is_transition_allowable: self.is_transition_allowable,
//             powerpm_id: self.powerpm_id,
//         }
//     }

//     closed spec fn id(&self) -> int
//     {
//         self.powerpm_id
//     }
// }

// // This structure temporarily holds some per-shard info between when 
// // we set up and start each shard. It exists so that the non-Verus caller
// // doesn't see the tracked structures used here.
// #[verifier::reject_recursive_types(K)]
// #[verifier::reject_recursive_types(I)]
// #[verifier::reject_recursive_types(L)]
// pub struct TrustedKvStoreShardInfo<PM, K, I, L>
//     where 
//         PM: PersistentMemoryRegion,
//         K: Hash + PmCopy + Sized + std::fmt::Debug,
//         I: PmCopy + Sized + std::fmt::Debug,
//         L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
// {
//     atomic_pm: PersistentMemoryRegionAtomic<PM>,
//     inv: Tracked<AtomicInvariant::<ConcurrentKvStoreInvPred, ConcurrentKvStoreInvState<PM, K, I, L>, ConcurrentKvStoreInvPred>>,
//     res: Tracked<GhostVar<ConcurrentKvStoreView::<K, I, L>>>,
//     namespace: Ghost<int>,
// }

// impl<PM, K, I, L> TrustedKvStoreShardInfo<PM, K, I, L>
//     where 
//         PM: PersistentMemoryRegion,
//         K: Hash + PmCopy + Sized + std::fmt::Debug,
//         I: PmCopy + Sized + std::fmt::Debug,
//         L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
// {
//     pub closed spec fn inv(self) -> bool 
//     {
//         &&& self.atomic_pm.inv()
//         &&& self.atomic_pm.id() == self.inv@.constant().durable_id
//         &&& self.res@.id() == self.inv@.constant().caller_id 
//         &&& self.inv@.namespace() == self.namespace@
//     }

//     pub closed spec fn matches_setup_args(self, pm: PM, ps: SetupParameters) -> bool 
//     {
//         &&& self.atomic_pm.constants() == pm.constants()
//         &&& self.inv@.constant().ps == ps 
//         &&& self.inv@.constant().pm_constants == pm.constants()
//         &&& self.res@@ == ConcurrentKvStoreView::<K, I, L>{
//             ps: ps,
//             pm_constants: pm.constants(),
//             kv: RecoveredKvStore::<K, I, L>::init(ps).kv,
//         }
//     }

//     fn get_res(self) -> (result: Tracked<GhostVar<ConcurrentKvStoreView::<K, I, L>>>)
//         ensures 
//             result == self.spec_get_res()
//     {
//         self.res
//     }

//     spec fn spec_get_res(self) -> Tracked<GhostVar<ConcurrentKvStoreView::<K, I, L>>> 
//     {
//         self.res
//     }

//     pub closed spec fn pm_constants(self) -> PersistentMemoryConstants 
//     {
//         self.atomic_pm.constants()
//     }
// }

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
pub struct ShardedKvInfo<PM, K, I, L>
    where 
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    shard_inv: Tracked<AtomicInvariant::<ShardingPredicate, ShardStates<K, I, L>, ShardingPredicate>>,
    gvar: Tracked<GhostVar<ConcurrentKvStoreView::<K, I, L>>>,
    pm_vec: Vec<(PersistentMemoryRegionAtomic<PM>, Tracked<AtomicInvariant::<ConcurrentKvStoreInvPred, ConcurrentKvStoreInvState<PM, K, I, L>, ConcurrentKvStoreInvPred>>)>,
    pm_constants: Ghost<PersistentMemoryConstants>,
}

impl<PM, K, I, L> ShardedKvInfo<PM, K, I, L>
    where 
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub closed spec fn inv(self) -> bool 
    {
        let nshards = self.pm_vec@.len();
        &&& nshards >= 1
        &&& self.shard_inv@.constant().nshard() == nshards
        &&& self.gvar@.id() == self.shard_inv@.constant().combined_id
        &&& self.pm_constants == self.pm_vec[0].0.constants()
    }

    pub closed spec fn kv_view(self) -> ConcurrentKvStoreView::<K, I, L> 
    {
        self.gvar@@
    }

    pub closed spec fn pm_constants(self) -> PersistentMemoryConstants 
    {
        self.pm_constants@
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
pub struct TrustedShardedKvStore<PM, K, I, L>
    where 
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    untrusted_kv_impl: ShardedKvStore<PM, K, I, L>,
    powerpm_id: Ghost<int>,
}   

impl<PM, K, I, L> TrustedShardedKvStore<PM, K, I, L>
    where 
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    // TODO: at least some of this should probably be moved into a verified file?
    pub exec fn setup_shards(mut pms: Vec<PM>, ps: &SetupParameters) -> (result: Result<ShardedKvInfo<PM, K, I, L>, (KvError, Option<PM>)>)
        requires 
            forall |i| 0 <= i < pms@.len() ==> #[trigger] pms[i].inv(),
            forall |i, j| 0 <= i < j < pms@.len() ==> 
                #[trigger] pms[i].constants() == #[trigger] pms[j].constants(),
            pms@.len() <= MAX_SHARDS,
        ensures 
            match result {
                Ok(info) => {
                    let pm_constants = info.pm_constants();
                    &&& info.inv()
                    &&& info.kv_view() == (ConcurrentKvStoreView::<K, I, L>{
                        ps: *ps,
                        pm_constants: pm_constants,
                        kv: RecoveredKvStore::<K, I, L>::init(*ps).kv,
                    })
                }
                Err((KvError::InvalidParameter, _)) => !ps.valid(),
                Err((KvError::KeySizeTooSmall, _)) => K::spec_size_of() == 0,
                Err((KvError::OutOfSpace, Some(pm))) => 
                    pm@.len() < ConcurrentKvStore::<PM, K, I, L>::spec_space_needed_for_setup(*ps),
                Err((KvError::TooFewShards, None)) => pms@.len() == 0,
                Err(_) => false
            }
    {
        if pms.len() == 0 {
            return Err((KvError::TooFewShards, None));
        }

        let ghost shard_namespace = 5; // TODO: what is this? what should it be set to?
        let mut pm_vec: Vec<(PersistentMemoryRegionAtomic<PM>, Tracked<AtomicInvariant<ConcurrentKvStoreInvPred, ConcurrentKvStoreInvState<PM, K, I, L>, ConcurrentKvStoreInvPred>>)> = Vec::new();
        let tracked mut shard_res = Map::<int, GhostVar<ConcurrentKvStoreView::<K, I, L>>>::tracked_empty();
        let ghost pm_constants = pms[0].constants(); // the precondition specifies that all the constants should be the same, so we can use any

        // This loop drains the `pms` vec and sets up each PM region to be a `ConcurrentKvStore`.
        // This is inefficient but since we don't know how many shards we'll have or 
        // and we need to move ownership around, and Verus doesn't support drain(), we can't really
        // do any better. It's ok for this to be slow because it will only happen once.
        let mut idx: usize = 0;
        let nshards = pms.len();
        while pms.len() > 0 
            invariant 
                forall |i| 0 <= i < pms@.len() ==> #[trigger] pms[i].inv() && pms[i].constants() == pm_constants,
                idx == nshards - pms@.len(),
                0 <= idx <= MAX_SHARDS,
                1 <= nshards <= MAX_SHARDS,
                forall |i| 0 <= i < idx ==> #[trigger] shard_res.contains_key(i),
                forall |shard| #[trigger] shard_res.contains_key(shard) ==> {
                    &&& shard_res[shard]@.ps == ps
                    &&& shard_res[shard]@.pm_constants == pm_constants
                    &&& shard_res[shard]@.kv == RecoveredKvStore::<K, I, L>::init(*ps).kv
                },
                pm_vec@.len() == idx,
                forall |i| 0 <= i < pm_vec@.len() ==> #[trigger] pm_vec@[i].0.constants() == pm_constants,
        {
            let pm = pms.remove(0);
            // this assert is required to hit the trigger on pms[i].inv() in the invariant
            assert(forall |i| 0 <= i < pms@.len() ==> #[trigger] pms[i].inv());
            let (atomic_pm, inv, res) = 
                match ConcurrentKvStore::<PM, K, I, L>::setup(pm, ps, Ghost(shard_namespace)) {
                    Ok((atomic_pm, inv, res)) => (atomic_pm, inv, res),
                    Err((e, pm)) => {
                        assert(e == KvError::OutOfSpace ==> pm@.len() < ConcurrentKvStore::<PM, K, I, L>::spec_space_needed_for_setup(*ps));
                        return Err((e, Some(pm)));
                    }
            };

            assert(res@@.pm_constants == pm_constants);
            pm_vec.push((atomic_pm, inv));
            proof {
                assert(res@@.pm_constants == pm_constants);
                shard_res.tracked_insert(idx as int, res.get());
                assert(shard_res[idx as int]@.pm_constants == pm_constants);
            }
            idx += 1;
        }

        // We're now in a good place to set up the `ShardedKvStore`
        let namespace = 6;
        let (inv, gvar) = ShardedKvStore::<PM, K, I, L>::setup(nshards, Tracked(shard_res),
            Ghost(*ps), Ghost(pm_constants), Ghost(namespace as int)); 

        let info = ShardedKvInfo {
            shard_inv: inv,
            gvar,
            pm_vec,
            pm_constants: Ghost(pm_constants)
        };
        
        Ok(info)
    }

    // TODO: verify this function. It should return a structure that helps us manage the tracked ConcurrentKvStoreView 
    // that is needed for linearization(?)
    pub exec fn start_shards(info: ShardedKvInfo<PM, K, I, L>, id: u128) -> (result: Result<ShardedKvStore<PM, K, I, L>, KvError>)
    {
        assume(false); // TODO: remove and prove this function
        let mut pms = info.pm_vec;
        let mut kvs = Vec::new();
        let gvar = info.gvar;

        while pms.len() > 0 
        {
            assume(false); // TODO: remove and prove the loop
            let (pm, inv) = pms.remove(0);
            let kv = ConcurrentKvStore::<PM, K, I, L>::start(pm, id, inv)?;
            kvs.push(kv);
        }

        let skv = ShardedKvStore::<PM, K, I, L>::start(kvs, info.shard_inv, Ghost(NAMESPACE as int));
        Ok(skv)
    }

    pub exec fn create<CB>(&self, key: &K, item: &I) -> (result: Result<(), KvError>) 
        where
            CB: MutatingLinearizer<K, I, L, CreateOp<K, I, false>>,
    {
        assume(false);
        let tracked cb: CB = proof_from_false();
        let (result, _) = self.untrusted_kv_impl.create(key, item, Tracked(cb));
        result
    }

    pub exec fn update_item<CB>(&self, key: &K, item: &I) -> (result: Result<(), KvError>)
        where
            CB: MutatingLinearizer<K, I, L, UpdateItemOp<K, I, false>>,
    {
        assume(false);
        let tracked cb: CB = proof_from_false();
        let (result, _) = self.untrusted_kv_impl.update_item(key, item, Tracked(cb));
        result
    }

    pub exec fn read_item<CB>(&self, key: &K) -> (result: Result<I, KvError>)
        where
            CB: ReadLinearizer<K, I, L, ReadItemOp<K>>,
    {
        assume(false);
        let tracked cb: CB = proof_from_false();
        let (result, _) = self.untrusted_kv_impl.read_item(key, Tracked(cb));
        result
    }

    pub exec fn delete_item<CB>(&self, key: &K) -> (result: Result<(), KvError>)
        where 
            CB: MutatingLinearizer<K, I, L, DeleteOp<K>>,
    {
        assume(false);
        let tracked cb: CB = proof_from_false();
        let (result, _) = self.untrusted_kv_impl.delete(key, Tracked(cb));
        result
    }
}

impl<K, I, L, Op> MutatingLinearizer<K, I, L, Op> for ()
    where 
        Op: MutatingOperation<K, I, L>
{
    type Completion = Self;

    closed spec fn namespaces(self) -> Set<int>
    {
        Set::empty()
    }

    closed spec fn pre(self, id: int, op: Op) -> bool { true }

    closed spec fn post(self, complete: Self::Completion, id: int, op: Op, exec_result: Result<Op::KvResult, KvError>) -> bool 
    {
        true
    }

    proof fn apply(
        tracked self,
        op: Op,
        new_ckv: ConcurrentKvStoreView<TestKey, TestItem, TestListElement>,
        exec_result: Result<Op::KvResult, KvError>,
        tracked r: &mut GhostVarAuth<ConcurrentKvStoreView<TestKey, TestItem, TestListElement>>
    ) -> (tracked complete: Self::Completion) 
    {
        self
    }
}

impl<K, I, L, Op> ReadLinearizer<K, I, L, Op> for () 
    where 
        Op: ReadOnlyOperation<K, I, L>
{
    type Completion = Self;

    closed spec fn namespaces(self) -> Set<int>
    {
        Set::empty()
    }

    closed spec fn pre(self, id: int, op: Op) -> bool { true }

    closed spec fn post(self, complete: Self::Completion, id: int, op: Op, exec_result: Result<Op::KvResult, KvError>) -> bool 
    {
        true
    }

    proof fn apply(
        tracked self,
        op: Op,
        new_ckv: ConcurrentKvStoreView<TestKey, TestItem, TestListElement>,
        exec_result: Result<Op::KvResult, KvError>,
        tracked r: &mut GhostVarAuth<ConcurrentKvStoreView<TestKey, TestItem, TestListElement>>
    ) -> (tracked complete: Self::Completion) 
    {
        self
    }
}

}