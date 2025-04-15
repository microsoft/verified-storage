#![cfg_attr(verus_keep_ghost, verus::trusted)]
use builtin::*;
use builtin_macros::*;
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


verus! {

pub const MAX_SHARDS: isize = isize::MAX;

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
struct ShardedKvInfo<PM, K, I, L>
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
    pub exec fn setup_shards(mut pms: Vec<PM>, ps: &SetupParameters) -> (result: Result<ShardedKvInfo<PM, K, I, L>, (KvError, PM)>)
        requires 
            forall |i| 0 <= i < pms@.len() ==> #[trigger] pms[i].inv(),
            forall |i, j| 0 <= i < j < pms@.len() ==> 
                #[trigger] pms[i].constants() == #[trigger] pms[j].constants(),
            1 <= pms@.len() <= MAX_SHARDS,
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
                Err((KvError::OutOfSpace, pm)) => 
                    pm@.len() < ConcurrentKvStore::<PM, K, I, L>::spec_space_needed_for_setup(*ps),
                Err((KvError::TooFewShards, _)) => pms@.len() == 0,
                Err(_) => false
            }
    {
        if pms.len() == 0 {
            return Err(KvError::TooFewShards);
        }

        let ghost shard_namespace = 5; // TODO: what is this? what should it be set to?
        let mut pm_vec = Vec::new();
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
                }
        {
            let pm = pms.remove(0);
            let (atomic_pm, inv, res) = 
                match ConcurrentKvStore::<PM, K, I, L>::setup(pm, ps, Ghost(shard_namespace)) {
                    Ok((atomic_pm, inv, res)) => (atomic_pm, inv, res),
                    Err((e, pm)) => {
                        assert(e == KvError::OutOfSpace ==> pm@.len() < ConcurrentKvStore::<PM, K, I, L>::spec_space_needed_for_setup(*ps));
                        return Err((e, pm));
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
        
        Ok(ShardedKvInfo {
            shard_inv: inv,
            gvar,
            pm_vec,
            pm_constants: Ghost(pm_constants)
        })
    }

    // pub exec fn setup_shards(
    //     nshards: usize, 
    //     ps: &SetupParameters,
    //     shard_infos: &Vec<TrustedKvStoreShardInfo<PM, K, I, L>>
    // ) -> (result: Result<(), KvError>)
    //     requires 
    //         nshards >= 1,
    //         forall |i| 0 <= i < shard_infos@.len() ==> #[trigger] shard_infos[i].inv(),
    //         forall |i, j| 0 <= i < j < shard_infos@.len() ==> 
    //             #[trigger] shard_infos[i].pm_constants() == #[trigger] shard_infos[j].pm_constants(),
    //     ensures 
    //         match result {
    //             Ok(()) => {true}
    //             Err(KvError::InvalidParameter) => nshards != shard_infos.len(),
    //             Err(_) => false
    //         }
    // {
    //     if nshards != shard_infos.len() {
    //         return Err(KvError::InvalidParameter);
    //     }

    //     let ghost namespace = 6; // TODO: what should this be..?
    //     let tracked mut shard_res = Map::<int, GhostVar<ConcurrentKvStoreView::<K, I, L>>>::tracked_empty();
    //     for i in 0..nshards 
    //         invariant 
    //             forall |j| 0 <= j < i ==> shard_res.contains_key(j) && shard_res[j] == shard_infos[i as int].spec_get_res()@
    //     {
    //         let res = shard_infos[i].get_res();
    //         proof {
    //             shard_res.tracked_insert(i as int, res.get());
    //         }
    //     }

    //     // start the sharded kv store
    //     let (inv, gvar) = ShardedKvStore::<PM, K, I, L>::setup(
    //         nshards,
    //         Tracked(shard_res),
    //         Ghost(*ps),
    //         Ghost(shard_infos[0].pm_constants()),
    //         Ghost(namespace)
    //     );

    //     Ok(())        
    // }


    // pub exec fn setup_shard(pm: &mut Vec<PM>, ps: &SetupParameters) -> (result: Result<(), KvError>) 
    //     requires 
    //         forall |i| 0 <= i < old(pms)@.len() ==> #[trigger] old(pms)[i].inv(),
    //     ensures 
    //         pms@.len() == old(pms)@.len(),
    //         forall |i| 0 <= i < pms@.len() ==> #[trigger] pms[i].inv(),
    //         forall |i| 0 <= i < pms@.len() ==> #[trigger] pms[i].constants() == old(pms)[i].constants(),
    //         match result {
    //             Ok(()) => {
    //                 &&& ps.valid()
    //                 &&& forall |i| 0 <= i < pms@.len() ==> 
    //                     {
    //                         &&& #[trigger] pms@[i]@.flush_predicted()
    //                         &&& ConcurrentKvStore::<TrustedPermissionFactory, PM, K, I, L>::recover(pms@[i]@.durable_state) == Some(RecoveredKvStore::<K, I, L>::init(*ps))
    //                     }
    //             }
    //             Err(KvError::InvalidParameter) => !ps.valid(),
    //             Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
    //             Err(KvError::OutOfSpace) => {
    //                 ||| ConcurrentKvStore::<TrustedPermissionFactory, PM, K, I, L>::spec_space_needed_for_setup(*ps) > u64::MAX
    //                 ||| exists |i| {
    //                     &&& 0 <= i < pms@.len() 
    //                     &&& #[trigger] pms@[i]@.len() < ConcurrentKvStore::<TrustedPermissionFactory, PM, K, I, L>::spec_space_needed_for_setup(*ps)
    //                 }
    //             },
    //             Err(_) => false,
    //         }
    // {
    //     // check that the setup parameters are valid
    //     if ps.max_keys == 0 || ps.max_list_elements == 0 || ps.max_operations_per_transaction == 0 {
    //         return Err(KvError::InvalidParameter);
    //     }

    //     // make sure all regions are big enough
    //     let region_size = match ConcurrentKvStore::<TrustedPermissionFactory, PM, K, I, L>::space_needed_for_setup(&ps) {
    //         Ok(s) => s,
    //         Err(e) => {
    //             assert(ConcurrentKvStore::<TrustedPermissionFactory, PM, K, I, L>::spec_space_needed_for_setup(*ps) > u64::MAX); 
    //             assert(e != KvError::OutOfSpace ==> false);
    //             return Err(e);
    //         }
    //     };
        
    //     for i in 0..pms.len() 
    //         invariant
    //             forall |j| 0 <= j < i ==> #[trigger] pms@[j]@.len() >= region_size,
    //             old(pms) == pms,
    //             ps.valid(),
    //             forall |j| 0 <= j < pms@.len() ==> {
    //                 &&& #[trigger] pms[j].inv()
    //                 &&& pms[j].constants() == old(pms)[j].constants()
    //             },
    //             region_size == ConcurrentKvStore::<TrustedPermissionFactory, PM, K, I, L>::spec_space_needed_for_setup(*ps),
    //     {
    //         if pms[i].get_region_size() < region_size {
    //             assert(pms@[i as int]@.len() < ConcurrentKvStore::<TrustedPermissionFactory, PM, K, I, L>::spec_space_needed_for_setup(*ps));
    //             return Err(KvError::OutOfSpace);
    //         }
    //     }

    //     for i in 0..pms.len()  
    //         invariant 
    //             forall |j| 0 <= j < pms@.len() ==> #[trigger] pms@[j]@.len() >= region_size,

    //     {
    //         ConcurrentKvStore::<TrustedPermissionFactory, PM, K, I, L>::setup(pms.get_mut(i).unwrap(), ps)?;
    //     }

        
    //     // NOTE: concurrent KV store and sharded KV store get set up separately.
    //     // we should probably call both here and manage all of the sharding-related 
    //     // ghost state in this file to hide it from the caller
        

    //     // Nickolai called concurrent kv store setup on each shard
    //     // and then the sharded kv store setup ONCE. so we should probably
    //     // take all of the shards here and call all necessary setup functions

    //     Ok(())
    // }
}


}