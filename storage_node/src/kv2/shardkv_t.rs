// #![cfg_attr(verus_keep_ghost, verus::trusted)]
// use builtin::*;
// use builtin_macros::*;
// use vstd::prelude::*;

// verus! {

// pub struct TrustedShardedKvStore<PM, K, I, L>
//     where 
//         PM: PersistentMemoryRegion,
//         K: Hash + PmCopy + Sized + std::fmt::Debug,
//         I: PmCopy + Sized + std::fmt::Debug,
//         L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
// {
//     untrusted_kv_impl: ShardedKvStore<PM, K, I, L>,
//     powerpm_id: Ghost<int>,
// }

// // impl<PM, K, I, L> TrustedShardedKvStore<PM, K, I, L>
// //     where 
// //         PM: PersistentMemoryRegion,
// //         K: Hash + PmCopy + Sized + std::fmt::Debug,
// //         I: PmCopy + Sized + std::fmt::Debug,
// //         L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
// // {

// //     pub exec fn setup(pms: &mut Vec<PM>, ps: SetupParameters) -> (result: Result<(), KvError>) 
// //         requires 
// //             // old(pm).inv(),
// //             forall |i| 0 <= i < old(pms)@.len() ==> old(pms)@.inv(),
// //         ensures 
// //             pms@.len() == old(pms)@.len(),
// //             forall |i| 0 <= i < pms@.len() ==> pms@.inv()
// //             forall |i| 0 <= i < pms@.len() ==> pm.constants() == old(pm).constants(),
// //             match result {
// //                 Ok(()) ==> {

// //                 }
// //                 Err(KvError::InvalidParameter) => !ps.valid(),
// //                 Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
// //                 Err(KvError::OutOfSpace) => exists |i| 0 <= i < pms@.len() && pms@[i].len() < Self::spec_space_needed_for_setup(*ps),
// //                 Err(_) => false,
// //             }
// //     {
// //         // NOTE: concurrent KV store and sharded KV store get set up separately.
// //         // we should probably call both here and manage all of the sharding-related 
// //         // ghost state in this file to hide it from the caller
        

// //         // Nickolai called concurrent kv store setup on each shard
// //         // and then the sharded kv store setup ONCE. so we should probably
// //         // take all of the shards here and call all necessary setup functions
// //     }
// // }

// }