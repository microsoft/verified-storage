#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::durable::durablespec_t::*;
use crate::kv::kvimpl_t::*;
use crate::kv::kvspec_t::*;
use crate::kv::volatile::volatilespec_t::*;
use crate::pmem::pmemspec_t::*;
use std::hash::Hash;

verus! {
    pub trait DurableKvStore<PM, K, H, P, E> : Sized
    where
        PM: PersistentMemoryRegions,
        K: Hash + Eq + Clone + Serializable<E> + Sized + std::fmt::Debug,
        H: Serializable<E> + Header<K> + Sized + std::fmt::Debug,
        P: Serializable<E> + LogicalRange + std::fmt::Debug,
        E: std::fmt::Debug,
    {
        spec fn view(&self) -> DurableKvStoreView<K, H, P>;

        spec fn recover_to_kv_state(bytes: Seq<Seq<u8>>, id: u128) -> Option<AbstractKvStoreState<K, H, P>>;

        spec fn valid(self) -> bool;

        fn new(pmem: PM,
            kvstore_id: u128,
            max_keys: usize,
            lower_bound_on_max_pages: usize,
            logical_range_gaps_policy: LogicalRangeGapsPolicy
        ) -> (result: Result<Self, KvError<K, E>>)
            ensures
                match(result) {
                    Ok(durable_store) => {
                        &&& durable_store@.empty()
                        &&& durable_store.valid()
                    }
                    Err(_) => true // TODO
                };

        fn create(
            &mut self,
            header: H,
            perm: Tracked<&TrustedKvPermission<PM, K, H, P, Self, E>>
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                old(self).valid()
            ensures
                match result {
                    Ok(offset) => {
                        match self@[offset as int] {
                            Some(entry) => {
                                &&& entry.key() == header.spec_key()
                                &&& entry.header() == header
                                &&& entry.pages() == Seq::<P>::empty()
                            }
                            None => false
                        }
                    }
                    Err(_) => true // TODO
                }
        {
            Err(KvError::NotImplemented)
        }

        fn read_header(
            &self,
            offset: u64
        ) -> (result: Option<&H>)
            requires
                self.valid(),
            ensures
                match result {
                    Some(header) => {
                        match self@[offset as int] {
                            Some(entry) => entry.header() == header,
                            None => false
                        }
                    }
                    None => self@[offset as int].is_None()
                }
        {
            assume(false);
            None
        }

        fn read_header_and_pages(
            &self,
            offset: u64
        ) -> (result: Option<(&H, &Vec<P>)>)
            requires
                self.valid()
            ensures
                match result {
                    Some((header, pages)) => {
                        match self@[offset as int] {
                            Some(entry) => {
                                &&& entry.header() == header
                                &&& entry.pages() == pages@
                            }
                            None => false
                        }
                    }
                    None => self@[offset as int].is_None()
                }
        ;
    }
}
