#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::kvimpl_t::*;
use crate::kv::volatile::volatilespec_t::*;
use std::hash::Hash;

verus! {
    pub trait VolatileKvIndex<K, E> : Sized
    where
        K: Hash + Eq + Clone + Serializable<E> + Sized + std::fmt::Debug,
        E: std::fmt::Debug,
    {
        spec fn view(&self) -> VolatileKvIndexView<K>;

        spec fn valid(&self) -> bool;

        fn new(
            kvstore_id: u128,
            max_keys: usize,
        ) -> (result: Result<Self, KvError<K, E>>)
            ensures
                match result {
                    Ok(volatile_index) => {
                        &&& volatile_index@.empty()
                        &&& volatile_index.valid()
                    }
                    Err(_) => true // TODO
                }
        ;

        fn insert(
            &mut self,
            key: &K,
            offset: u64,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        &&& self@ == old(self)@.insert(*key, offset as int)
                    }
                    Err(_) => true // TODO
                }
        ;

        fn get(
            &self,
            key: &K
        ) -> (result: Option<u64>)
            requires
                self.valid(),
            ensures
                match result {
                    Some(offset) => match self@[*key] {
                            Some(val) => offset == val,
                            None => false
                        }
                    None => self@[*key].is_None()
                }
        ;

    }
}
