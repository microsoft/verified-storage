#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]

use crate::{Key, Value, KvInterface, init_and_mount_pm_fs, remount_pm_fs, unmount_pm_fs};
use storage_node::pmem::pmcopy_t::*;
use storage_node::pmem::traits_t::{ConstPmSized, PmSized, UnsafeSpecPmSized, PmSafe};
use storage_node::kv2::spec_t::*;
use pmsafe::PmCopy;
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;
use std::time::Duration;

pub struct ViperClient<K, V> 
    where
        K: PmCopy + Key + Debug + Hash,
        V: PmCopy + Value + Debug + Hash,
{
    kv: crate::ViperDB,
    _key_type: PhantomData<K>,
    _value_type: PhantomData<V>,
}

impl<K, V> KvInterface<K, V> for ViperClient<K, V> 
    where
        K: PmCopy + Key + Debug + Hash,
        V: PmCopy + Value + Debug + Hash,
{
    type E = bool;

    fn setup(num_keys: u64) -> Result<(), Self::E> { 
        Ok(())
    }

    fn start() -> Result<Self, Self::E> {
        // let viper_db = viper_Viper
        todo!()
    }

    fn timed_start() -> Result<(Self, Duration), Self::E> {
        todo!()
    }
    
    fn db_name() -> String {
        todo!()
    }

    fn put(&mut self, key: &K, value: &V) -> Result<(), Self::E> {
        todo!()
    }

    fn get(&mut self, key: &K) -> Result<V, Self::E> {
        todo!()
    }

    fn update(&mut self, key: &K, value: &V) -> Result<(), Self::E> {
        todo!()
    }

    fn delete(&mut self, key: &K) -> Result<(), Self::E> {
        todo!()
    }

    fn cleanup() {
        todo!()
    }

    fn flush(&mut self) {
        todo!()
    }
}