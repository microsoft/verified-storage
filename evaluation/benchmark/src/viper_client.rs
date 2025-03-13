#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]

use crate::{Key, Value, TestKey, TestValue, KEY_LEN, VALUE_LEN, KvInterface, init_and_mount_pm_fs, remount_pm_fs, unmount_pm_fs};
use storage_node::pmem::pmcopy_t::*;
use storage_node::pmem::traits_t::{ConstPmSized, PmSized, UnsafeSpecPmSized, PmSafe};
use storage_node::kv2::spec_t::*;
use pmsafe::PmCopy;
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;
use std::time::Duration;
use std::ffi::{c_void, CString};

pub struct ViperClient
{
    // kv: crate::ViperDB,
    kv: *mut crate::ViperDB,
    client: *mut crate::ViperDBClient,
}

impl KvInterface<TestKey, TestValue> for ViperClient
{
    type E = bool;

    fn setup(num_keys: u64) -> Result<(), Self::E> { 
        Ok(())
    }

    fn start() -> Result<Self, Self::E> {
        init_and_mount_pm_fs();
        
        let file = crate::MOUNT_POINT.to_owned() + "/viper";
        let file_cstring = CString::new(file.clone()).unwrap();
        let file_ptr = file_cstring.as_ptr();
        let init_size = 1073741824;

        let mut viper_db = unsafe { crate::viperdb_create(file_ptr, init_size) };
        let viper_client = unsafe { crate::viperdb_get_client(viper_db) };

        Ok(Self {
            kv: viper_db,
            client: viper_client,
        })
    }

    fn timed_start() -> Result<(Self, Duration), Self::E> {
        todo!()
    }
    
    fn db_name() -> String {
        "viper".to_string()
    }

    fn put(&mut self, key: &TestKey, value: &TestValue) -> Result<(), Self::E> {
        let key = &key.key as *const [u8; KEY_LEN];
        let value = &value.value as *const [u8; VALUE_LEN];
        println!("client addr {:p}", self.client);
        println!("key addr {:p}", key);
        let result = unsafe { crate::viperdb_put(self.client, key, value) };
        match result {
            true => Ok(()), 
            false => Err(false)
        }
    }

    fn get(&mut self, key: &TestKey) -> Result<TestValue, Self::E> {
        todo!()
    }

    fn update(&mut self, key: &TestKey, value: &TestValue) -> Result<(), Self::E> {
        todo!()
    }

    fn delete(&mut self, key: &TestKey) -> Result<(), Self::E> {
        todo!()
    }

    fn cleanup() {
        todo!()
    }

    fn flush(&mut self) {
        todo!()
    }
}

impl Drop for ViperClient
{
    fn drop(&mut self) {
        println!("dropping viper db");
        unsafe { crate::viperdb_cleanup(self.kv); }
    }
}