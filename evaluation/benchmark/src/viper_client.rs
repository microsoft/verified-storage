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
use std::thread::sleep;

pub struct ViperClient
{
    kv: *mut crate::ViperDBFFI,
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
        let init_size = 53687091200;

        println!("creating viper client");

        let kv = unsafe { crate::viperdb_create(file_ptr, init_size) };

        println!("done creating\n");

        Ok(Self { kv })
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
        let result = unsafe { crate::viperdb_put(self.kv, key, value) };
        match result {
            true => Ok(()), 
            false => Err(false)
        }
    }

    fn get(&mut self, key: &TestKey) -> Result<TestValue, Self::E> {
        let key = &key.key as *const [u8; KEY_LEN];
        let mut value = TestValue::default();
        let result = unsafe { crate::viperdb_get(self.kv, key, &mut value.value) };
        match result {
            true => Ok(value),
            false => Err(false)
        }
    }

    fn update(&mut self, key: &TestKey, value: &TestValue) -> Result<(), Self::E> {
        let key = &key.key as *const [u8; KEY_LEN];
        let value = &value.value as *const [u8; VALUE_LEN];
        let result = unsafe { crate::viperdb_update(self.kv, key, value) };
        // result is false if the value already exists, so ignore it
        Ok(())
    }

    fn delete(&mut self, key: &TestKey) -> Result<(), Self::E> {
        let key = &key.key as *const [u8; KEY_LEN];
        let result = unsafe { crate::viperdb_delete(self.kv, key) };
        match result {
            true => Ok(()),
            false => Err(false)
        }
    }

    fn cleanup() {
        sleep(Duration::from_secs(1));
        unmount_pm_fs();
    }

    fn flush(&mut self) {}
}

impl Drop for ViperClient
{
    fn drop(&mut self) {
        println!("dropping viper db");
        unsafe { crate::viperdb_cleanup(self.kv); }
        println!("done dropping viperdb");
    }
}