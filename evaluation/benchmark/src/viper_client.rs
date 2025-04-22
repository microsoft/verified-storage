#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]

use crate::{
    init_and_mount_pm_fs, remount_pm_fs, unmount_pm_fs, Key, KvInterface, MicrobenchmarkConfig,
    TestKey, TestValue, Value, KEY_LEN, VALUE_LEN,
};
use std::ffi::{c_void, CString};
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;
use std::thread::sleep;
use std::time::{Duration, Instant};

pub struct ViperClient {
    kv: *mut crate::ViperDBFFI,
    client: *mut crate::ViperDBClientFFI,
}

impl KvInterface<TestKey, TestValue> for ViperClient {
    type E = bool;

    fn setup(config: &MicrobenchmarkConfig) -> Result<(), Self::E> {
        let mount_point = &config.mount_point;
        let pm_dev = &config.pm_dev;

        init_and_mount_pm_fs(&mount_point, &pm_dev);

        let file = config.mount_point.to_owned() + "/viper";
        println!("viper file: {:?}", file);
        let file_cstring = CString::new(file.clone()).unwrap();
        let file_ptr = file_cstring.as_ptr();
        // let init_size = 53687091200;
        let init_size = config.viper_region_size;

        println!("setting up initial viper instance");

        {
            unsafe {
                let kv = crate::viperdb_create(file_ptr, init_size);
                let client = crate::viperdb_get_client(kv);

                crate::viperdb_client_cleanup(client);
                crate::viperdb_cleanup(kv);
            }
        }
        ViperClient::cleanup(&mount_point, &pm_dev);
        println!("done creating\n");

        Ok(())
    }

    fn start(config: &MicrobenchmarkConfig) -> Result<Self, Self::E> {
        // init_and_mount_pm_fs();
        let mount_point = &config.mount_point;
        let pm_dev = &config.pm_dev;

        let file = mount_point.to_owned() + "/viper";
        let file_cstring = CString::new(file.clone()).unwrap();
        let file_ptr = file_cstring.as_ptr();
        // let init_size = 53687091200;
        let init_size = config.viper_region_size;

        // println!("creating viper client");

        // let kv = unsafe { crate::viperdb_create(file_ptr, init_size) };
        // let client = unsafe { crate::viperdb_get_client(kv) };

        // println!("done creating\n");

        // Ok(Self { kv, client })

        // sleep(Duration::from_secs(10));

        remount_pm_fs(&mount_point, &pm_dev);

        let kv = unsafe { crate::viperdb_create(file_ptr, init_size) };
        let client = unsafe { crate::viperdb_get_client(kv) };

        Ok(Self { kv, client })
    }

    fn timed_start(config: &MicrobenchmarkConfig) -> Result<(Self, Duration), Self::E> {
        let mount_point = &config.mount_point;
        let pm_dev = &config.pm_dev;

        println!("running timed start");

        let file = mount_point.to_owned() + "/viper";
        let file_cstring = CString::new(file.clone()).unwrap();
        let file_ptr = file_cstring.as_ptr();
        // let init_size = 53687091200;
        let init_size = config.viper_region_size;

        remount_pm_fs(&mount_point, &pm_dev);

        let t0 = Instant::now();
        let kv = unsafe { crate::viperdb_create(file_ptr, init_size) };
        let client = unsafe { crate::viperdb_get_client(kv) };
        let dur = t0.elapsed();

        println!("timed start done");

        Ok((Self { kv, client }, dur))
    }

    fn db_name() -> String {
        "viper".to_string()
    }

    fn put(&mut self, key: &TestKey, value: &TestValue) -> Result<(), Self::E> {
        let key = &key.key as *const [u8; KEY_LEN];
        let value = &value.value as *const [u8; VALUE_LEN];
        let result = unsafe { crate::viperdb_put(self.client, key, value) };
        match result {
            true => Ok(()),
            false => Err(false),
        }
    }

    fn get(&mut self, key: &TestKey) -> Result<TestValue, Self::E> {
        let key = &key.key as *const [u8; KEY_LEN];
        let mut value = TestValue::default();
        let result = unsafe { crate::viperdb_get(self.client, key, &mut value.value) };
        match result {
            true => Ok(value),
            false => Err(false),
        }
    }

    fn update(&mut self, key: &TestKey, value: &TestValue) -> Result<(), Self::E> {
        let key = &key.key as *const [u8; KEY_LEN];
        let value = &value.value as *const [u8; VALUE_LEN];
        let result = unsafe { crate::viperdb_update(self.client, key, value) };
        // result is false if the value already exists, so ignore it
        Ok(())
    }

    fn delete(&mut self, key: &TestKey) -> Result<(), Self::E> {
        let key = &key.key as *const [u8; KEY_LEN];
        let result = unsafe { crate::viperdb_delete(self.client, key) };
        match result {
            true => Ok(()),
            false => Err(false),
        }
    }

    fn cleanup(mount_point: &str, pm_dev: &str) {
        sleep(Duration::from_secs(1));
        unmount_pm_fs(pm_dev);
    }

    fn flush(&mut self) {}
}

impl Drop for ViperClient {
    fn drop(&mut self) {
        println!("dropping viper db");
        unsafe {
            crate::viperdb_client_cleanup(self.client);
            crate::viperdb_cleanup(self.kv);
        }
        println!("done dropping viperdb");
    }
}
