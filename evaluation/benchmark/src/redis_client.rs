use redis::{Client, Connection, RedisResult, RedisError, Commands, FromRedisValue};
use crate::kv_interface::{KvInterface, Key, Value};
use std::process::*;
use std::thread::sleep;
use std::time::Duration;
use core::marker::PhantomData;
use storage_node::pmem::pmcopy_t::PmCopy;
use std::hash::{Hash, DefaultHasher, Hasher};

const INDEX_KEY: &str = "_indices";

pub struct RedisClient<K, V> 
    where
        K: PmCopy + Key,
        V: PmCopy + Value,
{
    server: Child,
    cxn: Connection,
    _key_type: PhantomData<K>,
    _value_type: PhantomData<V>,
}

impl<K, V> RedisClient<K, V> 
    where 
        K: PmCopy + Key,
        V: PmCopy + Value,
{
    pub fn new_connection() -> RedisResult<Connection> {
        let client = Client::open("redis://127.0.0.1/")?;
        let cxn = client.get_connection()?;
        Ok(cxn)
    }

    // TODO: does this increase redis latency by too much?
    fn hash(key_str: &str) -> u64 {
        let mut s = DefaultHasher::new();
        key_str.hash(&mut s);
        s.finish()
    }
}

impl<K, V> KvInterface<K, V> for RedisClient<K, V>
    where
        K: PmCopy + Key,
        V: PmCopy + Value + FromRedisValue,
{
    type E = RedisError;

    fn init() -> Result<Self, Self::E> {
        // TODO @hayley don't hardcode paths in this function

        println!("Mounting PM FS...");
        // Set up PM with a fresh file system instance
        let status = Command::new("sudo")
            .args(["mkfs.ext4", crate::PM_DEV, "-F"])
            .status()
            .expect("mkfs.ext4 failed");

        let status = Command::new("sudo")
            .args(["mount", "-o", "dax", crate::PM_DEV, crate::MOUNT_POINT])
            .status()
            .expect("mount failed");
        println!("Mounted");

        // Start the redis instance
        
        let redis_server = Command::new("sudo")
            .args(["../pmem-redis/src/redis-server"]) // path to server binary
            .args(["../pmem-redis/redis.conf"]) // config file
            .spawn()
            .expect("redis-server failed to start");
            
        println!("Started redis server");
        
        sleep(Duration::from_secs(2));

        // then establish a connection to it
        let cxn = Self::new_connection()?;

        println!("Connected to redis server");

        Ok(Self {
            server: redis_server,
            cxn,
            _key_type: PhantomData,
            _value_type: PhantomData,
        })
    }

    fn db_name() -> String {
        "redis".to_string()
    }

    // These operations use the same calls/KV structure as YCSB.

    #[allow(dependency_on_unit_never_type_fallback)]
    fn put(&mut self, key: &K, value: &V) -> Result<(), Self::E> {
        // 1. add key and field+value to a hash
        // NOTE: if you want to increase the number of fields in the value, this code 
        // will have to change
        let key_str = key.key_str();
        let field_str = value.field_str();
        let value_str = value.value_str();
        self.cxn.hset(key_str, field_str, value_str)?;

        // 2. add the key to the set of keys
        self.cxn.zadd(INDEX_KEY, key_str, Self::hash(key_str))?;

        Ok(())
    }

    fn get(&mut self, key: &K) -> Result<V, Self::E> {
        let key_str = key.key_str();
        let redis_value = self.cxn.hgetall::<&str, redis::Value>(key_str)?;
        let result = V::from_redis_value(&redis_value);
        result
    }

    fn update(&mut self, key: &K, value: &V) -> Result<(), Self::E> {
        let key_str = key.key_str();
        let field_str = value.field_str();
        let value_str = value.value_str();
        self.cxn.hset(key_str, field_str, value_str)?;

        Ok(())
    }

    fn delete(&mut self, key: &K) -> Result<(), Self::E> {
        let key_str = key.key_str();
        self.cxn.del(&key_str)?;
        self.cxn.zrem(INDEX_KEY, &key_str)?;

        Ok(())
    }
}

impl<K, V> Drop for RedisClient<K, V> 
    where
        K: PmCopy + Key,
        V: PmCopy + Value,
{
    // Automatically kills the server process when the RedisClient is 
    // dropped. I'm *pretty* sure the redis crate handles closing the 
    // connection when the Connection is dropped
    fn drop(&mut self) {
        self.server.kill().expect("redis-server could not be killed");
        println!("Stopped redis server, unmounting...");

        sleep(Duration::from_secs(2));

        let status = Command::new("sudo")
            .args(["umount", crate::PM_DEV])
            .status();
        if let Err(e) = status {
            println!("{:?}", e);
        }

        println!("Finished cleaning up redis");
    }
}