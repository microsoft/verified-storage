use crate::err::Error;
use crate::{MemoryPool, PmCopy};

pub trait KV<P: MemoryPool, K: PmCopy> {
    fn setup(
        mem_pool: &mut P,
        num_keys: u64,
        list_region_size: u64,
        journal_size: u64,
    ) -> Result<(), Error>;

    fn insert(mem_pool: &mut P, key: &K) -> Result<(), Error>;

    fn append<const N: usize>(mem_pool: &mut P, key: &K, list_entry: &[u8; N])
        -> Result<(), Error>;

    fn trim(mem_pool: &mut P, key: &K, trim_len: u64) -> Result<(), Error>;
}
