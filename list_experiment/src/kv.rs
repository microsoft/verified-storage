use crate::err::Error;
use crate::{MemoryPool, PmCopy};

pub trait KV<P: MemoryPool, K: PmCopy>: Sized {
    fn setup(
        mem_pool: &mut P,
        key_table_size: u64,
        list_table_size: u64,
        journal_size: u64,
    ) -> Result<Self, Error>;

    fn insert(&mut self, mem_pool: &mut P, key: &K) -> Result<(), Error>;

    fn append<const N: usize>(
        &mut self,
        mem_pool: &mut P,
        key: &K,
        list_entry: &[u8; N],
    ) -> Result<(), Error>;

    fn trim(&mut self, mem_pool: &mut P, key: &K, trim_len: u64) -> Result<(), Error>;

    fn read_list<const N: usize>(&self, mem_pool: &P, key: &K) -> Result<Vec<[u8; N]>, Error>;
}
