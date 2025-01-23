use crate::{journal::Journal, journaled_singleton_list::*, key_table::KeyTable, PmCopy};

pub struct SingletonKV<K: PmCopy, const N: usize> {
    key_table: KeyTable<K, SingletonMetadata>,
    list_table: SingletonListTable<N>,
    // list: DurableSingletonList<N>,
    journal: Journal,
}

struct SingletonMetadata {
    list_head: u64,
}

impl PmCopy for SingletonMetadata {}
