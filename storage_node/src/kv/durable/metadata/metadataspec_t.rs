use crate::pmem::wrpm_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::kv::kvimpl_t::*;
use crate::pmem::pmemspec_t::*;
use crate::kv::durable::oplog::oplogspec_t::*;
use crate::kv::durable::metadata::layout_v::*;
use crate::kv::durable::metadata::metadataimpl_v::*;
use crate::kv::durable::util_v::*;

verus! {
    pub struct MetadataTableViewEntry<K> {
        crc: u64,
        list_head_index: u64,
        item_index: u64,
        list_len: u64,
        key: K,
    }

    impl<K> MetadataTableViewEntry<K> {
        pub closed spec fn new(crc: u64, entry: ListEntryMetadata, key: K) -> Self {
            Self {
                crc,
                list_head_index: entry.spec_head(),
                item_index: entry.spec_item_index(),
                list_len: entry.spec_len(),
                key,
            }
        }

        pub closed spec fn crc(self) -> u64 {
            self.crc
        }

        pub closed spec fn list_head_index(self) -> u64 {
            self.list_head_index
        }

        pub closed spec fn item_index(self) -> u64 {
            self.item_index
        }

        pub closed spec fn len(self) -> u64 
        {
            self.list_len
        }

        pub closed spec fn key(self) -> K {
            self.key
        }
    }

    #[verifier::ext_equal]
    pub struct MetadataTableView<K> {
        pub durable_metadata_table: Seq<DurableEntry<MetadataTableViewEntry<K>>>,
        pub tentative_metadata_table: Seq<DurableEntry<MetadataTableViewEntry<K>>>,
    }

    impl<K> MetadataTableView<K>
    {
        pub open spec fn init(num_keys: u64) -> Self {
            Self {
                durable_metadata_table: Seq::new(
                    num_keys as nat,
                    |i: int| DurableEntry::Invalid
                ),
                tentative_metadata_table: Seq::new(
                    num_keys as nat,
                    |i: int| DurableEntry::Invalid
                ),
            }
        }

        pub open spec fn new(
            metadata_table: Seq<DurableEntry<MetadataTableViewEntry<K>>>
        ) -> Self {
            Self {
                durable_metadata_table: metadata_table,
                tentative_metadata_table: metadata_table
            }
        }

        pub open spec fn get_durable_metadata_table(self) -> Seq<DurableEntry<MetadataTableViewEntry<K>>>
        {
            self.durable_metadata_table
        }

        // pub closed spec fn spec_index(self, index: int) -> Option<MetadataTableViewEntry<K>> {
        //     if 0 <= index < self.metadata_table.len() {
        //         self.metadata_table[index]
        //     } else {
        //         None
        //     }
        // }

        pub open spec fn valid_item_indices(self) -> Set<int> {
            Set::new(|i: int| exists |j: int| {
                    &&& 0 <= j < self.durable_metadata_table.len() 
                    &&& #[trigger] self.durable_metadata_table[j] matches DurableEntry::Valid(entry)
                    &&& entry.item_index() == i
                }
            )
        }
    }
}
