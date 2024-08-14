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
        pub crc: u64,
        pub list_head_index: u64,
        pub item_index: u64,
        pub list_len: u64,
        pub key: K,
    }

    impl<K> MetadataTableViewEntry<K> {
        pub open spec fn new(crc: u64, entry: ListEntryMetadata, key: K) -> Self {
            Self {
                crc,
                list_head_index: entry.head,
                item_index: entry.item_index,
                list_len: entry.length,
                key,
            }
        }

        pub closed spec fn crc(self) -> u64 {
            self.crc
        }

        pub closed spec fn list_head_index(self) -> u64 {
            self.list_head_index
        }

        pub open spec fn item_index(self) -> u64 {
            self.item_index
        }

        pub closed spec fn len(self) -> u64 
        {
            self.list_len
        }

        pub open spec fn key(self) -> K {
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

        pub open spec fn inv(self) -> bool
        {
            &&& forall |i| #![trigger self.durable_metadata_table[i]] {
                  let entries = self.durable_metadata_table;
                  0 <= i < entries.len() ==> !(entries[i] is Tentative)
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

        pub open spec fn get_tentative_metadata_table(self) -> Seq<DurableEntry<MetadataTableViewEntry<K>>>
        {
            self.tentative_metadata_table
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

        // We return the free indices as a set, not a seq, because the order they are listed in
        // doesn't actually matter, and then we don't have to worry about matching the order
        // they are kept in in executable code.
        // An index is only considered free if it is free in BOTH the tentative and durable views
        // of the table. If it's free in the tentative but not the durable, we haven't completed
        // the deallocation yet and the index should not be reallocated. If it's free in durable
        // but not tentative, we have a pending creation op at that index, so it's not free.
        pub open spec fn free_indices(self) -> Set<u64> {
            Set::new(|i: u64| {
                &&& 0 <= i < self.tentative_metadata_table.len() 
                &&& self.tentative_metadata_table[i as int] matches DurableEntry::Invalid 
                &&& self.durable_metadata_table[i as int] matches DurableEntry::Invalid
            })
        }
    }
}
