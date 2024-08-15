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
        pub entry: ListEntryMetadata,
        pub key: K,
    }

    impl<K> MetadataTableViewEntry<K> {
        pub open spec fn new(crc: u64, entry: ListEntryMetadata, key: K) -> Self {
            Self {
                crc,
                entry,
                key,
            }
        }

        pub closed spec fn crc(self) -> u64 {
            self.crc
        }

        pub closed spec fn list_head_index(self) -> u64 {
            self.entry.head
        }

        pub open spec fn item_index(self) -> u64 {
            self.entry.item_index
        }

        pub closed spec fn len(self) -> u64 
        {
            self.entry.length
        }

        pub open spec fn key(self) -> K {
            self.key
        }
    }

    #[verifier::ext_equal]
    pub struct MetadataTableView<K> {
        pub durable_metadata_table: Seq<DurableEntry<MetadataTableViewEntry<K>>>,
        pub outstanding_cdb_writes: Seq<Option<bool>>,
        pub outstanding_entry_writes: Seq<Option<MetadataTableViewEntry<K>>>,
    }

    impl<K> MetadataTableView<K>
    {
        pub open spec fn init(num_keys: u64) -> Self {
            Self {
                durable_metadata_table: Seq::new(num_keys as nat, |i: int| DurableEntry::Invalid),
                outstanding_cdb_writes: Seq::new(num_keys as nat, |i: int| None),
                outstanding_entry_writes: Seq::new(num_keys as nat, |i: int| None),
            }
        }

        pub open spec fn inv(self) -> bool
        {
            &&& forall |i| #![trigger self.durable_metadata_table[i]] {
                  let entries = self.durable_metadata_table;
                  0 <= i < entries.len() ==> !(entries[i] is Tentative)
            }
        }

        pub open spec fn no_outstanding_writes_to_index(self, idx: int) -> bool
        {
            &&& self.outstanding_cdb_writes[idx] is None
            &&& self.outstanding_entry_writes[idx] is None
        }

        pub open spec fn no_outstanding_writes(self) -> bool
        {
            forall|i| 0 <= i < self.durable_metadata_table.len() ==> self.no_outstanding_writes_to_index(i)
        }

        pub open spec fn no_outstanding_writes_except_to_index(self, idx: int) -> bool
        {
            forall|i| 0 <= i < self.durable_metadata_table.len() && i != idx ==> self.no_outstanding_writes_to_index(i)
        }

        pub open spec fn new(
            metadata_table: Seq<DurableEntry<MetadataTableViewEntry<K>>>
        ) -> Self {
            Self {
                durable_metadata_table: metadata_table,
                outstanding_cdb_writes: Seq::new(metadata_table.len() as nat, |i: int| None),
                outstanding_entry_writes: Seq::new(metadata_table.len() as nat, |i: int| None),
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

        // We return the free indices as a set, not a seq, because the order they are listed in
        // doesn't actually matter, and then we don't have to worry about matching the order
        // they are kept in in executable code.
        // An index is only considered free if it is free in the durable view of the table and
        // if it has no outstanding writes.
        pub open spec fn free_indices(self) -> Set<u64> {
            Set::new(|i: u64| {
                &&& 0 <= i < self.durable_metadata_table.len() 
                &&& self.outstanding_cdb_writes[i as int] is None
                &&& self.outstanding_entry_writes[i as int] is None
                &&& self.durable_metadata_table[i as int] matches DurableEntry::Invalid
            })
        }
    }
}
