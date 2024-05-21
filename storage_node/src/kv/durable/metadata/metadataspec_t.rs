use crate::pmem::wrpm_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::kv::kvimpl_t::*;
use crate::pmem::pmemspec_t::*;
use crate::kv::durable::oplog::oplogspec_t::*;
use crate::kv::durable::metadata::layout_v::*;
use crate::kv::durable::metadata::metadataimpl_v::*;

verus! {
    pub struct TrustedMetadataPermission {
        ghost is_state_allowable: spec_fn(Seq<u8>) -> bool
    }

    impl CheckPermission<Seq<u8>> for TrustedMetadataPermission {
        closed spec fn check_permission(&self, state: Seq<u8>) -> bool {
            (self.is_state_allowable)(state)
        }
    }

    impl TrustedMetadataPermission {
         // TODO: REMOVE THIS
         #[verifier::external_body]
         pub proof fn fake_metadata_perm() -> (tracked perm: Self)
         {
             Self {
                 is_state_allowable: |s| true
             }
         }
    }

    pub struct MetadataTableViewEntry<K> {
        valid: bool,
        crc: u64,
        list_head_index: u64,
        item_index: u64,
        list_len: u64,
        key: K,
    }

    impl<K> MetadataTableViewEntry<K> {
        pub closed spec fn new(valid: u64, crc: u64, entry: ListEntryMetadata, key: K) -> Self {
            Self {
                valid: valid == CDB_TRUE,
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

        pub closed spec fn valid(self) -> bool {
            self.valid
        }
    }

    pub struct MetadataTableView<K> {
        metadata_header: MetadataTableHeader,
        metadata_table: Seq<MetadataTableViewEntry<K>>,
    }

    impl<K> MetadataTableView<K>
    {
        pub closed spec fn init(element_size: u32, node_size: u32, num_keys: u64) -> Self {
            Self {
                metadata_table: Seq::new(
                    num_keys as nat,
                    |i: int| MetadataTableViewEntry {
                        valid: false,
                        // it doesn't matter what these values are because the entry is invalid,
                        // so we just fill them in with arbitrary values
                        crc: arbitrary(),
                        list_head_index: arbitrary(),
                        item_index: arbitrary(),
                        list_len: arbitrary(),
                        key: arbitrary(),
                    }
                ),
                metadata_header: MetadataTableHeader {
                    element_size,
                    node_size,
                    num_keys,
                    version_number: METADATA_TABLE_VERSION_NUMBER,
                    _padding: 0,
                    program_guid: METADATA_TABLE_PROGRAM_GUID,
                },
            }
        }

        pub closed spec fn new(
            metadata_header: MetadataTableHeader, 
            metadata_table: Seq<MetadataTableViewEntry<K>>
        ) -> Self {
            Self {
                metadata_header,
                metadata_table,
            }
        }

        pub closed spec fn get_metadata_header(self) -> MetadataTableHeader
        {
            self.metadata_header
        }

        pub closed spec fn get_metadata_table(self) -> Seq<MetadataTableViewEntry<K>>
        {
            self.metadata_table
        }

        pub closed spec fn spec_index(self, index: int) -> Option<MetadataTableViewEntry<K>> {
            if 0 <= index < self.metadata_table.len() {
                Some(self.metadata_table[index])
            } else {
                None
            }
        }
    }
}