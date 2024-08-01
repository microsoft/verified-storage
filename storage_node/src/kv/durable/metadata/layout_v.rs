use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use vstd::bytes::*;
use vstd::prelude::*;
use vstd::ptr::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmemspec_t::*;
use crate::kv::durable::metadata::metadataspec_t::*;
use crate::kv::durable::util_v::*;
use crate::pmem::traits_t::*;
use crate::util_v::*;
use deps_hack::{PmSafe, PmSized};

verus! {
    // Metadata region
    // Starts with a metadata header that is written at setup and
    // subsequently immutable.
    pub const ABSOLUTE_POS_OF_METADATA_HEADER: u64 = 0;
    pub const RELATIVE_POS_OF_ELEMENT_SIZE: u64 = 0;
    pub const RELATIVE_POS_OF_NODE_SIZE: u64 = 4;
    pub const RELATIVE_POS_OF_NUM_KEYS: u64 = 8;
    pub const RELATIVE_POS_OF_VERSION_NUMBER: u64 = 16;
    pub const RELATIVE_POS_OF_PADDING: u64 = 24;
    pub const RELATIVE_POS_OF_PROGRAM_GUID: u64 = 32;
    pub const ABSOLUTE_POS_OF_HEADER_CRC: u64 = 48;

    pub const ABSOLUTE_POS_OF_METADATA_TABLE: u64 = 56;

    // The current version number, and the only one whose contents
    // this program can read, is the following:
    pub const METADATA_TABLE_VERSION_NUMBER: u64 = 1;

    // This GUID was generated randomly and is meant to describe the
    // durable list program, even if it has future versions.
    pub const METADATA_TABLE_PROGRAM_GUID: u128 = 0xC357BD8AA950BDA76345F1DCEC7DBF3Fu128;

    // TODO: we use node size in some places and elements per node in others
    // should probably standardize this
    #[repr(C)]
    #[derive(PmSized, PmSafe, Copy, Clone)]
    pub struct MetadataTableHeader
    {
        pub element_size: u32, // NOTE: this includes the CRC of each element
        pub node_size: u32,
        pub num_keys: u64,
        pub version_number: u64,
        pub _padding: u64, // TODO: this should be item size
        pub program_guid: u128,
    }

    // TODO: should this be trusted?
    impl PmCopy for MetadataTableHeader {}

    // Per-entry relative offsets for list entry metadata
    // The list metadata region is an array of list entry metadata
    // structures, each of which contains metadata about the list
    // associated with a given key of type K. K must be Sized,
    // but we need to be generic over any K, so the key is the last
    // field of the structure to avoid layout weirdness.
    // This means it is easiest to put the CRC *before* the corresponding
    // ListEntryMetadata structure, so the constants here are a bit weird

    pub const RELATIVE_POS_OF_VALID_CDB: u64 = 0;
    pub const RELATIVE_POS_OF_ENTRY_METADATA_CRC: u64 = 8;
    pub const RELATIVE_POS_OF_ENTRY_METADATA: u64 = 16; // pos of the ListEntryMetadata structure to its slot's offset
    pub const RELATIVE_POS_OF_ENTRY_METADATA_HEAD: u64 = 0; // pos of head field relative to ListEntryMetadata structure pos
    pub const RELATIVE_POS_OF_ENTRY_METADATA_TAIL: u64 = 8;
    pub const RELATIVE_POS_OF_ENTRY_METADATA_LENGTH: u64 = 16;
    pub const RELATIVE_POS_OF_ENTRY_METADATA_FIRST_OFFSET: u64 = 24;
    pub const RELATIVE_POS_OF_ENTRY_METADATA_ITEM_INDEX: u64 = 32;
    pub const RELATIVE_POS_OF_ENTRY_KEY: u64 = 56; // relative to the start of the slot (not the start of the metadata struct)    

    #[repr(C)]
    #[derive(PmSized, PmSafe, Copy, Clone, Debug)]
    pub struct ListEntryMetadata
    {
        pub head: u64,
        pub tail: u64,
        pub length: u64,
        pub first_entry_offset: u64, // offset of the first live entry in the head node
        pub item_index: u64,
    }

    impl ListEntryMetadata {
        pub closed spec fn spec_new(head: u64, tail: u64, length: u64, first_entry_offset: u64, item_index: u64,) -> Self {
            Self {head, tail, length, first_entry_offset, item_index}
        }

        pub exec fn new(head: u64, tail: u64, length: u64, first_entry_offset: u64, item_index: u64) -> (out: Self)
            ensures 
                out == Self::spec_new(head, tail, length, first_entry_offset, item_index)
        {
            Self {head, tail, length, first_entry_offset, item_index}
        }

        pub fn get_head(&self) -> (out: u64) 
            ensures
                out == self.spec_head()
        {
            self.head
        }

        pub closed spec fn spec_head(self) -> u64 
        {
            self.head
        }
        
        pub closed spec fn spec_tail(self) -> u64 
        {
            self.tail
        }

        pub closed spec fn spec_item_index(self) -> u64 
        {
            self.item_index
        }

        pub closed spec fn spec_len(self) -> u64 
        {
            self.length
        }
    }

    pub open spec fn validate_metadata_entry<K>(bytes: Seq<u8>) -> bool
        where 
            K: PmCopy,
        recommends
            bytes.len() == ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
            RELATIVE_POS_OF_VALID_CDB + u64::spec_size_of() <= bytes.len(),
            RELATIVE_POS_OF_ENTRY_METADATA_CRC + u64::spec_size_of() <= bytes.len(),
            RELATIVE_POS_OF_ENTRY_METADATA + ListEntryMetadata::spec_size_of() <= bytes.len(),
    {
        let cdb_bytes = extract_bytes(bytes, RELATIVE_POS_OF_VALID_CDB as nat, u64::spec_size_of());
        let crc_bytes = extract_bytes(bytes, RELATIVE_POS_OF_ENTRY_METADATA_CRC as nat, u64::spec_size_of());
        let metadata_bytes = extract_bytes(bytes, RELATIVE_POS_OF_ENTRY_METADATA as nat,
                                           ListEntryMetadata::spec_size_of());
        let key_bytes = extract_bytes(bytes, RELATIVE_POS_OF_ENTRY_KEY as nat, K::spec_size_of());

        let cdb = u64::spec_from_bytes(cdb_bytes);
        let crc = u64::spec_from_bytes(crc_bytes);
        
        &&& u64::bytes_parseable(cdb_bytes)
        &&& u64::bytes_parseable(crc_bytes)
        &&& ListEntryMetadata::bytes_parseable(metadata_bytes)
        &&& K::bytes_parseable(key_bytes)
        &&& {
            ||| cdb == CDB_FALSE
            ||| {
                &&& cdb == CDB_TRUE
                &&& crc == spec_crc_u64(metadata_bytes + key_bytes)
            }
        }   
    }

    pub open spec fn validate_metadata_entries<K>(mem: Seq<u8>, num_keys: nat, metadata_node_size: nat) -> bool
        where 
            K: PmCopy,
        recommends
            mem.len() >= num_keys * metadata_node_size,
    {
        forall |i: nat| i < num_keys ==> validate_metadata_entry::<K>(#[trigger] extract_bytes(mem, i * metadata_node_size,
                                                                                        metadata_node_size))
    }

    pub open spec fn parse_metadata_entry<K>(bytes: Seq<u8>) -> DurableEntry<MetadataTableViewEntry<K>>
        where 
            K: PmCopy,
        recommends
            bytes.len() == ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
            RELATIVE_POS_OF_VALID_CDB + u64::spec_size_of() <= bytes.len(),
            RELATIVE_POS_OF_ENTRY_METADATA_CRC + u64::spec_size_of() <= bytes.len(),
            RELATIVE_POS_OF_ENTRY_METADATA + ListEntryMetadata::spec_size_of() <= bytes.len(),
            validate_metadata_entry::<K>(bytes)
    {
        let cdb_bytes = extract_bytes(bytes, RELATIVE_POS_OF_VALID_CDB as nat, u64::spec_size_of());
        let crc_bytes = extract_bytes(bytes, RELATIVE_POS_OF_ENTRY_METADATA_CRC as nat, u64::spec_size_of());
        let metadata_bytes = extract_bytes(bytes, RELATIVE_POS_OF_ENTRY_METADATA as nat,
                                           ListEntryMetadata::spec_size_of());
        let key_bytes = extract_bytes(bytes, RELATIVE_POS_OF_ENTRY_KEY as nat, K::spec_size_of());

        let cdb = u64::spec_from_bytes(cdb_bytes);
        let crc = u64::spec_from_bytes(crc_bytes);
        let metadata = ListEntryMetadata::spec_from_bytes(metadata_bytes);
        let key = K::spec_from_bytes(key_bytes);
        
        if cdb == CDB_FALSE {
            DurableEntry::Invalid
        } else {
            DurableEntry::Valid(MetadataTableViewEntry::<K>::new(crc, metadata, key))
        }
    }

    pub open spec fn parse_metadata_table<K>(mem: Seq<u8>, num_keys: u64, metadata_node_size: u32)
                                             -> Option<MetadataTableView<K>>
        where 
            K: PmCopy
    {
        let table_entry_slot_size =
              ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of();
        // check that the metadata in the header makes sense/is valid
        if mem.len() < num_keys * table_entry_slot_size {
            None
        } else {
            if !validate_metadata_entries::<K>(mem, num_keys as nat, metadata_node_size as nat) {
                None
            }
            else {
                Some(MetadataTableView::<K>::new(Seq::new(
                    num_keys as nat,
                    |i: int| parse_metadata_entry(extract_bytes(mem, (i * metadata_node_size as int) as nat,
                                                              metadata_node_size as nat))
                )))
            }
        }
    }


    impl PmCopy for ListEntryMetadata {}

}
