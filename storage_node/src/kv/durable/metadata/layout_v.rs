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

    pub open spec(checked) fn parse_metadata_entry<K>(bytes: Seq<u8>) -> Option<(K, ListEntryMetadata)>
        where 
            K: PmCopy,
        recommends
            bytes.len() == ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
            RELATIVE_POS_OF_VALID_CDB + u64::spec_size_of() <= bytes.len(),
            RELATIVE_POS_OF_ENTRY_METADATA_CRC + u64::spec_size_of() <= bytes.len(),
            RELATIVE_POS_OF_ENTRY_METADATA + ListEntryMetadata::spec_size_of() <= bytes.len(),
    {
        let cdb = spec_u64_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_VALID_CDB as int, RELATIVE_POS_OF_VALID_CDB + u64::spec_size_of()));
        let crc = spec_u64_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_ENTRY_METADATA_CRC as int, RELATIVE_POS_OF_ENTRY_METADATA_CRC + u64::spec_size_of()));
        let metadata_bytes = bytes.subrange(RELATIVE_POS_OF_ENTRY_METADATA as int, RELATIVE_POS_OF_ENTRY_METADATA + ListEntryMetadata::spec_size_of());
        let key_bytes = bytes.subrange(RELATIVE_POS_OF_ENTRY_KEY as int, RELATIVE_POS_OF_ENTRY_KEY + K::spec_size_of());
        let metadata = ListEntryMetadata::spec_from_bytes(metadata_bytes);
        let key = K::spec_from_bytes(key_bytes);
    
        if cdb == CDB_FALSE {
            None 
        } else {
            // If the CRC does not match the contents, it's not a valid entry
            if crc != spec_crc_u64(metadata_bytes + key_bytes) {
                None 
            } else {
                Some((key, metadata))
            }
        }
    }

    pub open spec fn parse_metadata_table<K>(mem: Seq<u8>, num_keys: u64) -> Option<Seq<Option<MetadataTableViewEntry<K>>>>
        where 
            K: PmCopy
    {
        let table_entry_slot_size = ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of();
        // check that the metadata in the header makes sense/is valid
        if mem.len() < table_entry_slot_size * num_keys {
            None
        } else {
            let table_view = Seq::new(
                num_keys as nat,
                |i: int| {
                    let bytes = mem.subrange(i * table_entry_slot_size, i * table_entry_slot_size + table_entry_slot_size);
                    let cdb_bytes = bytes.subrange(RELATIVE_POS_OF_VALID_CDB as int, RELATIVE_POS_OF_VALID_CDB + u64::spec_size_of());
                    let crc_bytes = bytes.subrange(RELATIVE_POS_OF_ENTRY_METADATA_CRC as int, RELATIVE_POS_OF_ENTRY_METADATA_CRC + u64::spec_size_of());
                    let entry_bytes = bytes.subrange(RELATIVE_POS_OF_ENTRY_METADATA as int, RELATIVE_POS_OF_ENTRY_METADATA + ListEntryMetadata::spec_size_of());
                    let key_bytes = bytes.subrange(RELATIVE_POS_OF_ENTRY_KEY as int, RELATIVE_POS_OF_ENTRY_KEY + K::spec_size_of());

                    let cdb = u64::spec_from_bytes(cdb_bytes);
                    let crc = u64::spec_from_bytes(crc_bytes);
                    let entry = ListEntryMetadata::spec_from_bytes(entry_bytes);
                    let key = K::spec_from_bytes(key_bytes);

                    // we can't check CRCs in this closure, since its return value is only used to construct the Seq
                    // we can't construct the view here because we need to check the CRCs, so just return a tuple with all 
                    // of the information we need and organize it into a nicer structure later
                    (cdb, crc, entry, key)

                }
            );
            // Finally, return None if any of the CRCs are invalid
            if !(forall |i: int| 0 <= i < table_view.len() ==> {
                let (cdb, crc, entry, key) = #[trigger] table_view[i];
                cdb == CDB_TRUE ==> crc == spec_crc_u64(entry.spec_to_bytes() + key.spec_to_bytes())
            }) {
                None
            } else {
                Some(Seq::new(
                    table_view.len(),
                    |i: int| {
                        let (cdb, crc, entry, key) = table_view[i];
                        if cdb == CDB_FALSE {
                            None 
                        } else {
                            Some(MetadataTableViewEntry::new(cdb, crc, entry, key))
                        }
                        
                    }
                ))
            }
        }
    }


    impl PmCopy for ListEntryMetadata {}

}
