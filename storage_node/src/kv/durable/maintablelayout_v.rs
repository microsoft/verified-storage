use builtin::*;
use builtin_macros::*;
use vstd::arithmetic::mul::lemma_mul_strict_inequality;
use core::fmt::Debug;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse;
use vstd::bytes::*;
use vstd::prelude::*;
use crate::kv::durable::commonlayout_v::*;
use crate::kv::durable::inv_v::*;
use crate::kv::durable::maintable_v::*;
use crate::kv::durable::util_v::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::*;
use crate::util_v::*;
use deps_hack::{PmSafe, PmSized};

verus! {
    // Metadata region

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

    impl PmCopy for ListEntryMetadata {}

    impl ListEntryMetadata {
        pub open spec fn spec_new(head: u64, tail: u64, length: u64, first_entry_offset: u64, item_index: u64,) -> Self {
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

    pub open spec fn validate_main_entry<K>(bytes: Seq<u8>, num_keys: nat) -> bool
        where 
            K: PmCopy,
        recommends
            bytes.len() == ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
            RELATIVE_POS_OF_VALID_CDB + u64::spec_size_of() <= bytes.len(),
            RELATIVE_POS_OF_ENTRY_METADATA_CRC + u64::spec_size_of() <= bytes.len(),
            RELATIVE_POS_OF_ENTRY_METADATA + ListEntryMetadata::spec_size_of() <= bytes.len(),
    {
        let cdb_bytes = extract_bytes(bytes, 0, u64::spec_size_of());
        let crc_bytes = extract_bytes(bytes, u64::spec_size_of(), u64::spec_size_of());
        let metadata_bytes = extract_bytes(bytes, (u64::spec_size_of() * 2) as nat,
                                           ListEntryMetadata::spec_size_of());
        let key_bytes = extract_bytes(bytes, (ListEntryMetadata::spec_size_of() + u64::spec_size_of() * 2) as nat, K::spec_size_of());

        let cdb = u64::spec_from_bytes(cdb_bytes);
        let crc = u64::spec_from_bytes(crc_bytes);
        let metadata = ListEntryMetadata::spec_from_bytes(metadata_bytes);

        &&& u64::bytes_parseable(cdb_bytes)
        &&& {
            ||| cdb == CDB_FALSE
            ||| {
                &&& cdb == CDB_TRUE
                &&& crc == spec_crc_u64(metadata_bytes + key_bytes)
                &&& u64::bytes_parseable(crc_bytes)
                &&& ListEntryMetadata::bytes_parseable(metadata_bytes)
                &&& K::bytes_parseable(key_bytes)
                &&& 0 <= metadata.item_index < num_keys
            }
        }   
    }

    pub open spec fn validate_main_entries<K>(mem: Seq<u8>, num_keys: nat, main_table_entry_size: nat) -> bool
        where 
            K: PmCopy,
        recommends
            mem.len() >= num_keys * main_table_entry_size,
    {
        forall |i: nat| i < num_keys ==> validate_main_entry::<K>(#[trigger] extract_bytes(mem, index_to_offset(i, main_table_entry_size),
                                                                                        main_table_entry_size), num_keys)
    }

    pub open spec fn parse_main_entries<K>(mem: Seq<u8>, num_keys: nat, main_table_entry_size: nat) -> Seq<Option<MainTableViewEntry<K>>>
        where 
            K: PmCopy,
    {
        Seq::new(
            num_keys as nat,
            |i: int| parse_main_entry(extract_bytes(mem, index_to_offset(i as nat, main_table_entry_size),
                                                      main_table_entry_size as nat), num_keys as nat)
        )
    }

    pub open spec fn parse_main_entry<K>(bytes: Seq<u8>, num_keys: nat) -> Option<MainTableViewEntry<K>>
        where 
            K: PmCopy,
        recommends
            bytes.len() == ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
            // RELATIVE_POS_OF_VALID_CDB + u64::spec_size_of() <= bytes.len(),
            // RELATIVE_POS_OF_ENTRY_METADATA_CRC + u64::spec_size_of() <= bytes.len(),
            // RELATIVE_POS_OF_ENTRY_METADATA + ListEntryMetadata::spec_size_of() <= bytes.len(),
            validate_main_entry::<K>(bytes, num_keys)
    {
        let cdb_bytes = extract_bytes(bytes, 0, u64::spec_size_of());
        let crc_bytes = extract_bytes(bytes, u64::spec_size_of(), u64::spec_size_of());
        let metadata_bytes = extract_bytes(bytes, u64::spec_size_of() * 2,
                                           ListEntryMetadata::spec_size_of());
        let key_bytes = extract_bytes(bytes, u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of(), K::spec_size_of());

        let cdb = u64::spec_from_bytes(cdb_bytes);
        let crc = u64::spec_from_bytes(crc_bytes);
        let metadata = ListEntryMetadata::spec_from_bytes(metadata_bytes);
        let key = K::spec_from_bytes(key_bytes);
        
        if cdb == CDB_FALSE {
            None
        } else {
            // cdb == CDB_TRUE
            Some(MainTableViewEntry::<K>::new(metadata, key))
        }
    }

    pub open spec fn parse_main_table<K>(mem: Seq<u8>, num_keys: u64, main_table_entry_size: u32)
                                         -> Option<MainTableView<K>>
        where 
            K: PmCopy
    {
        let table_entry_slot_size =
              ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of();
        // check that the metadata in the header makes sense/is valid
        if mem.len() < num_keys * table_entry_slot_size {
            None
        } else {
            if !validate_main_entries::<K>(mem, num_keys as nat, main_table_entry_size as nat) {
                None
            }
            else {
                let entries = parse_main_entries(mem, num_keys as nat, main_table_entry_size as nat);
                if no_duplicate_item_indexes(entries) {
                    Some(MainTableView::<K>::new(entries))
                } else {
                    None
                }
            }
        }
    }

    // pub open spec fn validate_main_entries_after_parse<K>(entries: Seq<DurableEntry<MainTableViewEntry<K>>>, 
    //         num_keys: nat, main_table_entry_size: nat) -> bool 
    //     where 
    //         K: PmCopy
    // {
    //     // check the contents of each entry
    //     &&& forall |i: int| 0 <= i < num_keys ==> validate_main_entry_after_parse(#[trigger] entries[i], num_keys)
    //     // check that there are no duplicate item indexes
    //     &&& no_duplicate_item_indexes(entries)
    // }

    // pub open spec fn validate_main_entry_after_parse<K>(
    //         entry: DurableEntry<MainTableViewEntry<K>>, num_keys: nat) -> bool
    //     where 
    //         K: PmCopy
    // {
    //     match entry {
    //         DurableEntry::Valid(entry) => {
    //             // TODO: does it make ANY sense to check that the bytes are parseable 
    //             // after they have been parsed?? 
    //             let crc_bytes = entry.crc.spec_to_bytes();
    //             let metadata_bytes = entry.entry.spec_to_bytes();
    //             let key_bytes = entry.key.spec_to_bytes();

    //             &&& entry.cdb == CDB_TRUE
    //             &&& entry.crc == spec_crc_u64(metadata_bytes + key_bytes)
    //             &&& u64::bytes_parseable(crc_bytes)
    //             &&& ListEntryMetadata::bytes_parseable(metadata_bytes)
    //             &&& K::bytes_parseable(key_bytes)
    //             &&& 0 <= entry.entry.item_index < num_keys
    //         }
    //         _ => true
    //     }
    // }

    pub open spec fn no_duplicate_item_indexes<K>(entries: Seq<Option<MainTableViewEntry<K>>>) -> bool 
        where 
            K: PmCopy
    {
        forall |i: int, j: int| {
            &&& 0 <= i < entries.len()
            &&& 0 <= j < entries.len()
            &&& i != j
            &&& entries[i] is Some
            &&& entries[j] is Some
        } ==> #[trigger] entries[i].unwrap().item_index() != #[trigger] entries[j].unwrap().item_index()
    }

    // // This function parses metadata entries before they are validated. It works the same
    // // way as the old parse-after-validate function, although we have not yet checked 
    // // that the fields are parseable or that the CDBs are correct. 
    // pub open spec fn parse_main_entries_before_validate<K>(mem: Seq<u8>, num_keys: u64, 
    //         main_table_entry_size: u32) -> Seq<DurableEntry<MainTableViewEntry<K>>>
    //     where 
    //         K: PmCopy
    // {
    //     Seq::new(num_keys as nat, |i: int| parse_main_entry_before_validate(extract_bytes(mem, (i * main_table_entry_size as int) as nat,
    //         main_table_entry_size as nat), num_keys as nat))
    // }

    // pub open spec fn parse_main_entry_before_validate<K>(bytes: Seq<u8>, num_keys: nat) -> DurableEntry<MainTableViewEntry<K>>
    // where 
    //     K: PmCopy
    // {
    //     let cdb_bytes = extract_bytes(bytes, 0, u64::spec_size_of());
    //     let crc_bytes = extract_bytes(bytes, u64::spec_size_of(), u64::spec_size_of());
    //     let metadata_bytes = extract_bytes(bytes, u64::spec_size_of() * 2,
    //                                     ListEntryMetadata::spec_size_of());
    //     let key_bytes = extract_bytes(bytes, u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of(), K::spec_size_of());

    //     let cdb = u64::spec_from_bytes(cdb_bytes);
    //     let crc = u64::spec_from_bytes(crc_bytes);
    //     let metadata = ListEntryMetadata::spec_from_bytes(metadata_bytes);
    //     let key = K::spec_from_bytes(key_bytes);
        
    //     if cdb == CDB_FALSE {
    //         DurableEntry::Invalid
    //     } else {
    //         DurableEntry::Valid(MainTableViewEntry::<K>::new(cdb, crc, metadata, key))
    //     }
    // }

    // pub open spec fn parse_main_table2<K>(mem: Seq<u8>, num_keys: u64, 
    //         main_table_entry_size: u32) -> Option<MainTableView<K>>
    //     where 
    //         K: PmCopy
    // {
    //     let table_entry_slot_size =
    //           ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of();
        
    //     // Check that the sequence of bytes is large enough to parse
    //     if mem.len() < num_keys * table_entry_slot_size {
    //         None
    //     } else {
    //         // Parse the entries. These entries have not yet been validated so they may be meaningless/corrupted
    //         let entries = parse_main_entries_before_validate(mem, num_keys, main_table_entry_size);
    //         if validate_main_entries_after_parse(entries, num_keys as nat, main_table_entry_size as nat) {
    //             Some(MainTableView::<K>::new(entries))
    //         } else {
    //             None
    //         } 
    //     }
    // }

    pub proof fn lemma_metadata_fits<K>(k: int, num_keys: int, main_table_entry_size: int)
        requires
            0 <= k < num_keys,
            0 <= main_table_entry_size,
        ensures
            k * main_table_entry_size + main_table_entry_size <= num_keys * main_table_entry_size
    {
        vstd::arithmetic::mul::lemma_mul_inequality(k + 1, num_keys, main_table_entry_size);
        vstd::arithmetic::mul::lemma_mul_basics(main_table_entry_size);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(main_table_entry_size, k, 1);
    }

    pub proof fn lemma_if_table_parseable_then_all_entries_parseable<K>(mem: Seq<u8>, num_keys: u64, main_table_entry_size: u32)
    where 
        K: PmCopy
    requires
        parse_main_table::<K>(mem, num_keys, main_table_entry_size) is Some,
        main_table_entry_size == u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of() + K::spec_size_of(),
        num_keys * main_table_entry_size <= mem.len(),
        K::spec_size_of() > 0,
        ListEntryMetadata::spec_size_of() > 0,
    ensures 
        forall |i: nat| i < num_keys ==> {
            let cdb_bytes = extract_bytes(mem, #[trigger] index_to_offset(i, main_table_entry_size as nat), u64::spec_size_of());
            let crc_bytes = extract_bytes(mem, index_to_offset(i, main_table_entry_size as nat) + u64::spec_size_of(), u64::spec_size_of());
            let entry_bytes = extract_bytes(mem, index_to_offset(i, main_table_entry_size as nat) + u64::spec_size_of() * 2, ListEntryMetadata::spec_size_of());
            let key_bytes = extract_bytes(mem, index_to_offset(i, main_table_entry_size as nat) + u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of() as nat, K::spec_size_of());
            let cdb = u64::spec_from_bytes(cdb_bytes);
            &&& u64::bytes_parseable(cdb_bytes)
            &&& {
                ||| cdb == CDB_FALSE 
                ||| {
                    &&& cdb == CDB_TRUE
                    &&& u64::bytes_parseable(crc_bytes)
                    &&& ListEntryMetadata::bytes_parseable(entry_bytes)
                    &&& K::bytes_parseable(key_bytes)
                    &&& crc_bytes == spec_crc_bytes(entry_bytes + key_bytes)
                }
            }
        }
    {
        assert(validate_main_entries::<K>(mem, num_keys as nat, main_table_entry_size as nat));
        assert forall |i: nat| i < num_keys implies {
            let cdb_bytes = extract_bytes(mem, #[trigger] index_to_offset(i, main_table_entry_size as nat), u64::spec_size_of());
            let crc_bytes = extract_bytes(mem, index_to_offset(i, main_table_entry_size as nat) + u64::spec_size_of(), u64::spec_size_of());
            let entry_bytes = extract_bytes(mem, index_to_offset(i, main_table_entry_size as nat) + u64::spec_size_of() * 2, ListEntryMetadata::spec_size_of());
            let key_bytes = extract_bytes(mem, index_to_offset(i, main_table_entry_size as nat) + u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of() as nat, K::spec_size_of());
            let cdb = u64::spec_from_bytes(cdb_bytes);
            &&& u64::bytes_parseable(cdb_bytes)
            &&& {
                ||| cdb == CDB_FALSE 
                ||| {
                    &&& cdb == CDB_TRUE
                    &&& u64::bytes_parseable(crc_bytes)
                    &&& ListEntryMetadata::bytes_parseable(entry_bytes)
                    &&& K::bytes_parseable(key_bytes)
                    &&& crc_bytes == spec_crc_bytes(entry_bytes + key_bytes)
                }
            }
        } by {
            lemma_mul_strict_inequality(i as int, num_keys as int, main_table_entry_size as int);
            if i + 1 < num_keys {
                lemma_mul_strict_inequality((i + 1) as int, num_keys as int, main_table_entry_size as int);
            } 
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(main_table_entry_size as int, i as int, 1int);
            lemma_subrange_of_extract_bytes_equal(mem, index_to_offset(i, main_table_entry_size as nat), index_to_offset(i, main_table_entry_size as nat), main_table_entry_size as nat, u64::spec_size_of());
            lemma_subrange_of_extract_bytes_equal(mem, index_to_offset(i, main_table_entry_size as nat), index_to_offset(i, main_table_entry_size as nat) + u64::spec_size_of(), main_table_entry_size as nat, u64::spec_size_of());
            lemma_subrange_of_extract_bytes_equal(mem, index_to_offset(i, main_table_entry_size as nat), index_to_offset(i, main_table_entry_size as nat) + u64::spec_size_of() * 2, main_table_entry_size as nat, ListEntryMetadata::spec_size_of());
            lemma_subrange_of_extract_bytes_equal(mem, index_to_offset(i, main_table_entry_size as nat), index_to_offset(i, main_table_entry_size as nat) + u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of() as nat, main_table_entry_size as nat, K::spec_size_of());
        }
    }

    pub open spec fn address_belongs_to_invalid_main_table_entry(
        addr: int,
        mem: Seq<u8>,
        num_keys: u64,
        main_table_entry_size: u32,
    ) -> bool
    {
        let which_entry = addr / main_table_entry_size as int;
        let cdb_bytes = extract_bytes(mem, index_to_offset(which_entry as nat, main_table_entry_size as nat),
                                      u64::spec_size_of());
        &&& which_entry < num_keys
        &&& addr - which_entry * main_table_entry_size >= u64::spec_size_of()
        &&& u64::bytes_parseable(cdb_bytes)
        &&& u64::spec_from_bytes(cdb_bytes) == CDB_FALSE
    }

    pub proof fn lemma_validate_main_entry_doesnt_depend_on_fields_of_invalid_entries<K>(
        mem1: Seq<u8>,
        mem2: Seq<u8>,
        num_keys: u64,
        main_table_entry_size: u32,
        i: nat,
    )
        where 
            K: PmCopy + std::fmt::Debug,
        requires
            mem1.len() == mem2.len(),
            mem1.len() >= num_keys * main_table_entry_size,
            main_table_entry_size ==
                ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
            forall|addr: int| 0 <= addr < mem1.len() && mem1[addr] != mem2[addr] ==>
                       #[trigger] address_belongs_to_invalid_main_table_entry(addr, mem1, num_keys, main_table_entry_size),
            i < num_keys
        ensures
            validate_main_entry::<K>(extract_bytes(mem1, i * main_table_entry_size as nat, main_table_entry_size as nat),
                                         num_keys as nat) ==
            validate_main_entry::<K>(extract_bytes(mem2, i * main_table_entry_size as nat, main_table_entry_size as nat),
                                         num_keys as nat)
    {
        lemma_subrange_of_subrange_forall(mem1);
        lemma_subrange_of_subrange_forall(mem2);

        let bytes1 = extract_bytes(mem1, i * main_table_entry_size as nat, main_table_entry_size as nat);
        let cdb_bytes1 = extract_bytes(bytes1, 0, u64::spec_size_of());
        let crc_bytes1 = extract_bytes(bytes1, u64::spec_size_of(), u64::spec_size_of());
        let metadata_bytes1 = extract_bytes(bytes1, (u64::spec_size_of() * 2) as nat,
                                           ListEntryMetadata::spec_size_of());
        let key_bytes1 = extract_bytes(bytes1,
                                      (ListEntryMetadata::spec_size_of() + u64::spec_size_of() * 2) as nat,
                                      K::spec_size_of());
        let cdb1 = u64::spec_from_bytes(cdb_bytes1);

        let bytes2 = extract_bytes(mem2, i * main_table_entry_size as nat, main_table_entry_size as nat);
        let cdb_bytes2 = extract_bytes(bytes2, 0, u64::spec_size_of());
        let crc_bytes2 = extract_bytes(bytes2, u64::spec_size_of(), u64::spec_size_of());
        let metadata_bytes2 = extract_bytes(bytes2, (u64::spec_size_of() * 2) as nat,
                                           ListEntryMetadata::spec_size_of());
        let key_bytes2 = extract_bytes(bytes2,
                                      (ListEntryMetadata::spec_size_of() + u64::spec_size_of() * 2) as nat,
                                      K::spec_size_of());
        let cdb2 = u64::spec_from_bytes(cdb_bytes2);

        lemma_valid_entry_index(i, num_keys as nat, main_table_entry_size as nat);
        assert(cdb_bytes1 == cdb_bytes2) by {
            assert forall|addr: int| i * main_table_entry_size <= addr < i * main_table_entry_size + u64::spec_size_of()
                    implies mem1[addr] == mem2[addr] by {
                let which_entry = addr / main_table_entry_size as int;
                assert(which_entry == i) by {
                    lemma_fundamental_div_mod_converse(addr, main_table_entry_size as int, i as int,
                                                       addr - i * main_table_entry_size);
                }
                assert(addr - which_entry * main_table_entry_size < u64::spec_size_of());
                assert(!address_belongs_to_invalid_main_table_entry(addr, mem1, num_keys, main_table_entry_size));
            }
            assert(cdb_bytes1 =~= cdb_bytes2);
        }
        
        if cdb1 == CDB_FALSE {
            assert(cdb2 == CDB_FALSE);
        }
        else {
            assert forall|addr: int| i * main_table_entry_size <= addr < i * main_table_entry_size + main_table_entry_size
                       implies mem1[addr] == mem2[addr] by {
                let which_entry = addr / main_table_entry_size as int;
                assert(which_entry == i) by {
                    lemma_fundamental_div_mod_converse(addr, main_table_entry_size as int, i as int,
                                                       addr - i * main_table_entry_size);
                }
                assert(!address_belongs_to_invalid_main_table_entry(addr, mem1, num_keys, main_table_entry_size));
            }
            assert(crc_bytes1 =~= crc_bytes2);
            assert(metadata_bytes1 =~= metadata_bytes2);
            assert(key_bytes1 =~= key_bytes2);
        }
    }

    pub proof fn lemma_validate_main_entries_doesnt_depend_on_fields_of_invalid_entries<K>(
        mem1: Seq<u8>,
        mem2: Seq<u8>,
        num_keys: u64,
        main_table_entry_size: u32,
    )
        where 
            K: PmCopy + std::fmt::Debug,
        requires
            mem1.len() == mem2.len(),
            mem1.len() >= num_keys * main_table_entry_size,
            main_table_entry_size ==
                ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
            forall|addr: int| 0 <= addr < mem1.len() && mem1[addr] != mem2[addr] ==>
                       #[trigger] address_belongs_to_invalid_main_table_entry(addr, mem1, num_keys, main_table_entry_size),
        ensures
            validate_main_entries::<K>(mem1, num_keys as nat, main_table_entry_size as nat) ==
            validate_main_entries::<K>(mem2, num_keys as nat, main_table_entry_size as nat)
    {
        assert forall |i: nat| i < num_keys implies
            validate_main_entry::<K>(#[trigger] extract_bytes(mem1, index_to_offset(i, main_table_entry_size as nat),
                                                                  main_table_entry_size as nat), num_keys as nat) ==
            validate_main_entry::<K>(extract_bytes(mem2, index_to_offset(i, main_table_entry_size as nat),
                                                       main_table_entry_size as nat), num_keys as nat) by {
            lemma_validate_main_entry_doesnt_depend_on_fields_of_invalid_entries::<K>(
                mem1, mem2, num_keys, main_table_entry_size, i
            );
        }

        if validate_main_entries::<K>(mem1, num_keys as nat, main_table_entry_size as nat) {
            assert forall |i: nat| i < num_keys implies
                validate_main_entry::<K>(#[trigger] extract_bytes(mem2, index_to_offset(i, main_table_entry_size as nat),
                                                                      main_table_entry_size as nat), num_keys as nat) 
            by {
                assert(validate_main_entry::<K>(extract_bytes(mem1, index_to_offset(i, main_table_entry_size as nat),
                                                                  main_table_entry_size as nat), num_keys as nat));
            }
        }
        else {
            let i = choose|i: nat| {
                &&& i < num_keys
                &&& !validate_main_entry::<K>(#[trigger] extract_bytes(mem1, index_to_offset(i, main_table_entry_size as nat),
                                                                         main_table_entry_size as nat),
                                                num_keys as nat)
            };
            assert(!validate_main_entry::<K>(extract_bytes(mem2, index_to_offset(i, main_table_entry_size as nat),
                                                               main_table_entry_size as nat),
                                                 num_keys as nat));
        }
    }

    pub proof fn lemma_parse_main_entry_doesnt_depend_on_fields_of_invalid_entries<K>(
        mem1: Seq<u8>,
        mem2: Seq<u8>,
        num_keys: u64,
        main_table_entry_size: u32,
        i: nat,
    )
        where 
            K: PmCopy + std::fmt::Debug,
        requires
            mem1.len() == mem2.len(),
            mem1.len() >= num_keys * main_table_entry_size,
            main_table_entry_size ==
                ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
            forall|addr: int| 0 <= addr < mem1.len() && mem1[addr] != mem2[addr] ==>
                       #[trigger] address_belongs_to_invalid_main_table_entry(addr, mem1, num_keys, main_table_entry_size),
            i < num_keys,
            validate_main_entry::<K>(extract_bytes(mem1, index_to_offset(i, main_table_entry_size as nat), main_table_entry_size as nat),
                                         num_keys as nat),
            validate_main_entry::<K>(extract_bytes(mem2, index_to_offset(i, main_table_entry_size as nat), main_table_entry_size as nat),
                                         num_keys as nat),
        ensures
            parse_main_entry::<K>(extract_bytes(mem1, index_to_offset(i, main_table_entry_size as nat), main_table_entry_size as nat),
                                      num_keys as nat) ==
            parse_main_entry::<K>(extract_bytes(mem2, index_to_offset(i, main_table_entry_size as nat), main_table_entry_size as nat),
                                      num_keys as nat)
    {
        lemma_subrange_of_subrange_forall(mem1);
        lemma_subrange_of_subrange_forall(mem2);

        let bytes1 = extract_bytes(mem1, i * main_table_entry_size as nat, main_table_entry_size as nat);
        let cdb_bytes1 = extract_bytes(bytes1, 0, u64::spec_size_of());
        let crc_bytes1 = extract_bytes(bytes1, u64::spec_size_of(), u64::spec_size_of());
        let metadata_bytes1 = extract_bytes(bytes1, (u64::spec_size_of() * 2) as nat,
                                           ListEntryMetadata::spec_size_of());
        let key_bytes1 = extract_bytes(bytes1,
                                      (ListEntryMetadata::spec_size_of() + u64::spec_size_of() * 2) as nat,
                                      K::spec_size_of());
        let cdb1 = u64::spec_from_bytes(cdb_bytes1);

        let bytes2 = extract_bytes(mem2, i * main_table_entry_size as nat, main_table_entry_size as nat);
        let cdb_bytes2 = extract_bytes(bytes2, 0, u64::spec_size_of());
        let crc_bytes2 = extract_bytes(bytes2, u64::spec_size_of(), u64::spec_size_of());
        let metadata_bytes2 = extract_bytes(bytes2, (u64::spec_size_of() * 2) as nat,
                                           ListEntryMetadata::spec_size_of());
        let key_bytes2 = extract_bytes(bytes2,
                                      (ListEntryMetadata::spec_size_of() + u64::spec_size_of() * 2) as nat,
                                      K::spec_size_of());
        let cdb2 = u64::spec_from_bytes(cdb_bytes2);

        lemma_valid_entry_index(i, num_keys as nat, main_table_entry_size as nat);
        assert(cdb_bytes1 == cdb_bytes2) by {
            assert forall|addr: int| i * main_table_entry_size <= addr < i * main_table_entry_size + u64::spec_size_of()
                    implies mem1[addr] == mem2[addr] by {
                let which_entry = addr / main_table_entry_size as int;
                assert(which_entry == i) by {
                    lemma_fundamental_div_mod_converse(addr, main_table_entry_size as int, i as int,
                                                       addr - i * main_table_entry_size);
                }
                assert(addr - which_entry * main_table_entry_size < u64::spec_size_of());
                assert(!address_belongs_to_invalid_main_table_entry(addr, mem1, num_keys, main_table_entry_size));
            }
            assert(cdb_bytes1 =~= cdb_bytes2);
        }
        
        if cdb1 == CDB_FALSE {
            assert(cdb2 == CDB_FALSE);
        }
        else {
            assert forall|addr: int| i * main_table_entry_size <= addr < i * main_table_entry_size + main_table_entry_size
                       implies mem1[addr] == mem2[addr] by {
                let which_entry = addr / main_table_entry_size as int;
                assert(which_entry == i) by {
                    lemma_fundamental_div_mod_converse(addr, main_table_entry_size as int, i as int,
                                                       addr - i * main_table_entry_size);
                }
                assert(!address_belongs_to_invalid_main_table_entry(addr, mem1, num_keys, main_table_entry_size));
            }
            assert(crc_bytes1 =~= crc_bytes2);
            assert(metadata_bytes1 =~= metadata_bytes2);
            assert(key_bytes1 =~= key_bytes2);
        }
    }

    pub proof fn lemma_parse_main_table_doesnt_depend_on_fields_of_invalid_entries<K>(
        mem1: Seq<u8>,
        mem2: Seq<u8>,
        num_keys: u64,
        main_table_entry_size: u32,
    )
        where 
            K: PmCopy + std::fmt::Debug,
        requires
            mem1.len() == mem2.len(),
            mem1.len() >= num_keys * main_table_entry_size,
            main_table_entry_size ==
                ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
            forall|addr: int| 0 <= addr < mem1.len() && mem1[addr] != mem2[addr] ==>
                       #[trigger] address_belongs_to_invalid_main_table_entry(addr, mem1, num_keys, main_table_entry_size),
        ensures
            parse_main_table::<K>(mem1, num_keys, main_table_entry_size) ==
            parse_main_table::<K>(mem2, num_keys, main_table_entry_size)
    {
        if mem1.len() < num_keys * main_table_entry_size {
            return;
        }

        lemma_validate_main_entries_doesnt_depend_on_fields_of_invalid_entries::<K>(
            mem1, mem2, num_keys, main_table_entry_size
        );

        if !validate_main_entries::<K>(mem1, num_keys as nat, main_table_entry_size as nat) {
            return;
        }

        assert forall|i: int| 0 <= i < num_keys implies
            parse_main_entry::<K>(#[trigger] extract_bytes(mem1, (i * main_table_entry_size as int) as nat,
                                                               main_table_entry_size as nat), num_keys as nat) ==
            parse_main_entry::<K>(extract_bytes(mem2, (i * main_table_entry_size as int) as nat,
                                                    main_table_entry_size as nat), num_keys as nat) by {
            lemma_parse_main_entry_doesnt_depend_on_fields_of_invalid_entries::<K>(
                mem1, mem2, num_keys, main_table_entry_size, i as nat
            );
        }

        let table1 = parse_main_table::<K>(mem1, num_keys, main_table_entry_size);
        let table2 = parse_main_table::<K>(mem2, num_keys, main_table_entry_size);

        // To finish the proof, we have to prove that it's impossible for one 
        // table to parse successfully and for the other to fail the duplicate 
        // item index check
        match (table1, table2) {
            (Some(table1), Some(table2)) => {
                assert(forall |i: int| {
                    &&& 0 <= i < num_keys 
                    &&& #[trigger] table1.durable_main_table[i] is Some
                } ==> table2.durable_main_table[i] is Some);
            }
            (None, Some(table2)) => {
                let entries = parse_main_entries::<K>(mem1, num_keys as nat, main_table_entry_size as nat);
                assert(!no_duplicate_item_indexes(entries));
                assert(forall |i: int| 0 <= i < num_keys ==>
                    #[trigger] entries[i] == table2.durable_main_table[i]);
            }
            (Some(table1), None) => {
                let entries = parse_main_entries::<K>(mem2, num_keys as nat, main_table_entry_size as nat);
                assert(!no_duplicate_item_indexes(entries));
                assert(forall |i: int| 0 <= i < num_keys ==>
                    #[trigger] entries[i] == table1.durable_main_table[i]);
            }
            (None, None) => {}
        }
        
        assert(parse_main_table::<K>(mem1, num_keys, main_table_entry_size) =~=
               parse_main_table::<K>(mem2, num_keys, main_table_entry_size));
    }

}
