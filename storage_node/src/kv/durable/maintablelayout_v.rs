use builtin::*;
use builtin_macros::*;
use vstd::arithmetic::mul::*;
use core::fmt::Debug;
use vstd::arithmetic::div_mod::*;
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
use deps_hack::{PmCopy};

verus! {
    // Metadata region

    #[repr(C)]
    #[derive(PmCopy, Copy, Debug)]
    pub struct ListEntryMetadata
    {
        pub head: u64,
        pub tail: u64,
        pub length: u64,
        pub first_entry_offset: u64, // offset of the first live entry in the head node
        pub item_index: u64,
    }

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
            u64::spec_size_of() + u64::spec_size_of() + ListEntryMetadata::spec_size_of() <= bytes.len(),
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
                // no duplicates
                if reverse_item_mapping_exists(entries) && reverse_key_mapping_exists(entries) {
                    Some(MainTableView::<K>::new(entries))
                } else {
                    None
                }
            }
        }
    }

    pub open spec fn trigger_main_entry(i: int) -> bool
    {
        true
    }

    // TODO: make these functions more general?
    // The reverse mapping-related spec fns and proofs help prove that the main table has no
    // duplicate keys or item indexes without instantiating a lot of expensive triggers
    pub open spec fn reverse_item_mapping<K>(entries: Seq<Option<MainTableViewEntry<K>>>, reverse_mapping: spec_fn(u64) -> int) -> bool 
    {
        forall |i: int| 0 <= i < entries.len() && entries[i] is Some ==> 
            i == reverse_mapping(#[trigger] entries[i].unwrap().item_index())
    }

    pub open spec fn reverse_key_mapping<K>(entries: Seq<Option<MainTableViewEntry<K>>>, reverse_mapping: spec_fn(K) -> int) -> bool 
    {
        forall |i: int| 0 <= i < entries.len() && entries[i] is Some ==> 
            i == reverse_mapping(#[trigger] entries[i].unwrap().key())
    }

    pub open spec fn reverse_item_mapping_exists<K>(entries: Seq<Option<MainTableViewEntry<K>>>) -> bool 
        where 
            K: PmCopy
    {
        exists |f: spec_fn(u64) -> int| reverse_item_mapping(entries, f)
    }

    pub open spec fn reverse_key_mapping_exists<K>(entries: Seq<Option<MainTableViewEntry<K>>>) -> bool 
    where 
        K: PmCopy
    {
        exists |f: spec_fn(K) -> int| reverse_key_mapping(entries, f)
    }

    spec fn no_dup_keys_map<K>(entries: Seq<Option<MainTableViewEntry<K>>>, f: spec_fn(K) -> int) -> bool 
    {
        forall |i| 0 <= i < entries.len() && entries[i] is Some ==> 
            f(#[trigger] entries[i].unwrap().key()) == i
    }

    spec fn no_dup_item_indexes_map<K>(entries: Seq<Option<MainTableViewEntry<K>>>, f: spec_fn(u64) -> int) -> bool 
    {
        forall |i| 0 <= i < entries.len() && entries[i] is Some ==> 
            f(#[trigger] entries[i].unwrap().item_index()) == i
    }

    pub open spec fn no_duplicate_item_indexes<K>(entries: Seq<Option<MainTableViewEntry<K>>>) -> bool 
        where 
            K: PmCopy
    {
        forall |i: int, j: int|
            #![trigger trigger_main_entry(i), trigger_main_entry(j)]
        {
            &&& trigger_main_entry(i)
            &&& trigger_main_entry(j)
            &&& 0 <= i < entries.len()
            &&& 0 <= j < entries.len()
            &&& i != j
            &&& entries[i] is Some
            &&& entries[j] is Some
        } ==> entries[i].unwrap().item_index() != entries[j].unwrap().item_index()
    }

    pub proof fn lemma_reverse_item_mapping_implies_no_duplicate_item_indexes<K>(entries: Seq<Option<MainTableViewEntry<K>>>)
        where 
            K: PmCopy
        requires 
            reverse_item_mapping_exists(entries)
        ensures 
            no_duplicate_item_indexes(entries)
    {}

    pub proof fn lemma_reverse_key_mapping_implies_no_duplicate_keys<K>(entries: Seq<Option<MainTableViewEntry<K>>>)
        where 
            K: PmCopy
        requires 
            reverse_key_mapping_exists(entries)
        ensures 
            no_duplicate_keys(entries)
    {}

    pub proof fn lemma_no_duplicate_keys_implies_reverse_key_mapping_exists<K>(entries: Seq<Option<MainTableViewEntry<K>>>)
        where 
            K: PmCopy
        requires 
            no_duplicate_keys(entries)
        ensures 
            reverse_key_mapping_exists(entries)
    {
        let f = |k: K| choose |i: int| 0 <= i < entries.len() && entries[i] is Some && #[trigger] entries[i].unwrap().key() == k;
        assert forall |i| 0 <= i < entries.len() && entries[i] is Some implies
            f(#[trigger] entries[i].unwrap().key()) == i by {
            assert(trigger_main_entry(f(entries[i].unwrap().key())));
            assert(trigger_main_entry(i));
        }
        assert(no_dup_keys_map(entries, f));
        assert(reverse_key_mapping(entries, f));
    }

    pub proof fn lemma_no_duplicate_item_indexes_implies_reverse_item_mapping_exists<K>(entries: Seq<Option<MainTableViewEntry<K>>>)
        where 
            K: PmCopy
        requires 
            no_duplicate_item_indexes(entries)
        ensures 
            reverse_item_mapping_exists(entries)
    {
        let f = |e: u64| choose |i: int| 0 <= i < entries.len() && entries[i] is Some && #[trigger] entries[i].unwrap().item_index() == e;
        assert forall |i| 0 <= i < entries.len() && entries[i] is Some implies
            f(#[trigger] entries[i].unwrap().item_index()) == i by {
            assert(trigger_main_entry(f(entries[i].unwrap().item_index())));
            assert(trigger_main_entry(i));
        }
        assert(no_dup_item_indexes_map(entries, f));
        assert(reverse_item_mapping(entries, f));
    }

    pub proof fn lemma_no_dup_iff_reverse_mappings_exist<K>(entries: Seq<Option<MainTableViewEntry<K>>>)
        where 
            K: PmCopy,
        ensures 
            reverse_item_mapping_exists(entries) <==> no_duplicate_item_indexes(entries),
            reverse_key_mapping_exists(entries) <==> no_duplicate_keys(entries),
    {
        if reverse_item_mapping_exists(entries) {
            lemma_reverse_item_mapping_implies_no_duplicate_item_indexes(entries);
        }
        if no_duplicate_item_indexes(entries) {
            lemma_no_duplicate_item_indexes_implies_reverse_item_mapping_exists(entries);
        }
        if reverse_key_mapping_exists(entries) {
            lemma_reverse_key_mapping_implies_no_duplicate_keys(entries);
        }
        if no_duplicate_keys(entries) {
            lemma_no_duplicate_keys_implies_reverse_key_mapping_exists(entries);
        }
    }

    // TODO: replace no duplicate key/item spec fns with reverse mapping versions
    pub open spec fn no_duplicate_keys<K>(entries: Seq<Option<MainTableViewEntry<K>>>) -> bool 
        where 
            K: PmCopy 
    {
        forall |i: int, j: int|
            #![trigger trigger_main_entry(i), trigger_main_entry(j)]
        {
            &&& trigger_main_entry(i)
            &&& trigger_main_entry(j)
            &&& 0 <= i < entries.len()
            &&& 0 <= j < entries.len()
            &&& i != j
            &&& entries[i] is Some
            &&& entries[j] is Some
        } ==> entries[i].unwrap().key() != entries[j].unwrap().key()
    }

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
                assert(!(reverse_item_mapping_exists(entries) && reverse_key_mapping_exists(entries)));
                if !reverse_item_mapping_exists(entries) {
                    assert(!no_duplicate_item_indexes(entries)) by {
                        lemma_no_dup_iff_reverse_mappings_exist(entries);
                    }
                } else {
                    assert(!reverse_key_mapping_exists(entries));
                    assert(!no_duplicate_keys(entries)) by {
                        lemma_no_dup_iff_reverse_mappings_exist(entries);
                    }
                }
                assert(forall |i: int| 0 <= i < num_keys ==>
                    #[trigger] entries[i] == table2.durable_main_table[i]);
            }
            (Some(table1), None) => {
                let entries = parse_main_entries::<K>(mem2, num_keys as nat, main_table_entry_size as nat);
                assert(!(reverse_item_mapping_exists(entries) && reverse_key_mapping_exists(entries)));
                if !reverse_item_mapping_exists(entries) {
                    assert(!no_duplicate_item_indexes(entries)) by {
                        lemma_no_dup_iff_reverse_mappings_exist(entries);
                    }
                } else {
                    assert(!reverse_key_mapping_exists(entries));
                    assert(!no_duplicate_keys(entries)) by {
                        lemma_no_dup_iff_reverse_mappings_exist(entries);
                    }
                }
                assert(forall |i: int| 0 <= i < num_keys ==>
                    #[trigger] entries[i] == table1.durable_main_table[i]);
            }
            (None, None) => {}
        }
        
        assert(parse_main_table::<K>(mem1, num_keys, main_table_entry_size) =~=
               parse_main_table::<K>(mem2, num_keys, main_table_entry_size));
    }

    pub proof fn lemma_main_table_recovery_after_updating_entry<K>(
        mem1: Seq<u8>,
        mem2: Seq<u8>,
        num_keys: u64,
        main_table_entry_size: u32,
        index: u64,
        entry: ListEntryMetadata,
        key: K,
    )
        where 
            K: PmCopy + std::fmt::Debug,
        requires
            parse_main_table::<K>(mem1, num_keys, main_table_entry_size) is Some,
            mem1.len() == mem2.len(),
            index < num_keys,
            forall|addr: int| {
                let start = index_to_offset(index as nat, main_table_entry_size as nat);
                &&& #[trigger] trigger_addr(addr)
                &&& 0 <= addr < mem1.len()
                &&& !(start <= addr < start + main_table_entry_size)
            } ==> mem2[addr] == mem1[addr],
            main_table_entry_size ==
                ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
            ({
                let start = index_to_offset(index as nat, main_table_entry_size as nat);
                let entry_bytes = extract_bytes(mem2, start, main_table_entry_size as nat);
                let cdb_bytes = extract_bytes(entry_bytes, 0, u64::spec_size_of());
                cdb_bytes == (CDB_FALSE as u64).spec_to_bytes()
            }),
        ensures
            parse_main_table::<K>(mem2, num_keys, main_table_entry_size) is Some,
            ({
                let table1 = parse_main_table::<K>(mem1, num_keys, main_table_entry_size).unwrap().durable_main_table;
                let table2 = parse_main_table::<K>(mem2, num_keys, main_table_entry_size).unwrap().durable_main_table;
                &&& table2.len() == table1.len()
                &&& table2[index as int] is None
                &&& forall|i: int| 0 <= i < table2.len() && i != index ==> #[trigger] table2[i] == table1[i]
            }),
    {
        let start = index_to_offset(index as nat, main_table_entry_size as nat);
        lemma_valid_entry_index(index as nat, num_keys as nat, main_table_entry_size as nat);
        assert forall|i: nat| i < num_keys implies {
            let local_start = #[trigger] index_to_offset(i, main_table_entry_size as nat);
            let entry_bytes1 = extract_bytes(mem1, local_start, main_table_entry_size as nat);
            let entry_bytes2 = extract_bytes(mem2, local_start, main_table_entry_size as nat);
            let entry1 = parse_main_entry::<K>(entry_bytes1, num_keys as nat);
            let entry2 = parse_main_entry::<K>(entry_bytes2, num_keys as nat);
            &&& validate_main_entry::<K>(entry_bytes2, num_keys as nat)
            &&& if i == index { entry2 is None } else { entry2 == entry1 }
        } by {
            let local_start = index_to_offset(i, main_table_entry_size as nat);
            assert(validate_main_entry::<K>(
                #[trigger] extract_bytes(mem1, local_start, main_table_entry_size as nat),
                num_keys as nat
            ));
            lemma_valid_entry_index(i, num_keys as nat, main_table_entry_size as nat);
            if i == index {
                broadcast use pmcopy_axioms;
                assert(validate_main_entry::<K>(
                    #[trigger] extract_bytes(mem2, index_to_offset(i, main_table_entry_size as nat),
                                             main_table_entry_size as nat),
                    num_keys as nat
                ));
            }
            else {
                lemma_entries_dont_overlap_unless_same_index(i, index as nat, main_table_entry_size as nat);
                assert forall|addr: int| local_start <= addr < local_start + main_table_entry_size implies
                    #[trigger] mem1[addr] == mem2[addr] by {
                    assert(trigger_addr(addr));
                    assert(!(start <= addr < start + main_table_entry_size));
                }
                assert(extract_bytes(mem1, local_start, main_table_entry_size as nat) =~=
                       extract_bytes(mem2, local_start, main_table_entry_size as nat));
            }
        }
    
        assert(validate_main_entries::<K>(mem2, num_keys as nat, main_table_entry_size as nat));
        let entries1 = parse_main_entries::<K>(mem1, num_keys as nat, main_table_entry_size as nat);
        let entries2 = parse_main_entries::<K>(mem2, num_keys as nat, main_table_entry_size as nat);
        if !no_duplicate_item_indexes(entries2) {
            let (i, j) = choose|i: int, j: int| {
                &&& 0 <= i < entries2.len()
                &&& 0 <= j < entries2.len()
                &&& i != j
                &&& #[trigger] entries2[i] is Some
                &&& #[trigger] entries2[j] is Some
                &&& entries2[i].unwrap().item_index() == entries2[j].unwrap().item_index()
            };
            assert({
                &&& 0 <= i < entries1.len()
                &&& 0 <= j < entries1.len()
                &&& i != j
                &&& #[trigger] entries1[i] is Some
                &&& #[trigger] entries1[j] is Some
                &&& entries1[i].unwrap().item_index() == entries1[j].unwrap().item_index()
            });
            assert(false);
        }
        if !no_duplicate_keys(entries2) {
            let (i, j) = choose|i: int, j: int| {
                &&& 0 <= i < entries2.len()
                &&& 0 <= j < entries2.len()
                &&& i != j
                &&& #[trigger] entries2[i] is Some
                &&& #[trigger] entries2[j] is Some
                &&& entries2[i].unwrap().key() == entries2[j].unwrap().key()
            };
            assert({
                &&& 0 <= i < entries1.len()
                &&& 0 <= j < entries1.len()
                &&& i != j
                &&& #[trigger] entries1[i] is Some
                &&& #[trigger] entries1[j] is Some
                &&& entries1[i].unwrap().key() == entries1[j].unwrap().key()
            });
            assert(false);
        }
        lemma_no_dup_iff_reverse_mappings_exist(entries2);
    }


}
