//! This file describes the persistent-memory layout of the
//! item table implementation.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.
//! TODO: it should probably be _t because the specified layout needs
//! to be checked to make sure it matches how Rust will lay it out
//!
//! The item table has a header region with immutable metadata that is
//! written when the table is first created. This is analogous to the
//! global metadata region in each multilog.
//!
//! Table entry (relative offsets):
//!     bytes 0..2:             valid bits
//!     bytes 2..10:            CRC for the entry (not including these bytes)
//!     bytes 10..<item size>:  The item stored in this entry. Size is set at
//!                             setup time but is not known at compile time.
//!

use crate::kv::durable::commonlayout_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::util_v::*;
use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use vstd::bytes::*;
use vstd::prelude::*;

use super::itemtable_v::DurableItemTableView;

use crate::kv::durable::inv_v::*;
use crate::kv::durable::util_v::*;
use crate::pmem::traits_t::*;
use deps_hack::{PmSafe, PmSized};

verus! {
    // Constants

    #[repr(C)]
    #[derive(PmSized, PmSafe, Copy, Clone, Debug)]
    pub struct ItemTableMetadata
    {
        pub version_number: u64,
        pub item_size: u64, // just I::size_of() -- does not include key, CRC, CDB
        pub num_keys: u64,
        pub _padding: u64,
        pub program_guid: u128,
    }

    // TODO: should this be trusted?
    impl PmCopy for ItemTableMetadata {}

    // pub const RELATIVE_POS_OF_VALID_CDB: u64 = 0;
    pub const RELATIVE_POS_OF_ITEM_CRC: u64 = 0;
    pub const RELATIVE_POS_OF_ITEM: u64 = 8;

    // NOTE: this should only be called on entries that are pointed to by a valid, live main table entry.
    // We do not require that any other entries have valid CRCs
    pub open spec fn validate_item_table_entry<I, K>(bytes: Seq<u8>) -> bool 
        where 
            I: PmCopy,
            K: PmCopy + std::fmt::Debug,
        recommends
            bytes.len() == I::spec_size_of() + u64::spec_size_of()
    {
        let crc_bytes = extract_bytes(bytes, 0, u64::spec_size_of());
        let item_bytes = extract_bytes(bytes, u64::spec_size_of(), I::spec_size_of());
        &&& u64::bytes_parseable(crc_bytes)
        &&& I::bytes_parseable(item_bytes)
        &&& crc_bytes == spec_crc_bytes(item_bytes)
    }

    pub open spec fn validate_item_table_entries<I, K>(mem: Seq<u8>, num_keys: nat, valid_indices: Set<u64>) -> bool 
        where 
            I: PmCopy,
            K: PmCopy + std::fmt::Debug,
        recommends
            mem.len() >= num_keys * (I::spec_size_of() + u64::spec_size_of())
    {
        let entry_size = I::spec_size_of() + u64::spec_size_of();
        forall |i: u64| i < num_keys && valid_indices.contains(i) ==> 
            validate_item_table_entry::<I, K>(#[trigger] extract_bytes(mem, index_to_offset(i as nat, entry_size as nat), entry_size))
    }

    // NOTE: this should only be called on entries that are pointed to by a valid, live main table entry.
    // We do not require that any other entries have valid CRCs
    pub open spec fn parse_item_entry<I, K>(bytes: Seq<u8>) -> Option<I>
        where 
            I: PmCopy,
            K: PmCopy + std::fmt::Debug,
        recommends
            bytes.len() == I::spec_size_of() + u64::spec_size_of(),
            // TODO: should we pass in the valid indices and check in recommends that this entry is valid?
    {
        let crc_bytes = extract_bytes(bytes, RELATIVE_POS_OF_ITEM_CRC as nat, u64::spec_size_of());
        let item_bytes = extract_bytes(bytes, RELATIVE_POS_OF_ITEM as nat, I::spec_size_of());
        
        if u64::bytes_parseable(crc_bytes) && I::bytes_parseable(item_bytes) && crc_bytes == spec_crc_bytes(item_bytes) {
            Some(I::spec_from_bytes(item_bytes))
        }
        else {
            None
        }
    }


    // The set of valid indices comes from the main table; an item is valid if a valid main table entry points to it
    pub open spec fn parse_item_table<I, K>(mem: Seq<u8>, num_keys: nat, valid_indices: Set<u64>) -> Option<DurableItemTableView<I>>
        where 
            I: PmCopy,
            K: PmCopy + std::fmt::Debug,
    {
        // Check that the header is valid and the memory is the correct size.
        // We probably already did these checks when we parsed the metadata header, but
        // do them again here just in case
        if mem.len() < num_keys * (I::spec_size_of() + u64::spec_size_of()) { 
            None
        } else {
            if !validate_item_table_entries::<I, K>(mem, num_keys, valid_indices) {
                None 
            } else {
                let item_entry_size = I::spec_size_of() + u64::spec_size_of();
                let item_table_view = Seq::new(
                    num_keys as nat,
                    |i: int| {
                        // TODO: probably can't have if {} in here
                        if i <= u64::MAX && valid_indices.contains(i as u64) {
                            let bytes = extract_bytes(mem, index_to_offset(i as nat, item_entry_size as nat), item_entry_size as nat);
                            parse_item_entry::<I, K>(bytes)
                        } else {
                            None
                        }
                    }
                );
                Some(DurableItemTableView::new(item_table_view))
            }
        }
    }

    pub open spec fn address_belongs_to_invalid_item_table_entry<I>(
        addr: int,
        num_keys: u64,
        valid_indices: Set<u64>
    ) -> bool
        where 
            I: PmCopy,
    {
        let entry_size = (I::spec_size_of() + u64::spec_size_of()) as int;
        let which_entry = addr / entry_size;
        &&& 0 <= which_entry < num_keys
        &&& !valid_indices.contains(which_entry as u64)
    }

    pub proof fn lemma_parse_item_table_doesnt_depend_on_fields_of_invalid_entries<I, K>(
        mem1: Seq<u8>,
        mem2: Seq<u8>,
        num_keys: u64,
        valid_indices: Set<u64>
    )
        where 
            I: PmCopy,
            K: PmCopy + std::fmt::Debug,
        requires
            mem1.len() == mem2.len(),
            mem1.len() >= num_keys * (I::spec_size_of() + u64::spec_size_of()),
            forall|addr: int| 0 <= addr < mem2.len() && mem1[addr] != #[trigger] mem2[addr] ==>
                address_belongs_to_invalid_item_table_entry::<I>(addr, num_keys, valid_indices)
        ensures
            parse_item_table::<I, K>(mem1, num_keys as nat, valid_indices) ==
            parse_item_table::<I, K>(mem2, num_keys as nat, valid_indices)
    {
        if mem1.len() < num_keys * (I::spec_size_of() + u64::spec_size_of()) {
            return;
        }

        let entry_size = I::spec_size_of() + u64::spec_size_of();
        assert forall |i: u64| i < num_keys && #[trigger] valid_indices.contains(i) implies
            extract_bytes(mem1, index_to_offset(i as nat, entry_size as nat), entry_size) ==
            extract_bytes(mem2, index_to_offset(i as nat, entry_size as nat), entry_size) by {
            lemma_valid_entry_index(i as nat, num_keys as nat, entry_size as nat);
            assert forall|addr: int| i * entry_size <= addr < i * entry_size + entry_size implies mem1[addr] == mem2[addr] by {
                assert(addr / entry_size as int == i) by {
                    lemma_addr_in_entry_divided_by_entry_size(i as nat, entry_size as nat, addr as int);
                }
            }
            assert(extract_bytes(mem1, index_to_offset(i as nat, entry_size as nat), entry_size) =~=
                   extract_bytes(mem2, index_to_offset(i as nat, entry_size as nat), entry_size));

        }
        assert(validate_item_table_entries::<I, K>(mem1, num_keys as nat, valid_indices) =~=
               validate_item_table_entries::<I, K>(mem2, num_keys as nat, valid_indices));
        let item_table_view1 = Seq::new(
            num_keys as nat,
            |i: int| {
                // TODO: probably can't have if {} in here
                if i <= u64::MAX && valid_indices.contains(i as u64) {
                    let bytes = extract_bytes(mem1, index_to_offset(i as nat, entry_size as nat), entry_size as nat);
                    parse_item_entry::<I, K>(bytes)
                } else {
                    None
                }
            }
        );
        let item_table_view2 = Seq::new(
            num_keys as nat,
            |i: int| {
                // TODO: probably can't have if {} in here
                if i <= u64::MAX && valid_indices.contains(i as u64) {
                    let bytes = extract_bytes(mem2, index_to_offset(i as nat, entry_size as nat), entry_size as nat);
                    parse_item_entry::<I, K>(bytes)
                } else {
                    None
                }
            }
        );
        assert(item_table_view1 =~= item_table_view2);
    }
}
