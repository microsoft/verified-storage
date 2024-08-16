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
//! Metadata header (absolute offsets):
//!     bytes 0..8:     Version number of the program that created this metadata
//!     bytes 8..16:    Size of the items stored in the table
//!     bytes 16..32:   Program GUID for this program
//!     bytes 32..40:   CRC of the above 32 bytes
//!
//! The table area starts after the metadata header.
//!
//! Table entry (relative offsets):
//!     bytes 0..2:             valid bits
//!     bytes 2..10:            CRC for the entry (not including these bytes)
//!     bytes 10..<item size>:  The item stored in this entry. Size is set at
//!                             setup time but is not known at compile time.
//!

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::util_v::*;
use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use vstd::bytes::*;
use vstd::prelude::*;
use vstd::ptr::*;

use super::itemtablespec_t::DurableItemTableView;

use crate::pmem::traits_t::*;
use deps_hack::{PmSafe, PmSized};
use crate::log::layout_v::GlobalMetadata;
use crate::kv::durable::util_v::*;

verus! {
    // Constants

    // These constants describe the position of various parts of the
    // item table's layout. It's simpler than the multilog.

    pub const ABSOLUTE_POS_OF_METADATA_HEADER: u64 = 0;
    pub const RELATIVE_POS_OF_VERSION_NUMBER: u64 = 0;
    pub const RELATIVE_POS_OF_ITEM_SIZE: u64 = 8;
    pub const RELATIVE_POS_OF_NUM_KEYS: u64 = 16;
    pub const RELATIVE_POS_OF_PADDING: u64 = 24;
    pub const RELATIVE_POS_OF_PROGRAM_GUID: u64 = 32;
    pub const ABSOLUTE_POS_OF_HEADER_CRC: u64 = 48;

    // TODO: it may be more performant to skip some space and
    // start this at 256
    pub const ABSOLUTE_POS_OF_TABLE_AREA: u64 = 0;

    // This GUID was generated randomly and is meant to describe the
    // item table program, even if it has future versions.

    pub const ITEM_TABLE_PROGRAM_GUID: u128 = 0x799051C2EA1DD93680DD23065E8C9EFFu128;

    // The current version number, and the only one whose contents
    // this program can read, is the following:

    pub const ITEM_TABLE_VERSION_NUMBER: u64 = 1;

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
        let crc_bytes = extract_bytes(bytes, RELATIVE_POS_OF_ITEM_CRC as nat, u64::spec_size_of());
        let item_bytes = extract_bytes(bytes, RELATIVE_POS_OF_ITEM as nat, I::spec_size_of());
        &&& u64::bytes_parseable(crc_bytes)
        &&& I::bytes_parseable(item_bytes)
        &&& crc_bytes == spec_crc_bytes(item_bytes)
    }

    pub open spec fn validate_item_table_entries<I, K>(mem: Seq<u8>, num_keys: nat, valid_indices: Set<int>) -> bool 
        where 
            I: PmCopy,
            K: PmCopy + std::fmt::Debug,
        recommends
            mem.len() >= num_keys * (I::spec_size_of() + u64::spec_size_of())
    {
        let entry_size = I::spec_size_of() + u64::spec_size_of();
        forall |i: nat| i < num_keys && valid_indices.contains(i as int) ==> 
            validate_item_table_entry::<I, K>(#[trigger] extract_bytes(mem, i * entry_size, entry_size))
    }

    // NOTE: this should only be called on entries that are pointed to by a valid, live main table entry.
    // We do not require that any other entries have valid CRCs
    pub open spec fn parse_metadata_entry<I, K>(bytes: Seq<u8>) -> Option<I>
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
    pub open spec fn parse_item_table<I, K>(mem: Seq<u8>, num_keys: nat, valid_indices: Set<int>) -> Option<DurableItemTableView<I>>
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
                        if valid_indices.contains(i) {
                            let bytes = extract_bytes(mem, (i * item_entry_size) as nat, item_entry_size as nat);
                            parse_metadata_entry::<I, K>(bytes)
                        } else {
                            None
                        }
                    }
                );
                Some(DurableItemTableView::new(item_table_view))
            }
        }
    }
}
