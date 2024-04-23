//! This file describes the persistent-memory layout of the
//! item table implementation.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.
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
//!     bytes 0..8:             CRC for the entry (not including these bytes)
//!     bytes 8..<item size>:   The item stored in this entry. Size is set at
//!                             setup time but is not known at compile time.
//!

use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use vstd::prelude::*;

verus! {
    // Constants

    // These constants describe the position of various parts of the
    // item table's layout. It's simpler than the multilog.

    pub const ABSOLUTE_POS_OF_METADATA_HEADER: u64 = 0;
    pub const RELATIVE_POS_OF_VERSION_NUMBER: u64: 0;
    pub const RELATIVE_POS_OF_ITEM_SIZE: u64 = 8;
    pub const RELATIVE_POS_OF_PROGRAM_GUID: u64 = 16;
    pub const LENGTH_OF_METADATA_HEADER: u64 = 32;
    pub const ABSOLUTE_POS_OF_HEADER_CRC: u64 = 32;

    // TODO: it may be more performant to skip some space and
    // start this at 256
    pub const ABSOLUTE_POS_OF_TABLE_AREA: u64 = 40;

    // This GUID was generated randomly and is meant to describe the
    // item table program, even if it has future versions.

    pub const ITEM_TABLE_PROGRAM_GUID: u128 = 0x799051C2EA1DD93680DD23065E8C9EFFu128;

    // The current version number, and the only one whose contents
    // this program can read, is the following:

    pub const ITEM_TABLE_VERSION_NUMBER: u64 = 1;
}
