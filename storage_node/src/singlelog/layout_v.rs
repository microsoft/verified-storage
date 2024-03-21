use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;

verus! {
    pub trait SuperBlock : Sized {
        spec fn parse_sb(sb_bytes: Seq<u8>) -> Self;

        spec fn get_log_size(&self) -> u64;
    }

    pub trait Headers {
        type Header : Serializable;

        spec fn parse_header_with_cdb(cdb: u64, header_bytes: Seq<u8>) -> Option<Self::Header>;

        spec fn get_logical_log_head(header: Self::Header) -> u64;

        spec fn get_logical_log_tail(header: Self::Header) -> u64;
    }

    pub trait LogContents {

    }

    pub open spec fn parse_cdb(cdb_bytes: Seq<u8>) -> u64
    {
        spec_u64_from_le_bytes(cdb_bytes)
    }
}
