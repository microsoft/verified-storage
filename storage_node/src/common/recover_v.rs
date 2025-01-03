use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::seq::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe};
use crate::pmem::pmemutil_v::*;
use super::subrange_v::*;

verus! {

pub open spec fn recover_object<T>(s: Seq<u8>, start: int, crc_addr: int) -> Option<T>
    where
        T: PmCopy
{
    if {
        &&& 0 <= start
        &&& start + T::spec_size_of() <= s.len()
        &&& 0 <= crc_addr
        &&& crc_addr + u64::spec_size_of() <= s.len()
    } {
        let object_bytes = extract_section(s, start, T::spec_size_of());
        let crc_bytes = extract_section(s, crc_addr, u64::spec_size_of());
        if {
            &&& T::bytes_parseable(object_bytes)
            &&& u64::bytes_parseable(crc_bytes)
            &&& crc_bytes == spec_crc_bytes(object_bytes)
        } {
            Some(T::spec_from_bytes(object_bytes))
        }
        else {
            None
        }
    }
    else {
        None
    }
}

pub open spec fn recover_cdb(s: Seq<u8>, addr: int) -> Option<bool>
{
    if 0 <= addr && addr + u64::spec_size_of() <= s.len() {
        let cdb_bytes = extract_section(s, addr, u64::spec_size_of());
        if u64::bytes_parseable(cdb_bytes) {
            let cdb = u64::spec_from_bytes(cdb_bytes);
            if cdb == CDB_FALSE {
                Some(false)
            } else if cdb == CDB_TRUE {
                Some(true)
            } else {
                None
            }
        }
        else {
            None
        }
    }
    else {
        None
    }
}

}

