use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::set_lib::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe};
use crate::pmem::pmemutil_v::*;

verus! {

#[verifier::opaque]
pub open spec fn opaque_subrange<T>(s: Seq<T>, i: int, j: int) -> Seq<T>
{
    s.subrange(i, j)
}

pub open spec fn opaque_section<T>(s: Seq<T>, i: int, len: nat) -> Seq<T>
{
    opaque_subrange(s, i, i + len)
}

#[verifier::opaque]
pub open spec fn opaque_update_bytes(s: Seq<u8>, addr: int, bytes: Seq<u8>) -> Seq<u8>
{
    update_bytes(s, addr, bytes)
}

pub open spec fn opaque_match_except_in_range(s1: Seq<u8>, s2: Seq<u8>, start: int, end: int) -> bool
{
    &&& s1.len() == s2.len()
    &&& 0 <= start <= end <= s1.len()
    &&& opaque_subrange(s1, 0, start) == opaque_subrange(s2, 0, start)
    &&& opaque_subrange(s1, end, s1.len() as int) == opaque_subrange(s2, end, s2.len() as int)
}

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
        let object_bytes = opaque_section(s, start, T::spec_size_of());
        let crc_bytes = opaque_section(s, crc_addr, u64::spec_size_of());
        if crc_bytes == spec_crc_bytes(object_bytes) && T::bytes_parseable(object_bytes) {
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
        let cdb_bytes = opaque_section(s, addr, u64::spec_size_of());
        let cdb = u64::spec_from_bytes(cdb_bytes);
        if cdb == CDB_FALSE { Some(false) } else if cdb == CDB_TRUE { Some(true) } else { None }
    }
    else {
        None
    }
}

pub proof fn lemma_can_result_from_partial_write_effect_on_opaque(
    s2: Seq<u8>,
    s1: Seq<u8>,
    write_addr: int,
    bytes: Seq<u8>
)
    requires
        can_result_from_partial_write(s2, s1, write_addr, bytes),
        0 <= write_addr,
        write_addr + bytes.len() <= s1.len(),
    ensures
        opaque_match_except_in_range(s1, s2, write_addr, write_addr + bytes.len()),
{
    lemma_can_result_from_partial_write_effect(s2, s1, write_addr, bytes);
    reveal(opaque_subrange);
    assert(opaque_subrange(s1, 0, write_addr) =~= opaque_subrange(s2, 0, write_addr));
    assert(opaque_subrange(s1, write_addr + bytes.len(), s1.len() as int) =~=
           opaque_subrange(s2, write_addr + bytes.len(), s2.len() as int));
}



pub proof fn lemma_auto_can_result_from_partial_write_effect_on_opaque()
    ensures
        forall|s2: Seq<u8>, s1: Seq<u8>, write_addr: int, bytes: Seq<u8>|
        {
            &&& #[trigger] can_result_from_partial_write(s2, s1, write_addr, bytes)
            &&& 0 <= write_addr
            &&& write_addr + bytes.len() <= s1.len()
        } ==> opaque_match_except_in_range(s1, s2, write_addr, write_addr + bytes.len())
{
    assert forall|s2: Seq<u8>, s1: Seq<u8>, write_addr: int, bytes: Seq<u8>|
           {
               &&& #[trigger] can_result_from_partial_write(s2, s1, write_addr, bytes)
               &&& 0 <= write_addr
               &&& write_addr + bytes.len() <= s1.len()
           } implies opaque_match_except_in_range(s1, s2, write_addr, write_addr + bytes.len()) by {
        lemma_can_result_from_partial_write_effect_on_opaque(s2, s1, write_addr, bytes);
    }
}

pub proof fn lemma_can_result_from_write_effect_on_read_state(
    v2: PersistentMemoryRegionView,
    v1: PersistentMemoryRegionView,
    write_addr: int,
    bytes: Seq<u8>
)
    requires
        v1.valid(),
        v2.can_result_from_write(v1, write_addr, bytes),
        0 <= write_addr,
        write_addr + bytes.len() <= v1.len(),
    ensures
        v2.valid(),
        opaque_match_except_in_range(v1.read_state, v2.read_state, write_addr, write_addr + bytes.len()),
        opaque_subrange(v2.read_state, write_addr, write_addr + bytes.len()) == bytes,
{
    let s1 = v1.read_state;
    let s2 = v2.read_state;
    let start = write_addr;
    let end = write_addr + bytes.len();

    reveal(opaque_subrange);
    assert(opaque_subrange(s1, 0, start) =~= opaque_subrange(s2, 0, start));
    assert(opaque_subrange(s1, end, s1.len() as int) =~= opaque_subrange(s2, end, s2.len() as int));
    assert(opaque_subrange(v2.read_state, start, end) =~= bytes);
}

pub proof fn lemma_can_result_from_write_lack_of_effect_on_read_state(
    v2: PersistentMemoryRegionView,
    v1: PersistentMemoryRegionView,
    write_addr: int,
    bytes: Seq<u8>,
    start: int,
    end: int,
)
    requires
        v1.valid(),
        v2.can_result_from_write(v1, write_addr, bytes),
        0 <= write_addr,
        write_addr + bytes.len() <= v1.len(),
        0 <= start <= end <= v1.len(),
        end <= write_addr || write_addr + bytes.len() <= start,
    ensures
        v2.valid(),
        opaque_subrange(v2.read_state, start, end) == opaque_subrange(v1.read_state, start, end),
{
    reveal(opaque_subrange);
    assert(opaque_subrange(v2.read_state, start, end) =~= opaque_subrange(v1.read_state, start, end));
}

pub proof fn lemma_auto_can_result_from_write_effect_on_read_state()
    ensures
        forall|v2: PersistentMemoryRegionView, v1: PersistentMemoryRegionView, write_addr: int, bytes: Seq<u8>|
        {
            &&& v1.valid()
            &&& #[trigger] v2.can_result_from_write(v1, write_addr, bytes)
            &&& 0 <= write_addr
            &&& write_addr + bytes.len() <= v1.len()
        } ==> {
            &&& v2.valid()
            &&& opaque_match_except_in_range(v1.read_state, v2.read_state, write_addr, write_addr + bytes.len())
            &&& opaque_subrange(v2.read_state, write_addr, write_addr + bytes.len()) == bytes
        },
        forall|v2: PersistentMemoryRegionView, v1: PersistentMemoryRegionView, write_addr: int, bytes: Seq<u8>,
          start: int, end: int|
        {
            &&& v1.valid()
            &&& #[trigger] v2.can_result_from_write(v1, write_addr, bytes)
            &&& 0 <= write_addr
            &&& write_addr + bytes.len() <= v1.len()
            &&& 0 <= start <= end <= v1.len()
            &&& end <= write_addr || write_addr + bytes.len() <= start
        } ==> {
            &&& v2.valid()
            &&& #[trigger] opaque_subrange(v2.read_state, start, end) == opaque_subrange(v1.read_state, start, end)
        },
{
    assert forall|v2: PersistentMemoryRegionView, v1: PersistentMemoryRegionView, write_addr: int, bytes: Seq<u8>|
        {
            &&& #[trigger] v2.can_result_from_write(v1, write_addr, bytes)
            &&& 0 <= write_addr
            &&& write_addr + bytes.len() <= v1.len()
            &&& v1.valid()
        } implies {
            &&& v2.valid()
            &&& opaque_match_except_in_range(v1.read_state, v2.read_state, write_addr, write_addr + bytes.len())
            &&& opaque_subrange(v2.read_state, write_addr, write_addr + bytes.len()) == bytes
        } by {
        lemma_can_result_from_write_effect_on_read_state(v2, v1, write_addr, bytes);
    }

    assert forall|v2: PersistentMemoryRegionView, v1: PersistentMemoryRegionView, write_addr: int, bytes: Seq<u8>,
             start: int, end: int|
        {
            &&& #[trigger] v2.can_result_from_write(v1, write_addr, bytes)
            &&& 0 <= write_addr
            &&& write_addr + bytes.len() <= v1.len()
            &&& v1.valid()
            &&& 0 <= start <= end <= v1.len()
            &&& end <= write_addr || write_addr + bytes.len() <= start
        } implies {
            &&& v2.valid()
            &&& #[trigger] opaque_subrange(v2.read_state, start, end) == opaque_subrange(v1.read_state, start, end)
        } by {
        lemma_can_result_from_write_lack_of_effect_on_read_state(v2, v1, write_addr, bytes, start, end);
    }
}

}
