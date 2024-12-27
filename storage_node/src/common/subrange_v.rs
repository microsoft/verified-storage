use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::seq::*;
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

pub open spec fn opaque_match_in_range<T>(s1: Seq<T>, s2: Seq<T>, start: int, end: int) -> bool
{
    &&& s1.len() == s2.len()
    &&& 0 <= start <= end <= s1.len()
    &&& opaque_subrange(s1, start, end) == opaque_subrange(s2, start, end)
}

pub open spec fn opaque_match_except_in_range<T>(s1: Seq<T>, s2: Seq<T>, start: int, end: int) -> bool
{
    &&& s1.len() == s2.len()
    &&& 0 <= start <= end <= s1.len()
    &&& opaque_match_in_range(s1, s2, 0, start)
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
        let cdb_bytes = opaque_section(s, addr, u64::spec_size_of());
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

pub broadcast proof fn broadcast_can_result_from_partial_write_effect_on_opaque(
    s2: Seq<u8>,
    s1: Seq<u8>,
    write_addr: int,
    bytes: Seq<u8>
)
    requires
        #[trigger] can_result_from_partial_write(s2, s1, write_addr, bytes),
        0 <= write_addr,
        write_addr + bytes.len() <= s1.len(),
    ensures
        opaque_match_except_in_range(s1, s2, write_addr, write_addr + bytes.len())
{
    reveal(opaque_subrange);
    let end = write_addr + bytes.len();
    lemma_can_result_from_partial_write_effect(s2, s1, write_addr, bytes);
    assert(opaque_subrange(s1, 0, write_addr) =~= opaque_subrange(s2, 0, write_addr));
    assert(opaque_subrange(s1, end, s1.len() as int) =~= opaque_subrange(s2, end, s1.len() as int));
}

pub broadcast proof fn broadcast_can_result_from_partial_write_effect_on_opaque_subranges(
    s2: Seq<u8>,
    s1: Seq<u8>,
    write_addr: int,
    bytes: Seq<u8>,
    inner_start: int,
    inner_end: int
)
    requires
        #[trigger] can_result_from_partial_write(s2, s1, write_addr, bytes),
        0 <= write_addr,
        write_addr + bytes.len() <= s1.len(),
        0 <= inner_start <= inner_end <= write_addr || write_addr + bytes.len() <= inner_start <= inner_end <= s1.len(),
    ensures
        opaque_subrange(s1, inner_start, inner_end) == #[trigger] opaque_subrange(s2, inner_start, inner_end),
{
    broadcast use broadcast_can_result_from_partial_write_effect_on_opaque;
    let end = write_addr + bytes.len();
    lemma_auto_opaque_subrange_subrange(s2, 0, write_addr);
    lemma_auto_opaque_subrange_subrange(s1, 0, write_addr);
    lemma_auto_opaque_subrange_subrange(s2, end, s1.len() as int);
    lemma_auto_opaque_subrange_subrange(s1, end, s1.len() as int);
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
        opaque_match_in_range(v1.read_state, v2.read_state, start, end),
{
    reveal(opaque_subrange);
    assert(opaque_subrange(v2.read_state, start, end) =~= opaque_subrange(v1.read_state, start, end));
}

pub broadcast proof fn broadcast_can_result_from_write_effect_on_read_state(
    v2: PersistentMemoryRegionView,
    v1: PersistentMemoryRegionView,
    write_addr: int,
    bytes: Seq<u8>
)
    requires
        v1.valid(),
        #[trigger] v2.can_result_from_write(v1, write_addr, bytes),
        0 <= write_addr,
        write_addr + bytes.len() <= v1.len(),
    ensures
        v2.valid(),
        opaque_match_except_in_range(v1.read_state, v2.read_state, write_addr, write_addr + bytes.len()),
        opaque_subrange(v2.read_state, write_addr, write_addr + bytes.len()) == bytes,
{
    lemma_can_result_from_write_effect_on_read_state(v2, v1, write_addr, bytes);
}

pub broadcast proof fn broadcast_can_result_from_write_effect_on_read_state_subranges(
    v2: PersistentMemoryRegionView,
    v1: PersistentMemoryRegionView,
    write_addr: int,
    bytes: Seq<u8>,
    inner_start: int,
    inner_end: int,
)
    requires
        v1.valid(),
        #[trigger] v2.can_result_from_write(v1, write_addr, bytes),
        0 <= write_addr,
        write_addr + bytes.len() <= v1.len(),
        0 <= inner_start <= inner_end <= write_addr || write_addr + bytes.len() <= inner_start <= inner_end <= v1.len(),
    ensures
        opaque_subrange(v1.read_state, inner_start, inner_end) ==
            #[trigger] opaque_subrange(v2.read_state, inner_start, inner_end),
{
    broadcast use broadcast_can_result_from_write_effect_on_read_state;
    let end = write_addr + bytes.len();
    lemma_auto_opaque_subrange_subrange(v1.read_state, 0, write_addr);
    lemma_auto_opaque_subrange_subrange(v2.read_state, 0, write_addr);
    lemma_auto_opaque_subrange_subrange(v1.read_state, end, v1.len() as int);
    lemma_auto_opaque_subrange_subrange(v2.read_state, end, v1.len() as int);
}

pub broadcast proof fn broadcast_length_of_opaque_subrange<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        #[trigger] opaque_subrange(s, i, j).len() == j - i,
{
    reveal(opaque_subrange);
}

pub proof fn lemma_opaque_subrange_subrange<T>(s: Seq<T>, outer_start: int, outer_end: int,
                                               inner_start: int, inner_end: int)
    requires
        0 <= outer_start <= inner_start <= inner_end <= outer_end <= s.len(),
    ensures
        opaque_subrange(s, inner_start, inner_end) ==
            opaque_subrange(opaque_subrange(s, outer_start, outer_end),
                            inner_start - outer_start, inner_end - outer_start),
           
{
    reveal(opaque_subrange);
    assert(opaque_subrange(s, inner_start, inner_end) =~=
           opaque_subrange(opaque_subrange(s, outer_start, outer_end),
                           inner_start - outer_start, inner_end - outer_start));
}

pub proof fn lemma_auto_opaque_subrange_subrange<T>(s: Seq<T>, outer_start: int, outer_end: int)
    requires
        0 <= outer_start <= outer_end <= s.len(),
    ensures
        forall|inner_start: int, inner_end: int|
            outer_start <= inner_start <= inner_end <= outer_end ==>
                #[trigger] opaque_subrange(s, inner_start, inner_end) ==
                opaque_subrange(opaque_subrange(s, outer_start, outer_end),
                                inner_start - outer_start, inner_end - outer_start),
{
    assert forall|inner_start: int, inner_end: int|
            outer_start <= inner_start <= inner_end <= outer_end implies
                #[trigger] opaque_subrange(s, inner_start, inner_end) ==
                opaque_subrange(opaque_subrange(s, outer_start, outer_end),
                                inner_start - outer_start, inner_end - outer_start) by {
        lemma_opaque_subrange_subrange(s, outer_start, outer_end, inner_start, inner_end);
    }
}

pub broadcast proof fn broadcast_opaque_subrange_subrange_dangerous<T>(
    s: Seq<T>,
    outer_start: int,
    outer_end: int,
    inner_start: int,
    inner_end: int
)
    requires
        0 <= outer_start <= inner_start <= inner_end <= outer_end <= s.len(),
    ensures
        #[trigger] opaque_subrange(s, inner_start, inner_end) ==
                   opaque_subrange(#[trigger] opaque_subrange(s, outer_start, outer_end),
                                   inner_start - outer_start, inner_end - outer_start),
{
    lemma_opaque_subrange_subrange(s, outer_start, outer_end, inner_start, inner_end);
}

pub broadcast proof fn broadcast_update_bytes_effect_on_opaque(s1: Seq<u8>, addr: int, bytes: Seq<u8>)
    requires
        0 <= addr,
        addr + bytes.len() <= s1.len(),
    ensures
        opaque_match_except_in_range(s1, update_bytes(s1, addr, bytes), addr, addr + bytes.len()),
        opaque_subrange(#[trigger] update_bytes(s1, addr, bytes), addr, addr + bytes.len()) == bytes,
{
    reveal(opaque_subrange);
    let end = addr + bytes.len();
    let s2 = update_bytes(s1, addr, bytes);
    assert(opaque_subrange(s2, addr, end) =~= bytes);
    assert(opaque_subrange(s2, 0, addr) =~= opaque_subrange(s1, 0, addr));
    assert(opaque_subrange(s2, end, s1.len() as int) =~= opaque_subrange(s1, end, s1.len() as int));
}

pub broadcast proof fn broadcast_update_bytes_effect_on_opaque_subranges(
    s1: Seq<u8>,
    addr: int,
    bytes: Seq<u8>,
    inner_start: int,
    inner_end: int
)
    requires
        0 <= addr,
        addr + bytes.len() <= s1.len(),
        0 <= inner_start <= inner_end <= addr || addr + bytes.len() <= inner_start <= inner_end <= s1.len(),
    ensures
        #[trigger] opaque_subrange(update_bytes(s1, addr, bytes), inner_start, inner_end) ==
                       opaque_subrange(s1, inner_start, inner_end),
{
    broadcast use broadcast_update_bytes_effect_on_opaque;
    broadcast use group_match_except_in_range;
}

pub broadcast proof fn broadcast_opaque_update_bytes_effect_on_opaque(
    s1: Seq<u8>,
    addr: int,
    bytes: Seq<u8>
)
    requires
        0 <= addr,
        addr + bytes.len() <= s1.len(),
    ensures
        opaque_match_except_in_range(s1, opaque_update_bytes(s1, addr, bytes), addr, addr + bytes.len()),
        opaque_subrange(#[trigger] opaque_update_bytes(s1, addr, bytes), addr, addr + bytes.len()) == bytes,
{
    reveal(opaque_update_bytes);
    broadcast use broadcast_update_bytes_effect_on_opaque;
}

pub broadcast proof fn broadcast_opaque_update_bytes_effect_on_opaque_subranges(
    s1: Seq<u8>,
    addr: int,
    bytes: Seq<u8>,
    inner_start: int,
    inner_end: int
)
    requires
        0 <= addr,
        addr + bytes.len() <= s1.len(),
        0 <= inner_start <= inner_end <= addr || addr + bytes.len() <= inner_start <= inner_end <= s1.len(),
    ensures
        #[trigger] opaque_subrange(opaque_update_bytes(s1, addr, bytes), inner_start, inner_end) ==
                       opaque_subrange(s1, inner_start, inner_end),
{
    reveal(opaque_update_bytes);
    broadcast use broadcast_update_bytes_effect_on_opaque_subranges;
}

pub broadcast proof fn broadcast_opaque_match_except_in_range_effect_on_subranges<T>(
    s1: Seq<T>,
    s2: Seq<T>,
    outer_start: int,
    outer_end: int,
    inner_start: int,
    inner_end: int
)
    requires
        #[trigger] opaque_match_except_in_range(s1, s2, outer_start, outer_end),
        0 <= inner_start <= inner_end <= outer_start || outer_end <= inner_start <= inner_end <= s1.len(),
    ensures
        #[trigger] opaque_subrange(s2, inner_start, inner_end) == opaque_subrange(s1, inner_start, inner_end),
{
    lemma_auto_opaque_subrange_subrange(s1, 0, outer_start);
    lemma_auto_opaque_subrange_subrange(s2, 0, outer_start);
    lemma_auto_opaque_subrange_subrange(s1, outer_end, s1.len() as int);
    lemma_auto_opaque_subrange_subrange(s2, outer_end, s2.len() as int);
}

pub broadcast proof fn broadcast_opaque_match_except_in_range_can_widen_range<T>(
    s1: Seq<T>,
    s2: Seq<T>,
    outer_start: int,
    outer_end: int,
    inner_start: int,
    inner_end: int
)
    requires
        #[trigger] opaque_match_except_in_range(s1, s2, inner_start, inner_end),
        0 <= outer_start <= inner_start <= inner_end <= outer_end <= s1.len(),
    ensures
        #[trigger] opaque_match_except_in_range(s1, s2, outer_start, outer_end),
{
    lemma_auto_opaque_subrange_subrange(s1, 0, inner_start);
    lemma_auto_opaque_subrange_subrange(s2, 0, inner_start);
    lemma_auto_opaque_subrange_subrange(s1, inner_end, s1.len() as int);
    lemma_auto_opaque_subrange_subrange(s2, inner_end, s2.len() as int);
}

pub proof fn lemma_concatenate_opaque_subranges<T>(s: Seq<T>, pos1: int, pos2: int, pos3: int)
    requires
        0 <= pos1 <= pos2 <= pos3 <= s.len(),
    ensures
        opaque_subrange(s, pos1, pos3) == opaque_subrange(s, pos1, pos2) + opaque_subrange(s, pos2, pos3),
{
    reveal(opaque_subrange);
    assert(opaque_subrange(s, pos1, pos3) =~= opaque_subrange(s, pos1, pos2) + opaque_subrange(s, pos2, pos3));
}

pub proof fn lemma_concatenate_three_opaque_subranges<T>(s: Seq<T>, pos1: int, pos2: int, pos3: int, pos4: int)
    requires
        0 <= pos1 <= pos2 <= pos3 <= pos4 <= s.len(),
    ensures
        opaque_subrange(s, pos1, pos4) ==
            opaque_subrange(s, pos1, pos2) + opaque_subrange(s, pos2, pos3) + opaque_subrange(s, pos3, pos4),
{
    reveal(opaque_subrange);
    assert(opaque_subrange(s, pos1, pos4) =~=
               opaque_subrange(s, pos1, pos2) + opaque_subrange(s, pos2, pos3) + opaque_subrange(s, pos3, pos4));
}

pub proof fn lemma_concatenate_four_opaque_subranges<T>(s: Seq<T>, pos1: int, pos2: int, pos3: int, pos4: int, pos5: int)
    requires
        0 <= pos1 <= pos2 <= pos3 <= pos4 <= pos5 <= s.len(),
    ensures
        opaque_subrange(s, pos1, pos5) ==
            opaque_subrange(s, pos1, pos2) + opaque_subrange(s, pos2, pos3) + opaque_subrange(s, pos3, pos4)
            + opaque_subrange(s, pos4, pos5),
{
    reveal(opaque_subrange);
    assert(opaque_subrange(s, pos1, pos5) =~=
               opaque_subrange(s, pos1, pos2) + opaque_subrange(s, pos2, pos3) + opaque_subrange(s, pos3, pos4)
               + opaque_subrange(s, pos4, pos5));
}

pub broadcast proof fn broadcast_opaque_match_in_range_effect_on_subranges<T>(
    s1: Seq<T>,
    s2: Seq<T>,
    outer_start: int,
    outer_end: int,
    inner_start: int,
    inner_end: int
)
    requires
        #[trigger] opaque_match_in_range(s1, s2, outer_start, outer_end),
        0 <= outer_start <= inner_start <= inner_end <= outer_end <= s1.len() == s2.len(),
    ensures
        #[trigger] opaque_subrange(s2, inner_start, inner_end) == opaque_subrange(s1, inner_start, inner_end),
{
    reveal(opaque_subrange);
    lemma_auto_opaque_subrange_subrange(s1, outer_start, outer_end);
    lemma_auto_opaque_subrange_subrange(s2, outer_start, outer_end);
}

pub broadcast proof fn broadcast_opaque_match_in_range_can_narrow_range<T>(
    s1: Seq<T>,
    s2: Seq<T>,
    outer_start: int,
    outer_end: int,
    inner_start: int,
    inner_end: int
)
    requires
        #[trigger] opaque_match_in_range(s1, s2, outer_start, outer_end),
        0 <= outer_start <= inner_start <= inner_end <= outer_end <= s1.len() == s2.len(),
    ensures
        #[trigger] opaque_subrange(s2, inner_start, inner_end) == opaque_subrange(s1, inner_start, inner_end),
{
    reveal(opaque_subrange);
    lemma_auto_opaque_subrange_subrange(s1, outer_start, outer_end);
    lemma_auto_opaque_subrange_subrange(s2, outer_start, outer_end);
}

pub broadcast group group_can_result_from_write_effect {
    broadcast_can_result_from_partial_write_effect_on_opaque,
    broadcast_can_result_from_partial_write_effect_on_opaque_subranges,
    broadcast_can_result_from_write_effect_on_read_state,
    broadcast_can_result_from_write_effect_on_read_state_subranges,
}

pub broadcast group group_update_bytes_effect {
    broadcast_update_bytes_effect_on_opaque,
    broadcast_update_bytes_effect_on_opaque_subranges,
    broadcast_opaque_update_bytes_effect_on_opaque,
    broadcast_opaque_update_bytes_effect_on_opaque_subranges,
}

pub broadcast group group_match_except_in_range {
    broadcast_opaque_match_except_in_range_effect_on_subranges,
    broadcast_opaque_match_except_in_range_can_widen_range,
}

pub broadcast group group_match_in_range {
    broadcast_opaque_match_in_range_effect_on_subranges,
    broadcast_opaque_match_in_range_can_narrow_range,
}

pub broadcast group group_opaque_subrange {
    group_can_result_from_write_effect,
    group_update_bytes_effect,
    broadcast_length_of_opaque_subrange,
}

}

