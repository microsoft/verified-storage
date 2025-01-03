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

pub open spec fn extract_section<T>(s: Seq<T>, i: int, len: nat) -> Seq<T>
{
    s.subrange(i, i + len)
}

pub open spec fn seqs_match_in_range<T>(s1: Seq<T>, s2: Seq<T>, start: int, end: int) -> bool
{
    &&& s1.len() == s2.len()
    &&& 0 <= start <= end <= s1.len()
    &&& s1.subrange(start, end) == s2.subrange(start, end)
}

pub open spec fn seqs_match_except_in_range<T>(s1: Seq<T>, s2: Seq<T>, start: int, end: int) -> bool
{
    &&& start <= end
    &&& seqs_match_in_range(s1, s2, 0, start)
    &&& seqs_match_in_range(s1, s2, end, s1.len() as int)
}

pub open spec fn pm_views_match_in_range(
    v1: PersistentMemoryRegionView,
    v2: PersistentMemoryRegionView,
    start: int,
    end: int,
) -> bool
{
    &&& seqs_match_in_range(v1.durable_state, v2.durable_state, start, end)
    &&& seqs_match_in_range(v1.read_state, v2.read_state, start, end)
}

pub open spec fn pm_views_match_except_in_range(
    v1: PersistentMemoryRegionView,
    v2: PersistentMemoryRegionView,
    start: int,
    end: int,
) -> bool
{
    &&& seqs_match_except_in_range(v1.durable_state, v2.durable_state, start, end)
    &&& seqs_match_except_in_range(v1.read_state, v2.read_state, start, end)
}

pub proof fn lemma_can_result_from_partial_write_effect_on_match(
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
        seqs_match_except_in_range(s1, s2, write_addr, write_addr + bytes.len()),
{
    lemma_can_result_from_partial_write_effect(s2, s1, write_addr, bytes);
    assert(s1.subrange(0, write_addr) =~= s2.subrange(0, write_addr));
    assert(s1.subrange(write_addr + bytes.len(), s1.len() as int) =~=
           s2.subrange(write_addr + bytes.len(), s2.len() as int));
}

pub broadcast proof fn broadcast_can_result_from_partial_write_effect_on_match(
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
        seqs_match_except_in_range(s1, s2, write_addr, write_addr + bytes.len())
{
    let end = write_addr + bytes.len();
    lemma_can_result_from_partial_write_effect(s2, s1, write_addr, bytes);
    assert(s1.subrange(0, write_addr) =~= s2.subrange(0, write_addr));
    assert(s1.subrange(end, s1.len() as int) =~= s2.subrange(end, s1.len() as int));
}

pub broadcast proof fn broadcast_can_result_from_partial_write_effect_on_subranges(
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
        s1.subrange(inner_start, inner_end) == #[trigger] s2.subrange(inner_start, inner_end),
{
    broadcast use broadcast_can_result_from_partial_write_effect_on_match;
    broadcast use broadcast_subrange_subrange_dangerous;
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
        seqs_match_except_in_range(v1.read_state, v2.read_state, write_addr, write_addr + bytes.len()),
        v2.read_state.subrange(write_addr, write_addr + bytes.len()) == bytes,
{
    let s1 = v1.read_state;
    let s2 = v2.read_state;
    let start = write_addr;
    let end = write_addr + bytes.len();

    assert(s1.subrange(0, start) =~= s2.subrange(0, start));
    assert(s1.subrange(end, s1.len() as int) =~= s2.subrange(end, s2.len() as int));
    assert(v2.read_state.subrange(start, end) =~= bytes);
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
        seqs_match_in_range(v1.read_state, v2.read_state, start, end),
{
    assert(v2.read_state.subrange(start, end) =~= v1.read_state.subrange(start, end));
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
        seqs_match_except_in_range(v1.read_state, v2.read_state, write_addr, write_addr + bytes.len()),
        v2.read_state.subrange(write_addr, write_addr + bytes.len()) == bytes,
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
        v1.read_state.subrange(inner_start, inner_end) ==
            #[trigger] v2.read_state.subrange(inner_start, inner_end),
{
    broadcast use broadcast_can_result_from_write_effect_on_read_state;
    broadcast use broadcast_subrange_subrange_dangerous;
}

pub broadcast proof fn broadcast_length_of_subrange<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        #[trigger] s.subrange(i, j).len() == j - i,
{
}

pub proof fn lemma_subrange_subrange<T>(s: Seq<T>, outer_start: int, outer_end: int,
                                               inner_start: int, inner_end: int)
    requires
        0 <= outer_start <= inner_start <= inner_end <= outer_end <= s.len(),
    ensures
        s.subrange(inner_start, inner_end) ==
            s.subrange(outer_start, outer_end).subrange(inner_start - outer_start, inner_end - outer_start),
           
{
    assert(s.subrange(inner_start, inner_end) =~=
           s.subrange(outer_start, outer_end).subrange(inner_start - outer_start, inner_end - outer_start));
}

pub proof fn lemma_auto_subrange_subrange<T>(s: Seq<T>, outer_start: int, outer_end: int)
    requires
        0 <= outer_start <= outer_end <= s.len(),
    ensures
        forall|inner_start: int, inner_end: int|
            outer_start <= inner_start <= inner_end <= outer_end ==>
                #[trigger] s.subrange(inner_start, inner_end) ==
                s.subrange(outer_start, outer_end).subrange(inner_start - outer_start, inner_end - outer_start),
{
    assert forall|inner_start: int, inner_end: int|
            outer_start <= inner_start <= inner_end <= outer_end implies
                #[trigger] s.subrange(inner_start, inner_end) ==
                s.subrange(outer_start, outer_end).subrange(inner_start - outer_start, inner_end - outer_start) by {
        lemma_subrange_subrange(s, outer_start, outer_end, inner_start, inner_end);
    }
}

pub broadcast proof fn broadcast_subrange_subrange_dangerous<T>(
    s: Seq<T>,
    outer_start: int,
    outer_end: int,
    inner_start: int,
    inner_end: int
)
    requires
        0 <= outer_start <= inner_start <= inner_end <= outer_end <= s.len(),
    ensures
        #[trigger] s.subrange(inner_start, inner_end) ==
                   (#[trigger] s.subrange(outer_start, outer_end)).subrange(inner_start - outer_start,
                                                                            inner_end - outer_start),
{
    lemma_subrange_subrange(s, outer_start, outer_end, inner_start, inner_end);
}

pub broadcast proof fn broadcast_update_bytes_effect_on_match(s1: Seq<u8>, addr: int, bytes: Seq<u8>)
    requires
        0 <= addr,
        addr + bytes.len() <= s1.len(),
    ensures
        seqs_match_except_in_range(s1, update_bytes(s1, addr, bytes), addr, addr + bytes.len()),
        (#[trigger] update_bytes(s1, addr, bytes)).subrange(addr, addr + bytes.len()) == bytes,
{
    let end = addr + bytes.len();
    let s2 = update_bytes(s1, addr, bytes);
    assert(s2.subrange(addr, end) =~= bytes);
    assert(s2.subrange(0, addr) =~= s1.subrange(0, addr));
    assert(s2.subrange(end, s1.len() as int) =~= s1.subrange(end, s1.len() as int));
}

pub broadcast proof fn broadcast_update_bytes_effect_on_subranges(
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
        #[trigger] update_bytes(s1, addr, bytes).subrange(inner_start, inner_end) ==
            s1.subrange(inner_start, inner_end),
{
    broadcast use broadcast_update_bytes_effect_on_match;
    broadcast use group_match_in_range;
}

pub broadcast proof fn lemma_concatenate_subranges<T>(s: Seq<T>, pos1: int, pos2: int, pos3: int)
    requires
        0 <= pos1 <= pos2 <= pos3 <= s.len(),
    ensures
        s.subrange(pos1, pos3) == #[trigger] s.subrange(pos1, pos2) + #[trigger] s.subrange(pos2, pos3),
{
    assert(s.subrange(pos1, pos3) =~= s.subrange(pos1, pos2) + s.subrange(pos2, pos3));
}

pub proof fn lemma_concatenate_three_subranges<T>(s: Seq<T>, pos1: int, pos2: int, pos3: int, pos4: int)
    requires
        0 <= pos1 <= pos2 <= pos3 <= pos4 <= s.len(),
    ensures
        s.subrange(pos1, pos4) ==
            s.subrange(pos1, pos2) + s.subrange(pos2, pos3) + s.subrange(pos3, pos4),
{
    assert(s.subrange(pos1, pos4) =~=
               s.subrange(pos1, pos2) + s.subrange(pos2, pos3) + s.subrange(pos3, pos4));
}

pub proof fn lemma_concatenate_four_subranges<T>(s: Seq<T>, pos1: int, pos2: int, pos3: int, pos4: int, pos5: int)
    requires
        0 <= pos1 <= pos2 <= pos3 <= pos4 <= pos5 <= s.len(),
    ensures
        s.subrange(pos1, pos5) ==
            s.subrange(pos1, pos2) + s.subrange(pos2, pos3) + s.subrange(pos3, pos4)
            + s.subrange(pos4, pos5),
{
    assert(s.subrange(pos1, pos5) =~=
               s.subrange(pos1, pos2) + s.subrange(pos2, pos3) + s.subrange(pos3, pos4)
               + s.subrange(pos4, pos5));
}

pub broadcast proof fn broadcast_seqs_match_in_range_effect_on_subranges<T>(
    s1: Seq<T>,
    s2: Seq<T>,
    outer_start: int,
    outer_end: int,
    inner_start: int,
    inner_end: int,
)
    requires
        #[trigger] seqs_match_in_range(s1, s2, outer_start, outer_end),
        0 <= outer_start <= inner_start <= inner_end <= outer_end <= s1.len(),
    ensures
        #[trigger] s2.subrange(inner_start, inner_end) == s1.subrange(inner_start, inner_end),
{
    broadcast use broadcast_subrange_subrange_dangerous;
}

pub broadcast proof fn broadcast_seqs_match_in_range_can_narrow_range<T>(
    s1: Seq<T>,
    s2: Seq<T>,
    outer_start: int,
    outer_end: int,
    inner_start: int,
    inner_end: int,
)
    requires
        #[trigger] seqs_match_in_range(s1, s2, outer_start, outer_end),
        0 <= outer_start <= inner_start <= inner_end <= outer_end <= s1.len(),
    ensures
        #[trigger] s2.subrange(inner_start, inner_end) == s1.subrange(inner_start, inner_end),
{
    broadcast use broadcast_subrange_subrange_dangerous;
}

pub broadcast group group_can_result_from_write_effect {
    broadcast_can_result_from_partial_write_effect_on_match,
    broadcast_can_result_from_partial_write_effect_on_subranges,
    broadcast_can_result_from_write_effect_on_read_state,
    broadcast_can_result_from_write_effect_on_read_state_subranges,
}

pub broadcast group group_update_bytes_effect {
    broadcast_update_bytes_effect_on_match,
    broadcast_update_bytes_effect_on_subranges,
}

pub broadcast group group_match_in_range {
    broadcast_seqs_match_in_range_effect_on_subranges,
    broadcast_seqs_match_in_range_can_narrow_range,
}

pub broadcast group group_auto_subrange {
    group_can_result_from_write_effect,
    group_update_bytes_effect,
    broadcast_length_of_subrange,
}

}

