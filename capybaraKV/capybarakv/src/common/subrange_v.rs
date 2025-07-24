// This file provides utility functions and proofs for working with subranges of sequences and their properties.
// It includes operations for extracting subranges, comparing sequences within specific ranges, and verifying
// the effects of partial writes on sequences and persistent memory views. It includes several broadcast
// lemmas and broadcast groups for ease of use.

use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::seq::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe};
use crate::pmem::pmemutil_v::*;

verus! {

// Extracts a subrange of a sequence starting at index `i` with length `len`.
pub open spec fn extract_section<T>(s: Seq<T>, i: int, len: nat) -> Seq<T>
{
    s.subrange(i, i + len)
}

// Indicates whether two sequences match within a specified range [start, end).
pub open spec fn seqs_match_in_range<T>(s1: Seq<T>, s2: Seq<T>, start: int, end: int) -> bool
{
    &&& s1.len() == s2.len()
    &&& 0 <= start <= end <= s1.len()
    &&& s1.subrange(start, end) == s2.subrange(start, end)
}

// Indicates whether two sequences match except within a specified range [start, end).
pub open spec fn seqs_match_except_in_range<T>(s1: Seq<T>, s2: Seq<T>, start: int, end: int) -> bool
{
    &&& s1.len() == s2.len()
    &&& start <= end
    &&& seqs_match_in_range(s1, s2, 0, start)
    &&& seqs_match_in_range(s1, s2, end, s1.len() as int)
}

// Indicates whether two persistent memory views match within a specified range [start, end).
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

// Indicates whether two persistent memory views match except within a specified range [start, end).
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

// Proves that two sequences related by can_result_from_partial_write match
// except in the specified range.
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

// Proves (in a way that can be used by broadcast) that two sequences related by
// can_result_from_partial_write match except in the range of the write.
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

// Proves, in a way that can be used by broadcast, that two sequences related by
// can_result_from_partial_write match in any subrange that doesn't
// overlap with the write range. It's triggered by saying
// `s1.subrange(inner_start, inner_end)` where `s1` is the original sequence
// that gets written to.
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

// Proves that if two persistent memory views are related by can_result_from_write,
// then (1) the state resulting from the write operation is valid, (2) the two
// read states match except in the range of the write, and (3) the subrange of the
// resulting read state that corresponds to the write range equals the bytes written.
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


// Proves, in a way that can be used by broadcast, that if two persistent memory views are related by
// can_result_from_write, then (1) the state resulting from the write operation is valid, (2) the two
// read states match except in the range of the write, and (3) the subrange of the resulting read state
// that corresponds to the write range equals the bytes written.
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

// Proves, in a way that can be used by broadcast, that if two persistent memory views are related by
// can_result_from_write, then the two read states match in any subrange that doesn't overlap with the
// write range. The trigger is `v2.read_state.subrange(inner_start, inner_end)` where `v2` is the
// persistent memory view that results from the write.
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

// Proves that the length of a subrange is equal to the difference between its start and end indices.
pub broadcast proof fn broadcast_length_of_subrange<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        #[trigger] s.subrange(i, j).len() == j - i,
{
}

// Proves that a subrange of a subrange is equivalent to a single subrange operation.
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

// Proves, in a way that can be used by broadcast, that a subrange of a subrange is equivalent to a single
// subrange operation. The trigger has two parts: `s.subrange(inner_start, inner_end)` and
// `s.subrange(outer_start, outer_end)`. The function ends in `_dangerous` because it can lead
// to a large number of cascading quantifier instatiations.
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

// Proves, in a way that can be used by broadcast, how updating a subsequence with `update_bytes`
// affects subranges of the resulting sequence. It makes the two sequences match except in the
// range of the update, and it makes the subrange of the resulting sequence that corresponds to the
// update range equal to the bytes written. The trigger is `update_bytes(s1, addr, bytes)`.
pub broadcast proof fn broadcast_update_bytes_effect(s1: Seq<u8>, addr: int, bytes: Seq<u8>)
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

// Proves, in a way that can be used by broadcast, how updating bytes in a sequence with `update_bytes`
// affecs subranges of the resulting sequence that don't overlap with the update range. The trigger
// is `update_bytes(s1, addr, bytes).subrange(inner_start, inner_end)` where `s1` is the original sequence
// that gets written to.
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
    broadcast use broadcast_update_bytes_effect;
    broadcast use broadcast_seqs_match_in_range_can_narrow_range;
}

// Proves, in a way that can be used by broadcast, that concatenating two consecutive subranges gives
// the same result as a single subrange operation. The trigger is two parts, one for each consecutive
// subrange.
pub broadcast proof fn lemma_concatenate_subranges<T>(s: Seq<T>, pos1: int, pos2: int, pos3: int)
    requires
        0 <= pos1 <= pos2 <= pos3 <= s.len(),
    ensures
        s.subrange(pos1, pos3) == #[trigger] s.subrange(pos1, pos2) + #[trigger] s.subrange(pos2, pos3),
{
    assert(s.subrange(pos1, pos3) =~= s.subrange(pos1, pos2) + s.subrange(pos2, pos3));
}

// Proves that concatenating three consecutive subranges gives the same result as a single subrange
// operation.
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

// Proves that concatenating four consecutive subranges is equivalent to a single subrange operation.
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

// Proves, in a way that can be used by broadcast, that if two sequences match in a range,
// then they also match in any subrange of that range. The trigger is two parts:
// `seqs_match_in_range(s1, s2, outer_start, outer_end)` and `s1.subrange(inner_start, inner_end)`.
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

// Proves, in a way that can be used by broadcast, that if sequences s1 and s2 match
// in range `[inner_start, inner_end)` and s2 and s3 match in range `[outer_start, outer_end)`,
// where the inner range is a subrange of the outer range, then s1 and s3 also match in the
// inner range. The trigger is two parts:
// `seqs_match_in_range(s1, s2, inner_start, inner_end)` and
// `seqs_match_in_range(s2, s3, outer_start, outer_end)`.
pub broadcast proof fn broadcast_seqs_match_in_range_transitive<T>(
    s1: Seq<T>,
    s2: Seq<T>,
    s3: Seq<T>,
    outer_start: int,
    outer_end: int,
    inner_start: int,
    inner_end: int,
)
    requires
        seqs_match_in_range(s1, s2, inner_start, inner_end),
        0 <= outer_start <= inner_start <= inner_end <= outer_end <= s1.len(),
        #[trigger] seqs_match_in_range(s2, s3, outer_start, outer_end),
    ensures
        #[trigger] seqs_match_in_range(s1, s3, inner_start, inner_end),
{
    broadcast use broadcast_seqs_match_in_range_can_narrow_range;
}

// Groups broadcasts related to the effects of `can_result_from_write`
// and its variants (e.g., `can_result_from_partial_write`).
pub broadcast group group_can_result_from_write_effect {
    broadcast_can_result_from_partial_write_effect_on_match,
    broadcast_can_result_from_partial_write_effect_on_subranges,
    broadcast_can_result_from_write_effect_on_read_state,
    broadcast_can_result_from_write_effect_on_read_state_subranges,
}

// Groups broadcasts related to the effects of `update_bytes`.
pub broadcast group group_update_bytes_effect {
    broadcast_update_bytes_effect,
    broadcast_update_bytes_effect_on_subranges,
}

}

