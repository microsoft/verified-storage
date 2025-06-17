// This file contains utility functions and specifications for memory alignment operations.
// It includes methods for calculating alignment, reserving space, and ensuring proper alignment for memory operations.

use builtin::*;
use builtin_macros::*;
use crate::pmem::pmcopy_t::{pmcopy_axioms, PmCopy};
use crate::pmem::traits_t::{align_of, size_of};
use vstd::arithmetic::overflow::CheckedU64;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_vanish};

verus! {

// Returns a boolean indicating whether a given address is aligned to a specified alignment.
pub open spec fn is_aligned(addr: int, alignment: int) -> bool
    recommends
        0 < alignment
{
    addr % alignment == 0
}

// Calculates the additional space needed to align an address to a specified alignment.
// Returns the space needed for alignment.
pub closed spec fn space_needed_for_alignment(addr: int, alignment: int) -> int
    recommends
        0 < alignment
{
    let remainder = addr % alignment;
    if remainder == 0 {
        0
    }
    else {
        alignment - remainder
    }
}

// Rounds up a given address to the nearest aligned address based on the specified alignment.
// Returns the aligned address.
pub open spec fn round_up_to_alignment(addr: int, alignment: int) -> int
    recommends
        0 < alignment
{
    addr + space_needed_for_alignment(addr, alignment)
}

// Proves that the space needed for alignment is always bounded by the alignment value.
// Ensures the result is within the valid range.
pub proof fn lemma_auto_space_needed_for_alignment_bounded()
    ensures
        forall|addr: int, alignment: int| 0 < alignment ==>
            0 <= #[trigger] space_needed_for_alignment(addr, alignment) < alignment,
{
}

// Computes the space needed for alignment for a given address and alignment (usize).
// Returns the space needed as a usize value.
pub exec fn get_space_needed_for_alignment_usize(addr: u64, alignment: usize) -> (result: usize)
    requires
        0 < alignment,
    ensures
        result == space_needed_for_alignment(addr as int, alignment as int)
{
    let remainder: usize = (addr % (alignment as u64)) as usize;
    if remainder == 0 {
        remainder
    }
    else {
        alignment - remainder
    }
}

// Rounds up a given address to the nearest aligned address for a specific type T.
// Returns the aligned address as a u64 value.
pub exec fn exec_round_up_to_alignment<T>(addr: u64) -> (result: u64)
    where
        T: PmCopy,
    requires
        0 < T::spec_align_of(),
        round_up_to_alignment(addr as int, T::spec_align_of() as int) <= u64::MAX,
    ensures
        result == round_up_to_alignment(addr as int, T::spec_align_of() as int),
{
    let alignment_needed = get_space_needed_for_alignment_usize(addr, align_of::<T>());
    addr + (alignment_needed as u64)
}

// Computes the space needed for alignment for a given address and alignment (u64).
// Returns the space needed as a u64 value.
pub exec fn get_space_needed_for_alignment(addr: u64, alignment: u64) -> (result: u64)
    requires
        0 < alignment,
    ensures
        result == space_needed_for_alignment(addr as int, alignment as int)
{
    let remainder = addr % alignment;
    if remainder == 0 {
        remainder
    }
    else {
        alignment - remainder
    }
}

// Proves that `space_needed_for_alignment` works correctly and ensures alignment.
pub proof fn lemma_space_needed_for_alignment_works(addr: int, alignment: int)
    requires
        0 < alignment,
    ensures
        0 <= space_needed_for_alignment(addr, alignment) < alignment,
        is_aligned(addr + space_needed_for_alignment(addr, alignment), alignment)
{
    let remainder = addr % alignment;
    if remainder != 0 {
        assert(addr == alignment * (addr / alignment) + (addr % alignment)) by {
            lemma_fundamental_div_mod(addr, alignment);
        }
        assert(addr + alignment - remainder == alignment * (addr / alignment) + alignment);
        assert((addr + alignment - remainder) % alignment == alignment % alignment) by {
            lemma_mod_multiples_vanish(addr / alignment, alignment, alignment);
        }
    }
}

// Reserves space for a specific type T starting from a given offset.
// Returns the bounds of the reserved space (its beginning and end) as a tuple.
pub open spec fn spec_reserve_space<T>(offset: int) -> (bounds: (int, int))
    where
        T: PmCopy,
    recommends
        0 < T::spec_align_of(),
{
    let start = round_up_to_alignment(offset, T::spec_align_of() as int);
    let end = start + T::spec_size_of();
    (start, end)
}

// Reserves a specified amount of space with a given alignment starting from an offset.
// Returns the bounds of the reserved space (its beginning and end) as a tuple.
pub open spec fn spec_reserve_specified_space(offset: int, size: int, alignment: int) -> (bounds: (int, int))
    recommends
        0 < alignment,
{
    let start = round_up_to_alignment(offset, alignment);
    let end = start + size;
    (start, end)
}

// Aligns a CheckedU64 value to the nearest specified alignment (u64).
// Returns the aligned CheckedU64 value.
#[inline]
pub exec fn align_checked_u64(v: &CheckedU64, alignment: u64) -> (result: CheckedU64)
    requires
        0 < alignment,
    ensures
        v@ <= result@,
        result@ < v@ + alignment,
        result@ == round_up_to_alignment(v@ as int, alignment as int),
        is_aligned(result@ as int, alignment as int),
{
    proof {
        lemma_space_needed_for_alignment_works(v@ as int, alignment as int);
    }

    if v.is_overflowed() {
        CheckedU64::new_overflowed(Ghost(round_up_to_alignment(v@ as int, alignment as int)))
    }
    else {
        v.add_value(get_space_needed_for_alignment(v.unwrap(), alignment))
    }
}

// Aligns a CheckedU64 value to the nearest specified alignment (usize).
// Returns the aligned CheckedU64 value.
#[inline]
pub exec fn align_checked_u64_to_usize(v: &CheckedU64, alignment: usize) -> (result: CheckedU64)
    requires
        0 < alignment,
    ensures
        v@ <= result@,
        result@ < v@ + alignment,
        result@ == round_up_to_alignment(v@ as int, alignment as int),
        is_aligned(result@ as int, alignment as int),
{
    proof {
        lemma_space_needed_for_alignment_works(v@ as int, alignment as int);
    }

    if v.is_overflowed() {
        CheckedU64::new_overflowed(Ghost(round_up_to_alignment(v@ as int, alignment as int)))
    }
    else {
        v.add_value(get_space_needed_for_alignment_usize(v.unwrap(), alignment) as u64)
    }
}

// Reserves space for a specific type T starting from a CheckedU64 offset.
// Returns the bounds of the reserved space (beginning and end) as a tuple of
// CheckedU64 values.
#[inline]
pub exec fn reserve_space<T>(offset: &CheckedU64) -> (bounds: (CheckedU64, CheckedU64))
    where
        T: PmCopy
    requires
        0 < T::spec_align_of(),
    ensures
        ({
            let (start, end) = bounds;
            &&& offset@ <= start@ < offset@ + T::spec_align_of()
            &&& start@ == round_up_to_alignment(offset@ as int, T::spec_align_of() as int)
            &&& is_aligned(start@ as int, T::spec_align_of() as int)
            &&& end@ - start@ == T::spec_size_of()
        })
{
    let start = align_checked_u64_to_usize(&offset, align_of::<T>());
    let end = start.add_value(size_of::<T>() as u64);
    (start, end)
}

// Reserves a specified amount of space with a given alignment starting from a CheckedU64 offset.
// Returns the bounds of the reserved space (its beginning and end) as a tuple of CheckedU64 values.
#[inline]
pub exec fn reserve_specified_space(offset: &CheckedU64, size: u64, alignment: u64)
                                    -> (bounds: (CheckedU64, CheckedU64))
    requires
        0 < alignment,
    ensures
        ({
            let (start, end) = bounds;
            &&& offset@ <= start@ < offset@ + alignment
            &&& start@ == round_up_to_alignment(offset@ as int, alignment as int)
            &&& is_aligned(start@ as int, alignment as int)
            &&& end@ - start@ == size
        })
{
    let start = align_checked_u64(&offset, alignment);
    let end = start.add_value(size);
    (start, end)
}

// Reserves a specified amount of space with a given alignment starting from a CheckedU64 offset.
// Uses CheckedU64 for both size and offset.
// Returns the bounds of the reserved space (its beginning and end) as a tuple of CheckedU64 values.
#[inline]
pub exec fn reserve_specified_space_checked_u64(offset: &CheckedU64, size: &CheckedU64, alignment: u64)
                                                    -> (bounds: (CheckedU64, CheckedU64))
    requires
        0 < alignment,
    ensures
        ({
            let (start, end) = bounds;
            &&& offset@ <= start@ < offset@ + alignment
            &&& start@ == round_up_to_alignment(offset@ as int, alignment as int)
            &&& is_aligned(start@ as int, alignment as int)
            &&& end@ - start@ == size@
        })
{
    let start = align_checked_u64(&offset, alignment);
    let end = start.add_checked(size);
    (start, end)
}

}

