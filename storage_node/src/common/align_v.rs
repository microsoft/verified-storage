use builtin::*;
use builtin_macros::*;
use crate::pmem::pmcopy_t::PmCopy;
use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_vanish};

verus! {

#[verifier::opaque]
pub open spec fn opaque_aligned(addr: int, alignment: int) -> bool
    recommends
        0 < alignment
{
    addr % alignment == 0
}

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

pub open spec fn round_up_to_alignment(addr: int, alignment: int) -> int
    recommends
        0 < alignment
{
    addr + space_needed_for_alignment(addr, alignment)
}

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

pub proof fn lemma_space_needed_for_alignment_works(addr: int, alignment: int)
    requires
        0 < alignment,
    ensures
        0 <= space_needed_for_alignment(addr, alignment) < alignment,
        opaque_aligned(addr + space_needed_for_alignment(addr, alignment), alignment)
{
    reveal(opaque_aligned);
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

pub open spec fn spec_allocate_space<T>(offset: int) -> (bounds: (int, int))
    where
        T: PmCopy
    recommends
        0 < T::spec_align_of(),
{
    let start = round_up_to_alignment(offset, T::spec_align_of() as int);
    let end = start + T::spec_size_of();
    (start, end)
}

pub open spec fn spec_allocate_specified_space(offset: int, size: int, alignment: int) -> (bounds: (int, int))
    recommends
        0 < alignment,
{
    let start = round_up_to_alignment(offset, alignment);
    let end = start + size;
    (start, end)
}

}
