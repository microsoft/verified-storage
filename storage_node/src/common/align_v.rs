use builtin::*;
use builtin_macros::*;
use crate::pmem::pmcopy_t::PmCopy;
use crate::pmem::traits_t::align_of;
use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_vanish};

verus! {

pub open spec fn is_aligned(addr: int, alignment: int) -> bool
    recommends
        0 < alignment
{
    addr % alignment == 0
}

pub closed spec fn space_needed_for_alignment(addr: int, alignment: int) -> int
{
    if alignment <= 0 {
        0
    } else {
        let remainder = addr % alignment;
        if remainder == 0 {
            0
        }
        else {
            alignment - remainder
        }
    }
}

pub open spec fn round_up_to_alignment(addr: int, alignment: int) -> int
{
    addr + space_needed_for_alignment(addr, alignment)
}

pub proof fn lemma_auto_space_needed_for_alignment_bounded()
    ensures
        forall|addr: int, alignment: int| #![trigger space_needed_for_alignment(addr, alignment)] {
            let space = space_needed_for_alignment(addr, alignment);
            &&& 0 <= space
            &&& if alignment > 0 { space < alignment } else { space == 0 }
        },
{
}

pub exec fn get_space_needed_for_alignment_usize(addr: u64, alignment: usize) -> (result: usize)
    ensures
        result == space_needed_for_alignment(addr as int, alignment as int)
{
    if alignment == 0 {
        0
    }
    else {
        let remainder: usize = (addr % (alignment as u64)) as usize;
        if remainder == 0 {
            remainder
        }
        else {
            alignment - remainder
        }
    }
}

pub exec fn exec_round_up_to_alignment<T>(addr: u64) -> (result: u64)
    where
        T: PmCopy,
    requires
        round_up_to_alignment(addr as int, T::spec_align_of() as int) <= u64::MAX,
    ensures
        result == round_up_to_alignment(addr as int, T::spec_align_of() as int),
{
    let alignment_needed = get_space_needed_for_alignment_usize(addr, align_of::<T>());
    addr + (alignment_needed as u64)
}

pub exec fn get_space_needed_for_alignment(addr: u64, alignment: u64) -> (result: u64)
    ensures
        result == space_needed_for_alignment(addr as int, alignment as int)
{
    if alignment == 0 {
        0
    }
    else {
        let remainder = addr % alignment;
        if remainder == 0 {
            remainder
        }
        else {
            alignment - remainder
        }
    }
}

pub proof fn lemma_space_needed_for_alignment_works(addr: int, alignment: int)
    ensures
        0 <= space_needed_for_alignment(addr, alignment),
        alignment > 0 ==> space_needed_for_alignment(addr, alignment) < alignment,
        alignment > 0 ==> is_aligned(addr + space_needed_for_alignment(addr, alignment), alignment),
        alignment <= 0 ==> space_needed_for_alignment(addr, alignment) == 0,
{
    if alignment > 0 {
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
}

}
