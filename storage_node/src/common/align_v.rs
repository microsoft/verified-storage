use builtin::*;
use builtin_macros::*;
use crate::pmem::pmcopy_t::{PmCopy, pmcopy_axioms};
use crate::pmem::traits_t::align_of;
use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_vanish};

verus! {

#[verifier::opaque]
pub open spec fn opaque_aligned(addr: nat, alignment: nat) -> bool
    recommends
        0 < alignment
{
    addr % alignment == 0
}

pub closed spec fn space_needed_for_alignment(addr: nat, alignment: nat) -> nat
    recommends
        0 < alignment
{
    let remainder = addr % alignment;
    if remainder == 0 {
        0
    }
    else {
        (alignment - remainder) as nat
    }
}

pub open spec fn round_up_to_alignment(addr: nat, alignment: nat) -> nat
    recommends
        0 < alignment
{
    addr + space_needed_for_alignment(addr, alignment)
}

pub proof fn lemma_auto_space_needed_for_alignment_bounded()
    ensures
        forall|addr: nat, alignment: nat| 0 < alignment ==>
            #[trigger] space_needed_for_alignment(addr, alignment) < alignment,
{
}

pub exec fn get_space_needed_for_alignment_usize(addr: u64, alignment: usize) -> (result: usize)
    requires
        0 < alignment,
    ensures
        result == space_needed_for_alignment(addr as nat, alignment as nat)
{
    let remainder: usize = (addr % (alignment as u64)) as usize;
    if remainder == 0 {
        remainder
    }
    else {
        alignment - remainder
    }
}

pub exec fn exec_round_up_to_alignment<T>(addr: u64) -> (result: u64)
    where
        T: PmCopy,
    requires
        0 < T::spec_align_of(),
        round_up_to_alignment(addr as nat, T::spec_align_of()) <= u64::MAX,
    ensures
        result == round_up_to_alignment(addr as nat, T::spec_align_of()),
{
    broadcast use pmcopy_axioms;
    let alignment_needed = get_space_needed_for_alignment_usize(addr, align_of::<T>());
    addr + (alignment_needed as u64)
}

pub exec fn get_space_needed_for_alignment(addr: u64, alignment: u64) -> (result: u64)
    requires
        0 < alignment,
    ensures
        result == space_needed_for_alignment(addr as nat, alignment as nat)
{
    let remainder = addr % alignment;
    if remainder == 0 {
        remainder
    }
    else {
        alignment - remainder
    }
}

pub proof fn lemma_space_needed_for_alignment_works(addr: nat, alignment: nat)
    requires
        0 < alignment,
    ensures
        space_needed_for_alignment(addr, alignment) < alignment,
        opaque_aligned(addr + space_needed_for_alignment(addr, alignment), alignment)
{
    reveal(opaque_aligned);
    let remainder = addr % alignment;
    if remainder != 0 {
        assert(addr == alignment * (addr / alignment) + (addr % alignment)) by {
            lemma_fundamental_div_mod(addr as int, alignment as int);
        }
        assert(addr + alignment - remainder == alignment * (addr / alignment) + alignment);
        assert((addr + alignment - remainder) % (alignment as int) == alignment % alignment) by {
            lemma_mod_multiples_vanish(addr as int / alignment as int, alignment as int, alignment as int);
        }
    }
}

pub open spec fn spec_allocate_space<T>(offset: nat) -> (bounds: (nat, nat))
    where
        T: PmCopy,
    recommends
        0 < T::spec_align_of(),
{
    let start = round_up_to_alignment(offset, T::spec_align_of());
    let end = start + T::spec_size_of();
    (start, end)
}

pub open spec fn spec_allocate_specified_space(offset: nat, size: nat, alignment: nat) -> (bounds: (nat, nat))
    recommends
        0 < alignment,
{
    let start = round_up_to_alignment(offset, alignment);
    let end = start + size;
    (start, end)
}

}
