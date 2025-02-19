use builtin::*;
use builtin_macros::*;
use crate::pmem::pmcopy_t::{pmcopy_axioms, PmCopy};
use crate::pmem::traits_t::{align_of, size_of};
use super::overflow_v::OverflowableU64;
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

pub proof fn lemma_auto_space_needed_for_alignment_bounded()
    ensures
        forall|addr: int, alignment: int| 0 < alignment ==>
            0 <= #[trigger] space_needed_for_alignment(addr, alignment) < alignment,
{
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

pub open spec fn spec_reserve_specified_space(offset: int, size: int, alignment: int) -> (bounds: (int, int))
    recommends
        0 < alignment,
{
    let start = round_up_to_alignment(offset, alignment);
    let end = start + size;
    (start, end)
}

impl OverflowableU64 {
    #[inline]
    pub exec fn align_u64(&self, alignment: u64) -> (result: Self)
        requires
            0 < alignment,
        ensures
            self@ <= result@,
            result@ < self@ + alignment,
            result@ == round_up_to_alignment(self@ as int, alignment as int),
            is_aligned(result@ as int, alignment as int),
    {
        proof {
            lemma_space_needed_for_alignment_works(self@ as int, alignment as int);
        }

        if self.is_overflowed() {
            Self::new_overflowed(Ghost(round_up_to_alignment(self@ as int, alignment as int)))
        }
        else {
            self.add(get_space_needed_for_alignment(self.unwrap(), alignment))
        }
    }

    #[inline]
    pub exec fn align(&self, alignment: usize) -> (result: Self)
        requires
            0 < alignment,
        ensures
            self@ <= result@,
            result@ < self@ + alignment,
            result@ == round_up_to_alignment(self@ as int, alignment as int),
            is_aligned(result@ as int, alignment as int),
    {
        proof {
            lemma_space_needed_for_alignment_works(self@ as int, alignment as int);
        }

        if self.is_overflowed() {
            Self::new_overflowed(Ghost(round_up_to_alignment(self@ as int, alignment as int)))
        }
        else {
            self.add(get_space_needed_for_alignment_usize(self.unwrap(), alignment) as u64)
        }
    }
}

#[inline]
pub exec fn reserve_space<T>(offset: &OverflowableU64) -> (bounds: (OverflowableU64, OverflowableU64))
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
    let start = offset.align(align_of::<T>());
    let end = start.add(size_of::<T>() as u64);
    (start, end)
}

#[inline]
pub exec fn reserve_specified_space(offset: &OverflowableU64, size: u64, alignment: u64)
                                    -> (bounds: (OverflowableU64, OverflowableU64))
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
    let start = offset.align_u64(alignment);
    let end = start.add(size);
    (start, end)
}

#[inline]
pub exec fn reserve_specified_space_overflowable_u64(offset: &OverflowableU64, size: &OverflowableU64, alignment: u64)
                                                    -> (bounds: (OverflowableU64, OverflowableU64))
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
    let start = offset.align_u64(alignment);
    let end = start.add_overflowable_u64(size);
    (start, end)
}

}
