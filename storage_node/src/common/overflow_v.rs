use builtin::*;
use builtin_macros::*;
use crate::common::align_v::{get_space_needed_for_alignment, lemma_space_needed_for_alignment_works,
                             opaque_aligned, round_up_to_alignment};
use crate::pmem::pmcopy_t::{pmcopy_axioms, PmCopy};
use crate::pmem::traits_t::{size_of, align_of};
use vstd::arithmetic::div_mod::{lemma_div_is_ordered_by_denominator, lemma_div_plus_one, lemma_fundamental_div_mod,
                                lemma_mod_division_less_than_divisor};
use vstd::arithmetic::mul::{lemma_mul_by_zero_is_zero, lemma_mul_inequality, lemma_mul_is_commutative};
use vstd::prelude::*;

verus! {

pub struct OverflowingU64 {
    i: Ghost<int>,
    v: u64,
    overflowed: bool,
}

impl View for OverflowingU64
{
    type V = int;

    closed spec fn view(&self) -> int
    {
        self.i@
    }
}

impl Clone for OverflowingU64 {
    exec fn clone(&self) -> (result: Self)
        ensures
            result@ == self@
    {
        proof { use_type_invariant(self); }
        Self{ i: self.i, v: self.v, overflowed: self.overflowed }
    }
}

impl OverflowingU64 {
    #[verifier::type_invariant]
    spec fn well_formed(self) -> bool
    {
        if self.i@ > u64::MAX {
            &&& self.v == u64::MAX
            &&& self.overflowed
        } else {
            &&& self.v == self.i
            &&& !self.overflowed
        }
    }

    pub closed spec fn spec_new(v: u64) -> OverflowingU64
    {
        OverflowingU64{ i: Ghost(v as int), v, overflowed: false }
    }

    #[verifier::when_used_as_spec(spec_new)]
    pub exec fn new(v: u64) -> (result: Self)
        ensures
            result@ == v
    {
        Self{ i: Ghost(v as int), v, overflowed: false }
    }

    pub open spec fn spec_is_overflowed(&self) -> bool
    {
        self@ > u64::MAX
    }

    #[verifier::when_used_as_spec(spec_is_overflowed)]
    pub exec fn is_overflowed(&self) -> (result: bool)
        ensures
            result == self.spec_is_overflowed()
    {
        proof { use_type_invariant(self) }
        self.overflowed
    }

    pub exec fn unwrap(&self) -> (result: u64)
        requires
            !self.is_overflowed(),
        ensures
            result == self@,
    {
        proof { use_type_invariant(self) }
        self.v
    }

    pub exec fn to_option(&self) -> (result: Option<u64>)
        ensures
            match result {
                Some(v) => self@ == v && v <= u64::MAX,
                None => self@ > u64::MAX,
            }
    {
        proof { use_type_invariant(self); }
        if self.overflowed {
            None
        }
        else {
            Some(self.v)
        }
    }

    #[inline]
    pub exec fn add(&self, v2: u64) -> (result: Self)
        ensures
            result@ == self@ + v2,
    {
        proof {
            use_type_invariant(&self);
        }
        let i: Ghost<int> = Ghost(&self@ + v2);
        if self.overflowed || v2 > u64::MAX - self.v {
            assert(i@ > u64::MAX);
            Self{ i, v: u64::MAX, overflowed: true }
        }
        else {
            Self{ i, v: self.v + v2, overflowed: false }
        }
    }

    #[inline]
    pub exec fn add_usize(&self, v2: usize) -> (result: Self)
        ensures
            result@ == self@ + v2,
    {
        self.add(v2 as u64)
    }

    #[inline]
    pub exec fn align_u64(&self, alignment: u64) -> (result: Self)
        requires
            0 < alignment,
        ensures
            self@ <= result@,
            result@ < self@ + alignment,
            result@ == round_up_to_alignment(self@, alignment as int),
            opaque_aligned(result@, alignment as int),
    {
        proof {
            use_type_invariant(self);
            lemma_space_needed_for_alignment_works(self@, alignment as int);
        }

        if self.overflowed {
            Self{
                i: Ghost(round_up_to_alignment(self.i@, alignment as int)),
                v: self.v,
                overflowed: true,
            }
        }
        else {
            let increment_amount = get_space_needed_for_alignment(self.v, alignment);
            self.add(increment_amount)
        }
    }

    #[inline]
    pub exec fn align(&self, alignment: usize) -> (result: Self)
        requires
            0 < alignment,
        ensures
            self@ <= result@,
            result@ < self@ + alignment,
            result@ == round_up_to_alignment(self@, alignment as int),
            opaque_aligned(result@, alignment as int),
    {
        proof {
            use_type_invariant(self);
            lemma_space_needed_for_alignment_works(self@, alignment as int);
        }

        if self.overflowed {
            Self{
                i: Ghost(round_up_to_alignment(self.i@, alignment as int)),
                v: self.v,
                overflowed: true,
            }
        }
        else {
            let increment_amount = get_space_needed_for_alignment(self.v, alignment as u64);
            self.add(increment_amount)
        }
    }

    #[inline]
    pub exec fn add_overflowing_u64(&self, v2: &OverflowingU64) -> (result: Self)
        ensures
            result@ == self@ + v2@,
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(v2);
        }
        let i: Ghost<int> = Ghost(self@ + v2@);
        if self.is_overflowed() || v2.is_overflowed() || self.v > u64::MAX - v2.v {
            assert(i@ > u64::MAX);
            Self{ i, v: u64::MAX, overflowed: true }
        }
        else {
            Self{ i, v: self.v + v2.v, overflowed: false }
        }
    }

    #[inline]
    pub exec fn mul(&self, v2: u64) -> (result: Self)
        ensures
            result@ == self@ * v2,
    {
        proof {
            use_type_invariant(self);
        }
        let i: Ghost<int> = Ghost(self@ * v2);
        if v2 == 0 {
            assert(i@ == 0) by {
                lemma_mul_by_zero_is_zero(self@);
            }
            Self{ i, v: 0, overflowed: false }
        }
        else if self.overflowed {
            assert(self@ * v2 >= self@ * 1 == self@) by {
                lemma_mul_inequality(1, v2 as int, self@);
                lemma_mul_is_commutative(self@, v2 as int);
            }
            Self{ i, v: self.v, overflowed: true }
        }
        else if self.v > u64::MAX / v2 {
            proof {
                assert(self@ >= self.v >= u64::MAX / v2 + 1);
                assert(self@ >= (u64::MAX + v2) / v2 as int) by {
                    lemma_div_plus_one(u64::MAX as int, v2 as int);
                }
                assert(v2 * ((u64::MAX + v2) / (v2 as int)) == u64::MAX + v2 - ((u64::MAX + v2) % (v2 as int))) by {
                    lemma_fundamental_div_mod(u64::MAX + v2, v2 as int);
                }
                assert(v2 * ((u64::MAX + v2) / (v2 as int)) > u64::MAX) by {
                    assert(0 <= (u64::MAX + v2) % (v2 as int) < v2) by {
                        lemma_mod_division_less_than_divisor(u64::MAX + v2, v2 as int);
                    }
                }
                assert(self@ * v2 >= ((u64::MAX + v2) / (v2 as int)) * v2) by {
                    lemma_mul_inequality((u64::MAX + v2) / (v2 as int), self@, v2 as int);
                }
                assert(self@ * v2 > u64::MAX);
            }
            Self{ i, v: u64::MAX, overflowed: true }
        }
        else {
            proof {
                assert(self.v * v2 <= (u64::MAX / v2) * v2) by {
                    lemma_mul_inequality(self.v as int, u64::MAX as int / v2 as int, v2 as int);
                }
                assert((u64::MAX / v2) * v2 == u64::MAX - u64::MAX % v2) by {
                    lemma_fundamental_div_mod(u64::MAX as int, v2 as int);
                }
                assert((u64::MAX / v2) * v2 <= u64::MAX) by {
                    lemma_mod_division_less_than_divisor(u64::MAX as int, v2 as int);
                }
            }
            Self{ i, v: self.v * v2, overflowed: false }
        }
    }

    #[inline]
    pub exec fn mul_overflowing_u64(&self, v2: &Self) -> (result: Self)
        ensures
            result@ == self@ * v2@,
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(v2);
        }
        let i: Ghost<int> = Ghost(self@ * v2@);
        if v2.overflowed {
            if self.v == 0 {
                assert(i@ == 0) by {
                    lemma_mul_by_zero_is_zero(v2@);
                }
                Self{ i, v: 0, overflowed: false }
            }
            else {
                assert(i@ > u64::MAX) by {
                    lemma_mul_inequality(1, self@, v2@);
                }
                Self{ i, v: u64::MAX, overflowed: true }
            }
        }
        else {
            self.mul(v2.v)
        }
    }
}

#[inline]
pub exec fn allocate_space<T>(offset: &OverflowingU64) -> (bounds: (OverflowingU64, OverflowingU64))
    where
        T: PmCopy
    requires
        0 < T::spec_align_of(),
    ensures
        ({
            let (start, end) = bounds;
            &&& offset@ <= start@ < offset@ + T::spec_align_of()
            &&& start@ == round_up_to_alignment(offset@, T::spec_align_of() as int)
            &&& opaque_aligned(start@, T::spec_align_of() as int)
            &&& end@ - start@ == T::spec_size_of()
        })
{
    let start = offset.align(align_of::<T>());
    let end = start.add_usize(size_of::<T>());
    (start, end)
}

#[inline]
pub exec fn allocate_specified_space(offset: &OverflowingU64, size: u64, alignment: u64)
                                     -> (bounds: (OverflowingU64, OverflowingU64))
    requires
        0 < alignment,
    ensures
        ({
            let (start, end) = bounds;
            &&& offset@ <= start@ < offset@ + alignment
            &&& start@ == round_up_to_alignment(offset@, alignment as int)
            &&& opaque_aligned(start@, alignment as int)
            &&& end@ - start@ == size
        })
{
    let start = offset.align_u64(alignment);
    let end = start.add(size);
    (start, end)
}

#[inline]
pub exec fn allocate_specified_space_overflowing_u64(offset: &OverflowingU64, size: &OverflowingU64, alignment: u64)
                                                     -> (bounds: (OverflowingU64, OverflowingU64))
    requires
        0 < alignment,
    ensures
        ({
            let (start, end) = bounds;
            &&& offset@ <= start@ < offset@ + alignment
            &&& start@ == round_up_to_alignment(offset@, alignment as int)
            &&& opaque_aligned(start@, alignment as int)
            &&& end@ - start@ == size@
        })
{
    let start = offset.align_u64(alignment);
    let end = start.add_overflowing_u64(size);
    (start, end)
}

}
