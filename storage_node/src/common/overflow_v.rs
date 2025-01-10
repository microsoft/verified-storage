use builtin::*;
use builtin_macros::*;
use crate::common::align_v::{get_space_needed_for_alignment, lemma_space_needed_for_alignment_works,
                             is_aligned, round_up_to_alignment};
use crate::pmem::pmcopy_t::{pmcopy_axioms, PmCopy};
use crate::pmem::traits_t::{size_of, align_of};
use vstd::arithmetic::div_mod::{lemma_div_is_ordered_by_denominator, lemma_div_plus_one, lemma_fundamental_div_mod,
                                lemma_mod_division_less_than_divisor};
use vstd::arithmetic::mul::{lemma_mul_by_zero_is_zero, lemma_mul_inequality, lemma_mul_is_commutative};
use vstd::prelude::*;

verus! {

pub struct OverflowingU64 {
    i: Ghost<nat>,
    v: Option<u64>,
}

impl View for OverflowingU64
{
    type V = nat;

    closed spec fn view(&self) -> nat
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
        Self{ i: self.i, v: self.v }
    }
}

impl OverflowingU64 {
    #[verifier::type_invariant]
    spec fn well_formed(self) -> bool
    {
        match self.v {
            Some(v) => self.i@ == v,
            None => self.i@ > u64::MAX,
        }
    }

    pub closed spec fn spec_new(v: u64) -> OverflowingU64
    {
        OverflowingU64{ i: Ghost(v as nat), v: Some(v) }
    }

    #[verifier::when_used_as_spec(spec_new)]
    pub exec fn new(v: u64) -> (result: Self)
        ensures
            result@ == v
    {
        Self{ i: Ghost(v as nat), v: Some(v) }
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
        self.v.is_none()
    }

    pub exec fn unwrap(&self) -> (result: u64)
        requires
            !self.is_overflowed(),
        ensures
            result == self@,
    {
        proof { use_type_invariant(self) }
        self.v.unwrap()
    }

    pub exec fn to_option(&self) -> (result: Option<u64>)
        ensures
            match result {
                Some(v) => self@ == v && v <= u64::MAX,
                None => self@ > u64::MAX,
            }
    {
        proof { use_type_invariant(self); }
        self.v
    }

    #[inline]
    pub exec fn add(&self, v2: u64) -> (result: Self)
        ensures
            result@ == self@ + v2,
    {
        proof {
            use_type_invariant(&self);
        }
        let i: Ghost<nat> = Ghost((&self@ + v2) as nat);
        if self.v.is_none() || v2 > u64::MAX - self.v.unwrap() {
            assert(i@ > u64::MAX);
            Self{ i, v: None }
        }
        else {
            Self{ i, v: Some(self.v.unwrap() + v2) }
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
            result@ == round_up_to_alignment(self@ as int, alignment as int),
            is_aligned(result@ as int, alignment as int),
    {
        proof {
            use_type_invariant(self);
            lemma_space_needed_for_alignment_works(self@ as int, alignment as int);
        }

        match self.v {
            None => Self{
                i: Ghost(round_up_to_alignment(self.i@ as int, alignment as int) as nat),
                v: None,
            },
            Some(v) => {
                let increment_amount = get_space_needed_for_alignment(v, alignment);
                self.add(increment_amount)
            },
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
            use_type_invariant(self);
            lemma_space_needed_for_alignment_works(self@ as int, alignment as int);
        }

        match self.v {
            None => Self{
                i: Ghost(round_up_to_alignment(self.i@ as int, alignment as int) as nat),
                v: None,
            },
            Some(v) => {
                let increment_amount = get_space_needed_for_alignment(v, alignment as u64);
                self.add(increment_amount)
            },
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
        let i: Ghost<nat> = Ghost((self@ + v2@) as nat);
        if self.is_overflowed() || v2.is_overflowed() || self.v.unwrap() > u64::MAX - v2.v.unwrap() {
            assert(i@ > u64::MAX);
            Self{ i, v: None }
        }
        else {
            Self{ i, v: Some(self.v.unwrap() + v2.v.unwrap()) }
        }
    }

    #[inline]
    pub exec fn mul(&self, v2: u64) -> (result: Self)
        ensures
            result@ == self@ as int * v2 as int,
    {
        proof {
            use_type_invariant(self);
        }
        let i: Ghost<nat> = Ghost((self@ * v2) as nat);
        if v2 == 0 {
            assert(i@ == 0) by {
                lemma_mul_by_zero_is_zero(self@ as int);
            }
            Self{ i, v: Some(0) }
        }
        else if self.is_overflowed() {
            assert(self@ * v2 >= self@ * 1 == self@) by {
                lemma_mul_inequality(1, v2 as int, self@ as int);
                lemma_mul_is_commutative(self@ as int, v2 as int);
            }
            Self{ i, v: None }
        }
        else if self.v.unwrap() > u64::MAX / v2 {
            proof {
                assert(self@ >= self.v.unwrap() >= u64::MAX / v2 + 1);
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
                    lemma_mul_inequality((u64::MAX + v2) / (v2 as int), self@ as int, v2 as int);
                }
                assert(self@ * v2 > u64::MAX);
            }
            Self{ i, v: None }
        }
        else {
            proof {
                assert(self.v.unwrap() * v2 <= (u64::MAX / v2) * v2) by {
                    lemma_mul_inequality(self.v.unwrap() as int, u64::MAX as int / v2 as int, v2 as int);
                }
                assert((u64::MAX / v2) * v2 == u64::MAX - u64::MAX % v2) by {
                    lemma_fundamental_div_mod(u64::MAX as int, v2 as int);
                }
                assert((u64::MAX / v2) * v2 <= u64::MAX) by {
                    lemma_mod_division_less_than_divisor(u64::MAX as int, v2 as int);
                }
            }
            Self{ i, v: Some(self.v.unwrap() * v2) }
        }
    }

    #[inline]
    pub exec fn mul_overflowing_u64(&self, v2: &Self) -> (result: Self)
        ensures
            result@ == self@ as int * v2@ as int,
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(v2);
        }
        let i: Ghost<nat> = Ghost(self@ * v2@);
        if v2.is_overflowed() {
            if self.v.is_some() && self.v.unwrap() == 0 {
                assert(i@ == 0) by {
                    lemma_mul_by_zero_is_zero(v2@ as int);
                }
                Self{ i, v: Some(0) }
            }
            else {
                assert(i@ > u64::MAX) by {
                    lemma_mul_inequality(1, self@ as int, v2@ as int);
                }
                Self{ i, v: None }
            }
        }
        else {
            self.mul(v2.v.unwrap())
        }
    }
}

#[inline]
pub exec fn reserve_space<T>(offset: &OverflowingU64) -> (bounds: (OverflowingU64, OverflowingU64))
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
    let end = start.add_usize(size_of::<T>());
    (start, end)
}

#[inline]
pub exec fn reserve_specified_space(offset: &OverflowingU64, size: u64, alignment: u64)
                                    -> (bounds: (OverflowingU64, OverflowingU64))
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
pub exec fn reserve_specified_space_overflowing_u64(offset: &OverflowingU64, size: &OverflowingU64, alignment: u64)
                                                    -> (bounds: (OverflowingU64, OverflowingU64))
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
    let end = start.add_overflowing_u64(size);
    (start, end)
}

}
