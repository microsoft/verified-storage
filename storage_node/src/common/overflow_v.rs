use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::common::subrange_v::opaque_aligned;
use vstd::arithmetic::div_mod::{lemma_div_is_ordered_by_denominator, lemma_div_plus_one, lemma_fundamental_div_mod,
                                lemma_mod_division_less_than_divisor, lemma_mod_multiples_vanish};
use vstd::arithmetic::mul::{lemma_mul_inequality, lemma_mul_is_commutative};

verus! {

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

pub proof fn lemma_space_needed_for_alignment_works(addr: int, alignment: int)
    requires
        0 < alignment,
    ensures
        space_needed_for_alignment(addr, alignment) >= 0,
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

pub exec fn increment_addr(current_addr: u64, increment_amount: u64, size: u64) -> (result: Option<u64>)
    requires
        0 <= current_addr <= size,
    ensures
        ({
            let new_addr = current_addr + increment_amount;
            match result {
                Some(v) => new_addr <= size && v == new_addr,
                None => new_addr > size,
            }
        })
{
    if current_addr > u64::MAX - increment_amount {
        None
    }
    else {
        let new_addr = current_addr + increment_amount;
        if new_addr <= size {
            Some(new_addr)
        }
        else {
            None
        }
    }
}

pub exec fn align_addr(current_addr: u64, alignment: u64, size: u64) -> (result: Option<u64>)
    requires
        0 <= current_addr <= size,
        0 < alignment,
    ensures
        ({
            let new_addr = round_up_to_alignment(current_addr as int, alignment as int);
            match result {
                Some(v) => {
                    &&& current_addr <= new_addr
                    &&& new_addr <= size
                    &&& v == new_addr
                    &&& opaque_aligned(new_addr as int, alignment as int)
                },
                None => new_addr > size,
            }
        })
{
    let remainder = current_addr % alignment;
    let increment_amount = if remainder == 0 {
        0
    }
    else {
        alignment - remainder
    };
    proof {
        lemma_space_needed_for_alignment_works(current_addr as int, alignment as int);
    }
    increment_addr(current_addr, increment_amount, size)
}

pub exec fn increment_and_align_addr(current_addr: u64, increment_amount: u64, alignment: u64, size: u64)
                                     -> (result: Option<u64>)
    requires
        0 <= current_addr <= size,
        0 < alignment,
    ensures
        ({
            let new_addr = round_up_to_alignment(current_addr + increment_amount, alignment as int);
            match result {
                Some(v) => {
                    &&& current_addr + increment_amount <= new_addr
                    &&& new_addr <= size
                    &&& v == new_addr
                    &&& opaque_aligned(new_addr as int, alignment as int)
                },
                None => new_addr > size,
            }
        })
{
    let new_addr = increment_addr(current_addr, increment_amount, size)?;
    align_addr(new_addr, alignment, size)
}

pub struct SaturatingU64 {
    i: Ghost<int>,
    v: u64,
}

impl View for SaturatingU64
{
    type V = int;

    closed spec fn view(&self) -> int
    {
        self.i@
    }
}

impl Clone for SaturatingU64 {
    exec fn clone(&self) -> (result: Self)
        ensures
            result@ == self@
    {
        proof { use_type_invariant(self); }
        Self{ i: self.i, v: self.v }
    }
}

impl SaturatingU64 {
    #[verifier::type_invariant]
    spec fn well_formed(self) -> bool
    {
        if self.i@ > u64::MAX { self.v == u64::MAX } else { self.v == self.i }
    }

    pub closed spec fn spec_new(v: u64) -> SaturatingU64
    {
        SaturatingU64{ i: Ghost(v as int), v }
    }

    #[verifier::when_used_as_spec(spec_new)]
    pub exec fn new(v: u64) -> (result: Self)
        ensures
            result@ == v
    {
        Self{ i: Ghost(v as int), v }
    }

    pub open spec fn spec_is_saturated(&self) -> bool
    {
        self@ >= u64::MAX
    }

    #[verifier::when_used_as_spec(spec_is_saturated)]
    pub exec fn is_saturated(&self) -> (result: bool)
        ensures
            result == self.spec_is_saturated()
    {
        proof { use_type_invariant(self) }
        self.v == u64::MAX
    }

    pub closed spec fn spec_unwrap(&self) -> u64
    {
        self.v
    }

    #[verifier::when_used_as_spec(spec_unwrap)]
    pub exec fn unwrap(&self) -> (result: u64)
        ensures
            if result < u64::MAX { self@ == result } else { self.is_saturated() },
            result == self.spec_unwrap(),
    {
        proof { use_type_invariant(self) }
        self.v
    }

    pub exec fn to_option(&self) -> (result: Option<u64>)
        ensures
            match result {
                Some(v) => self@ == v && v < u64::MAX,
                None => self@ >= u64::MAX,
            }
    {
        proof { use_type_invariant(self); }
        if self.v == u64::MAX {
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
        if v2 > u64::MAX - self.v {
            Self{ i, v: u64::MAX }
        }
        else {
            Self{ i, v: self.v + v2 }
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
    pub exec fn align(&self, alignment: usize) -> (result: Self)
        requires
            0 < alignment,
        ensures
            self@ <= result@ < self@ + alignment,
            result@ == round_up_to_alignment(self@, alignment as int),
            opaque_aligned(result@, alignment as int),
    {
        proof {
            use_type_invariant(self);
            lemma_space_needed_for_alignment_works(self@, alignment as int);
        }

        if self.v == u64::MAX {
            return Self{
                i: Ghost(round_up_to_alignment(self.i@, alignment as int)),
                v: self.v,
            };
        }

        let alignment = alignment as u64;
        let remainder = self.v % alignment;
        let increment_amount = if remainder == 0 {
            0
        }
        else {
            alignment - remainder
        };
        self.add(increment_amount)
    }

    #[inline]
    pub exec fn add_saturating_u64(&self, v2: &SaturatingU64) -> (result: Self)
        ensures
            result@ == self@ + v2@,
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(v2);
        }
        let i: Ghost<int> = Ghost(self@ + v2@);
        if v2.is_saturated() || self.v > u64::MAX - v2.v {
            Self{ i, v: u64::MAX }
        }
        else {
            Self{ i, v: self.v + v2.v }
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
        if v2 == 0 || self.v == 0 {
            Self{ i, v: 0 }
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
            Self{ i, v: u64::MAX }
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

                // A special case is when we're already saturated at `u64::MAX`.
                // We have to prove that `v2 == 1`. We do this by contradiction.
                if self.v == u64::MAX && v2 != 1 {
                    assert(u64::MAX / 2 < u64::MAX) by (compute_only);
                    lemma_div_is_ordered_by_denominator(u64::MAX as int, 2, v2 as int);
                    assert(false);
                }
            }
            Self{ i, v: self.v * v2 }
        }
    }
}

}
