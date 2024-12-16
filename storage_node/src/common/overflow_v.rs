use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::common::subrange_v::opaque_aligned;

verus! {

pub closed spec fn space_needed_for_alignment(addr: int, alignment: int) -> int
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
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(addr, alignment);
        }
        assert(addr + alignment - remainder == alignment * (addr / alignment) + alignment);
        assert((addr + alignment - remainder) % alignment == alignment % alignment) by {
            vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(addr / alignment, alignment, alignment);
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
            if result < u64::MAX { self@ == result } else { self.is_saturated() }
    {
        proof { use_type_invariant(self) }
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
    pub exec fn add_and_align(&self, v2: u64, alignment: usize) -> (result: Self)
        requires
            0 < alignment,
        ensures
            self@ + v2 <= result@ < self@ + v2 + alignment,
            result@ == round_up_to_alignment(self@ + v2, alignment as int),
            opaque_aligned(result@, alignment as int),
    {
        self.add(v2).align(alignment)
    }
}

}
