use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::common::subrange_v::{space_needed_for_alignment, opaque_aligned};

verus! {

pub enum OverflowingU64 {
    Overflow{ i: Ghost<int> },
    Normal{ v: u64 },
}

impl View for OverflowingU64
{
    type V = int;

    open spec fn view(&self) -> int
    {
        match self {
            Self::Overflow{ i } => i@,
            Self::Normal{ v } => v as int,
        }
    }
}

impl OverflowingU64 {
    pub open spec fn unwrap(self) -> u64
        recommends
            self is Normal
    {
        self->v
    }

    pub open spec fn valid(self) -> bool
    {
        match self {
            Self::Overflow{ i } => i@ > u64::MAX,
            Self::Normal{ v } => true,
        }
    }

    pub open spec fn from_int(v: int) -> Self
    {
        if v <= u64::MAX {
            Self::Normal{ v: v as u64 }
        }
        else {
            Self::Overflow{ i: Ghost(v) }
        }
    }

    pub open spec fn spec_add_int(self, v2: int) -> Self
    {
        Self::from_int(self@ + v2)
    }

    pub open spec fn spec_add(self, v2: u64) -> Self
    {
        self.spec_add_int(v2 as int)
    }

    #[inline]
    #[verifier::when_used_as_spec(spec_add)]
    pub exec fn add(self, v2: u64) -> (result: Self)
        requires
            self.valid(),
        ensures
            result.valid(),
            result == self.spec_add(v2),
            result@ == self@ + v2,
    {
        match self {
            Self::Overflow{ i } =>
                Self::Overflow{ i: Ghost((i@ + v2) as int) },
            Self::Normal{ v: v1 } =>
                if v2 > u64::MAX - v1 {
                    Self::Overflow{ i: Ghost((v1 + v2) as int) }
                }
                else {
                    Self::Normal{ v: (v1 + v2) as u64 }
                },
        }
    }

    pub open spec fn spec_add_usize(self, v2: usize) -> Self
    {
        self.spec_add_int(v2 as int)
    }

    #[inline]
    #[verifier::when_used_as_spec(spec_add_usize)]
    pub exec fn add_usize(self, v2: usize) -> (result: Self)
        requires
            self.valid(),
        ensures
            result.valid(),
            result == self.spec_add_usize(v2),
            result@ == self@ + v2,
    {
        self.add(v2 as u64)
    }

    pub open spec fn spec_align(self, alignment: usize) -> Self
        recommends
            0 < alignment
    {
        self.spec_add_int(space_needed_for_alignment(self@, alignment as int))
    }
}

}
