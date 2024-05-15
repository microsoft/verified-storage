use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::invariant::*;
use vstd::pcm::*;
use vstd::pcm_lib::*;
use vstd::prelude::*;

verus! {

pub enum PersistentMemoryByteResourceValue {
    HalfAuthority{ state: PersistentMemoryByte },
    FullAuthority{ state: PersistentMemoryByte },
    Empty,
    Invalid,
}

impl PersistentMemoryByteResourceValue {
    pub open spec fn valid(self) -> bool {
        !(self is Invalid)
    }

    pub open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (PersistentMemoryByteResourceValue::Empty, _) => other,
            (_, PersistentMemoryByteResourceValue::Empty) => self,
            (
                PersistentMemoryByteResourceValue::HalfAuthority{ state: state1 },
                PersistentMemoryByteResourceValue::HalfAuthority{ state: state2 },
            ) => if state1 == state2 {
                    PersistentMemoryByteResourceValue::FullAuthority { state: state1 }
                 }
                 else {
                    PersistentMemoryByteResourceValue::Invalid
                 }
            (_, _) => PersistentMemoryByteResourceValue::Invalid {  },
        }
    }
}

#[verifier::ext_equal]
pub struct PersistentMemoryResourceValue {
    pub m: spec_fn(int) -> PersistentMemoryByteResourceValue,
}

impl PCM for PersistentMemoryResourceValue {
    open spec fn valid(self) -> bool {
        forall |i| (#[trigger] (self.m)(i)).valid()
    }

    open spec fn op(self, other: Self) -> Self {
        Self{ m: |i| PersistentMemoryByteResourceValue::op((self.m)(i), (other.m)(i)) }
    }

    open spec fn unit() -> Self {
        Self{ m: |i| PersistentMemoryByteResourceValue::Empty }
    }

    proof fn closed_under_incl(a: Self, b: Self) {
        let ab = Self::op(a, b);
        assert forall |i| (#[trigger] (a.m)(i)).valid() by {
            assert((ab.m)(i).valid());
        }
    }

    proof fn commutative(a: Self, b: Self) {
        assert(Self::op(a, b) =~= Self::op(b, a));
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        assert(Self::op(Self::op(a, b), c) =~= Self::op(a, Self::op(b, c)));
    }

    proof fn op_unit(a: Self) {
        let au = Self::op(a, Self::unit());
        assert(au =~= a);
    }

    proof fn unit_valid() {
    }
}

pub struct PersistentMemoryRegionInvariantConstants
{
    pub loc: Loc,
    pub size: usize,
}

pub struct PersistentMemoryRegionInvariantState
{
    pub perm: PersistentMemoryPermission,
    pub authority: Resource<PersistentMemoryResourceValue>,
}

pub struct PersistentMemoryRegionInvariantPredicate { }
impl InvariantPredicate<PersistentMemoryRegionInvariantConstants, PersistentMemoryRegionInvariantState>
        for PersistentMemoryRegionInvariantPredicate {
    open spec fn inv(c: PersistentMemoryRegionInvariantConstants, s: PersistentMemoryRegionInvariantState)
                     -> bool {
        &&& s.authority.loc() == c.loc
        &&& s.perm@.len() == c.size
        &&& forall |i| 0 <= i < c.size ==>
            #[trigger] (s.authority.value().m)(i) ==
            PersistentMemoryByteResourceValue::HalfAuthority{ state: s.perm@.state[i] }
    }
}

pub struct PersistentMemorySubregion
{
    pub start_pos: int,
    pub end_pos: int,
    pub authority: Resource<PersistentMemoryResourceValue>,
}

impl PersistentMemorySubregion
{
    pub open spec fn valid(self) -> bool
    {
    }
}

}
