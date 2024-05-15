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
    WriteAuthority{ state: PersistentMemoryByte },
    WriteAuthorityComplement{ state: PersistentMemoryByte },
    ReadAuthority{ state: PersistentMemoryByte, num_readers: int },
    ReadAuthorityComplement{ state: PersistentMemoryByte, num_readers: int },
    FullAuthority{ state: PersistentMemoryByte },
    Empty,
    Invalid,
}

impl PCM for PersistentMemoryByteResourceValue {
    open spec fn valid(self) -> bool {
        match self {
            PersistentMemoryByteResourceValue::WriteAuthority{ .. } => true,
            PersistentMemoryByteResourceValue::WriteAuthorityComplement{ .. } => true,
            PersistentMemoryByteResourceValue::ReadAuthority{ num_readers, .. } => num_readers > 0,
            PersistentMemoryByteResourceValue::ReadAuthorityComplement{ num_readers, .. } => num_readers > 0,
            PersistentMemoryByteResourceValue::FullAuthority{ .. } => true,
            PersistentMemoryByteResourceValue::Empty => true,
            PersistentMemoryByteResourceValue::Invalid => false,
        }
    }

    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (PersistentMemoryByteResourceValue::Empty, _) => other,
            (_, PersistentMemoryByteResourceValue::Empty) => self,
            (
                PersistentMemoryByteResourceValue::ReadAuthority{ state: state1, num_readers: num_readers1 },
                PersistentMemoryByteResourceValue::ReadAuthority{ state: state2, num_readers: num_readers2 },
            ) => if state1 == state2 && num_readers1 > 0 && num_readers2 > 0 {
                    PersistentMemoryByteResourceValue::ReadAuthority {
                        state: state1, num_readers: num_readers1 + num_readers2
                    }
                 }
                 else {
                    PersistentMemoryByteResourceValue::Invalid
                 },
            (
                PersistentMemoryByteResourceValue::ReadAuthority{ state: state1, num_readers: num_readers1 },
                PersistentMemoryByteResourceValue::ReadAuthorityComplement{ state: state2, num_readers: num_readers2 },
            ) => if state1 == state2 {
                    if num_readers2 > num_readers1 > 0 {
                        PersistentMemoryByteResourceValue::ReadAuthorityComplement {
                            state: state1, num_readers: num_readers2 - num_readers1
                        }
                    }
                    else if num_readers2 == num_readers1 > 0 {
                        PersistentMemoryByteResourceValue::FullAuthority{ state: state1 }
                    }
                    else {
                        PersistentMemoryByteResourceValue::Invalid
                    }
                 }
                 else {
                    PersistentMemoryByteResourceValue::Invalid
                 },
            (
                PersistentMemoryByteResourceValue::ReadAuthorityComplement{ state: state2, num_readers: num_readers2 },
                PersistentMemoryByteResourceValue::ReadAuthority{ state: state1, num_readers: num_readers1 },
            ) => if state1 == state2 {
                    if num_readers2 > num_readers1 > 0 {
                        PersistentMemoryByteResourceValue::ReadAuthorityComplement {
                            state: state1, num_readers: num_readers2 - num_readers1
                        }
                    }
                    else if num_readers2 == num_readers1 > 0 {
                        PersistentMemoryByteResourceValue::FullAuthority{ state: state1 }
                    }
                    else {
                        PersistentMemoryByteResourceValue::Invalid
                    }
                 }
                 else {
                    PersistentMemoryByteResourceValue::Invalid
                 },
            (
                PersistentMemoryByteResourceValue::WriteAuthority{ state: state1 },
                PersistentMemoryByteResourceValue::WriteAuthorityComplement{ state: state2 },
            ) => if state1 == state2 {
                    PersistentMemoryByteResourceValue::FullAuthority{ state: state1 }
                 }
                 else {
                    PersistentMemoryByteResourceValue::Invalid
                 },
            (
                PersistentMemoryByteResourceValue::WriteAuthorityComplement{ state: state2 },
                PersistentMemoryByteResourceValue::WriteAuthority{ state: state1 },
            ) => if state1 == state2 {
                    PersistentMemoryByteResourceValue::FullAuthority{ state: state1 }
                 }
                 else {
                    PersistentMemoryByteResourceValue::Invalid
                 },
            (_, _) => PersistentMemoryByteResourceValue::Invalid {  },
        }
    }

    open spec fn unit() -> Self {
        Self::Empty
    }

    proof fn closed_under_incl(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }

    proof fn unit_valid() {
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

}
