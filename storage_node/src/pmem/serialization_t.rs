use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;

use deps_hack::zerocopy::transmute;

verus! {
    pub trait Serializable : Sized {
        spec fn spec_serialize(&self) -> Seq<u8>;

        // TODO: this should really be a constant, but verus doesn't
        // support associated constants right now
        spec fn spec_serialized_len() -> u64;

        fn serialized_len() -> (out: u64)
            ensures
                out == Self::spec_serialized_len()
        ;

        // // TODO: think about how to represent the destination
        // fn serialize(&self, destination: &mut [u8])
        //     requires
        //         old(destination)@.len() == Self::spec_serialized_len()
        //     ensures
        //         destination@ =~= self.spec_serialize(),
        // ;

        // fn deserialize(source: &[u8]) -> (result: Self)
        //     requires
        //         source@.len() == Self::spec_serialized_len()
        //     ensures
        //         result == Self::spec_deserialize(source@)
        // ;

        spec fn spec_deserialize(bytes: Seq<u8>) -> Self;

        // NOTE: this is NOT a view method and should only be used to
        // initially set up the ghost state for a PersistentMemoryRegion.
        // TODO: express that more clearly? Enforce it somehow?
        spec fn view_as_pm_bytes(&self) -> Seq<PersistentMemoryByte>;
    }

    pub open spec fn view_serializable_seq_as_pm_bytes<S>(serializable_seq: Seq<S>) -> Seq<PersistentMemoryByte>
        where
            S: Serializable
        decreases
            serializable_seq.len()
    {
        if serializable_seq.len() == 0 {
            Seq::empty()
        } else {
            serializable_seq[0].view_as_pm_bytes() +
                view_serializable_seq_as_pm_bytes(serializable_seq.subrange(1, serializable_seq.len() as int))
        }
    }

    // NOTE: verus has trouble proving termination when this is used in postconditions.
    // Might be better to take it out entirely...
    pub open spec fn view_serializable_seq_as_bytes<S>(serializable_seq: Seq<S>) -> Seq<u8>
        where
            S: Serializable
        decreases
            serializable_seq.len()
    {
        if serializable_seq.len() == 0 {
            Seq::empty()
        } else {
            serializable_seq[0].spec_serialize() +
                view_serializable_seq_as_bytes(serializable_seq.subrange(1, serializable_seq.len() as int))
        }
    }

    // implementations of serialization for some basic types
    impl Serializable for u64 {
        closed spec fn spec_serialize(&self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(*self)
        }

        // TODO: this should really be a constant, but verus doesn't
        // support associated constants right now
        closed spec fn spec_serialized_len() -> u64
        {
            8
        }

        fn serialized_len() -> (out: u64)
        {
            8
        }

        // // TODO: think about how to represent the destination
        // fn serialize(&self, destination: &mut [u8])
        //     // requires
        //     //     old(destination)@.len() == Self::spec_serialized_len()
        //     // ensures
        //     //     destination@ =~= self.spec_serialize(),
        // {
        //     // transmute!() casts the u64 to an array of bytes in-place
        //     // then we copy it to PM
        //     let bytes: [u8; 8] = transmute!(*self);
        //     destination.copy_from_slice(&bytes);
        // }

        // fn deserialize(source: &[u8]) -> Self
        // {
        //     // let val: u64 = transmute!(source);
        //     // val
        // }

        closed spec fn spec_deserialize(bytes: Seq<u8>) -> Self
        {
            spec_u64_from_le_bytes(bytes)
        }

        // NOTE: this is NOT a view method and should only be used to
        // initially set up the ghost state for a PersistentMemoryRegion.
        // TODO: express that more clearly? Enforce it somehow?
        closed spec fn view_as_pm_bytes(&self) -> Seq<PersistentMemoryByte>;
    }
}
