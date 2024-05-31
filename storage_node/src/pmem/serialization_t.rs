use crate::pmem::pmemspec_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes;
use vstd::bytes::*;
use vstd::prelude::*;
use vstd::ptr::*;
use vstd::layout::*;
use crate::pmem::markers_t::PmSafe;

use deps_hack::crc64fast::Digest;
use core::slice;
use std::convert::TryInto;
use std::ptr;
use std::mem::MaybeUninit;

verus! {
    // Objects can only be written to PM if they derive PmSafe
    pub trait Serializable : Sized + PmSafe + Copy {}

    pub trait SerializableHelper : Serializable {
        spec fn spec_serialize(self) -> Seq<u8>;

        spec fn spec_deserialize(bytes: Seq<u8>) -> Self;

        spec fn spec_serialized_len() -> nat;

        spec fn spec_crc(self) -> u64;

        exec fn serialized_len() -> (out: u64)
            ensures 
                out == Self::spec_serialized_len() as u64;

        exec fn deserialize_bytes(bytes: &[u8]) -> (out: Self) 
            where 
                Self: Sized, // Verus requires this even though it's already a bound on Serializable
            requires 
                bytes@.len() == Self::spec_serialized_len()
            ensures 
                out == Self::spec_deserialize(bytes@),
                out == Self::spec_deserialize(out.spec_serialize()),
                out.spec_crc() == spec_crc_u64(out.spec_serialize()),
                out.spec_serialize().len() == Self::spec_serialized_len(),
                forall |s: Self| #![auto] s == Self::spec_deserialize(s.spec_serialize()),
                forall |bytes: Seq<u8>, s: Self| bytes == s.spec_serialize() ==> 
                    s == Self::spec_deserialize(bytes);

        exec fn serialize_in_place(&self) -> (out: &[u8])
            ensures 
                out@ == self.spec_serialize();
    }

    impl<T> SerializableHelper for T where T: Serializable {
        closed spec fn spec_serialize(self) -> Seq<u8>;

        closed spec fn spec_deserialize(bytes: Seq<u8>) -> Self;

        closed spec fn spec_serialized_len() -> nat {
            size_of_as_usize::<Self>() as nat
        }

        open spec fn spec_crc(self) -> u64 {
            spec_crc_u64(self.spec_serialize())
        }

        #[verifier::external_body]
        fn serialized_len() -> u64
        {
            core::mem::size_of::<Self>() as u64
        }

        // This method returns an owned copy of the deserialized bytes in DRAM
        #[verifier::external_body]
        exec fn deserialize_bytes(bytes: &[u8]) -> (out: Self)  
        {
            let ptr = bytes.as_ptr() as *const Self;
            unsafe { *ptr }
        }

        #[verifier::external_body]
        exec fn serialize_in_place(&self) -> (out: &[u8])
        {
            let ptr = self as *const Self;
            unsafe { core::slice::from_raw_parts(ptr as *const u8, Self::serialized_len() as usize) }
        }
    }

    // This should be true for every Serializable type, but making it default does not automatically
    // make it true for all implementors and we can't put it in pre/postconditions of Serializable
    // methods due to cycle checking.
    pub open spec fn spec_serializable_inv<S: Serializable>() -> bool 
    {
        &&& forall |s: S| {
                &&& #[trigger] s.spec_serialize().len() == S::spec_serialized_len()
                &&& #[trigger] s.spec_crc() == #[trigger] spec_crc_u64(s.spec_serialize())
                &&& s == #[trigger] S::spec_deserialize(s.spec_serialize())
            }
        &&& forall |bytes: Seq<u8>, s: S| bytes == s.spec_serialize() ==> s == S::spec_deserialize(bytes)        
    }

    impl Serializable for u64 {}


    // is this name confusing?
    #[verifier::external_body]
    #[verifier::reject_recursive_types(S)]
    pub struct MaybeCorrupted<S>
        where 
            S: Serializable
    {
        val: MaybeUninit<S>,
    }

    impl<S> MaybeCorrupted<S>
        where 
            S: Serializable 
    {
        // The constructor doesn't have a postcondition because we do not know anything about 
        // the state of the bytes yet
        #[verifier::external_body]
        pub exec fn new() -> (out: Self)
        {
            MaybeCorrupted { 
                val: MaybeUninit::uninit()
            }
        }
        pub closed spec fn view(self) -> Seq<u8>;

        #[verifier::external_body]
        pub exec fn copy_from_slice(
            &mut self, 
            bytes: &[u8], 
            Ghost(true_val): Ghost<S>,
            Ghost(addrs): Ghost<Seq<int>>,
            Ghost(impervious_to_corruption): Ghost<bool>
        )
            requires 
                if impervious_to_corruption {
                    bytes@ == true_val.spec_serialize()
                } else {
                    maybe_corrupted(bytes@, true_val.spec_serialize(), addrs)
                },
                bytes@.len() == S::spec_serialized_len(),
            ensures 
                self@ == bytes@
        {
            self.copy_from_slice_helper(bytes, Ghost(true_val), Ghost(addrs), Ghost(impervious_to_corruption));
        }

        // TODO: remove this helper function and move its body back into `copy_from_slice` once 
        // https://github.com/verus-lang/verus/issues/1151 is fixed
        #[verifier::external]
        #[inline(always)]
        fn copy_from_slice_helper(
            &mut self, 
            bytes: &[u8], 
            Ghost(true_val): Ghost<S>,
            Ghost(addrs): Ghost<Seq<int>>,
            Ghost(impervious_to_corruption): Ghost<bool>
        ) 
        {
            // convert the MaybeUninit<S> to a mutable slice of `MaybeUninit<u8>`
            let mut self_bytes = self.val.as_bytes_mut();
            // copy bytes from the given slice to the mutable slice of `MaybeUninit<u8>`.
            // This returns a slice of initialized bytes, but it does NOT change the fact that 
            // the original S is still MaybeUninit
            // TODO: in newer versions of Rust, write_slice is renamed to copy_from_slice
            MaybeUninit::write_slice(self_bytes, bytes);
        }


        #[verifier::external_body]
        pub exec fn as_slice(&self) -> (out: &[u8])
            ensures 
                out@ == self@
        {
            let bytes = self.val.as_bytes();
            // SAFETY: even if we haven't initialized the bytes, there are no invalid values of u8, so we can 
            // safely assume that these bytes are initialized (even if the S may not be)
            unsafe { MaybeUninit::slice_assume_init_ref(bytes) }
        }

        #[verifier::external_body]
        pub exec fn assume_init(self, Ghost(true_val): Ghost<S>) -> (out: S)
            requires 
                self@ == true_val.spec_serialize()
            ensures 
                out == true_val
        {
            // SAFETY: The precondition establishes that self@ -- the ghost view of the maybe-corrupted bytes
            // written to self.val -- are equivalent to the serialization of the true value; i.e., we must have 
            // proven that the bytes are not corrupted, and therefore self.val is initialized.
            unsafe { self.val.assume_init() }
        }
    }

    // Right now unaligned reads return vecs and Verus can't easily switch between Vec/slice,
    // so we use a separate spec fn to specify that a vector lives in volatile memory (even
    // though that should always be the case anyway)
    // TODO: is this actually necessary?
    pub closed spec fn vec_is_volatile(bytes: Vec<u8>) -> bool;
}
