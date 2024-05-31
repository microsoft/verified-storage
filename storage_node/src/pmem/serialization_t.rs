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
    // TODO: is this enough to prevent someone from creating an
    // S from different data and passing it off as one that was
    // read normally?
    pub open spec fn maybe_corrupted_serialized<S>(
        read_val: S,
        true_val: S,
        start_addr: int
    ) -> bool
        where
            S: Serializable + Sized
    {
        maybe_corrupted(
            read_val.spec_serialize(),
            true_val.spec_serialize(),
            Seq::<int>::new(S::spec_serialized_len() as nat, |i: int| i + start_addr)
        )
    }

    pub open spec fn maybe_corrupted_serialized2<S>(
        read_val: S,
        true_val: S,
        addrs: Seq<int>,
    ) -> bool 
        where
            S: Serializable + Sized,
    {
        maybe_corrupted(
            read_val.spec_serialize(),
            true_val.spec_serialize(),
            addrs
        )
    }

    // TODO: these proofs should live somewhere else
    pub proof fn lemma_serialized_val_uncorrupted2<S>(
        read_val: S,
        true_val: S,
        val_addrs: Seq<int>,
        read_crc: u64,
        true_crc: u64,
        crc_addrs: Seq<int>,
    )
        where
            S: Serializable + Sized,
        requires
            // an impl of `Serializable can override the default impl, so
            // we have to require it here
            read_val.spec_crc() == spec_crc_u64(read_val.spec_serialize()),
            true_val.spec_crc() == spec_crc_u64(true_val.spec_serialize()),
            maybe_corrupted_serialized2(read_val, true_val, val_addrs),
            maybe_corrupted_serialized2(read_crc, true_crc, crc_addrs),
            read_crc == read_val.spec_crc(),
            true_crc == true_val.spec_crc(),
            forall |i: int, j| 0 <= i < crc_addrs.len() && 0 <= j < val_addrs.len() ==> crc_addrs[i] != val_addrs[j],
            all_elements_unique(val_addrs),
            all_elements_unique(crc_addrs),
            spec_serializable_inv::<u64>(),
            spec_serializable_inv::<S>(),
        ensures
            read_val == true_val
    {
        let read_val_bytes = read_val.spec_serialize();
        let true_val_bytes = true_val.spec_serialize();
        let read_crc_bytes = read_crc.spec_serialize();
        let true_crc_bytes = true_crc.spec_serialize();
        assert(true_crc == true_val.spec_crc());
        assert(true_val.spec_crc() == spec_crc_u64(true_val_bytes));
        assert(true_crc == spec_crc_u64(true_val_bytes));

        axiom_bytes_uncorrupted2(read_val_bytes, true_val_bytes, val_addrs,
                read_crc_bytes, true_crc_bytes, crc_addrs);
        assert(read_val_bytes == true_val_bytes);
        assert(S::spec_deserialize(read_val_bytes) == S::spec_deserialize(true_val_bytes));
        assert(S::spec_deserialize(read_val_bytes) == read_val);
        assert(S::spec_deserialize(true_val_bytes) == true_val);
    }

    // TODO: maybe use a specific type for the CDB?
    pub proof fn lemma_corruption_detecting_boolean_serialized2(
        read_cdb: u64,
        true_cdb: u64,
        addrs: Seq<int>,
    )
        requires
            maybe_corrupted_serialized2(read_cdb, true_cdb, addrs),
            read_cdb == CDB_FALSE || read_cdb == CDB_TRUE,
            true_cdb == CDB_FALSE || true_cdb == CDB_TRUE,
            all_elements_unique(addrs),
            spec_serializable_inv::<u64>()
        ensures
            read_cdb == true_cdb
    {
        assume(false); // TODO
        let read_cdb_bytes = read_cdb.spec_serialize();
        let true_cdb_bytes = true_cdb.spec_serialize();
        // lemma_auto_serialize_u64();
        axiom_corruption_detecting_boolean(read_cdb_bytes, true_cdb_bytes, addrs);
    }


    // TODO: remove this, replace with v2?
    pub proof fn lemma_serialized_val_uncorrupted<S>(
        read_val: S,
        true_val: S,
        val_addr: int,
        read_crc: u64,
        true_crc: u64,
        crc_addr: int,
    )
        where
            S: Serializable + Sized,
        requires
            // an impl of `Serializable can override the default impl, so
            // we have to require it here
            read_val.spec_crc() == spec_crc_u64(read_val.spec_serialize()),
            true_val.spec_crc() == spec_crc_u64(true_val.spec_serialize()),
            maybe_corrupted_serialized(read_val, true_val, val_addr),
            maybe_corrupted_serialized(read_crc, true_crc, crc_addr),
            read_crc == read_val.spec_crc(),
            true_crc == true_val.spec_crc(),
            crc_addr < crc_addr + CRC_SIZE <= val_addr || crc_addr >= val_addr + S::spec_serialized_len(),
            forall |s: S| #![auto] s == S::spec_deserialize(s.spec_serialize()),
            forall |bytes: Seq<u8>| #![auto] bytes.len() == S::spec_serialized_len() ==>
                    bytes == S::spec_deserialize(bytes).spec_serialize()
        ensures
            read_val == true_val
    {
        let read_val_bytes = read_val.spec_serialize();
        let true_val_bytes = true_val.spec_serialize();
        let read_crc_bytes = read_crc.spec_serialize();
        let true_crc_bytes = true_crc.spec_serialize();
        let val_addrs = Seq::<int>::new(S::spec_serialized_len() as nat, |i: int| i + val_addr);
        assert(true_crc == true_val.spec_crc());
        assert(true_val.spec_crc() == spec_crc_u64(true_val_bytes));
        assert(true_crc == spec_crc_u64(true_val_bytes));

        axiom_bytes_uncorrupted(read_val_bytes, true_val_bytes, val_addrs,
                                read_crc, true_crc, crc_addr);
        assert(read_val_bytes == true_val_bytes);
        assert(S::spec_deserialize(read_val_bytes) == S::spec_deserialize(true_val_bytes));
        assert(S::spec_deserialize(read_val_bytes) == read_val);
        assert(S::spec_deserialize(true_val_bytes) == true_val);
    }

    // TODO: maybe use a specific type for the CDB?
    pub proof fn lemma_corruption_detecting_boolean_serialized(
        read_cdb: u64,
        true_cdb: u64,
        addr: int,
    )
        requires
            maybe_corrupted_serialized(read_cdb, true_cdb, addr),
            read_cdb == CDB_FALSE || read_cdb == CDB_TRUE,
            true_cdb == CDB_FALSE || true_cdb == CDB_TRUE,
        ensures
            read_cdb == true_cdb
    {
        assume(false);
        let addrs = Seq::<int>::new(u64::spec_serialized_len() as nat, |i: int| i + addr);
        let read_cdb_bytes = read_cdb.spec_serialize();
        let true_cdb_bytes = true_cdb.spec_serialize();
        assert(maybe_corrupted(read_cdb_bytes, true_cdb_bytes, addrs));
        axiom_corruption_detecting_boolean(read_cdb_bytes, true_cdb_bytes, addrs);
    }

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
