#![verus::trusted]
use crate::pmem::pmemspec_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

use deps_hack::crc64fast::Digest;
use std::convert::TryInto;

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

    #[verifier::external_body]
    pub proof fn axiom_serialized_val_uncorrupted<S>(
        read_val: S,
        true_val: S,
        val_addr: int,
        read_crc: u64,
        true_crc: u64,
        crc_addr: int,
    )
        where
            S: Serializable + Sized
        requires
            maybe_corrupted_serialized(read_val, true_val, val_addr),
            maybe_corrupted_serialized(read_crc, true_crc, crc_addr),
            read_crc == read_val.spec_crc(),
            true_crc == true_val.spec_crc(),
            crc_addr < crc_addr + CRC_SIZE <= val_addr || crc_addr >= val_addr + S::spec_serialized_len()
            // TODO: is this enough to make sure the crc and read val are physically distinct?
        ensures
            read_val == true_val
    {}

    pub trait Serializable : Sized {
        spec fn spec_serialize(self) -> Seq<u8>;

        spec fn spec_deserialize(bytes: Seq<u8>) -> Self;

        // Q: should the sigs of these proof functions be marked proof?
        // $line_count$Proof${$
        proof fn lemma_auto_serialize_deserialize()
            ensures
                forall |s: Self| #![auto] s == Self::spec_deserialize(s.spec_serialize())
        ;

        proof fn lemma_auto_serialized_len()
            ensures
                forall |s: Self| #![auto] s.spec_serialize().len() == Self::spec_serialized_len()
        ;
        // $line_count$}$

        // TODO: this should really be a constant, but verus doesn't
        // support associated constants right now
        spec fn spec_serialized_len() -> u64;

        spec fn spec_crc(self) -> u64;

        fn serialized_len() -> (out: u64)
            ensures
                out == Self::spec_serialized_len()
        ;
    }

    impl Serializable for u64 {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self)
        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self
        {
            spec_u64_from_le_bytes(bytes)
        }

        // $line_count$Proof${$
        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(forall |s: Self| #![auto] s == Self::spec_deserialize(s.spec_serialize()));
        }

        proof fn lemma_auto_serialized_len()
        {
            lemma_auto_spec_u64_to_from_le_bytes(); // $line_count$Proof$
            assert(forall |s: Self| #![auto] s.spec_serialize().len() == 8);  // $line_count$Proof$
            assert(Self::spec_serialized_len() == 8);  // $line_count$Proof$
        }
        // $line_count$}$

        open spec fn spec_serialized_len() -> u64
        {
            8
        }

        closed spec fn spec_crc(self) -> u64;

        fn serialized_len() -> u64
        {
            8
        }
    }

    #[verifier::external_body]
    pub fn calculate_crc<S>(val: &S) -> (out: u64)
        where
            S: Serializable + Sized
        ensures
            val.spec_crc() == out@
    {
        let num_bytes: usize = S::serialized_len().try_into().unwrap();
        let s_pointer = val as *const S;
        let bytes_pointer = s_pointer as *const u8;
        // SAFETY: `bytes_pointer` always points to `num_bytes` consecutive, initialized
        // bytes because it was obtained by casting a regular Rust object reference
        // to a raw pointer.
        let bytes = unsafe {
            std::slice::from_raw_parts(bytes_pointer, num_bytes)
        };

        let mut digest = Digest::new();
        digest.write(bytes);
        digest.sum64()
    }
}
