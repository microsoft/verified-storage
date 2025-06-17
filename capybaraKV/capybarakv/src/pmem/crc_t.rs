// This file defines the `CrcDigest` structure, which provides functionality for computing
// CRC64 checksums over sequences of bytes or `PmCopy` objects. It integrates with the
// `crc64fast` crate for efficient CRC computation while maintaining ghost state for
// verification purposes using Verus.
//
// This file is in the trusted computing base (hence the `_t.rs` extension) because
// it relies on the unverified `crc64fast` crate and makes assumptions about its behavior.
// As such, it needs to be audited manually to have confidence in its correctness.

#![cfg_attr(verus_keep_ghost, verus::trusted)]
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

use deps_hack::crc64fast::Digest;

verus! {

    // Helper struct to hide the external crc64fast Digest type
    // from Verus while still keeping ghost state associated with it
    #[verifier::external_body]
    struct ExternalDigest
    {
        digest: Digest
    }

    // A structure for obtaining CRCs of byte sequences and/or
    // PmCopy objects and writing proofs about them.
    pub struct CrcDigest
    {
        digest: ExternalDigest,
        bytes_in_digest: Ghost<Seq<u8>>,
    }

    impl CrcDigest
    {
        // The ghost state that tracks the bytes that have been digested so far.
        pub closed spec fn bytes_in_digest(self) -> Seq<u8>
        {
            self.bytes_in_digest@
        }

        // Creates a new `CrcDigest` object with an empty digest.
        #[verifier::external_body]
        pub fn new() -> (output: Self)
            ensures
                output.bytes_in_digest() == Seq::<u8>::empty()
,
        {
            Self {
                digest: ExternalDigest{ digest: Digest::new() },
                bytes_in_digest: Ghost(Seq::<u8>::empty())
            }
        }

        // Writes a `PmCopy` object to the digest and updates the ghost state
        // accordingly.
        #[verifier::external_body]
        pub fn write<S>(&mut self, val: &S)
            where
                S: PmCopy,
            ensures
                self.bytes_in_digest() == old(self).bytes_in_digest() + val.spec_to_bytes(),
        {
            // Cast `val` to bytes, then add them to the digest.
            // The crc64fast crate that we use computes the CRC iteratively and does
            // not store copies of the bytes we write to the digest, so this
            // will (hopefully) not incur any copying beyond what is directly
            // necessary to compute the CRC.
            let num_bytes: usize = S::size_of().try_into().unwrap();
            let s_pointer = val as *const S;
            let bytes_pointer = s_pointer as *const u8;
            // SAFETY: `bytes_pointer` always points to `num_bytes` consecutive, initialized
            // bytes because it was obtained by casting a regular Rust object reference
            // to a raw pointer.
            let bytes = unsafe {
                std::slice::from_raw_parts(bytes_pointer, num_bytes)
            };
            self.digest.digest.write(bytes);
        }

        // Writes a slice of bytes to the digest and updates the ghost state
        // accordingly.
        #[verifier::external_body]
        pub fn write_bytes(&mut self, val: &[u8])
            ensures 
                self.bytes_in_digest() == old(self).bytes_in_digest() + val@,
        {
            self.digest.digest.write(val);
        }

        // Computes and returns the CRC for the sequence of bytes in the digest.
        #[verifier::external_body]
        pub fn sum64(&self) -> (output: u64)
            ensures
                output == spec_crc_u64(self.bytes_in_digest()),
                output.spec_to_bytes() == spec_crc_bytes(self.bytes_in_digest()),

        {
            self.digest.digest.sum64()
        }
    }
}
