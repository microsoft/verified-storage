//! This file contains the trusted specification for how a persistent
//! memory region (implementing trait `PersistentMemoryRegion`)
//! behaves.
//!
//! One of the things it models is what can happen to a persistent
//! memory region if the system crashes in the middle of a write.
//! Specifically, it says that on a crash some subset of the
//! outstanding byte writes will be flushed (performed before the
//! crash) and the rest of the outstanding byte writes will be
//! discarded. Furthermore, any 8-byte-aligned 8-byte chunk either has
//! all its outstanding writes flushed or all of them discarded.
//!
//! Following Perennial, this model uses prophecy to describe the
//! current state of the persistent memory. The abstract state of the
//! storage consists of a read state, which doesn't use prophecy, and
//! a durable state, which does use prophecy.
//
//! The read state is straightforward: It reflects all writes done so
//! far, regardless of whether those writes have been made durable and
//! will survive a crash. So it reflects what future reads will see,
//! at least until the next crash terminates the Verus program.
//!
//! The durable state represents what state would result if a crash
//! happened now. It forms this representation by predicting, every
//! time a write occurs, which of the bytes in that write will be made
//! durable before the next crash. Of course, this prediction can't be
//! made in reality, but that doesn't stop us from making the
//! prediction in ghost state.
//!
//! The semantics of a flush is that, if you're calling flush right
//! now, the predictor must have predicted that all outstanding
//! written bytes would be flushed to persistent memory before the
//! next crash. So a *precondition* of a flush operation is that the
//! read state matches the durable state.
//!
//! Modeling with an omniscient predictor is naturally unrealistic.
//! But in Perennial, it's been proved that any program correct under
//! the prophecy model is correct under the traditional model of a
//! storage system. So the model is a reasonable and sound one.
//!
//! Another thing this file models is how bit corruption manifests,
//! in terms of a Hamming bound (i.e., total number of bits that could
//! be corrupted on read).

#![cfg_attr(verus_keep_ghost, verus::trusted)]
use crate::pmem::pmcopy_t::*;
use crate::pmem::hamming_t::*;
use core::fmt::Debug;
use vstd::bytes::*;
use vstd::prelude::*;

use crc64fast::Digest;

verus! {

    // This function is used to copy bytes from a slice to a newly-allocated vector.
    // `std::slice::copy_from_slice` requires that the source and destination have the
    // same length, so this function allocates a buffer with the correct length, 
    // obtains a mutable reference to the vector as a slice, and copies the 
    // source bytes in. 
    //
    // This must be implemented in an external_body function because Verus does not
    // support the vec! macro and does not support mutable references.
    #[verifier::external_body]
    pub fn copy_from_slice(bytes: &[u8]) -> (out: Vec<u8>)
        ensures 
            out@ == bytes@
    {
        let mut buffer = vec![0; bytes.len()];
        let buffer_slice = buffer.as_mut_slice();
        buffer_slice.copy_from_slice(bytes);
        buffer
    }

    #[derive(Debug, Eq, PartialEq, Clone, Copy)]
    pub enum PmemError {
        InvalidFileName,
        CannotOpenPmFile,
        NotPm,
        PmdkError,
        AccessOutOfRange,
    }

    // This function indicates that the given bytes were read from
    // storage. If the storage was impervious to corruption, the bytes
    // are the last bytes written. Otherwise, they're a
    // possibly-corrupted version of those bytes.
    pub open spec fn bytes_read_from_storage(
        read_bytes: Seq<u8>,
        true_bytes: Seq<u8>,
        addr: int,
        pmc: PersistentMemoryConstants
    ) -> bool
    {
        let addrs = Seq::<int>::new(true_bytes.len(), |i: int| i + addr);
        pmc.valid() &&
        pmc.maybe_corrupted(read_bytes, true_bytes, addrs)
    }

    pub open spec fn spec_crc_bytes(bytes: Seq<u8>) -> Seq<u8> {
        spec_crc_u64(bytes).spec_to_bytes()
    }

    pub uninterp spec fn spec_crc_u64(bytes: Seq<u8>) -> u64;

    pub open spec fn spec_crc_hamming_bound(len: nat) -> nat {
        // From https://users.ece.cmu.edu/~koopman/crc/crc64.html as one example.
        // For the CRC64-ECMA variant.
        if len <= (32768+7)/8 {
            8
        } else if len <= (32768+7)/8 {
            7
        } else if len <= (126701+7)/8 {
            6
        } else if len <= (126701+7)/8 {
            5
        } else if len <= (8589606850+7)/8 {
            4
        } else if len <= (8589606850+7)/8 {
            3
        } else {
            2
        }
    }

    // This proof function is marked verifier::external_body to assume that the
    // CRC64 function, as captured by spec_crc_bytes(), correctly achieves the
    // Hamming bounds described in spec_crc_hamming_bound.  This is, in principle,
    // provable from the definition of the CRC64 function, but in practice it's
    // messy to prove, so we assume it as an axiom.
    #[verifier::external_body]
    pub proof fn crc_hamming_bound_valid(bytes1: Seq<u8>, bytes2: Seq<u8>, crc1: Seq<u8>, crc2: Seq<u8>)
        requires
            crc1 == spec_crc_bytes(bytes1),
            crc2 == spec_crc_bytes(bytes2),
            (bytes1 + crc1).len() == (bytes2 + crc2).len(),
        ensures
            bytes1 == bytes2 ||
            hamming(bytes1 + crc1, bytes2 + crc2) >= spec_crc_hamming_bound((bytes1 + crc1).len())
    {}

    // This executable method can be called to compute the CRC of a
    // sequence of bytes. It uses the `crc` crate.
    #[verifier::external_body]
    pub exec fn bytes_crc(bytes: &[u8]) -> (out: Vec<u8>)
        ensures
            spec_u64_to_le_bytes(spec_crc_u64(bytes@)) == out@,
            out@.len() == u64::spec_size_of(),
    {
        let mut digest = Digest::new();
        digest.write(bytes);
        u64_to_le_bytes(digest.sum64())
    }

    #[inline(always)]
    pub exec fn compare_crcs(crc1: &[u8], crc2: u64) -> (out: bool)
        requires 
            crc1@.len() == u64::spec_size_of()
        ensures 
            out ==> crc1@ == crc2.spec_to_bytes(),
            !out ==> crc1@ != crc2.spec_to_bytes()
    {
        broadcast use pmcopy_axioms;
        let crc1_u64 = u64_from_le_bytes(crc1);
        if crc1_u64 == crc2 {
            proof {
                axiom_from_bytes_equal::<u64>(crc1@, crc2.spec_to_bytes());
            }
        }
        crc1_u64 == crc2
    }

    pub const CDB_FALSE: u64 = 0xa32842d19001605e; // CRC(b"0")
    pub const CDB_TRUE: u64  = 0xab21aa73069531b7; // CRC(b"1")

    /// We model the persistent memory as getting flushed in chunks,
    /// where each chunk has `const_persistence_chunk_size()` bytes. We refer
    /// to chunk number `c` as the set of addresses `addr` such that
    /// `addr / const_persistence_chunk_size() == c`.

    pub open spec fn const_persistence_chunk_size() -> int { 8 }

    pub exec fn persistence_chunk_size() -> (out: usize)
        ensures 
            out == const_persistence_chunk_size()
    {
        8
    }

    /// We model the state of a region of persistent memory as a
    /// `PersistentMemoryRegionView`, which is two sequences of `u8`.
    /// The first is the latest bytes written, reflecting what will
    /// be read by a `read` operation. The second is the bytes that
    /// will be on persistent memory in the event of a crash,
    /// reflecting a prophecy of which outstanding writes will be
    /// made durable.

    #[verifier::ext_equal]
    pub struct PersistentMemoryRegionView
    {
        pub read_state: Seq<u8>,
        pub durable_state: Seq<u8>,
    }

    pub open spec fn update_bytes(s: Seq<u8>, addr: int, bytes: Seq<u8>) -> Seq<u8>
    {
        Seq::new(s.len(), |i: int| if addr <= i < addr + bytes.len() { bytes[i - addr] } else { s[i] })
    }

    pub open spec fn addr_in_chunk(chunk: int, addr: int) -> bool 
    {
        addr / const_persistence_chunk_size() == chunk
    }

    /// We model writes as prophesizing which bytes will be written,
    /// subject to the constraint that bytes in the same chunk
    /// (aligned on `const_persistence_chunk_size()` boundaries) will
    /// either all be written or have none of them written.

    pub open spec fn chunk_corresponds(s1: Seq<u8>, s2: Seq<u8>, chunk: int) -> bool
    {
        forall |addr: int| {
            &&& 0 <= addr < s1.len()
            &&& addr_in_chunk(chunk, addr)
        } ==> #[trigger] s1[addr] == s2[addr]
    }

    pub open spec fn chunk_trigger(chunk: int) -> bool
    {
        true
    }

    pub open spec fn can_result_from_partial_write(post: Seq<u8>, pre: Seq<u8>, addr: int, bytes: Seq<u8>) -> bool
    {
        &&& post.len() == pre.len()
        &&& forall |chunk| #[trigger] chunk_trigger(chunk) ==> {
              ||| chunk_corresponds(post, pre, chunk)
              ||| chunk_corresponds(post, update_bytes(pre, addr, bytes), chunk)
        }
    }

    impl PersistentMemoryRegionView
    {
        pub open spec fn len(self) -> nat
        {
            self.read_state.len()
        }

        pub open spec fn valid(self) -> bool
        {
            self.read_state.len() == self.durable_state.len()
        }

        pub open spec fn can_result_from_write(self, pre: Self, addr: int, bytes: Seq<u8>) -> bool
        {
            &&& self.read_state == update_bytes(pre.read_state, addr, bytes)
            &&& can_result_from_partial_write(self.durable_state, pre.durable_state, addr, bytes)
        }

        pub open spec fn flush_predicted(self) -> bool
        {
            self.durable_state == self.read_state
        }
    }

    // The struct `PersistentMemoryConstants` contains fields that
    // remain the same across all operations on persistent memory.

    pub struct PersistentMemoryConstants {
        // Mask of corrupted bits on this persistent memory device.
        pub corruption: Seq<u8>,
    }

    impl PersistentMemoryConstants {
        pub open spec fn impervious_to_corruption(self) -> bool {
            popcnt(self.corruption) == 0
        }

        pub open spec fn valid(self) -> bool {
            popcnt(self.corruption) < 2
        }

        pub open spec fn maybe_corrupted_byte(self, byte: u8, true_byte: u8, addr: int) -> bool {
            &&& 0 <= addr < self.corruption.len()
            &&& exists |mask: u8| byte == #[trigger] (true_byte ^ (mask & self.corruption[addr]))
        }

        // A sequence of bytes `bytes` read from addresses `addrs` is a
        // possible corruption of the actual last-written bytes
        // `true_bytes` to those addresses if those addresses are all
        // distinct and if each corresponding byte pair is related by
        // `maybe_corrupted_byte`.
        pub open spec fn maybe_corrupted(self, bytes: Seq<u8>, true_bytes: Seq<u8>, addrs: Seq<int>) -> bool {
            &&& bytes.len() == true_bytes.len() == addrs.len()
            &&& forall |i: int| #![auto] 0 <= i < bytes.len() ==> self.maybe_corrupted_byte(bytes[i], true_bytes[i], addrs[i])
        }
    }

    pub trait PersistentMemoryRegion : Sized
    {
        spec fn view(&self) -> PersistentMemoryRegionView;

        spec fn inv(&self) -> bool;

        spec fn constants(&self) -> PersistentMemoryConstants;

        proof fn lemma_inv_implies_view_valid(&self)
            requires
                self.inv()
            ensures
                self@.valid(),
                self.constants().valid(),
        ;

        fn get_region_size(&self) -> (result: u64)
            requires
                self.inv()
            ensures
                result == self@.len()
        ;

        fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
            where 
                S: PmCopy + Sized,
            requires
                self.inv(),
                addr + S::spec_size_of() <= self@.len(),
                // We must have previously written a serialized S to this addr
                S::bytes_parseable(self@.read_state.subrange(addr as int, addr + S::spec_size_of()))
            ensures
                match bytes {
                    Ok(bytes) => bytes_read_from_storage(bytes@,
                                                        self@.read_state.subrange(addr as int, addr + S::spec_size_of()),
                                                        addr as int,
                                                        self.constants()),
                    _ => false,
                }
            ;

        fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>) 
            requires 
                self.inv(),
                addr + num_bytes <= self@.len(),
            ensures 
                match bytes {
                    Ok(bytes) => bytes_read_from_storage(bytes@,
                                                        self@.read_state.subrange(addr as int, addr + num_bytes as nat),
                                                        addr as int,
                                                        self.constants()),
                    _ => false,
                }
                
        ;

        fn write(&mut self, addr: u64, bytes: &[u8])
            requires
                old(self).inv(),
                addr + bytes@.len() <= old(self)@.len(),
            ensures
                self.inv(),
                self.constants() == old(self).constants(),
                self@.can_result_from_write(old(self)@, addr as int, bytes@),
        ;

        fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S)
            where
                S: PmCopy + Sized
            requires
                old(self).inv(),
                addr + S::spec_size_of() <= old(self)@.len(),
            ensures
                self.inv(),
                self.constants() == old(self).constants(),
                self@.can_result_from_write(old(self)@, addr as int, to_write.spec_to_bytes()),
        ;

        fn flush(&mut self)
            requires
                old(self).inv(),
            ensures
                old(self)@.flush_predicted(), // it must have been prophesized that this flush would happen
                self.inv(),
                self.constants() == old(self).constants(),
                self@ == old(self)@,
        ;
    }

    // This function extracts the subsequence of `bytes` that lie
    // between `pos` and `pos + len` inclusive of `pos` but exclusive
    // of `pos + len`.
    pub open spec fn extract_bytes(bytes: Seq<u8>, pos: nat, len: nat) -> Seq<u8>
    {
        bytes.subrange(pos as int, (pos + len) as int)
    }

}
