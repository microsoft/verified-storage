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
//! Another thing this file models is how bit corruption manifests. It
//! models a persistent memory region as either impervious to
//! corruption or not so. If a memory is impervious to corruption,
//! then bit corruption never occurs and reads always return the
//! last-written bytes. However, if memory isn't impervious to
//! corruption, then all that's guaranteed is that the bytes that are
//! read and the last-written bytes are related by `maybe_corrupted`.
//!
//! This file also provides axioms allowing possibly-corrupted bytes
//! to be freed of suspicion of corruption. Both axioms require the
//! use of CRCs to detect possible corruption, and model a CRC match
//! as showing evidence of an absence of corruption.

use crate::pmem::pmcopy_t::*;
use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use vstd::bytes::*;
use vstd::prelude::*;

use deps_hack::crc64fast::Digest;

verus! {

    // map_err
    #[verifier::external_fn_specification]
    pub fn map_err<T, E, F, O: FnOnce(E) -> F>(result: Result<T, E>, op: O) -> (mapped_result: Result<T, F>)
        requires 
            result.is_err() ==> op.requires((result.get_Err_0(),)), 
        ensures 
            result.is_err() ==> mapped_result.is_err() && op.ensures(
                (result.get_Err_0(),),
                mapped_result.get_Err_0(),
            ),
            result.is_ok() ==> mapped_result == Result::<T, F>::Ok(result.get_Ok_0()),
    {
        result.map_err(op)
    }

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
        let mut buffer_slice = buffer.as_mut_slice();
        buffer_slice.copy_from_slice(bytes);
        buffer
    }

    #[derive(Debug, Eq, PartialEq, Clone)]
    pub enum PmemError {
        InvalidFileName,
        CannotOpenPmFile,
        NotPm,
        PmdkError,
        AccessOutOfRange,
    }

    /// This is our model of bit corruption. It models corruption of a
    /// read byte sequence as a sequence of corruptions happening to
    /// each byte. This way, we can concatenate two read byte
    /// sequences (say, to do a wrapping read) and consider them to be
    /// analogously corrupted. We don't allow arbitrary concatenation
    /// of bytes to prevent proofs from assembling CRC collisions and
    /// thereby proving `false`. Specifically, we only allow byte
    /// sequences to be put together if they all came from different
    /// addresses.

    // A byte `byte` read from address `addr` is a possible corruption
    // of the actual last-written byte `true_byte` to that address if
    // they're related by `maybe_corrupted_byte`.
    pub closed spec fn maybe_corrupted_byte(byte: u8, true_byte: u8, addr: int) -> bool;

    // A sequence of bytes `bytes` read from addresses `addrs` is a
    // possible corruption of the actual last-written bytes
    // `true_bytes` to those addresses if those addresses are all
    // distinct and if each corresponding byte pair is related by
    // `maybe_corrupted_byte`.
    pub open spec fn maybe_corrupted(bytes: Seq<u8>, true_bytes: Seq<u8>, addrs: Seq<int>) -> bool {
        &&& bytes.len() == true_bytes.len() == addrs.len()
        &&& forall |i: int| #![auto] 0 <= i < bytes.len() ==> maybe_corrupted_byte(bytes[i], true_bytes[i], addrs[i])
    }

    // This function indicates that the given bytes were read from
    // storage. If the storage was impervious to corruption, the bytes
    // are the last bytes written. Otherwise, they're a
    // possibly-corrupted version of those bytes.
    pub open spec fn bytes_read_from_storage(
        read_bytes: Seq<u8>,
        true_bytes: Seq<u8>,
        addr: int,
        impervious_to_corruption: bool
    ) -> bool
    {
        if impervious_to_corruption {
            read_bytes == true_bytes
        }
        else {
            let addrs = Seq::<int>::new(true_bytes.len(), |i: int| i + addr);
            maybe_corrupted(read_bytes, true_bytes, addrs)
        }
    }

    pub open spec fn spec_crc_bytes(bytes: Seq<u8>) -> Seq<u8> {
        spec_crc_u64(bytes).spec_to_bytes()
    }

    pub closed spec fn spec_crc_u64(bytes: Seq<u8>) -> u64;

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

    /// We make two assumptions about how CRCs can be used to detect
    /// corruption.

    /// The first assumption, encapsulated in
    /// `axiom_bytes_uncorrupted`, is that if we store byte sequences
    /// `x` and `y` to persistent memory where `y` is the CRC of `x`,
    /// then we can detect an absence of corruption by reading both of
    /// them. Specifically, if we read from those locations and get
    /// `x_c` and `y_c` (corruptions of `x` and `y` respectively), and
    /// `y_c` is the CRC of `x_c`, then we can conclude that `x` wasn't
    /// corrupted, i.e., that `x_c == x`.

    #[verifier(external_body)]
    pub proof fn axiom_bytes_uncorrupted2(x_c: Seq<u8>, x: Seq<u8>, x_addrs: Seq<int>,
                                         y_c: Seq<u8>, y: Seq<u8>, y_addrs: Seq<int>)
        requires
            maybe_corrupted(x_c, x, x_addrs),
            maybe_corrupted(y_c, y, y_addrs),
            y_c == spec_crc_bytes(x_c),
            y == spec_crc_bytes(x),
            x_addrs.no_duplicates(),
            y_addrs.no_duplicates(),
        ensures
            x == x_c
    {}

    #[verifier::external_body]
    #[inline(always)]
    pub exec fn compare_crcs(crc1: &[u8], crc2: u64) -> (out: bool)
        requires 
            crc1@.len() == u64::spec_size_of()
        ensures 
            out ==> crc1@ == crc2.spec_to_bytes(),
            !out ==> crc1@ != crc2.spec_to_bytes()
    {
        let crc1_u64 = u64_from_le_bytes(crc1);
        crc1_u64 == crc2
    }

    /// The second assumption, encapsulated in
    /// `axiom_corruption_detecting_boolean`, is that the values
    /// `CDB_FALSE` and `CDB_TRUE` are so randomly different from each
    /// other that corruption can't make one appear to be the other.
    /// That is, if we know we wrote either `CDB_FALSE` or `CDB_TRUE`
    /// to a certain part of persistent memory, and when we read that
    /// same part we get `CDB_FALSE` or `CDB_TRUE`, we can conclude it
    /// matches what we last wrote to it. To justify the assumption
    /// that `CDB_FALSE` and `CDB_TRUE` are different from each other,
    /// we set them to CRC(b"0") and CRC(b"1"), respectively.

    pub const CDB_FALSE: u64 = 0xa32842d19001605e; // CRC(b"0")
    pub const CDB_TRUE: u64  = 0xab21aa73069531b7; // CRC(b"1")

    #[verifier(external_body)]
    pub proof fn axiom_corruption_detecting_boolean(cdb_c: Seq<u8>, cdb: Seq<u8>, addrs: Seq<int>)
        requires
            maybe_corrupted(cdb_c, cdb, addrs),
            addrs.no_duplicates(),
            cdb.len() == u64::spec_size_of(),
            cdb_c == CDB_FALSE.spec_to_bytes() || cdb_c == CDB_TRUE.spec_to_bytes(),
            cdb == CDB_FALSE.spec_to_bytes() || cdb == CDB_TRUE.spec_to_bytes(),
        ensures
            cdb_c == cdb
    {}

    /// We model the persistent memory as getting flushed in chunks,
    /// where each chunk has `const_persistence_chunk_size()` bytes. We refer
    /// to chunk number `c` as the set of addresses `addr` such that
    /// `addr / const_persistence_chunk_size() == c`.

    pub open spec fn const_persistence_chunk_size() -> int { 8 }

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
    }

    impl PersistentMemoryConstants {
        pub spec fn impervious_to_corruption(self) -> bool;
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
                self@.valid()
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
                                                        self.constants().impervious_to_corruption()),
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
                                                        self.constants().impervious_to_corruption()),
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
