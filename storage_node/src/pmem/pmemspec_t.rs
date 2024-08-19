//! This file contains the trusted specification for how a collection
//! of persistent memory regions (implementing trait
//! `PersistentMemoryRegions`) behaves.
//!
//! One of the things it models is what can happen to a persistent
//! memory region if the system crashes in the middle of a write.
//! Specifically, it says that on a crash some subset of the
//! outstanding byte writes will be flushed (performed before the
//! crash) and the rest of the outstanding byte writes will be
//! discarded. Furthermore, any 8-byte-aligned 8-byte chunk either has
//! all its outstanding writes flushed or all of them discarded.
//!
//! To obviate the need to model what happens when there are multiple
//! outstanding writes to the same byte, the specification says that
//! writes are only allowed to bytes that have no outstanding writes.
//! To obviate the need to model what happens when a byte with an
//! outstanding write is read, the specification says that reads (like
//! writes) are only allowed to access bytes that have no outstanding
//! writes.
//!
//! Another thing this file models is how bit corruption manifests. It
//! models a collection of persistent memory regions as either
//! impervious to corruption or not so. If a memory is impervious to
//! corruption, then bit corruption never occurs and reads always
//! return the last-written bytes. However, if memory isn't impervious
//! to corruption, then all that's guaranteed is that the bytes that
//! are read and the last-written bytes are related by
//! `maybe_corrupted`.
//!
//! This file also provides axioms allowing possibly-corrupted bytes
//! to be freed of suspicion of corruption. Both axioms require the
//! use of CRCs to detect possible corruption, and model a CRC match
//! as showing evidence of an absence of corruption.
use crate::pmem::device_t::*;
use crate::pmem::serialization_t::*;
use crate::pmem::timestamp_t::*;
use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use vstd::bytes::*;
use vstd::prelude::*;

use deps_hack::crc64fast::Digest;

verus! {

    #[verus::trusted]
    #[derive(Debug)]
    pub enum PmemError {
        InvalidFileName,
        CannotOpenPmFile,
        NotPm,
        PmdkError,
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
    #[verus::trusted]
    pub closed spec fn maybe_corrupted_byte(byte: u8, true_byte: u8, addr: int) -> bool;

    #[verus::trusted]
    pub open spec fn all_elements_unique(seq: Seq<int>) -> bool {
        forall |i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] != seq[j]
    }

    // A sequence of bytes `bytes` read from addresses `addrs` is a
    // possible corruption of the actual last-written bytes
    // `true_bytes` to those addresses if those addresses are all
    // distinct and if each corresponding byte pair is related by
    // `maybe_corrupted_byte`.
    #[verus::trusted]
    pub open spec fn maybe_corrupted(bytes: Seq<u8>, true_bytes: Seq<u8>, addrs: Seq<int>) -> bool {
        &&& bytes.len() == true_bytes.len() == addrs.len()
        &&& forall |i: int| #![auto] 0 <= i < bytes.len() ==> maybe_corrupted_byte(bytes[i], true_bytes[i], addrs[i])
    }

    #[verus::trusted]
    pub const CRC_SIZE: u64 = 8;

    #[verus::trusted]
    pub closed spec fn spec_crc_bytes(bytes: Seq<u8>) -> Seq<u8>;

    // This executable method can be called to compute the CRC of a
    // sequence of bytes. It uses the `crc` crate.
    #[verus::trusted]
    #[verifier::external_body]
    pub exec fn bytes_crc(bytes: &[u8]) -> (out: Vec<u8>)
        ensures
            spec_crc_bytes(bytes@) == out@,
            out@.len() == CRC_SIZE
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
    #[verus::trusted]
    pub proof fn axiom_bytes_uncorrupted(x_c: Seq<u8>, x: Seq<u8>, x_addrs: Seq<int>,
                                         y_c: Seq<u8>, y: Seq<u8>, y_addrs: Seq<int>)
        requires
            maybe_corrupted(x_c, x, x_addrs),
            maybe_corrupted(y_c, y, y_addrs),
            y == spec_crc_bytes(x),
            y_c == spec_crc_bytes(x_c),
            all_elements_unique(x_addrs),
            all_elements_unique(y_addrs),
        ensures
            x == x_c
    {}

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

    #[verus::trusted]
    pub const CDB_FALSE: u64 = 0xa32842d19001605e; // CRC(b"0")
    #[verus::trusted]
    pub const CDB_TRUE: u64  = 0xab21aa73069531b7; // CRC(b"1")

    #[verus::trusted]
    #[verifier(external_body)]
    pub proof fn axiom_corruption_detecting_boolean(cdb_c: Seq<u8>, cdb: Seq<u8>, addrs: Seq<int>)
        requires
            maybe_corrupted(cdb_c, cdb, addrs),
            all_elements_unique(addrs),
            cdb.len() == 8,
            spec_u64_from_le_bytes(cdb) == CDB_FALSE || spec_u64_from_le_bytes(cdb) == CDB_TRUE,
            spec_u64_from_le_bytes(cdb_c) == CDB_FALSE || spec_u64_from_le_bytes(cdb_c) == CDB_TRUE,
        ensures
            cdb_c == cdb
    {}

    /// We model the persistent memory as getting flushed in chunks,
    /// where each chunk has `PERSISTENCE_CHUNK_SIZE` bytes. We refer
    /// to chunk number `c` as the set of addresses `addr` such that
    /// `addr / PERSISTENCE_CHUNK_SIZE == c`.

    #[verus::trusted]
    pub spec const PERSISTENCE_CHUNK_SIZE: int = 8;

    /// We model the state of each byte of persistent memory as
    /// follows. `state_at_last_flush` contains the contents
    /// immediately after the most recent flush. `outstanding_write`
    /// contains `None` if there's no outstanding write, or `Some(b)`
    /// if there's an outstanding write of `b`. We don't model the
    /// possibility of there being multiple outstanding writes because
    /// we restrict reads and writes to not be allowed at locations
    /// with currently outstanding writes.

    #[verus::trusted]
    #[verifier::ext_equal]
    pub struct PersistentMemoryByte {
        pub state_at_last_flush: u8,
        pub outstanding_write: Option<u8>,
    }

    #[verus::trusted]
    impl PersistentMemoryByte {
        pub open spec fn write(self, byte: u8) -> Self
        {
            Self {
                state_at_last_flush: self.state_at_last_flush,
                outstanding_write: Some(byte),
            }
        }

        pub open spec fn flush_byte(self) -> u8
        {
            match self.outstanding_write {
                None => self.state_at_last_flush,
                Some(b) => b
            }
        }

        pub open spec fn flush(self) -> Self
        {
            Self {
                state_at_last_flush: self.flush_byte(),
                outstanding_write: None,
            }
        }
    }

    /// We model the state of a region of persistent memory as a
    /// `PersistentMemoryRegionView`, which is essentially just a sequence
    /// of `PersistentMemoryByte` values.

    #[verus::trusted]
    #[verifier::ext_equal]
    pub struct PersistentMemoryRegionView
    {
        pub state: Seq<PersistentMemoryByte>,
        pub device_id: u128,
        pub timestamp: PmTimestamp
    }

    #[verus::trusted]
    impl PersistentMemoryRegionView
    {
        pub open spec fn len(self) -> nat
        {
            self.state.len()
        }

        pub open spec fn write(self, addr: int, bytes: Seq<u8>) -> Self
        {
            Self {
                state: self.state.map(|pos: int, pre_byte: PersistentMemoryByte|
                                         if addr <= pos < addr + bytes.len() { pre_byte.write(bytes[pos - addr]) }
                                         else { pre_byte }),
                device_id: self.device_id,
                timestamp: self.timestamp
            }
        }

        pub open spec fn flush(self) -> Self
        {
            Self {
                state: self.state.map(|_addr, b: PersistentMemoryByte| b.flush()),
                device_id: self.device_id,
                timestamp: self.timestamp.inc_timestamp()
            }
        }

        // If the provided timestamp is greater than the current one and has the same device ID,
        // then a flush has been performed on this device but not yet reflected in this region.
        // Flush the ghost state of each byte and update the region's timestamp to record the
        // fact that it has now observed this flush.
        // It doesn't actually matter if there are any outstanding writes in this region, since
        // this operation does not perform a runtime flush.
        pub open spec fn update_region_with_timestamp(self, timestamp: PmTimestamp) -> Self
        {
            if timestamp.gt(self.timestamp) && timestamp.device_id() == self.device_id {
                Self {
                    state: self.state.map(|pos: int, pre_byte: PersistentMemoryByte| pre_byte.flush()),
                    device_id: self.device_id,
                    timestamp
                }
            } else {
                self
            }

        }

        pub open spec fn equal_except_for_timestamps(self, rhs: PersistentMemoryRegionView) -> bool
        {
            self.state =~= rhs.state && self.device_id == rhs.device_id
        }

        pub open spec fn no_outstanding_writes_in_range(self, i: int, j: int) -> bool
        {
            forall |k| i <= k < j ==> (#[trigger] self.state[k].outstanding_write).is_none()
        }

        pub open spec fn no_outstanding_writes(self) -> bool
        {
            Self::no_outstanding_writes_in_range(self, 0, self.state.len() as int)
        }

        pub open spec fn committed(self) -> Seq<u8>
        {
            self.state.map(|_addr, b: PersistentMemoryByte| b.state_at_last_flush)
        }

        // This specification function describes what it means for
        // chunk number `chunk` in `self` to match the corresponding
        // bytes in `bytes` if outstanding writes to those bytes in
        // `self` haven't happened yet.
        pub open spec fn chunk_corresponds_ignoring_outstanding_writes(self, chunk: int, bytes: Seq<u8>) -> bool
        {
            forall |addr: int| {
                &&& 0 <= addr < self.len()
                &&& addr / PERSISTENCE_CHUNK_SIZE == chunk
            } ==> #[trigger] bytes[addr] == self.state[addr].state_at_last_flush
        }

        // This specification function describes what it means for
        // chunk number `chunk` in `self` to match the corresponding
        // bytes in `bytes` if outstanding writes to those bytes in
        // `self` have all been performed.
        pub open spec fn chunk_corresponds_after_flush(self, chunk: int, bytes: Seq<u8>) -> bool
        {
            forall |addr: int| {
                &&& 0 <= addr < self.len()
                &&& addr / PERSISTENCE_CHUNK_SIZE == chunk
            } ==> #[trigger] bytes[addr] == self.state[addr].flush_byte()
        }

        // This specification function describes whether `self` can
        // crash as a sequence of bytes `bytes`. It can do so if, for
        // each chunk, that chunk either matches the corresponding
        // part of `bytes` ignoring outstanding writes to that chunk
        // or matches it after performing outstanding writes to that
        // chunk. In other words, each byte can be flushed or
        // unflushed, but bytes in the same chunk must always make the
        // same flushed/unflushed choice.
        pub open spec fn can_crash_as(self, bytes: Seq<u8>) -> bool
        {
            &&& bytes.len() == self.len()
            &&& forall |chunk| {
                  ||| self.chunk_corresponds_ignoring_outstanding_writes(chunk, bytes)
                  ||| self.chunk_corresponds_after_flush(chunk, bytes)
              }
        }
    }

    /// We model the state of a sequence of regions of persistent
    /// memory as a `PersistentMemoryRegionsView`, which is essentially
    /// just a sequence of `PersistentMemoryRegionView` values.

    #[verus::trusted]
    #[verifier::ext_equal]
    pub struct PersistentMemoryRegionsView {
        pub regions: Seq<PersistentMemoryRegionView>,
        pub timestamp: PmTimestamp,
        pub device_id: u128,
    }

    #[verus::trusted]
    impl PersistentMemoryRegionsView {
        pub open spec fn len(self) -> nat
        {
            self.regions.len()
        }

        pub open spec fn spec_index(self, i: int) -> PersistentMemoryRegionView
        {
            self.regions[i]
        }

        pub open spec fn device_id(&self) -> u128
        {
            self.device_id
        }

        pub open spec fn equal_except_for_timestamps(self, rhs: PersistentMemoryRegionsView) -> bool
        {
            &&& self.device_id == rhs.device_id
            &&& self.len() == rhs.len()
            &&& forall |i: int| #![auto] 0 <= i < self.len() ==> self[i].equal_except_for_timestamps(rhs[i])
        }

        pub open spec fn all_timestamps_match(self) -> bool
        {
            forall |i: int| #![auto] 0 <= i < self.len() ==> self.regions[i].timestamp == self.timestamp
        }

        // We do not update region timestamps during `write` because the timestamp represents
        // the most recent flush observed by each region, and writing does not invoke a flush.
        pub open spec fn write(self, index: int, addr: int, bytes: Seq<u8>) -> Self
        {
            Self {
                regions: self.regions.map(|pos: int, pre_view: PersistentMemoryRegionView|
                    if pos == index {
                        pre_view.write(addr, bytes)
                    } else {
                        pre_view
                    }
                ),
                timestamp: self.timestamp,
                device_id: self.device_id
            }
        }


        pub open spec fn flush(self) -> Self
        {
            Self {
                regions: self.regions.map(|_pos, pm: PersistentMemoryRegionView| pm.flush()),
                device_id: self.device_id,
                timestamp: self.timestamp.inc_timestamp(),
            }
        }

        /// Updates any regions in the view that have a timestamp lower than the given one, as this
        /// indicates that a global store fence has been invoked but not not observed by these
        /// regions.
        pub open spec fn update_regions_with_timestamp(self, timestamp: PmTimestamp) -> Self
        {
            if self.device_id() == timestamp.device_id() {
                Self {
                    regions: self.regions.map(|_pos, pm: PersistentMemoryRegionView| pm.update_region_with_timestamp(timestamp)),
                    timestamp: timestamp,
                    device_id: self.device_id
                }
            } else {
                self
            }

        }

        pub open spec fn no_outstanding_writes(self) -> bool {
            forall |i: int| #![auto] 0 <= i < self.len() ==> self[i].no_outstanding_writes()
        }

        pub open spec fn no_outstanding_writes_in_range(self, index: int, start: int, end: int) -> bool
        {
            self[index].no_outstanding_writes_in_range(start, end)
        }

        pub open spec fn committed(self) -> Seq<Seq<u8>>
        {
            Seq::<Seq<u8>>::new(self.len(), |i: int| self[i].committed())
        }

        pub open spec fn can_crash_as(self, crash_regions: Seq<Seq<u8>>) -> bool
        {
            &&& crash_regions.len() == self.len()
            &&& forall |i: int| #![auto] 0 <= i < self.len() ==> self[i].can_crash_as(crash_regions[i])
        }
    }

    // The struct `PersistentMemoryConstants` contains fields that
    // remain the same across all operations on persistent memory.

    #[verus::trusted]
    pub struct PersistentMemoryConstants {
        pub impervious_to_corruption: bool
    }

    #[verus::trusted]
    pub trait PersistentMemoryRegion : Sized
    {
        type RegionDesc : RegionDescriptor;

        spec fn view(&self) -> PersistentMemoryRegionView;

        spec fn inv(&self) -> bool;

        spec fn spec_device_id(&self) -> u128;

        fn device_id(&self) -> (result: u128)
            requires
                self.inv()
            ensures
                result == self.spec_device_id(),
                result == self@.device_id;

        fn new(region_descriptor: Self::RegionDesc) -> (result: Result<Self, PmemError>)
            ensures
                match result {
                    Ok(pm) => {
                        &&& pm@.len() == region_descriptor@.len
                        &&& pm.inv()
                        &&& pm@.no_outstanding_writes()
                        &&& pm.spec_device_id() == region_descriptor@.device_id
                        &&& pm@.timestamp == region_descriptor@.timestamp
                    },
                    Err(_) => false
                };

        fn get_region_size(&self) -> (result: u64)
            requires
                self.inv()
            ensures
                result == self@.len();

        fn read(&self, addr: u64, num_bytes: u64) -> (bytes: Vec<u8>)
            requires
                self.inv(),
                addr + num_bytes <= self@.len()
            ensures
                bytes@ == self@.committed().subrange(addr as int, addr + num_bytes);

        fn read_and_deserialize<S>(&self, addr: u64) -> (output: &S)
            where
                S: Serializable + Sized
            requires
                self.inv(),
                addr + S::spec_serialized_len() <= self@.len()
            ensures
            ({
                let true_val = S::spec_deserialize(
                    self@.committed().subrange(addr as int, addr + S::spec_serialized_len()));
                output == true_val
            })
        ;

        fn write(&mut self, addr: u64, bytes: &[u8])
            requires
                old(self).inv(),
                addr + bytes@.len() <= old(self)@.len(),
                addr + bytes@.len() <= u64::MAX
            ensures
                self.inv(),
                self@ == self@.write(addr as int, bytes@),
                forall |r: PersistentMemoryRegionsView| r.device_id == self.spec_device_id() ==>
                            r.timestamp == self@.timestamp
                ;


        fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S)
            where
                S: Serializable + Sized
            requires
                old(self).inv(),
                addr + S::spec_serialized_len() <= old(self)@.len(),
            ensures
                ({
                    let written = old(self)@.write(addr as int, to_write.spec_serialize());
                    &&& written == self@
                })
        ;


        fn flush(&mut self)
            requires
                old(self).inv()
            ensures
                self.inv(),
                self@ == old(self)@.flush(),
                self@.device_id == old(self)@.device_id,
                self@.timestamp.value() == old(self)@.timestamp.value() + 1,
                self@.timestamp.device_id() == old(self)@.timestamp.device_id()
                ;

        fn update_region_timestamp(&mut self, new_timestamp: Ghost<PmTimestamp>)
            requires
                old(self).inv(),
                new_timestamp@.gt(old(self)@.timestamp),
                old(self)@.timestamp.device_id() == new_timestamp@.device_id(),
            ensures
                self.inv(),
                self@ == old(self)@.update_region_with_timestamp(new_timestamp@);
    }

    /// The `PersistentMemoryRegions` trait represents an ordered list
    /// of one or more persistent memory regions.

    #[verus::trusted]
    pub trait PersistentMemoryRegions : Sized
    {
        spec fn view(&self) -> PersistentMemoryRegionsView;

        spec fn inv(&self) -> bool;

        spec fn constants(&self) -> PersistentMemoryConstants;

        spec fn spec_device_id(&self) -> u128;

        fn device_id(&self) -> (result: u128)
            ensures
                result == self.spec_device_id(),
                result == self@.device_id;

        fn update_timestamps(&mut self, new_timestamp: Ghost<PmTimestamp>)
            requires
                old(self).inv(),
                new_timestamp@.gt(old(self)@.timestamp),
                new_timestamp@.device_id() == old(self)@.timestamp.device_id()
            ensures
                self.inv(),
                self@.timestamp == new_timestamp,
                self@.equal_except_for_timestamps(old(self)@),
                forall |s| old(self)@.can_crash_as(s) <==> self@.can_crash_as(s);

        fn get_num_regions(&self) -> (result: usize)
            requires
                self.inv()
            ensures
                result == self@.len();

        fn get_region_size(&self, index: usize) -> (result: u64)
            requires
                self.inv(),
                index < self@.len()
            ensures
                result == self@[index as int].len();

        fn read(&self, index: usize, addr: u64, num_bytes: u64) -> (bytes: Vec<u8>)
            requires
                self.inv(),
                index < self@.len(),
                addr + num_bytes <= self@[index as int].len(),
                // Reads aren't permitted where there are still outstanding writes
                self@.no_outstanding_writes_in_range(index as int, addr as int, addr + num_bytes),
            ensures
                ({
                    let true_bytes = self@[index as int].committed().subrange(addr as int, addr + num_bytes);
                    let addrs = Seq::<int>::new(num_bytes as nat, |i: int| i + addr);
                    // If the persistent memory regions are impervious
                    // to corruption, read returns the last bytes
                    // written. Otherwise, it returns a
                    // possibly-corrupted version of those bytes.
                    if self.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    }
                    else {
                        maybe_corrupted(bytes@, true_bytes, addrs)
                    }
                });

        // TODO: should we be able to read more than one S with a single read call?
        // Note that addr is a regular offset in terms of bytes, but the result is of type S
        fn read_and_deserialize<S>(&self, index: usize, addr: u64) -> (output: &S)
            where
                S: Serializable + Sized
            requires
                self.inv(),
                index < self@.len(),
                addr + S::spec_serialized_len() <= self@[index as int].len(),
                self@.no_outstanding_writes_in_range(index as int, addr as int, addr + S::spec_serialized_len()),
                // TODO: should require that we have previously written an S to this address
            ensures
            ({
                let true_val = S::spec_deserialize(
                    self@[index as int].committed().subrange(addr as int, addr + S::spec_serialized_len()));
                let addrs = Seq::<int>::new(S::spec_serialized_len() as nat, |i: int| i + addr);
                if self.constants().impervious_to_corruption {
                    output == true_val
                } else {
                    &&& maybe_corrupted_serialized(*output, true_val, addr as int)
                }
            })
        ;

        // TODO: remove and fully replace with serialize_and_write
        fn write(&mut self, index: usize, addr: u64, bytes: &[u8])
            requires
                old(self).inv(),
                index < old(self)@.len(),
                addr + bytes@.len() <= old(self)@[index as int].len(),
                // Writes aren't allowed where there are already outstanding writes.
                old(self)@.no_outstanding_writes_in_range(index as int, addr as int, addr + bytes@.len()),
            ensures
                self.inv(),
                self.constants() == old(self).constants(),
                ({
                    let written = old(self)@.write(index as int, addr as int, bytes@);
                    &&& self@ == written
                    &&& self@.timestamp == old(self)@.timestamp
                });

        // TODO: should this take a &[S] or just S?
        // We should probably only be able to write an S to this address if we can be sure
        // that we are not partially overwriting another structure? since a subsequent
        // read would make that structure invalid.
        // how to represent that though? need to map addresses to types in spec code...
        // or something similar...
        // Note that addr is a regular offset in terms of bytes, but to_write is type S
        fn serialize_and_write<S>(&mut self, index: usize, addr: u64, to_write: &S)
            where
                S: Serializable + Sized
            requires
                old(self).inv(),
                index < old(self)@.len(),
                addr + S::spec_serialized_len() <= old(self)@[index as int].len(),
                old(self)@.no_outstanding_writes_in_range(index as int, addr as int, addr + S::spec_serialized_len()),
            ensures
                self.inv(),
                self.constants() == old(self).constants(),
                ({
                    let written = old(self)@.write(index as int, addr as int, to_write.spec_serialize());
                    &&& self@ == written
                    &&& self@.timestamp == old(self)@.timestamp
                });


        fn flush(&mut self)
            requires
                old(self).inv(),
            ensures
                self.inv(),
                self.constants() == old(self).constants(),
                ({
                    let flushed = old(self)@.flush();
                    &&& self@ == flushed
                    &&& self@.device_id == old(self)@.device_id
                    &&& self@.all_timestamps_match() // TODO: maybe invariant?
                    &&& self@.timestamp.device_id() == old(self)@.timestamp.device_id()
                }),
                self@.timestamp.value() == old(self)@.timestamp.value() + 1
            ;
    }

    #[verus::trusted]
    pub trait CheckPermission<State>
    {
        spec fn check_permission(&self, state: State) -> bool;
    }
}
