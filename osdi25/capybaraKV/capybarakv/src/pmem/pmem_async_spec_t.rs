//! This file contains a specification for how a persistent memory region
//! (implementing trait `AsyncPersistentMemoryRegion`) behaves.  This spec
//! differs from the one in `pmemspec_t.rs` in that this specification
//! explicitly models outstanding writes, instead of modeling them using
//! a prophecy specification.
//!
//! Formalizing this specification allows us to prove a correspondence
//! between the prophecy specification in `pmemspec_t.rs` and the explicit
//! asynchronous spec in this file.

#![cfg_attr(verus_keep_ghost, verus::trusted)]
use super::pmcopy_t::*;
use super::pmemspec_t::*;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {

    #[verifier::ext_equal]
    pub struct Write {
        pub addr: int,
        pub data: Seq<u8>,
    }

    pub open spec fn apply_write(s: Seq<u8>, w: Write) -> Seq<u8> {
        update_bytes(s, w.addr, w.data)
    }

    pub open spec fn apply_write_selective(s: Seq<u8>, w: Write, selected_chunks: Seq<bool>) -> Seq<u8>
        recommends
            selected_chunks.len() == size_to_chunks(s.len() as int),
    {
        Seq::new(s.len(), |i: int|
            if w.addr <= i < w.addr + w.data.len() && selected_chunks[addr_to_chunk(i)] {
                w.data[i-w.addr]
            } else {
                s[i]
            })
    }

    pub open spec fn addr_to_chunk(addr: int) -> int {
        addr / const_persistence_chunk_size()
    }

    pub open spec fn size_to_chunks(sz: int) -> int {
        (sz + const_persistence_chunk_size() - 1) / const_persistence_chunk_size()
    }

    #[verifier::ext_equal]
    pub struct PersistentMemoryRegionAsyncView {
        pub state_at_last_flush: Seq<u8>,
        pub outstanding_writes: Seq<Write>,
    }

    impl PersistentMemoryRegionAsyncView
    {
        pub open spec fn len(self) -> nat
        {
            self.state_at_last_flush.len()
        }

        pub open spec fn valid(self) -> bool
        {
            forall |i| 0 <= i < self.outstanding_writes.len() ==> {
                &&& 0 <= #[trigger] self.outstanding_writes[i].addr
                &&& self.outstanding_writes[i].addr + self.outstanding_writes[i].data.len() <= self.state_at_last_flush.len()
            }
        }

        pub open spec fn write(self, addr: int, bytes: Seq<u8>) -> Self
        {
            Self {
                state_at_last_flush: self.state_at_last_flush,
                outstanding_writes: self.outstanding_writes.push(Write{
                    addr: addr,
                    data: bytes,
                }),
            }
        }

        pub open spec fn flush(self) -> Self
            decreases
                self.outstanding_writes.len()
        {
            if self.outstanding_writes.len() == 0 {
                self
            } else {
                let w = self.outstanding_writes.first();
                Self{
                    state_at_last_flush: apply_write(self.state_at_last_flush, w),
                    outstanding_writes: self.outstanding_writes.skip(1),
                }.flush()
            }
        }

        pub open spec fn flush_selective(self, write_chunk_durability: Seq<Seq<bool>>) -> Seq<u8>
            recommends
                self.outstanding_writes.len() == write_chunk_durability.len(),
            decreases
                self.outstanding_writes.len()
        {
            if self.outstanding_writes.len() == 0 {
                self.state_at_last_flush
            } else {
                let w0 = self.outstanding_writes.first();
                let d0 = write_chunk_durability.first();
                Self{
                    state_at_last_flush: apply_write_selective(self.state_at_last_flush, w0, d0),
                    outstanding_writes: self.outstanding_writes.skip(1),
                }.flush_selective(write_chunk_durability.skip(1))
            }
        }

        pub open spec fn committed(self) -> Seq<u8>
        {
            self.state_at_last_flush
        }

        pub open spec fn readable(self) -> Seq<u8>
        {
            self.flush().committed()
        }

        pub open spec fn no_outstanding_writes(self) -> bool
        {
            self.outstanding_writes.len() == 0
        }

        // This specification function describes whether `self` can
        // crash as a sequence of bytes `bytes`, with a certain set
        // of chunks being made durable for each outstanding write.
        // Importantly, all of the bytes written to a chunk as part
        // of a single write are atomic with respect to a crash.
        pub open spec fn can_crash_as(self, bytes: Seq<u8>, write_chunk_durability: Seq<Seq<bool>>) -> bool
            recommends
                write_chunk_durability.len() == self.outstanding_writes.len()
        {
            &&& bytes.len() == self.len()
            &&& write_chunk_durability.len() == self.outstanding_writes.len()
            &&& forall |j| 0 <= j < write_chunk_durability.len() ==> #[trigger] write_chunk_durability[j].len() == size_to_chunks(self.len() as int)
            &&& bytes == self.flush_selective(write_chunk_durability)
        }
    }

    pub trait PersistentMemoryRegionAsync : Sized
    {
        spec fn view(&self) -> PersistentMemoryRegionAsyncView;

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
                S::bytes_parseable(self@.readable().subrange(addr as int, addr + S::spec_size_of()))
            ensures
                match bytes {
                    Ok(bytes) => bytes_read_from_storage(bytes@,
                                                         self@.readable().subrange(addr as int, addr + S::spec_size_of()),
                                                         addr as int,
                                                         self.constants()),
                    _ => false
                }
            ;

        fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>) 
            requires 
                self.inv(),
                addr + num_bytes <= self@.len(),
            ensures 
                match bytes {
                    Ok(bytes) => bytes_read_from_storage(bytes@,
                                                         self@.readable().subrange(addr as int, addr + num_bytes as nat),
                                                         addr as int,
                                                         self.constants()),
                    _ => false
                }
                
        ;

        fn write(&mut self, addr: u64, bytes: &[u8])
            requires
                old(self).inv(),
                addr + bytes@.len() <= old(self)@.len(),
            ensures
                self.inv(),
                self.constants() == old(self).constants(),
                self@ == old(self)@.write(addr as int, bytes@),
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
                self@ == old(self)@.write(addr as int, to_write.spec_to_bytes()),
                self@.flush().committed().subrange(addr as int, addr + S::spec_size_of()) == to_write.spec_to_bytes(),
                // if we serialize and write an S to this address, we expect to be able to get it back
                S::bytes_parseable(self@.flush().committed().subrange(addr as int, addr + S::spec_size_of())), 
        ;

        fn flush(&mut self)
            requires
                old(self).inv()
            ensures
                self.inv(),
                self.constants() == old(self).constants(),
                self@ == old(self)@.flush(),
        ;
    }

}
