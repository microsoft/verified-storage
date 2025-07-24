//! This file contains lemmas and utility executable functions about
//! persistent memory regions.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use crate::pmem::crc_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::crc_t::*;
use crate::pmem::hamming_t::*;
use crate::pmem::hamming_v::*;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {
    broadcast use pmcopy_axioms;

    proof fn cdb_hamming()
        ensures
            hamming(CDB_FALSE.spec_to_bytes(), CDB_TRUE.spec_to_bytes()) == 25
    {
        broadcast use pmcopy_axioms;
        spec_u64_to_le_bytes_to_open(CDB_FALSE);
        spec_u64_to_le_bytes_to_open(CDB_TRUE);
        assert(((0xa32842d19001605e as u64)       & 0xff) as u8 == 0x5e) by (bit_vector);
        assert(((0xa32842d19001605e as u64 >>  8) & 0xff) as u8 == 0x60) by (bit_vector);
        assert(((0xa32842d19001605e as u64 >> 16) & 0xff) as u8 == 0x01) by (bit_vector);
        assert(((0xa32842d19001605e as u64 >> 24) & 0xff) as u8 == 0x90) by (bit_vector);
        assert(((0xa32842d19001605e as u64 >> 32) & 0xff) as u8 == 0xd1) by (bit_vector);
        assert(((0xa32842d19001605e as u64 >> 40) & 0xff) as u8 == 0x42) by (bit_vector);
        assert(((0xa32842d19001605e as u64 >> 48) & 0xff) as u8 == 0x28) by (bit_vector);
        assert(((0xa32842d19001605e as u64 >> 56) & 0xff) as u8 == 0xa3) by (bit_vector);
        assert(((0xab21aa73069531b7 as u64)       & 0xff) as u8 == 0xb7) by (bit_vector);
        assert(((0xab21aa73069531b7 as u64 >>  8) & 0xff) as u8 == 0x31) by (bit_vector);
        assert(((0xab21aa73069531b7 as u64 >> 16) & 0xff) as u8 == 0x95) by (bit_vector);
        assert(((0xab21aa73069531b7 as u64 >> 24) & 0xff) as u8 == 0x06) by (bit_vector);
        assert(((0xab21aa73069531b7 as u64 >> 32) & 0xff) as u8 == 0x73) by (bit_vector);
        assert(((0xab21aa73069531b7 as u64 >> 40) & 0xff) as u8 == 0xaa) by (bit_vector);
        assert(((0xab21aa73069531b7 as u64 >> 48) & 0xff) as u8 == 0x21) by (bit_vector);
        assert(((0xab21aa73069531b7 as u64 >> 56) & 0xff) as u8 == 0xab) by (bit_vector);
        assert(popcnt_byte(0x5e^0xb7 as u8) == 5) by (compute);
        assert(popcnt_byte(0x60^0x31 as u8) == 3) by (compute);
        assert(popcnt_byte(0x01^0x95 as u8) == 3) by (compute);
        assert(popcnt_byte(0x90^0x06 as u8) == 4) by (compute);
        assert(popcnt_byte(0xd1^0x73 as u8) == 3) by (compute);
        assert(popcnt_byte(0x42^0xaa as u8) == 4) by (compute);
        assert(popcnt_byte(0x28^0x21 as u8) == 2) by (compute);
        assert(popcnt_byte(0xa3^0xab as u8) == 1) by (compute);
        assert(popcnt_seq(xor(CDB_FALSE.spec_to_bytes(), CDB_TRUE.spec_to_bytes())) == seq![5 as nat, 3, 3, 4, 3, 4, 2, 1]);
        assert(sum(seq![5 as nat, 3, 3, 4, 3, 4, 2, 1]) == 25) by (compute);
    }

    impl PersistentMemoryConstants {
        proof fn maybe_corrupted_byte_popcnt(self, byte: u8, true_byte: u8, addr: int)
            requires
                self.maybe_corrupted_byte(byte, true_byte, addr)
            ensures
                popcnt_byte(byte ^ true_byte) <= popcnt_byte(self.corruption[addr])
        {
            let c = self.corruption[addr];
            assert forall |mask: u8| popcnt_byte(#[trigger] (true_byte ^ (mask & c)) ^ true_byte) <= popcnt_byte(c) by {
                byte_xor_mask_popcnt_byte_le(true_byte, mask, c);
            };
        }

        pub proof fn maybe_corrupted_zero_addrs(self, bytes: Seq<u8>, true_bytes: Seq<u8>, addrs: Seq<int>)
            requires
                self.maybe_corrupted(bytes, true_bytes, addrs),
                self.impervious_to_corruption(),
            ensures
                bytes =~= true_bytes
        {
            assert forall |i: int| 0 <= i < bytes.len() implies bytes[i] == true_bytes[i] by {
                popcnt_index_le(self.corruption, addrs[i]);
                popcnt_byte_zero(self.corruption[addrs[i]]);
                assert forall |mask: u8| (mask & 0) == 0 by {
                    byte_and_zero(mask);
                };
                xor_byte_zero(true_bytes[i]);
            };
        }

        pub proof fn maybe_corrupted_zero(self, bytes: Seq<u8>, true_bytes: Seq<u8>)
            requires
                exists |addrs: Seq<int>| #[trigger] self.maybe_corrupted(bytes, true_bytes, addrs),
                self.impervious_to_corruption(),
            ensures
                bytes =~= true_bytes
        {
            assert forall |addrs: Seq<int>| #[trigger] self.maybe_corrupted(bytes, true_bytes, addrs) implies bytes =~= true_bytes by {
                self.maybe_corrupted_zero_addrs(bytes, true_bytes, addrs);
            };
        }


        proof fn maybe_corrupted_hamming(self, bytes: Seq<u8>, true_bytes: Seq<u8>, addrs: Seq<int>)
            requires
                self.maybe_corrupted(bytes, true_bytes, addrs),
                addrs.no_duplicates(),
            ensures
                hamming(bytes, true_bytes) <= popcnt(self.corruption)
        {
            assert forall |i: int| 0 <= i < bytes.len() implies #[trigger] popcnt_byte(bytes[i] ^ true_bytes[i]) <= popcnt_byte(self.corruption[addrs[i]]) by {
                self.maybe_corrupted_byte_popcnt(bytes[i], true_bytes[i], addrs[i]);
            };
            popcnt_ext_le(xor(bytes, true_bytes), S(self.corruption)[addrs]);
            popcnt_indexes_le(self.corruption, addrs);
        }

        proof fn _maybe_corrupted_crc(self,
                                      x_c: Seq<u8>, x: Seq<u8>, x_addrs: Seq<int>,
                                      y_c: Seq<u8>, y: Seq<u8>, y_addrs: Seq<int>)
            requires
                x_c.len() == x.len(),
                y == spec_crc_bytes(x),
                y_c == spec_crc_bytes(x_c),
                (x_addrs + y_addrs).no_duplicates(),
                self.maybe_corrupted(x_c, x, x_addrs),
                self.maybe_corrupted(y_c, y, y_addrs),
                popcnt(self.corruption) < spec_crc_hamming_bound((x+y).len()),
            ensures
                x == x_c
        {
            self.maybe_corrupted_hamming(x_c + y_c, x + y, x_addrs + y_addrs);
            crc_hamming_bound_valid(x_c, x, y_c, y);
        }

       /// The first main lemmas about corruption, `_maybe_corrupted_crc` above,
        /// is that if we have byte sequences `x` and `y` stored in persistent memory,
        /// where `y` is the CRC of `x`, then we can detect an absence of corruption
        /// by reading both of them and checking the CRC checksum.
        ///
        /// Specifically, if we read from those locations and get `x_c` and `y_c`
        /// (corruptions of `x` and `y` respectively), and `y_c` is the CRC of `x_c`,
        /// and the total number of corrupted bits is smaller than CRC64's Hamming
        /// bound, then we can conclude that `x` wasn't corrupted, i.e., `x_c == x`.
        ///
        /// The valid() predicate of PersistentMemoryConstants asserts that the max
        /// number of corrupted bits is less than CRC64's Hamming bound for any length,
        /// which simplifies the statement of the `maybe_corrupted_crc` lemma.

        pub proof fn maybe_corrupted_crc(self,
                                         x_c: Seq<u8>, x: Seq<u8>, x_addrs: Seq<int>,
                                         y_c: Seq<u8>, y: Seq<u8>, y_addrs: Seq<int>)
            requires
                x_c.len() == x.len(),
                y == spec_crc_bytes(x),
                y_c == spec_crc_bytes(x_c),
                (x_addrs + y_addrs).no_duplicates(),
                self.maybe_corrupted(x_c, x, x_addrs),
                self.maybe_corrupted(y_c, y, y_addrs),
                self.valid(),
            ensures
                x == x_c
        {
            self._maybe_corrupted_crc(x_c, x, x_addrs, y_c, y, y_addrs);
        }

        /// The second lemma, encapsulated in `maybe_corrupted_cdb`, is that the
        /// values `CDB_FALSE` and `CDB_TRUE` are so randomly different from each
        /// other that corruption can't make one appear to be the other.
        /// (CDB stands for Corruption-Detecting Boolean.)
        ///
        /// That is, if we know we wrote either `CDB_FALSE` or `CDB_TRUE`
        /// to a certain part of persistent memory, and when we read that
        /// same part we get `CDB_FALSE` or `CDB_TRUE`, we can conclude it
        /// matches what we last wrote to it.
        ///
        /// We set these values to CRC(b"0") and CRC(b"1"), respectively.

        pub proof fn maybe_corrupted_cdb(self, cdb_c: Seq<u8>, cdb: Seq<u8>, addrs: Seq<int>)
            requires
                self.valid(),
                self.maybe_corrupted(cdb_c, cdb, addrs),
                addrs.no_duplicates(),
                cdb.len() == u64::spec_size_of(),
                cdb_c == CDB_FALSE.spec_to_bytes() || cdb_c == CDB_TRUE.spec_to_bytes(),
                cdb == CDB_FALSE.spec_to_bytes() || cdb == CDB_TRUE.spec_to_bytes(),
            ensures
                cdb_c == cdb
        {
            if cdb_c != cdb {
                self.maybe_corrupted_hamming(cdb_c, cdb, addrs);
                cdb_hamming();
                xor_comm(CDB_FALSE.spec_to_bytes(), CDB_TRUE.spec_to_bytes());
            }
        }
    }

    // This executable function checks whether the given CRC read from
    // persistent memory is the actual CRC of the given bytes read
    // from persistent memory. It returns a boolean indicating whether
    // the check succeeds.
    //
    // It guarantees that, if the CRC last written to memory really
    // was the CRC of the data last written to memory, then:
    //
    // 1) If the function returns `true`, then the data read from
    // memory (`data_c`) constitute an uncorrupted copy of the correct
    // bytes last written to memory.
    //
    // 2) If the function returns `false`, then the persistent memory
    // region collection the data and CRC were read from are not
    // impervious to corruption.
    //
    // Parameters:
    //
    // `data_c` -- the possibly corrupted data read from memory
    //
    // `crc_c` -- the possibly corrupted CRC read from memory
    //
    // `true_bytes` (ghost) -- the true contents of the part of memory
    // that was read from
    //
    // `impervious_to_corruption` (ghost) -- whether that memory is
    // impervious to corruption
    //
    // `data_addr` (ghost) -- where the data were read from in memory
    //
    // `crc_addr` (ghost) -- where the CRC was read from in memory
    pub fn check_crc(
        data_c: &[u8],
        crc_c: &[u8],
        Ghost(true_bytes): Ghost<Seq<u8>>,
        Ghost(pmc): Ghost<PersistentMemoryConstants>,
        Ghost(data_addr): Ghost<int>,
        Ghost(crc_addr): Ghost<int>,
    ) -> (b: bool)
        requires
            pmc.valid(),
            crc_c@.len() == u64::spec_size_of(),
            bytes_read_from_storage(data_c@, true_bytes, data_addr, pmc),
            bytes_read_from_storage(crc_c@, spec_crc_bytes(true_bytes), crc_addr, pmc),
            ({
                let data_addrs = Seq::<int>::new(true_bytes.len(), |i: int| i + data_addr);
                let crc_addrs = Seq::<int>::new(spec_crc_bytes(true_bytes).len(), |i: int| i + crc_addr);
                (data_addrs + crc_addrs).no_duplicates()
            }),
        ensures
            if b {
                &&& data_c@ == true_bytes
                &&& crc_c@ == spec_crc_bytes(true_bytes)
            }
            else {
               !pmc.impervious_to_corruption()
            },
    {
        // Compute a CRC for the bytes we read.
        let computed_crc = calculate_crc_bytes(data_c);

        // Check whether the CRCs match. This is done in an external body function so that
        // we can convert the maybe-corrupted CRC to a u64 for comparison to the computed CRC.
        let crcs_match = compare_crcs(crc_c, computed_crc);

        proof {
            let true_crc_bytes = spec_crc_bytes(true_bytes);
            let data_addrs = Seq::<int>::new(true_bytes.len(), |i: int| i + data_addr);
            let true_crc_bytes = spec_crc_bytes(true_bytes);
            let crc_addrs = Seq::<int>::new(u64::spec_size_of(), |i: int| i + crc_addr);

            if pmc.impervious_to_corruption() {
                pmc.maybe_corrupted_zero(data_c@, true_bytes);
                pmc.maybe_corrupted_zero(crc_c@, true_crc_bytes);
            }

            if {
                &&& !pmc.impervious_to_corruption()
                &&& crcs_match
            } {
                pmc.maybe_corrupted_crc(data_c@, true_bytes, data_addrs, crc_c@, true_crc_bytes, crc_addrs);
            }
        }
        crcs_match
    }

    pub exec fn check_crc_for_two_reads(
        data1_c: &[u8],
        data2_c: &[u8],
        crc_c: &[u8],
        Ghost(true_bytes1): Ghost<Seq<u8>>,
        Ghost(true_bytes2): Ghost<Seq<u8>>,
        Ghost(pmc): Ghost<PersistentMemoryConstants>,
        Ghost(data_addr1): Ghost<int>,
        Ghost(data_addr2): Ghost<int>,
        Ghost(crc_addr): Ghost<int>,
    ) -> (b: bool)
        requires
            pmc.valid(),
            crc_c@.len() == u64::spec_size_of(),
            ({
                ||| data_addr1 + data1_c@.len() <= data_addr2
                ||| data_addr2 + data2_c@.len() <= data_addr1
            }),
            bytes_read_from_storage(data1_c@, true_bytes1, data_addr1, pmc),
            bytes_read_from_storage(data2_c@, true_bytes2, data_addr2, pmc),
            bytes_read_from_storage(crc_c@, spec_crc_bytes(true_bytes1 + true_bytes2), crc_addr, pmc),
            ({
                let data_addrs1 = Seq::<int>::new(true_bytes1.len(), |i: int| i + data_addr1);
                let data_addrs2 = Seq::<int>::new(true_bytes2.len(), |i: int| i + data_addr2);
                let crc_addrs = Seq::<int>::new(spec_crc_bytes(true_bytes1 + true_bytes2).len(), |i: int| i + crc_addr);
                (data_addrs1 + data_addrs2 + crc_addrs).no_duplicates()
            }),
        ensures
            ({
                if b {
                    &&& data1_c@ == true_bytes1
                    &&& data2_c@ == true_bytes2
                    &&& crc_c@ == spec_crc_bytes(true_bytes1 + true_bytes2)
                }
                else {
                    !pmc.impervious_to_corruption()
                }
            })
    {
        // calculate the CRC using a digest including both data1_c and data2_c
        let mut digest = CrcDigest::new();
        digest.write_bytes(data1_c);
        digest.write_bytes(data2_c);
        proof {
            assert(digest.bytes_in_digest() =~= data1_c@ + data2_c@);
        }
        let computed_crc = digest.sum64();

        assert(computed_crc == spec_crc_u64(data1_c@ + data2_c@));

        // Check whether the CRCs match. This is done in an external body function so that we can convert the maybe-corrupted
        // CRC to a u64 for comparison to the computed CRC.
        let crcs_match = compare_crcs(crc_c, computed_crc);

        proof {
            let data_c = data1_c@ + data2_c@;
            let true_data = true_bytes1 + true_bytes2;
            let true_crc_bytes = spec_crc_bytes(true_data);
            let data_addrs1 = Seq::<int>::new(data1_c@.len(), |i: int| i + data_addr1);
            let data_addrs2 = Seq::<int>::new(data2_c@.len(), |i: int| i + data_addr2);
            let crc_addrs = Seq::<int>::new(u64::spec_size_of(), |i: int| i + crc_addr);

            if pmc.impervious_to_corruption() {
                pmc.maybe_corrupted_zero_addrs(data_c, true_data, data_addrs1 + data_addrs2);
                pmc.maybe_corrupted_zero(crc_c@, true_crc_bytes);
                assert(extract_bytes(data_c, 0, data1_c@.len()) == data1_c@);
                assert(extract_bytes(data_c, data1_c@.len(), data2_c@.len()) == data2_c@);
                assert(data1_c@ == true_bytes1);
                assert(data2_c@ == true_bytes2);
            }

            if {
                &&& !pmc.impervious_to_corruption()
                &&& crcs_match
            } {
                pmc.maybe_corrupted_crc(data_c, true_data, data_addrs1 + data_addrs2,
                                        crc_c@, true_crc_bytes, crc_addrs);
                assert(extract_bytes(data_c, 0, data1_c@.len()) == data1_c@);
                assert(extract_bytes(data_c, data1_c@.len(), data2_c@.len()) == data2_c@);
                assert(data1_c@ == true_bytes1);
                assert(data2_c@ == true_bytes2);
            }
        }
        crcs_match
    }

    // This function converts the given encoded CDB read from persistent
    // memory into a boolean. It checks for corruption as it does so. It
    // guarantees that if it returns `Some` then there was no corruption,
    // and that if it returns `None` then the memory isn't impervious to
    // corruption.
    //
    // Parameters:
    //
    // `cdb_c` -- the possibly corrupted encoded CDB read from memory
    //
    // `true_cdb_bytes` (ghost) -- the true contents of the part of memory that was read
    //
    // `impervious_to_corruption` (ghost) -- whether that memory is
    // impervious to corruption
    //
    // `cdb_addr` (ghost) -- where the CDB was read from in memory
    //
    // Return value:
    //
    // `Some(b)` -- the encoded CDB is uncorrupted and encodes the boolean
    // `b`
    //
    // `None` -- corruption was detected, so the persistent memory regions
    // can't be impervious to corruption
    // 
    // We assume here that the CDB is stored contiguously, which will always be true
    // because we don't write CDBs to the log. If we do ever attempt to use this function
    // to check a CDB that was written to the log, verification will fail because the
    // addresses don't work out.
    pub fn check_cdb(
        cdb_c: MaybeCorruptedBytes<u64>,
        Ghost(true_cdb_bytes): Ghost<Seq<u8>>,
        Ghost(pmc): Ghost<PersistentMemoryConstants>,
        Ghost(cdb_addr): Ghost<int>,
    ) -> (result: Option<bool>)
        requires
            bytes_read_from_storage(cdb_c@, true_cdb_bytes, cdb_addr, pmc),
            ({
                let true_cdb = u64::spec_from_bytes(true_cdb_bytes);
                &&& u64::bytes_parseable(true_cdb_bytes)
                &&& true_cdb == CDB_FALSE || true_cdb == CDB_TRUE
            }),
        ensures
            ({
                let true_cdb = u64::spec_from_bytes(true_cdb_bytes);
                match result {
                    Some(b) => if b { true_cdb == CDB_TRUE }
                               else { true_cdb == CDB_FALSE },
                    None => !pmc.impervious_to_corruption(),
                }
            }),
    {
        let ghost cdb_addrs = Seq::<int>::new(u64::spec_size_of(), |i: int| i + cdb_addr);
                                            
        proof {
            // We may need to invoke the lemma `maybe_corrupted_cdb` to justify
            // concluding that, if we read `CDB_FALSE` or `CDB_TRUE`, it can't
            // have been corrupted.
            if pmc.impervious_to_corruption() {
                pmc.maybe_corrupted_zero(cdb_c@, true_cdb_bytes);
            }
            if !pmc.impervious_to_corruption() && (cdb_c@ == CDB_FALSE.spec_to_bytes() || cdb_c@ == CDB_TRUE.spec_to_bytes()) {
                pmc.maybe_corrupted_cdb(cdb_c@, true_cdb_bytes, cdb_addrs);
            }  
        }
        
        let cdb_val = cdb_c.extract_cdb(Ghost(true_cdb_bytes), Ghost(cdb_addrs), Ghost(pmc));
        assert(cdb_val.spec_to_bytes() == cdb_c@);

        // If the read encoded CDB is one of the expected ones, translate
        // it into a boolean; otherwise, indicate corruption.

        if *cdb_val == CDB_FALSE {
            Some(false)
        }
        else if *cdb_val == CDB_TRUE {
            Some(true)
        }
        else {
            proof {
                // This part of the proof can be flaky -- invoking this axiom helps stabilize it
                // by helping Z3 prove that the real CDB is neither valid value, which implies we are 
                // not impervious to corruption
               axiom_to_from_bytes::<u64>(*cdb_val);
            }
            None
        }
    }

    /// If the only outstanding write is `const_persistence_chunk_size()`-sized and
    /// -aligned, then there are only two possible resulting crash states,
    /// one with the write and one without.

    // This lemma establishes that, if we write a
    // `const_persistence_chunk_size()`-aligned segment of length
    // `const_persistence_chunk_size()`, then there are only two
    // possible crash states that can happen after the write is
    // initiated. In one of those crash states, nothing has changed;
    // in the other, all the written bytes have been updated according
    // to this write.
    pub proof fn lemma_only_two_crash_states_introduced_by_aligned_chunk_write(
        new_durable_state: Seq<u8>,
        durable_state: Seq<u8>,
        write_addr: int,
        bytes_to_write: Seq<u8>,
    )
        requires
            bytes_to_write.len() == const_persistence_chunk_size(),
            write_addr % const_persistence_chunk_size() == 0,
            0 <= write_addr,
            write_addr + const_persistence_chunk_size() <= durable_state.len(),
            can_result_from_partial_write(new_durable_state, durable_state, write_addr, bytes_to_write),
        ensures
            ({
                ||| new_durable_state == durable_state
                ||| new_durable_state == update_bytes(durable_state, write_addr, bytes_to_write)
            })
    {
        let chunk = write_addr / const_persistence_chunk_size();

        // Then, we just have to reason about this one written chunk. There are two cases:
        // (1) the chunk isn't flushed at all and (2) the chunk is entirely flushed.

        assert(chunk_trigger(chunk));
        if chunk_corresponds(new_durable_state, durable_state, chunk) {
            assert forall|addr: int| 0 <= addr < new_durable_state.len()
                implies #[trigger] new_durable_state[addr] == durable_state[addr] by {
                assert(chunk_trigger(addr / const_persistence_chunk_size()));
            }
            assert(new_durable_state =~= durable_state);
        }
        else {
            assert forall|addr: int| 0 <= addr < new_durable_state.len()
                implies #[trigger] new_durable_state[addr] ==
                        update_bytes(durable_state, write_addr, bytes_to_write)[addr] by {
                assert(chunk_trigger(addr / const_persistence_chunk_size()));
            }
            assert(new_durable_state =~= update_bytes(durable_state, write_addr, bytes_to_write));
        }
    }

    // This lemma establishes that, if we write a
    // `const_persistence_chunk_size()`-aligned segment of length
    // `const_persistence_chunk_size()`, then there are only two
    // possible crash states that can happen after the write is
    // initiated. In one of those crash states, nothing has changed;
    // in the other, all the written bytes have been updated according
    // to this write.
    pub proof fn lemma_auto_only_two_crash_states_introduced_by_aligned_chunk_write()
        ensures
            (forall|durable_state: Seq<u8>,
               write_addr: int,
               bytes_to_write: Seq<u8>,
               new_durable_state: Seq<u8>| {
               &&& bytes_to_write.len() == const_persistence_chunk_size()
               &&& write_addr % const_persistence_chunk_size() == 0
               &&& 0 <= write_addr
               &&& write_addr + const_persistence_chunk_size() <= durable_state.len()
               &&& #[trigger] can_result_from_partial_write(new_durable_state, durable_state,
                                                           write_addr, bytes_to_write)
            } ==>
            {
                ||| new_durable_state == durable_state
                ||| new_durable_state == update_bytes(durable_state, write_addr, bytes_to_write)
            })
    {
        assert forall|durable_state: Seq<u8>,
               write_addr: int,
               bytes_to_write: Seq<u8>,
               new_durable_state: Seq<u8>| {
               &&& bytes_to_write.len() == const_persistence_chunk_size()
               &&& write_addr % const_persistence_chunk_size() == 0
               &&& 0 <= write_addr
               &&& write_addr + const_persistence_chunk_size() <= durable_state.len()
               &&& #[trigger] can_result_from_partial_write(new_durable_state, durable_state,
                                                           write_addr, bytes_to_write)
            } implies
            {
                ||| new_durable_state == durable_state
                ||| new_durable_state == update_bytes(durable_state, write_addr, bytes_to_write)
            } by {
            lemma_only_two_crash_states_introduced_by_aligned_chunk_write(new_durable_state, durable_state, write_addr,
                                                                          bytes_to_write);
        }
    }

    // This function describes what it means for a certain set of
    // addresses to be inaccessible (i.e., irrelevant) to recovery
    // given the current state. It means that no matter what the
    // bytes at those addresses are set to, the recovery function
    // gives the same result.
    pub open spec fn addresses_not_accessed_by_recovery<T>(
        s: Seq<u8>,
        addrs: Set<int>,
        recover_fn: spec_fn(Seq<u8>) -> T,
    ) -> bool
    {
        forall|s2: Seq<u8>| {
            &&& s2.len() == s.len()
            &&& forall|i: int| #![trigger s2[i]] 0 <= i < s.len() && !addrs.contains(i) ==> s[i] == s2[i]
        } ==> #[trigger] recover_fn(s2) == recover_fn(s)
    }

    // This lemma establishes that, if we only write to addresses
    // that aren't accessed by a recovery function, then all additional
    // crash states introduced have the same recovered-to state as the
    // current one.
    pub proof fn lemma_if_addresses_unreachable_in_recovery_then_recovery_unchanged_by_write<T>(
        new_durable_state: Seq<u8>,
        durable_state: Seq<u8>,
        write_addr: int,
        bytes_to_write: Seq<u8>,
        addrs: Set<int>,
        recover_fn: spec_fn(Seq<u8>) -> T,
    )
        requires
            addresses_not_accessed_by_recovery::<T>(durable_state, addrs, recover_fn),
            forall|addr: int| write_addr <= addr < write_addr + bytes_to_write.len() ==> addrs.contains(addr),
            0 <= write_addr,
            write_addr + bytes_to_write.len() <= durable_state.len(),
            can_result_from_partial_write(new_durable_state, durable_state, write_addr, bytes_to_write),
        ensures
            recover_fn(new_durable_state) == recover_fn(durable_state)
    {
        assert(new_durable_state.len() == durable_state.len());
        assert forall|i: int| 0 <= i < durable_state.len() && !addrs.contains(i)
            implies new_durable_state[i] == durable_state[i] by {
            lemma_auto_can_result_from_partial_write_effect();
        }
    }

    // This lemma establishes that, if we only write to addresses
    // that aren't accessed by a recovery function, then all additional
    // crash states introduced have the same recovered-to state as the
    // current one.
    pub proof fn lemma_auto_if_addresses_unreachable_in_recovery_then_recovery_unchanged_by_write<T>(
        durable_state: Seq<u8>,
        addrs: Set<int>,
        recover_fn: spec_fn(Seq<u8>) -> T,
    )
        requires
            addresses_not_accessed_by_recovery::<T>(durable_state, addrs, recover_fn),
        ensures
            forall|new_durable_state: Seq<u8>, write_addr: int, bytes_to_write: Seq<u8>| {
                &&& forall|addr: int| write_addr <= addr < write_addr + bytes_to_write.len() ==> addrs.contains(addr)
                &&& 0 <= write_addr
                &&& write_addr + bytes_to_write.len() <= durable_state.len()
                &&& #[trigger] can_result_from_partial_write(new_durable_state, durable_state, write_addr,
                                                           bytes_to_write)
            } ==> recover_fn(new_durable_state) == recover_fn(durable_state)
    {
        assert forall|new_durable_state: Seq<u8>, write_addr: int, bytes_to_write: Seq<u8>| {
                &&& forall|addr: int| write_addr <= addr < write_addr + bytes_to_write.len() ==> addrs.contains(addr)
                &&& 0 <= write_addr
                &&& write_addr + bytes_to_write.len() <= durable_state.len()
                &&& #[trigger] can_result_from_partial_write(new_durable_state, durable_state, write_addr,
                                                           bytes_to_write)
            } implies recover_fn(new_durable_state) == recover_fn(durable_state) by {
            lemma_if_addresses_unreachable_in_recovery_then_recovery_unchanged_by_write(
                new_durable_state, durable_state, write_addr, bytes_to_write, addrs, recover_fn
            );
        }
    }

    // Calculates the CRC for a single `PmCopy` object.
    pub fn calculate_crc<S>(val: &S) -> (out: u64)
        where
            S: PmCopy + Sized,
        requires
            // this is true in the default implementation of `spec_crc`, but
            // an impl of `PmCopy` can override the default impl, so
            // we have to require it here
            val.spec_crc() == spec_crc_u64(val.spec_to_bytes())
        ensures
            val.spec_crc() == out,
            spec_crc_u64(val.spec_to_bytes()) == out,
    {
        let mut digest = CrcDigest::new();
        digest.write(val);
        digest.sum64()
    }

    pub fn calculate_crc_bytes(val: &[u8]) -> (out: u64) 
        ensures 
            out == spec_crc_u64(val@),
            out.spec_to_bytes() == spec_crc_bytes(val@),
    {
        let mut digest = CrcDigest::new();
        digest.write_bytes(val);
        proof {
            lemma_auto_spec_u64_to_from_le_bytes();
        }
        digest.sum64()
    }

    // This lemma establishes that for any `i` and `n`, if
    //
    // `forall |k| 0 <= k < n ==> mem1[i+k] == mem2[i+k]`
    //
    // holds, then
    //
    // `extract_bytes(mem1, i, n) == mem2.extract_bytes(mem2, i, n)`
    //
    // also holds.
    //
    // This is an obvious fact, so the body of the lemma is
    // empty. Nevertheless, the lemma is useful because it establishes
    // a trigger. Specifically, it hints Z3 that whenever Z3 is
    // thinking about two terms `extract_bytes(mem1, i, n)` and
    // `extract_bytes(mem2, i, n)` where `mem1` and `mem2` are the
    // specific memory byte sequences passed to this lemma, Z3 should
    // also think about this lemma's conclusion. That is, it should
    // try to prove that
    //
    // `forall |k| 0 <= k < n ==> mem1[i+k] == mem2[i+k]`
    //
    // and, whenever it can prove that, conclude that
    //
    // `extract_bytes(mem1, i, n) == mem2.extract_bytes(mem2, i, n)`
    pub proof fn lemma_establish_extract_bytes_equivalence(
        mem1: Seq<u8>,
        mem2: Seq<u8>,
    )
        ensures
            forall |i: nat, n: nat| extract_bytes(mem1, i, n) =~= extract_bytes(mem2, i, n) ==>
                #[trigger] extract_bytes(mem1, i, n) == #[trigger] extract_bytes(mem2, i, n)
    {
    }

    // This lemma proves that a subrange of a subrange is equal to the result of a single call to subrange.
    pub proof fn lemma_subrange_of_subrange_equal(mem: Seq<u8>, pos1: nat, pos2: nat, pos3: nat, pos4: nat)
        requires
            pos1 <= pos2 <= pos3 <= pos4 <= mem.len(),
        ensures
            mem.subrange(pos2 as int, pos3 as int) ==
            mem.subrange(pos1 as int, pos4 as int).subrange(pos2 - pos1, pos3 - pos1)
    {
        assert(mem.subrange(pos2 as int, pos3 as int) =~=
               mem.subrange(pos1 as int, pos4 as int).subrange(pos2 - pos1, pos3 - pos1));
    }

    // This lemma proves that a subrange of a subrange is equal to the result of a single call to
    // subrange.
    pub proof fn lemma_subrange_of_subrange_forall(mem: Seq<u8>)
        ensures
            forall|s1: int, e1: int, s2: int, e2: int|
               0 <= s1 <= e1 <= mem.len() && 0 <= s2 <= e2 <= e1 - s1 ==>
               mem.subrange(s1, e1).subrange(s2, e2) == mem.subrange(s1 + s2, s1 + e2)
    {
        assert forall|s1: int, e1: int, s2: int, e2: int|
               0 <= s1 <= e1 <= mem.len() && 0 <= s2 <= e2 <= e1 - s1 implies
               mem.subrange(s1, e1).subrange(s2, e2) == mem.subrange(s1 + s2, s1 + e2) by {
            mem.lemma_slice_of_slice(s1, e1, s2, e2);
        }
    }

    pub proof fn lemma_smaller_range_of_seq_is_subrange(mem1: Seq<u8>, i: int, j: int, k: int, l: int)
        requires 
            0 <= i <= k <= l <= j <= mem1.len()
        ensures 
            mem1.subrange(i, j).subrange(k - i, l - i) == mem1.subrange(k, l) 
    {
        assert(mem1.subrange(k, l) == mem1.subrange(i + k - i, i + l - i));
        assert(mem1.subrange(i, j).subrange(k - i, l - i) == mem1.subrange(i + k - i, i + l - i));
    }

    pub proof fn lemma_auto_smaller_range_of_seq_is_subrange(mem1: Seq<u8>)
        ensures 
            forall |i: int, j, k: int, l: int| 0 <= i <= k <= l <= j <= mem1.len() ==> mem1.subrange(i, j).subrange(k - i, l - i) == mem1.subrange(k, l) 
    {
        assert forall |i: int, j, k: int, l: int| 0 <= i <= k <= l <= j <= mem1.len() implies mem1.subrange(i, j).subrange(k - i, l - i) == mem1.subrange(k, l) by {
            lemma_smaller_range_of_seq_is_subrange(mem1, i, j, k, l);
        }
    }

    // This lemma proves that doing an update followed by a subrange gives you the
    // updated bytes.
    pub broadcast proof fn lemma_update_then_subrange_is_updated_bytes(s: Seq<u8>, addr: int, bytes: Seq<u8>)
        requires
            0 <= addr,
            addr + bytes.len() <= s.len(),
        ensures
            (#[trigger] update_bytes(s, addr, bytes)).subrange(addr, addr + bytes.len()) == bytes
    {
        assert(update_bytes(s, addr, bytes).subrange(addr, addr + bytes.len()) =~= bytes);
    }

    pub open spec fn no_outstanding_writes(v: PersistentMemoryRegionView) -> bool
    {
        v.read_state == v.durable_state
    }

    pub open spec fn no_outstanding_writes_in_range(v: PersistentMemoryRegionView, start: int, end: int) -> bool
    {
        forall|addr: int| 0 <= addr < v.len() && start <= addr < end ==> v.read_state[addr] == v.durable_state[addr]
    }

    pub proof fn lemma_can_result_from_partial_write_effect(
        s2: Seq<u8>,
        s1: Seq<u8>,
        write_addr: int,
        bytes: Seq<u8>
    )
        requires
            can_result_from_partial_write(s2, s1, write_addr, bytes),
        ensures
            forall|addr: int| 0 <= addr < s1.len() && !(write_addr <= addr < write_addr + bytes.len()) ==>
                #[trigger] s2[addr] == s1[addr],
            forall|addr: int| 0 <= addr < s1.len() && write_addr <= addr < write_addr + bytes.len() ==> {
                ||| #[trigger] s2[addr] == s1[addr]
                ||| s2[addr] == bytes[addr - write_addr]
            },
    {
        assert forall|addr: int| 0 <= addr < s1.len() && !(write_addr <= addr < write_addr + bytes.len()) implies
                #[trigger] s2[addr] == s1[addr] by {
            assert(chunk_trigger(addr / const_persistence_chunk_size()));
        }
        assert forall|addr: int| 0 <= addr < s1.len() && write_addr <= addr < write_addr + bytes.len() implies {
                   ||| #[trigger] s2[addr] == s1[addr]
                   ||| s2[addr] == bytes[addr - write_addr]
        } by {
            assert(chunk_trigger(addr / const_persistence_chunk_size()));
        }
    }

    pub proof fn lemma_auto_can_result_from_partial_write_effect()
        ensures
            forall|s2: Seq<u8>, s1: Seq<u8>, write_addr: int, bytes: Seq<u8>|
                #[trigger] can_result_from_partial_write(s2, s1, write_addr, bytes) ==> {
                &&& forall|addr: int| 0 <= addr < s1.len() && !(write_addr <= addr < write_addr + bytes.len()) ==>
                       #[trigger] s2[addr] == s1[addr]
                &&& forall|addr: int| 0 <= addr < s1.len() && write_addr <= addr < write_addr + bytes.len() ==> {
                       ||| #[trigger] s2[addr] == s1[addr]
                       ||| s2[addr] == bytes[addr - write_addr]
                   }
                }
    {
        assert forall|s2: Seq<u8>, s1: Seq<u8>, write_addr: int, bytes: Seq<u8>|
                   #[trigger] can_result_from_partial_write(s2, s1, write_addr, bytes) implies {
                &&& forall|addr: int| 0 <= addr < s1.len() && !(write_addr <= addr < write_addr + bytes.len()) ==>
                       #[trigger] s2[addr] == s1[addr]
                &&& forall|addr: int| 0 <= addr < s1.len() && write_addr <= addr < write_addr + bytes.len() ==> {
                       ||| #[trigger] s2[addr] == s1[addr]
                       ||| s2[addr] == bytes[addr - write_addr]
                   }
                } by {
            lemma_can_result_from_partial_write_effect(s2, s1, write_addr, bytes);
        }
    }

    pub proof fn lemma_noop_can_result_from_partial_write(
        s: Seq<u8>,
        write_addr: int,
        bytes: Seq<u8>
    )
        requires
            0 <= write_addr,
            write_addr + bytes.len() <= s.len(),
        ensures
            can_result_from_partial_write(s, s, write_addr, bytes)
    {
    }

    pub open spec fn flush_pm_view(v: PersistentMemoryRegionView) -> PersistentMemoryRegionView
    {
        PersistentMemoryRegionView{
            read_state: v.read_state,
            durable_state: v.read_state,
        }
    }

    pub open spec fn views_match_at_addr(
        v1: PersistentMemoryRegionView,
        v2: PersistentMemoryRegionView,
        addr: int
    ) -> bool
    {
        &&& v1.read_state[addr] == v2.read_state[addr]
        &&& v1.durable_state[addr] == v2.durable_state[addr]
    }

    pub open spec fn views_match_in_address_range(
        v1: PersistentMemoryRegionView,
        v2: PersistentMemoryRegionView,
        start: int,
        end: int,
    ) -> bool
    {
        forall|addr| #![trigger v1.read_state[addr]] #![trigger v1.durable_state[addr]]
                #![trigger v2.read_state[addr]] #![trigger v2.durable_state[addr]]
            start <= addr < end ==> views_match_at_addr(v1, v2, addr)
    }
    

}
