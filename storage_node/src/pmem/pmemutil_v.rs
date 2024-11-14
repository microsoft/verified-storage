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
use crate::pmem::subregion_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {
    broadcast use pmcopy_axioms;

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
        Ghost(impervious_to_corruption): Ghost<bool>,
        Ghost(data_addr): Ghost<int>,
        Ghost(crc_addr): Ghost<int>,
    ) -> (b: bool)
        requires
            crc_c@.len() == u64::spec_size_of(),
            bytes_read_from_storage(data_c@, true_bytes, data_addr, impervious_to_corruption),
            bytes_read_from_storage(crc_c@, spec_crc_bytes(true_bytes), crc_addr, impervious_to_corruption),
        ensures
            if b {
                &&& data_c@ == true_bytes
                &&& crc_c@ == spec_crc_bytes(true_bytes)
            }
            else {
               !impervious_to_corruption
            },
    {
        // Compute a CRC for the bytes we read.
        let computed_crc = calculate_crc_bytes(data_c);

        // Check whether the CRCs match. This is done in an external body function so that
        // we can convert the maybe-corrupted CRC to a u64 for comparison to the computed CRC.
        let crcs_match = compare_crcs(crc_c, computed_crc);

        proof {
            let true_crc_bytes = spec_crc_bytes(true_bytes);

            // We may need to invoke `axiom_bytes_uncorrupted` to justify that since the CRCs match,
            // we can conclude that the data matches as well. That axiom only applies in the case
            // when all three of the following conditions hold: (1) the last-written CRC really is
            // the CRC of the last-written data; (2) the persistent memory regions aren't impervious
            // to corruption; and (3) the CRC read from disk matches the computed CRC. If any of
            // these three is false, we can't invoke `axiom_bytes_uncorrupted`, but that's OK
            // because we don't need it. #1 is a requirement to call this lemma. If #2 is false,
            // then no corruption has happened. If #3 is false, then we've detected corruption.
            if {
                &&& !impervious_to_corruption
                &&& crcs_match
            } {
                let data_addrs = Seq::<int>::new(true_bytes.len(), |i: int| i + data_addr);
                let true_crc_bytes = spec_crc_bytes(true_bytes);
                let crc_addrs = Seq::<int>::new(u64::spec_size_of(), |i: int| i + crc_addr);
                axiom_bytes_uncorrupted2(data_c@, true_bytes, data_addrs, crc_c@, true_crc_bytes, crc_addrs);
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
        Ghost(impervious_to_corruption): Ghost<bool>,
        Ghost(data_addr1): Ghost<int>,
        Ghost(data_addr2): Ghost<int>,
        Ghost(crc_addr): Ghost<int>,
    ) -> (b: bool)
        requires
            crc_c@.len() == u64::spec_size_of(),
            ({
                ||| data_addr1 + data1_c@.len() <= data_addr2
                ||| data_addr2 + data2_c@.len() <= data_addr1
            }),
            bytes_read_from_storage(data1_c@, true_bytes1, data_addr1, impervious_to_corruption),
            bytes_read_from_storage(data2_c@, true_bytes2, data_addr2, impervious_to_corruption),
            bytes_read_from_storage(crc_c@, spec_crc_bytes(true_bytes1 + true_bytes2), crc_addr,
                                    impervious_to_corruption),
        ensures
            ({
                if b {
                    &&& data1_c@ == true_bytes1
                    &&& data2_c@ == true_bytes2
                    &&& crc_c@ == spec_crc_bytes(true_bytes1 + true_bytes2)
                }
                else {
                    !impervious_to_corruption
                }
            })
    {
        // calculate the CRC using a digest including both data1_c and data2_c
        let mut digest = CrcDigest::new();
        digest.write_bytes(data1_c);
        digest.write_bytes(data2_c);
        proof {
            reveal_with_fuel(Seq::flatten, 3);
            assert(digest.bytes_in_digest().flatten() =~= data1_c@ + data2_c@);
        }
        let computed_crc = digest.sum64();

        assert(computed_crc == spec_crc_u64(data1_c@ + data2_c@));

        // Check whether the CRCs match. This is done in an external body function so that we can convert the maybe-corrupted
        // CRC to a u64 for comparison to the computed CRC.
        let crcs_match = compare_crcs(crc_c, computed_crc);

        proof {
            // We may need to invoke `axiom_bytes_uncorrupted` to justify that since the CRCs match,
            // we can conclude that the data matches as well. That axiom only applies in the case
            // when all three of the following conditions hold: (1) the last-written CRC really is
            // the CRC of the last-written data; (2) the persistent memory regions aren't impervious
            // to corruption; and (3) the CRC read from disk matches the computed CRC. If any of
            // these three is false, we can't invoke `axiom_bytes_uncorrupted`, but that's OK
            // because we don't need it. #1 is a precondition for calling this lemma. If #2 is false,
            // then no corruption has happened. If #3 is false, then we've detected corruption.
            if {
                &&& !impervious_to_corruption
                &&& crcs_match
            } {
                let data_c = data1_c@ + data2_c@;
                let true_data = true_bytes1 + true_bytes2;
                let true_crc_bytes = spec_crc_bytes(true_data);
                let data_addrs1 = Seq::<int>::new(data1_c@.len(), |i: int| i + data_addr1);
                let data_addrs2 = Seq::<int>::new(data2_c@.len(), |i: int| i + data_addr2);
                let crc_addrs = Seq::<int>::new(u64::spec_size_of(), |i: int| i + crc_addr);
                axiom_bytes_uncorrupted2(data_c, true_data, data_addrs1 + data_addrs2,
                                         crc_c@, true_crc_bytes, crc_addrs);
                assert(extract_bytes(data_c, 0, data1_c@.len()) == data1_c@);
                assert(extract_bytes(data_c, data1_c@.len(), data2_c@.len()) == data2_c@);
                assert(data1_c@ == true_bytes1);
                assert(data2_c@ == true_bytes2);
            }
        }
        crcs_match
    }

    pub exec fn check_crc_for_two_reads_in_subregion<PM>(
        data1_c: &[u8],
        data2_c: &[u8],
        crc_c: &[u8],
        subregion: &PersistentMemorySubregion,
        pm_region: &PM,
        Ghost(relative_data_addr1): Ghost<int>,
        Ghost(relative_data_addr2): Ghost<int>,
        Ghost(relative_crc_addr): Ghost<int>,
    ) -> (b: bool)
        where 
            PM: PersistentMemoryRegion
        requires
            0 <= relative_data_addr1,
            0 <= relative_data_addr2,
            0 <= relative_crc_addr,
            relative_data_addr1 + data1_c@.len() <= subregion.len(),
            relative_data_addr2 + data2_c@.len() <= subregion.len(),
            relative_crc_addr + crc_c@.len() <= subregion.len(),
            subregion.start() + subregion.len() <= pm_region@.len(),
            ({
                ||| relative_data_addr1 + data1_c@.len() <= relative_data_addr2 <= subregion.len()
                ||| relative_data_addr2 + data2_c@.len() <= relative_data_addr1 <= subregion.len()
            }),
            crc_c@.len() == u64::spec_size_of(),
            ({
                let true_data_bytes1 =
                    subregion.view(pm_region).read_state.subrange(relative_data_addr1 as int,
                                                                  relative_data_addr1 + data1_c@.len());
                let true_data_bytes2 =
                    subregion.view(pm_region).read_state.subrange(relative_data_addr2 as int,
                                                                  relative_data_addr2 + data2_c@.len());
                let true_crc_bytes = spec_crc_bytes(true_data_bytes1 + true_data_bytes2);
                &&& bytes_read_from_storage(data1_c@, true_data_bytes1, relative_data_addr1 + subregion.start(),
                                          pm_region.constants().impervious_to_corruption)
                &&& bytes_read_from_storage(data2_c@, true_data_bytes2, relative_data_addr2 + subregion.start(),
                                          pm_region.constants().impervious_to_corruption)
                &&& bytes_read_from_storage(crc_c@, true_crc_bytes, relative_crc_addr + subregion.start(),
                                          pm_region.constants().impervious_to_corruption)
            }),
        ensures
            ({
                let true_data_bytes1 =
                    subregion.view(pm_region).read_state.subrange(relative_data_addr1 as int,
                                                                  relative_data_addr1 + data1_c@.len());
                let true_data_bytes2 =
                    subregion.view(pm_region).read_state.subrange(relative_data_addr2 as int,
                                                                  relative_data_addr2 + data2_c@.len());
                let true_crc_bytes = spec_crc_bytes(true_data_bytes1 + true_data_bytes2);
                if b {
                    &&& data1_c@ == true_data_bytes1
                    &&& data2_c@ == true_data_bytes2
                    &&& crc_c@ == true_crc_bytes
                }
                else {
                    !pm_region.constants().impervious_to_corruption
                }
            }),
    {
        // calculate the CRC using a digest including both data1_c and data2_c
        let mut digest = CrcDigest::new();
        digest.write_bytes(data1_c);
        digest.write_bytes(data2_c);
        proof {
            reveal_with_fuel(Seq::flatten, 3);
            assert(digest.bytes_in_digest().flatten() =~= data1_c@ + data2_c@);
        }
        let computed_crc = digest.sum64();

        assert(computed_crc == spec_crc_u64(data1_c@ + data2_c@));

        // Check whether the CRCs match. This is done in an external body function so that we can convert the maybe-corrupted
        // CRC to a u64 for comparison to the computed CRC.
        let crcs_match = compare_crcs(crc_c, computed_crc);

        proof {
            let true_data_bytes1 =
                subregion.view(pm_region).read_state.subrange(relative_data_addr1 as int,
                                                              relative_data_addr1 + data1_c@.len());
            let true_data_bytes2 =
                subregion.view(pm_region).read_state.subrange(relative_data_addr2 as int,
                                                              relative_data_addr2 + data2_c@.len());
            let true_crc_bytes = spec_crc_bytes(true_data_bytes1 + true_data_bytes2);

            // We may need to invoke `axiom_bytes_uncorrupted` to justify that since the CRCs match,
            // we can conclude that the data matches as well. That axiom only applies in the case
            // when all three of the following conditions hold: (1) the last-written CRC really is
            // the CRC of the last-written data; (2) the persistent memory regions aren't impervious
            // to corruption; and (3) the CRC read from disk matches the computed CRC. If any of
            // these three is false, we can't invoke `axiom_bytes_uncorrupted`, but that's OK
            // because we don't need it. If #1 is false, then this lemma isn't expected to prove
            // anything. If #2 is false, then no corruption has happened. If #3 is false, then we've
            // detected corruption.
            if {
                &&& !pm_region.constants().impervious_to_corruption
                &&& crcs_match
            } {
                let data_c = data1_c@ + data2_c@;
                let true_data = true_data_bytes1 + true_data_bytes2;
                let absolute_data_addrs1 = Seq::new(data1_c@.len(),
                                                    |i: int| i + relative_data_addr1 + subregion.start());
                let absolute_data_addrs2 = Seq::new(data2_c@.len(),
                                                    |i: int| i + relative_data_addr2 + subregion.start());
                let absolute_crc_addrs = Seq::new(u64::spec_size_of(),
                                                  |i: int| i + relative_crc_addr + subregion.start());
                axiom_bytes_uncorrupted2(data_c, true_data, absolute_data_addrs1 + absolute_data_addrs2,
                                         crc_c@, true_crc_bytes, absolute_crc_addrs);
                assert(extract_bytes(data_c, 0, data1_c@.len()) == data1_c@);
                assert(extract_bytes(data_c, data1_c@.len(), data2_c@.len()) == data2_c@);
                assert(data1_c@ == true_data_bytes1);
                assert(data2_c@ == true_data_bytes2);
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
        Ghost(impervious_to_corruption): Ghost<bool>,
        Ghost(cdb_addr): Ghost<int>,
    ) -> (result: Option<bool>)
        requires
            bytes_read_from_storage(cdb_c@, true_cdb_bytes, cdb_addr, impervious_to_corruption),
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
                    None => !impervious_to_corruption,
                }
            }),
    {
        let ghost cdb_addrs = Seq::<int>::new(u64::spec_size_of(), |i: int| i + cdb_addr);
                                            
        proof {
            // We may need to invoke the axiom
            // `axiom_corruption_detecting_boolean` to justify concluding
            // that, if we read `CDB_FALSE` or `CDB_TRUE`, it can't have
            // been corrupted.
            if !impervious_to_corruption && (cdb_c@ == CDB_FALSE.spec_to_bytes() || cdb_c@ == CDB_TRUE.spec_to_bytes()) {
                axiom_corruption_detecting_boolean(cdb_c@, true_cdb_bytes, cdb_addrs);
            }  
        }
        
        let cdb_val = cdb_c.extract_cdb(Ghost(true_cdb_bytes), Ghost(cdb_addrs), Ghost(impervious_to_corruption));
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

    // TODO DOCUMENTATION
    pub fn check_cdb_in_subregion<PM>(
        cdb_c: MaybeCorruptedBytes<u64>,
        subregion: &PersistentMemorySubregion,
        pm_region: &PM,
        Ghost(impervious_to_corruption): Ghost<bool>,
        Ghost(relative_cdb_addrs): Ghost<Seq<int>>,
    ) -> (result: Option<bool>)
        where 
            PM: PersistentMemoryRegion,
        requires
            forall |i: int| 0 <= i < relative_cdb_addrs.len() ==> relative_cdb_addrs[i] <= subregion.view(pm_region).len(),
            all_elements_unique(relative_cdb_addrs),
            ({
                let true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| subregion.view(pm_region).read_state[relative_cdb_addrs[i]]);
                let true_cdb = u64::spec_from_bytes(true_cdb_bytes);
                &&& u64::bytes_parseable(true_cdb_bytes)
                &&& true_cdb == CDB_FALSE || true_cdb == CDB_TRUE
                &&& if impervious_to_corruption { cdb_c@ == true_cdb_bytes }
                        else { subregion.maybe_corrupted_relative(cdb_c@, true_cdb_bytes, relative_cdb_addrs) }
            })
        ensures
            ({
                let true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| subregion.view(pm_region).read_state[relative_cdb_addrs[i]]);
                let true_cdb = u64::spec_from_bytes(true_cdb_bytes);
                match result {
                    Some(b) => if b { true_cdb == CDB_TRUE }
                               else { true_cdb == CDB_FALSE },
                    None => !impervious_to_corruption,
                }
            })
    {
        let ghost true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| subregion.view(pm_region).read_state[relative_cdb_addrs[i]]);
        let ghost absolute_cdb_addrs = Seq::new(relative_cdb_addrs.len(), |i: int| subregion.start() + relative_cdb_addrs[i]);
        proof {
            // We may need to invoke the axiom
            // `axiom_corruption_detecting_boolean` to justify concluding
            // that, if we read `CDB_FALSE` or `CDB_TRUE`, it can't have
            // been corrupted.
            if !impervious_to_corruption && (cdb_c@ == CDB_FALSE.spec_to_bytes() || cdb_c@ == CDB_TRUE.spec_to_bytes()) {
                axiom_corruption_detecting_boolean(cdb_c@, true_cdb_bytes, absolute_cdb_addrs);
            }  
        }
        
        let cdb_val = cdb_c.extract_cdb(Ghost(true_cdb_bytes), Ghost(absolute_cdb_addrs), Ghost(impervious_to_corruption));
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

    // This lemma establishes that, if the read state matches the
    // durable state (e.g., after a flush) and we write a
    // `const_persistence_chunk_size()`-aligned segment of length
    // `const_persistence_chunk_size()`, then there are only two
    // possible crash states that can happen after the write is
    // initiated. In one of those crash states, nothing has changed;
    // in the other, all the written bytes have been updated according
    // to this write.
    pub proof fn lemma_single_write_crash_effect_on_pm_region_view(
        new_durable_bytes: Seq<u8>,
        pm_region_view: PersistentMemoryRegionView,
        write_addr: int,
        bytes_to_write: Seq<u8>,
    )
        requires
            bytes_to_write.len() == const_persistence_chunk_size(),
            write_addr % const_persistence_chunk_size() == 0,
            0 <= write_addr,
            write_addr + const_persistence_chunk_size() <= pm_region_view.len(),
            can_result_from_partial_write(new_durable_bytes, pm_region_view.durable_state, write_addr, bytes_to_write),
            pm_region_view.read_state == pm_region_view.durable_state,
        ensures
            ({
                ||| new_durable_bytes == pm_region_view.durable_state
                ||| new_durable_bytes == update_bytes(pm_region_view.durable_state, write_addr, bytes_to_write)
            })
    {
        let chunk = write_addr / const_persistence_chunk_size();

        // Then, we just have to reason about this one written chunk. There are two cases:
        // (1) the chunk isn't flushed at all and (2) the chunk is entirely flushed.

        assert(chunk_trigger(chunk));
        if chunk_corresponds(new_durable_bytes, pm_region_view.durable_state, chunk) {
            assert forall|addr: int| 0 <= addr < new_durable_bytes.len()
                implies #[trigger] new_durable_bytes[addr] == pm_region_view.durable_state[addr] by {
                assert(chunk_trigger(addr / const_persistence_chunk_size()));
            }
            assert(new_durable_bytes =~= pm_region_view.durable_state);
        }
        else {
            assert forall|addr: int| 0 <= addr < new_durable_bytes.len()
                implies #[trigger] new_durable_bytes[addr] ==
                        update_bytes(pm_region_view.durable_state, write_addr, bytes_to_write)[addr] by {
                assert(chunk_trigger(addr / const_persistence_chunk_size()));
            }
            assert(new_durable_bytes =~= update_bytes(pm_region_view.durable_state, write_addr, bytes_to_write));
        }
    }

    // This lemma establishes that if one performs a write and then a
    // flush, then the committed contents reflect that write.
    pub proof fn lemma_write_reflected_after_write(
        pm_region_view: PersistentMemoryRegionView,
        new_pm_region_view: PersistentMemoryRegionView,
        addr: int,
        bytes: Seq<u8>,
    )
        requires
            0 <= addr,
            addr + bytes.len() <= pm_region_view.len(),
            new_pm_region_view.can_result_from_write(pm_region_view, addr, bytes),
        ensures
            new_pm_region_view.read_state.subrange(addr as int, addr + bytes.len()) == bytes
    {
        // All we need is to get Z3 to consider extensional equality.
         assert(new_pm_region_view.read_state.subrange(addr as int, addr + bytes.len()) =~= bytes);
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
        proof {
            digest.bytes_in_digest().lemma_flatten_one_element();
        }
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
            digest.bytes_in_digest().lemma_flatten_one_element();
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

    // This lemma proves that an extract_bytes of an extract_bytes is equal to the result of a single call to
    // extract_bytes.
    pub proof fn lemma_extract_bytes_of_extract_bytes_equal(mem: Seq<u8>, start1: nat, start2: nat, len1: nat, len2: nat)
        requires 
            start1 <= start2 <= start2 + len2 <= start1 + len1 <= mem.len()
        ensures 
            extract_bytes(mem, start2, len2) ==
            extract_bytes(extract_bytes(mem, start1, len1), (start2 - start1) as nat, len2)
    {
        lemma_subrange_of_subrange_equal(mem, start1, start2, start2 + len2, start1 + len1);
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

    pub proof fn lemma_can_result_from_write_effect_on_durable_state(
        v2: PersistentMemoryRegionView,
        v1: PersistentMemoryRegionView,
        write_addr: int,
        bytes: Seq<u8>
    )
        requires
            v1.valid(),
            v2.can_result_from_write(v1, write_addr, bytes),
        ensures
            forall|addr: int| 0 <= addr < v1.len() && !(write_addr <= addr < write_addr + bytes.len()) ==>
                #[trigger] v2.durable_state[addr] == v1.durable_state[addr],
            forall|addr: int| 0 <= addr < v1.len() && write_addr <= addr < write_addr + bytes.len() ==> {
                ||| #[trigger] v2.durable_state[addr] == v1.durable_state[addr]
                ||| v2.durable_state[addr] == bytes[addr - write_addr]
            },
    {
        assert forall|addr: int| 0 <= addr < v1.len() && !(write_addr <= addr < write_addr + bytes.len()) implies
                #[trigger] v2.durable_state[addr] == v1.durable_state[addr] by {
            assert(chunk_trigger(addr / const_persistence_chunk_size()));
        }
        assert forall|addr: int| 0 <= addr < v1.len() && write_addr <= addr < write_addr + bytes.len() implies {
                   ||| #[trigger] v2.durable_state[addr] == v1.durable_state[addr]
                   ||| v2.durable_state[addr] == bytes[addr - write_addr]
        } by {
            assert(chunk_trigger(addr / const_persistence_chunk_size()));
        }
    }

    pub proof fn lemma_auto_can_result_from_write_effect_on_durable_state()
        ensures
            forall |v2: PersistentMemoryRegionView, v1: PersistentMemoryRegionView, write_addr: int, bytes: Seq<u8>|
                #![trigger v2.can_result_from_write(v1, write_addr, bytes)]
            {
                &&& v1.valid()
                &&& v2.can_result_from_write(v1, write_addr, bytes)
            } ==> {
                &&& forall|addr: int| 0 <= addr < v1.len() && !(write_addr <= addr < write_addr + bytes.len()) ==>
                       #[trigger] v2.durable_state[addr] == v1.durable_state[addr]
                &&& forall|addr: int| 0 <= addr < v1.len() && write_addr <= addr < write_addr + bytes.len() ==> {
                       ||| #[trigger] v2.durable_state[addr] == v1.durable_state[addr]
                       ||| v2.durable_state[addr] == bytes[addr - write_addr]
                }
            }
    {
        assert forall |v2: PersistentMemoryRegionView, v1: PersistentMemoryRegionView, write_addr: int, bytes: Seq<u8>|
                   #![trigger v2.can_result_from_write(v1, write_addr, bytes)]
        {
            &&& v1.valid()
            &&& v2.can_result_from_write(v1, write_addr, bytes)
        } implies {
            &&& forall|addr: int| 0 <= addr < v1.len() && !(write_addr <= addr < write_addr + bytes.len()) ==>
                   #[trigger] v2.durable_state[addr] == v1.durable_state[addr]
            &&& forall|addr: int| 0 <= addr < v1.len() && write_addr <= addr < write_addr + bytes.len() ==> {
                   ||| #[trigger] v2.durable_state[addr] == v1.durable_state[addr]
                   ||| v2.durable_state[addr] == bytes[addr - write_addr]
            }
        } by {
            lemma_can_result_from_write_effect_on_durable_state(v2, v1, write_addr, bytes);
        }
    }

    pub proof fn lemma_can_result_from_write_effect(
        v2: PersistentMemoryRegionView,
        v1: PersistentMemoryRegionView,
        write_addr: int,
        bytes: Seq<u8>
    )
        requires
            v1.valid(),
            v2.can_result_from_write(v1, write_addr, bytes),
        ensures
            forall|addr: int| 0 <= addr < v1.len() && !(write_addr <= addr < write_addr + bytes.len()) ==>
                #[trigger] v2.durable_state[addr] == v1.durable_state[addr],
            forall|addr: int| 0 <= addr < v1.len() && write_addr <= addr < write_addr + bytes.len() ==> {
                ||| #[trigger] v2.durable_state[addr] == v1.durable_state[addr]
                ||| v2.durable_state[addr] == bytes[addr - write_addr]
            },
            forall|addr: int| 0 <= addr < v1.len() && !(write_addr <= addr < write_addr + bytes.len()) ==>
               #[trigger] v2.read_state[addr] == v1.read_state[addr],
            forall|addr: int| 0 <= addr < v1.len() && write_addr <= addr < write_addr + bytes.len() ==>
                #[trigger] v2.read_state[addr] == bytes[addr - write_addr],
    {
        lemma_can_result_from_write_effect_on_durable_state(v2, v1, write_addr, bytes);
    }

    pub proof fn lemma_auto_can_result_from_write_effect()
        ensures
            forall |v2: PersistentMemoryRegionView, v1: PersistentMemoryRegionView, write_addr: int, bytes: Seq<u8>|
                #![trigger v2.can_result_from_write(v1, write_addr, bytes)]
            {
                &&& v1.valid()
                &&& v2.can_result_from_write(v1, write_addr, bytes)
            } ==> {
                &&& forall|addr: int| 0 <= addr < v1.len() && !(write_addr <= addr < write_addr + bytes.len()) ==>
                       #[trigger] v2.durable_state[addr] == v1.durable_state[addr]
                &&& forall|addr: int| 0 <= addr < v1.len() && write_addr <= addr < write_addr + bytes.len() ==> {
                       ||| #[trigger] v2.durable_state[addr] == v1.durable_state[addr]
                       ||| v2.durable_state[addr] == bytes[addr - write_addr]
                }
                &&& forall|addr: int| 0 <= addr < v1.len() && !(write_addr <= addr < write_addr + bytes.len()) ==>
                       #[trigger] v2.read_state[addr] == v1.read_state[addr]
                &&& forall|addr: int| 0 <= addr < v1.len() && write_addr <= addr < write_addr + bytes.len() ==>
                        #[trigger] v2.read_state[addr] == bytes[addr - write_addr]
            }
    {
        assert forall |v2: PersistentMemoryRegionView, v1: PersistentMemoryRegionView, write_addr: int, bytes: Seq<u8>|
                #![trigger v2.can_result_from_write(v1, write_addr, bytes)]
            {
                &&& v1.valid()
                &&& v2.can_result_from_write(v1, write_addr, bytes)
            } implies {
                &&& forall|addr: int| 0 <= addr < v1.len() && !(write_addr <= addr < write_addr + bytes.len()) ==>
                       #[trigger] v2.durable_state[addr] == v1.durable_state[addr]
                &&& forall|addr: int| 0 <= addr < v1.len() && write_addr <= addr < write_addr + bytes.len() ==> {
                       ||| #[trigger] v2.durable_state[addr] == v1.durable_state[addr]
                       ||| v2.durable_state[addr] == bytes[addr - write_addr]
                }
                &&& forall|addr: int| 0 <= addr < v1.len() && !(write_addr <= addr < write_addr + bytes.len()) ==>
                       #[trigger] v2.read_state[addr] == v1.read_state[addr]
                &&& forall|addr: int| 0 <= addr < v1.len() && write_addr <= addr < write_addr + bytes.len() ==>
                        #[trigger] v2.read_state[addr] == bytes[addr - write_addr]
            } by {
            lemma_can_result_from_write_effect(v2, v1, write_addr, bytes);
        }
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
