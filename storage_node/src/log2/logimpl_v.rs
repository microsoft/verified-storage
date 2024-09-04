use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::slice::*;
use vstd::arithmetic::{mul::*, div_mod::*};

use crate::kv::durable::inv_v::*;
use crate::kv::kvimpl_t::KvError;
use crate::kv::layout_v::*;
use crate::pmem::{pmemspec_t::*, pmcopy_t::*, pmemutil_v::*, wrpm_t::*, subregion_v::*, traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe}};
use crate::log2::{append_v::*, layout_v::*, start_v::*, inv_v::*};
use crate::pmem::wrpm_t::WriteRestrictedPersistentMemoryRegion;
use crate::util_v::*;

verus! {
// An `AbstractLogState` is an abstraction of a single log. Its
// fields are:
//
// `head` -- the logical position of the first accessible byte
// in the log
//
// `log` -- the accessible bytes in the log, logically starting
// at position `head`
//
// `pending` -- the bytes tentatively appended past the end of the
// log, which will not become part of the log unless committed
// and which will be discarded on a crash
//
// `capacity` -- the maximum length of the `log` field
#[verifier::ext_equal]
pub struct AbstractLogState {
    pub head: int,
    pub log: Seq<u8>,
    pub pending: Seq<u8>,
    pub capacity: int,
}

impl AbstractLogState {

    // This is the specification for the initial state of an
    // abstract log.
    pub open spec fn initialize(capacity: int) -> Self {
        Self {
            head: 0int,
            log: Seq::<u8>::empty(),
            pending: Seq::<u8>::empty(),
            capacity: capacity
        }
    }

    // This is the specification for what it means to tentatively
    // append to a log. It appends the given bytes to the
    // `pending` field.
    pub open spec fn tentatively_append(self, bytes: Seq<u8>) -> Self {
        Self { pending: self.pending + bytes, ..self }
    }

    // This is the specification for what it means to commit a
    // log.  It adds all pending bytes to the log and clears the
    // pending bytes.
    pub open spec fn commit(self) -> Self {
        Self { log: self.log + self.pending, pending: Seq::<u8>::empty(), ..self }
    }

    // This is the specification for what it means to advance the
    // head to a given new value `new_value`.
    pub open spec fn advance_head(self, new_head: int) -> Self
    {
        let new_log = self.log.subrange(new_head - self.head, self.log.len() as int);
        Self { head: new_head, log: new_log, ..self }
    }

    // This is the specification for what it means to read `len`
    // bytes from a certain virtual position `pos` in the abstract
    // log.
    pub open spec fn read(self, pos: int, len: int) -> Seq<u8>
    {
        self.log.subrange(pos - self.head, pos - self.head + len)
    }

    // This is the specification for what it means to drop pending
    // appends. (This isn't a user-invokable operation; it's what
    // happens on a crash.)
    pub open spec fn drop_pending_appends(self) -> Self
    {
        Self { pending: Seq::<u8>::empty(), ..self }
    }
}

// This is the specification that `LogImpl` (TODO UPDATE) provides for data
// bytes it reads. It says that those bytes are correct unless
// there was corruption on the persistent memory between the last
// write and this read.
pub open spec fn read_correct_modulo_corruption(bytes: Seq<u8>, true_bytes: Seq<u8>,
    addrs: Seq<int>, impervious_to_corruption: bool) -> bool
{
    &&& all_elements_unique(addrs)
    &&& if impervious_to_corruption {
            // If the region is impervious to corruption, the bytes read
            // must match the true bytes, i.e., the bytes last written.
            bytes == true_bytes
        }
        else {
            // Otherwise, there must exist a sequence of distinct
            // addresses `addrs` such that the nth byte of `bytes` is
            // a possibly corrupted version of the nth byte of
            // `true_bytes` read from the nth address in `addrs`.  We
            // don't require the sequence of addresses to be
            // contiguous because the data might not be contiguous on
            // disk (e.g., if it wrapped around the log area).
            maybe_corrupted(bytes, true_bytes, addrs)
        }
}


// This enumeration represents the various errors that can be
// returned from log operations. They're self-explanatory.
#[derive(Debug)]
pub enum LogErr {
    InsufficientSpaceForSetup { required_space: u64 },
    StartFailedDueToLogIDMismatch { log_id_expected: u128, log_id_read: u128 },
    StartFailedDueToRegionSizeMismatch { region_size_expected: u64, region_size_read: u64 },
    StartFailedDueToProgramVersionNumberUnsupported { version_number: u64, max_supported: u64 },
    StartFailedDueToInvalidMemoryContents,
    CRCMismatch,
    InsufficientSpaceForAppend { available_space: u64 },
    CantReadBeforeHead { head: u128 },
    CantReadPastTail { tail: u128 },
    CantAdvanceHeadPositionBeforeHead { head: u128 },
    CantAdvanceHeadPositionBeyondTail { tail: u128 },
    PmemErr { err: PmemError } 
}

// This structure, `LogInfo`, is used by `UntrustedLogImpl`
// to store information about a single log. Its fields are:
//
// `log_area_len` -- how many bytes are in the log area on
//     persistent memory
//
// `head` -- the logical position of the log's head
//
// `head_log_area_offset` -- the offset into the log area
//     holding the byte at the head position. This is
//     always equal to `head % log_area_len`, and is
//     cached in this variable to avoid expensive modulo
//     operations.
//
// `log_length` -- the number of bytes in the log beyond the head
//
// `log_plus_pending_length` -- the number of bytes in the log and
//     the pending appends to the log combined
pub struct LogInfo {
    pub log_area_len: u64,
    pub head: u128,
    pub head_log_area_offset: u64,
    pub log_length: u64,
    pub log_plus_pending_length: u64,
}

impl LogInfo {
    pub open spec fn tentatively_append(self, num_bytes: u64) -> Self
    {
        Self{ log_plus_pending_length: (self.log_plus_pending_length + num_bytes) as u64, ..self }
    }
}

pub struct UntrustedLogImpl {
    cdb: bool,
    info: LogInfo,
    state: Ghost<AbstractLogState>
}

impl UntrustedLogImpl {
    pub closed spec fn spec_cdb(self) -> bool 
    {
        self.cdb
    }

    pub closed spec fn spec_info(self) -> LogInfo 
    {
        self.info
    }

    pub open spec fn recover(mem: Seq<u8>, log_start_addr: nat, log_size: nat) -> Option<AbstractLogState> 
    {
        if !metadata_types_set(mem, log_start_addr) {
            None
        } else {
            recover_state(mem, log_start_addr, log_size)
        }
    }

    pub exec fn get_pending_len<Perm, PM>(&self, wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PM>, overall_metadata: &OverallMetadata) -> (out: u64)
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires 
            self.inv(wrpm@, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
        ensures 
            out == self.spec_info().log_plus_pending_length - self.spec_info().log_length,
            out == self@.pending.len(),
    {
        self.info.log_plus_pending_length - self.info.log_length
    }

    // This specification function indicates whether a given view of
    // memory can only crash in a way that, after recovery, leads to a
    // certain abstract state.
    pub open spec fn can_only_crash_as_state(
        pm_region_view: PersistentMemoryRegionView,
        log_start_addr: nat, 
        log_size: nat,
        state: AbstractLogState,
    ) -> bool
    {
        forall |s| #[trigger] pm_region_view.can_crash_as(s) ==>
            UntrustedLogImpl::recover(s, log_start_addr, log_size) == Some(state)
    }

    // This function specifies how to view the in-memory state of
    // `self` as an abstract log state.
    pub closed spec fn view(&self) -> AbstractLogState
    {
        self.state@
    }

    pub closed spec fn inv(self, pm: PersistentMemoryRegionView, log_start_addr: nat, log_size: nat) -> bool
    {
        &&& self@.capacity >= self@.log.len()
        &&& self@.capacity == log_size - spec_log_area_pos()
        &&& no_outstanding_writes_to_metadata(pm, log_start_addr)
        &&& memory_matches_deserialized_cdb(pm, log_start_addr, self.cdb)
        &&& self.info.log_area_len + spec_log_area_pos() == log_size
        &&& log_start_addr + spec_log_area_pos() <= log_start_addr + log_size <= pm.len() <= u64::MAX
        &&& metadata_consistent_with_info(pm, log_start_addr, log_size, self.cdb, self.info)
        &&& info_consistent_with_log_area(pm, log_start_addr, log_size, self.info, self.state@)
        &&& Self::can_only_crash_as_state(pm, log_start_addr, log_size, self.state@.drop_pending_appends())
        &&& metadata_types_set(pm.committed(), log_start_addr)
        &&& self.info.log_plus_pending_length >= self.info.log_length
        &&& self.info.log_plus_pending_length - self.info.log_length == self.state@.pending.len()
    }

    pub proof fn lemma_same_log_view_preserves_invariant<Perm, PM>(
        self,
        wrpm1: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        wrpm2: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        log_start_addr: nat,
        log_size: nat,
        region_size: nat,
    )
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires 
            wrpm1@.len() == region_size,
            wrpm1@.len() == wrpm2@.len(),
            wrpm1.inv(),
            wrpm2.inv(),
            self.inv(wrpm1@, log_start_addr, log_size),
            get_subregion_view(wrpm1@, log_start_addr, log_size) == 
                get_subregion_view(wrpm2@, log_start_addr, log_size),
            0 <= log_start_addr < log_start_addr + log_size <= region_size,
            0 < spec_log_header_area_size() <= spec_log_area_pos() < log_size,
        ensures 
            self.inv(wrpm2@, log_start_addr, log_size)
    {
        lemma_bytes_match_in_equal_subregions(wrpm1@, wrpm2@, log_start_addr, log_size);
        Self::lemma_crash_state_with_matching_log_region_exists(wrpm1@, wrpm2@, log_start_addr, log_size);
        Self::lemma_crash_state_with_matching_log_region_exists(wrpm2@, wrpm1@, log_start_addr, log_size);
        Self::lemma_metadata_types_set_when_views_match_in_log_region(wrpm1@, wrpm2@, log_start_addr, log_size);
        self.lemma_memory_consistent_with_matching_log_region(wrpm1@, wrpm2@, log_start_addr, log_size);
        self.lemma_pm_view_can_only_crash_as_same_log_state_as_matching_view(wrpm1@, wrpm2@, log_start_addr, log_size);
    }

    proof fn lemma_memory_consistent_with_matching_log_region(
        self,
        v1: PersistentMemoryRegionView,
        v2: PersistentMemoryRegionView,
        log_start_addr: nat,
        log_size: nat,
    )
        requires 
            0 <= log_start_addr < log_start_addr + log_size <= v1.len(),
            0 < spec_log_header_area_size() <= spec_log_area_pos() < log_size,
            v1.len() == v2.len(),
            get_subregion_view(v1, log_start_addr, log_size) == 
                get_subregion_view(v2, log_start_addr, log_size),
            memory_matches_deserialized_cdb(v1, log_start_addr, self.cdb),
            metadata_consistent_with_info(v1, log_start_addr, log_size, self.cdb, self.info)
        ensures 
            memory_matches_deserialized_cdb(v2, log_start_addr, self.cdb),
            metadata_consistent_with_info(v2, log_start_addr, log_size, self.cdb, self.info)
    {
        lemma_establish_extract_bytes_equivalence(v1.committed(), v2.committed());
        lemma_bytes_match_in_equal_subregions(v1, v2, log_start_addr, log_size);
    }

    proof fn lemma_pm_view_can_only_crash_as_same_log_state_as_matching_view(
        self,
        v1: PersistentMemoryRegionView,
        v2: PersistentMemoryRegionView,
        log_start_addr: nat,
        log_size: nat,
    )
        requires 
            Self::can_only_crash_as_state(v1, log_start_addr, log_size, self.state@.drop_pending_appends()),
            0 <= log_start_addr < log_start_addr + log_size <= v1.len(),
            v1.len() == v2.len(),
            get_subregion_view(v1, log_start_addr, log_size) == 
                get_subregion_view(v2, log_start_addr, log_size),
            0 < spec_log_header_area_size() <= spec_log_area_pos() < log_size,
        ensures 
            Self::can_only_crash_as_state(v2, log_start_addr, log_size, self.state@.drop_pending_appends())
    {
        let views_must_match_at_addr = |addr: int| log_start_addr <= addr < log_start_addr + log_size;
        lemma_bytes_match_in_equal_subregions(v1, v2, log_start_addr, log_size);
        
        assert forall |s2| #[trigger] v2.can_crash_as(s2) implies 
            Self::recover(s2, log_start_addr, log_size) == Some(self.state@.drop_pending_appends()) 
        by {
            let s1 = lemma_get_crash_state_given_one_for_other_view_same_at_certain_addresses(
                v2, v1, s2, views_must_match_at_addr);
            assert forall |addr: int| log_start_addr <= addr < log_start_addr + log_size implies s1[addr] == s2[addr] by {
                assert(views_must_match_at_addr(addr));
            }
            assert(extract_bytes(s1, log_start_addr, log_size) == extract_bytes(s2, log_start_addr, log_size));
            Self::lemma_same_log_bytes_recover_to_same_state(s1, s2, log_start_addr, log_size);
        }
    }

    pub proof fn lemma_same_log_bytes_recover_to_same_state(
        s1: Seq<u8>,
        s2: Seq<u8>,
        log_start_addr: nat,
        log_size: nat,
    )
        requires 
            0 <= log_start_addr < log_start_addr + log_size <= s1.len(),
            s1.len() == s2.len(),
            0 < spec_log_header_area_size() <= spec_log_area_pos() < log_size,
            extract_bytes(s1, log_start_addr, log_size) == extract_bytes(s2, log_start_addr, log_size),
        ensures 
            Self::recover(s1, log_start_addr, log_size) == Self::recover(s2, log_start_addr, log_size)
    {
        lemma_establish_extract_bytes_equivalence(s1, s2);
        lemma_subrange_of_extract_bytes_equal(s1, log_start_addr, log_start_addr, log_size, u64::spec_size_of());
        let cdb = spec_check_log_cdb(s1, log_start_addr);
        if let Some(cdb) = cdb {
            let metadata_pos = spec_get_active_log_metadata_pos(cdb) + log_start_addr;
            lemma_subrange_of_extract_bytes_equal(s1, log_start_addr, metadata_pos, log_size, LogMetadata::spec_size_of() + u64::spec_size_of());
            lemma_active_metadata_bytes_equal_implies_metadata_types_set(s1, s2, log_start_addr, cdb);
            if metadata_types_set(s1, log_start_addr) {
                let crc_pos = spec_get_active_log_crc_pos(cdb) + log_start_addr;
                lemma_subrange_of_extract_bytes_equal(s1, log_start_addr, crc_pos, log_size, u64::spec_size_of());
                lemma_subrange_of_extract_bytes_equal(s1, log_start_addr, metadata_pos, log_size, LogMetadata::spec_size_of());
                lemma_subrange_of_extract_bytes_equal(s1, log_start_addr, log_start_addr + spec_log_area_pos(), 
                    log_size, (log_size - spec_log_area_pos()) as nat);
            }
        }
    }

    pub proof fn lemma_crash_state_with_matching_log_region_exists(
        v1: PersistentMemoryRegionView,
        v2: PersistentMemoryRegionView,
        log_start_addr: nat,
        log_size: nat,
    )
        requires 
            0 <= log_start_addr < log_start_addr + log_size <= v1.len(),
            0 < spec_log_header_area_size() <= spec_log_area_pos() < log_size,
            v1.len() == v2.len(),
            get_subregion_view(v1, log_start_addr, log_size) == 
                get_subregion_view(v2, log_start_addr, log_size),
        ensures 
            forall |s1| #[trigger] v1.can_crash_as(s1) ==> exists |s2| {
                &&& #[trigger] v2.can_crash_as(s2)
                &&& extract_bytes(s1, log_start_addr, log_size) == 
                        extract_bytes(s2, log_start_addr, log_size)
            }
    {
        let views_must_match_at_addr = |addr: int| log_start_addr <= addr < log_start_addr + log_size;
        assert forall |s1| #[trigger] v1.can_crash_as(s1) implies {
            exists |s2| {
                &&& #[trigger] v2.can_crash_as(s2) 
                &&& extract_bytes(s1, log_start_addr, log_size) == 
                        extract_bytes(s2, log_start_addr, log_size)
            }
        } by {
            lemma_bytes_match_in_equal_subregions(v1, v2, log_start_addr, log_size);
            let s2 = lemma_get_crash_state_given_one_for_other_view_same_at_certain_addresses(
                v1, v2, s1, views_must_match_at_addr);
            assert(v2.can_crash_as(s2));
            lemma_establish_extract_bytes_equivalence(s1, s2);  
            assert(forall |addr: int| views_must_match_at_addr(addr) ==> s1[addr] == s2[addr]);
            assert(extract_bytes(s1, log_start_addr, log_size) =~= 
                extract_bytes(s2, log_start_addr, log_size));         
        }
    }

    pub proof fn lemma_metadata_types_set_when_views_match_in_log_region(
        v1: PersistentMemoryRegionView,
        v2: PersistentMemoryRegionView,
        log_start_addr: nat,
        log_size: nat,
    )
        requires
            metadata_types_set(v1.committed(), log_start_addr),
            ({
                let v1_subregion = get_subregion_view(v1, log_start_addr, log_size);
                let v2_subregion = get_subregion_view(v2, log_start_addr, log_size);
                forall |addr: int| 0 <= addr < v1_subregion.len() ==> 
                    #[trigger] v1.state[addr + log_start_addr] == v2.state[addr + log_start_addr] 
            }),
            forall |addr: int| log_start_addr <= addr < log_start_addr + log_size ==> v1.state[addr] == v2.state[addr],
            0 <= log_start_addr < log_start_addr + log_size <= v1.len(),
            0 < spec_log_header_area_size() <= spec_log_area_pos() < log_size,
            v1.len() == v2.len(),
            spec_check_log_cdb(v1.committed(), log_start_addr) is Some,
        ensures 
            metadata_types_set(v2.committed(), log_start_addr),
    {
            broadcast use pmcopy_axioms;
            let v1_subregion = get_subregion_view(v1, log_start_addr, log_size);
            let v2_subregion = get_subregion_view(v2, log_start_addr, log_size);
            lemma_establish_extract_bytes_equivalence(v1.committed(), v2.committed());

            assert forall |addr: int| 0 <= addr < v1_subregion.len() implies 
                #[trigger] v1.state[addr + log_start_addr].state_at_last_flush == v1.state[addr + log_start_addr].state_at_last_flush
            by {
                assert(v1_subregion.state[addr].state_at_last_flush == v2_subregion.state[addr].state_at_last_flush);
                assert(v1_subregion.state[addr].state_at_last_flush == v1.state[addr + log_start_addr].state_at_last_flush);
                assert(v2_subregion.state[addr].state_at_last_flush == v2.state[addr + log_start_addr].state_at_last_flush);
            }

            lemma_subrange_of_extract_bytes_equal(v1.committed(), log_start_addr, log_start_addr, log_size, u64::spec_size_of());
            let cdb1 = spec_check_log_cdb(v1.committed(), log_start_addr).unwrap();
            let metadata_pos = spec_get_active_log_metadata_pos(cdb1) + log_start_addr;
            lemma_subrange_of_extract_bytes_equal(v1.committed(), log_start_addr, metadata_pos, log_size, LogMetadata::spec_size_of() + u64::spec_size_of());
            assert(extract_bytes(v1.committed(), metadata_pos, LogMetadata::spec_size_of() + u64::spec_size_of()) ==
                extract_bytes(v2.committed(), metadata_pos, LogMetadata::spec_size_of() + u64::spec_size_of()));
            assert(active_metadata_bytes_are_equal(v1.committed(), v2.committed(), log_start_addr));
            lemma_active_metadata_bytes_equal_implies_metadata_types_set(v1.committed(), v2.committed(), log_start_addr, cdb1);
    }

    pub proof fn lemma_same_bytes_preserve_log_invariant<Perm, PM>(
        self,
        wrpm1: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        wrpm2: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        log_start_addr: nat,
        log_size: nat,
        region_size: nat,
    )
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires 
            wrpm1@.len() == region_size,
            wrpm1@.len() == wrpm2@.len(),
            wrpm1.inv(),
            wrpm2.inv(),
            self.inv(wrpm1@, log_start_addr, log_size),
            wrpm1@.no_outstanding_writes(),
            wrpm2@.no_outstanding_writes(),
            self@ == self@.drop_pending_appends(),
            extract_bytes(wrpm1@.committed(), log_start_addr, log_size) == 
                extract_bytes(wrpm2@.committed(), log_start_addr, log_size),
            0 <= log_start_addr < log_start_addr + log_size < region_size,
            0 < spec_log_header_area_size() <= spec_log_area_pos() < log_size,

        ensures 
            self.inv(wrpm2@, log_start_addr, log_size)
    {
        broadcast use pmcopy_axioms;

        let mem1 = wrpm1@.committed();
        let mem2 = wrpm2@.committed();
        lemma_establish_extract_bytes_equivalence(mem1, mem2);

        lemma_same_log_bytes_recover_to_same_state(mem1, mem2, log_start_addr, log_size, region_size);

        lemma_subrange_of_extract_bytes_equal(mem1, log_start_addr, log_start_addr, log_size, u64::spec_size_of());
        let cdb1 = spec_check_log_cdb(mem1, log_start_addr);
        if let Some(cdb1) = cdb1 {
            let metadata_pos = spec_get_active_log_metadata_pos(cdb1); 
            let crc_pos = metadata_pos + LogMetadata::spec_size_of();
            // Proves that metadata, CRC, and log area are the same
            lemma_subrange_of_extract_bytes_equal(mem1, log_start_addr, log_start_addr + metadata_pos, log_size, LogMetadata::spec_size_of());
            lemma_subrange_of_extract_bytes_equal(mem1, log_start_addr, log_start_addr + crc_pos, log_size, u64::spec_size_of());
            lemma_subrange_of_extract_bytes_equal(mem1, log_start_addr, log_start_addr + spec_log_area_pos(), log_size, (log_size - spec_log_area_pos()) as nat);
        } 
        // else, notj are none.

        lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(wrpm2@);

        assert(forall |s| wrpm2@.can_crash_as(s) ==> s == wrpm2@.committed());
        
        let recover1 = UntrustedLogImpl::recover(wrpm1@.committed(), log_start_addr, log_size).unwrap();
        let recover2 = UntrustedLogImpl::recover(wrpm2@.committed(), log_start_addr, log_size).unwrap();
        assert(recover1 == recover2);
        assert(recover1.log == self.state@.drop_pending_appends().log);
        assert(recover1.log == recover2.log);

        assert(Self::can_only_crash_as_state(wrpm2@, log_start_addr, log_size, self.state@.drop_pending_appends()));
        
        assert(forall |pos_relative_to_head: int| {
            let log_area_offset =
                #[trigger] relative_log_pos_to_log_area_offset(pos_relative_to_head,
                                                                self.info.head_log_area_offset as int,
                                                                self.info.log_area_len as int);
            let absolute_addr = log_start_addr + spec_log_area_pos() + log_area_offset;
            let pmb = wrpm1@.state[absolute_addr];
            self.info.log_length <= pos_relative_to_head < self.info.log_plus_pending_length ==>
                    pmb.flush_byte() == self.state@.pending[pos_relative_to_head - self.info.log_length]
        });

        assert(info_consistent_with_log_area(wrpm2@, log_start_addr, log_size, self.info, self.state@));
    }

    // This lemma makes some facts about non-private fields of self visible
    pub proof fn lemma_reveal_log_inv<Perm, PM>(self, pm: WriteRestrictedPersistentMemoryRegion<Perm, PM>, log_start_addr: nat, log_size: nat) 
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires
            self.inv(pm@, log_start_addr, log_size),
        ensures
            log_start_addr + spec_log_area_pos() <= log_start_addr + log_size <= pm@.len() <= u64::MAX,
            metadata_types_set(pm@.committed(), log_start_addr),
            self@.capacity == log_size - spec_log_area_pos()
    {}

    pub proof fn lemma_inv_implies_current_and_recovery_metadata_match<Perm, PM>(
        self,
        wrpm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        log_start_addr: nat,
        log_size: nat
    )
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires 
            self.inv(wrpm_region@, log_start_addr, log_size)
        ensures 
            ({
                let recovery_view = Self::recover(wrpm_region@.committed(), log_start_addr, log_size);
                &&& recovery_view matches Some(recovery_view)
                &&& recovery_view.head == self@.head
                &&& recovery_view.capacity == self@.capacity
            })
    {}

    pub proof fn lemma_all_crash_states_recover_to_drop_pending_appends<Perm, PM>(
        self,
        wrpm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        log_start_addr: nat,
        log_size: nat,
    )
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires 
            self.inv(wrpm_region@, log_start_addr, log_size)
        ensures 
            forall |s| #[trigger] wrpm_region@.can_crash_as(s) ==> 
                UntrustedLogImpl::recover(s, log_start_addr, log_size) == Some(self@.drop_pending_appends())
    {
        broadcast use pmcopy_axioms;
        lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(wrpm_region@);
        assert forall |s| #[trigger] wrpm_region@.can_crash_as(s) implies 
            UntrustedLogImpl::recover(s, log_start_addr, log_size) == Some(self@.drop_pending_appends())
        by {
            let recover_log_state = UntrustedLogImpl::recover(s, log_start_addr, log_size).unwrap();
            let current_state = UntrustedLogImpl::recover(wrpm_region@.committed(), log_start_addr, log_size).unwrap();
    
            assert(extract_bytes(s, log_start_addr, spec_log_area_pos()) == extract_bytes(wrpm_region@.committed(), log_start_addr, spec_log_area_pos()));
            assert(extract_bytes(s, log_start_addr, u64::spec_size_of()) == extract_bytes(wrpm_region@.committed(), log_start_addr, u64::spec_size_of()));
    
            let current_cdb = recover_cdb(wrpm_region@.committed(), log_start_addr);
            let recover_cdb = recover_cdb(s, log_start_addr);
            assert(current_cdb == recover_cdb);
    
            let metadata_pos = spec_get_active_log_metadata_pos(current_cdb.unwrap());
            let crc_pos = spec_get_active_log_crc_pos(current_cdb.unwrap());
            lemma_metadata_fits_in_log_header_area();
            lemma_subrange_of_extract_bytes_equal(s, log_start_addr, metadata_pos + log_start_addr, spec_log_area_pos(), LogMetadata::spec_size_of());
            assert(extract_bytes(s, metadata_pos + log_start_addr, LogMetadata::spec_size_of()) == extract_bytes(wrpm_region@.committed(), metadata_pos + log_start_addr, LogMetadata::spec_size_of()));
            assert(extract_bytes(s, crc_pos + log_start_addr, u64::spec_size_of()) == extract_bytes(wrpm_region@.committed(), crc_pos + log_start_addr, u64::spec_size_of()));
    
            let current_metadata = spec_get_active_log_metadata(wrpm_region@.committed(), log_start_addr, current_cdb.unwrap());
            let recover_metadata = spec_get_active_log_metadata(s, log_start_addr, current_cdb.unwrap());
            assert(current_metadata == recover_metadata);
    
            let recovered_crash_log = recover_log(s, log_start_addr, log_size, current_metadata.head as int, current_metadata.log_length as int).unwrap();
            let recovered_current_log = recover_log(wrpm_region@.committed(), log_start_addr, log_size, current_metadata.head as int, current_metadata.log_length as int).unwrap();
            assert(recovered_crash_log == recovered_current_log);
            assert(self@.log == recovered_current_log.log);
    
            self.lemma_reveal_log_inv(wrpm_region, log_start_addr, log_size);
    
            self.lemma_inv_implies_current_and_recovery_metadata_match(wrpm_region, log_start_addr, log_size);
        }
    }

    // This lemma proves that updating the inactive metadata and crc is crash safe.
    #[verifier::rlimit(20)] // TODO: @hayley - obviating this rlimit expansion
    proof fn lemma_update_inactive_metadata_and_crc_crash_states_allowed_by_perm<Perm>(
        self,
        old_pm: PersistentMemoryRegionView,
        new_pm1: PersistentMemoryRegionView,
        new_pm2: PersistentMemoryRegionView,
        new_metadata: LogMetadata,
        inactive_metadata_pos: int,
        new_crc: u64,
        inactive_crc_pos: int,
        log_start_addr: nat,
        log_size: nat,
        prev_info: LogInfo,
        prev_state: AbstractLogState,
        perm: &Perm,
        crash_pred: spec_fn(Seq<u8>) -> bool,
    )
        where 
            Perm: CheckPermission<Seq<u8>>,
        requires 
            new_pm1 == old_pm.write(inactive_metadata_pos, new_metadata.spec_to_bytes()),
            new_pm2 == old_pm.write(inactive_metadata_pos, new_metadata.spec_to_bytes()).write(inactive_crc_pos, new_crc.spec_to_bytes()),
            forall |s| #[trigger] old_pm.can_crash_as(s) ==> crash_pred(s),
            log_start_addr as int % const_persistence_chunk_size() == 0,
            log_size as int % const_persistence_chunk_size() == 0,
            info_consistent_with_log_area(old_pm, log_start_addr as nat, log_size as nat, prev_info, prev_state),
            no_outstanding_writes_to_metadata(old_pm, log_start_addr as nat),
            metadata_consistent_with_info(old_pm, log_start_addr as nat, log_size as nat, self.cdb, prev_info),
            memory_matches_deserialized_cdb(old_pm, log_start_addr as nat, self.cdb),
            metadata_types_set(old_pm.committed(), log_start_addr as nat),
            inactive_crc_pos == spec_get_inactive_log_crc_pos(self.cdb) + log_start_addr,
            inactive_metadata_pos == spec_get_inactive_log_metadata_pos(self.cdb) + log_start_addr,
            forall |s1: Seq<u8>, s2: Seq<u8>| {
                &&& s1.len() == s2.len() 
                &&& #[trigger] crash_pred(s1)
                &&& states_differ_only_in_log_region(s1, s2, log_start_addr as nat, log_size as nat)
                &&& Self::recover(s1, log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends())
                &&& Self::recover(s2, log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends()) // or committed?
            } ==> #[trigger] crash_pred(s2),
            forall |s| crash_pred(s) ==> perm.check_permission(s),
            forall |s| #[trigger] old_pm.can_crash_as(s) ==> 
                UntrustedLogImpl::recover(s, log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends())
        ensures 
            forall |s| #[trigger] new_pm1.can_crash_as(s) ==> crash_pred(s),
            forall |s| #[trigger] new_pm2.can_crash_as(s) ==> crash_pred(s)
    {
        broadcast use pmcopy_axioms;
        lemma_metadata_fits_in_log_header_area();

        assert forall |s| #[trigger] new_pm1.can_crash_as(s) implies crash_pred(s) by {
            lemma_establish_extract_bytes_equivalence(s, old_pm.committed());
            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(new_pm1);
            assert(UntrustedLogImpl::recover(s, log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends()));
            lemma_crash_state_differing_only_in_log_region_exists(old_pm, new_pm1, 
                inactive_metadata_pos as int, new_metadata.spec_to_bytes(), log_start_addr as nat, log_size as nat);
        }

        assert forall |s| #[trigger] new_pm2.can_crash_as(s) implies crash_pred(s) by {
            lemma_establish_extract_bytes_equivalence(s, old_pm.committed());
            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(new_pm2);
            assert(UntrustedLogImpl::recover(s, log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends()));
            lemma_crash_state_differing_only_in_log_region_exists_wrapping(old_pm, new_pm2, 
                inactive_metadata_pos, new_metadata.spec_to_bytes(), inactive_crc_pos, 
                new_crc.spec_to_bytes(), log_start_addr as nat, log_size as nat);
        }
    }

    // This lemma proves that a write to WRPM for a non-wrapping log append is crash safe
    proof fn lemma_tentatively_append_is_crash_safe<Perm, PM>(
        self,
        wrpm_region:  WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        log_start_addr: nat,
        log_size: nat,
        write_addr: int,
        bytes_to_append: Seq<u8>,
        is_writable_absolute_addr: spec_fn(int) -> bool,
        crash_pred: spec_fn(Seq<u8>) -> bool,
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires
            // TODO: refactor/clean up; much of this is the same as precond of tentatively_append_to_log
            self.inv(wrpm_region@, log_start_addr, log_size),
            wrpm_region.inv(),
            no_outstanding_writes_to_metadata(wrpm_region@, log_start_addr),
            memory_matches_deserialized_cdb(wrpm_region@, log_start_addr, self.cdb),
            metadata_consistent_with_info(wrpm_region@, log_start_addr, log_size, self.cdb, self.info),
            info_consistent_with_log_area(wrpm_region@, log_start_addr, log_size, self.info, self.state@),
            metadata_types_set(wrpm_region@.committed(), log_start_addr),
            log_start_addr + spec_log_header_area_size() < log_start_addr + spec_log_area_pos() <= wrpm_region@.len(),
            forall |addr: int| #[trigger] is_writable_absolute_addr(addr) <==> {
                &&& log_start_addr + spec_log_area_pos() <= addr < log_start_addr + spec_log_area_pos() + log_size
                &&& log_area_offset_unreachable_during_recovery(self.info.head_log_area_offset as int,
                        self.info.log_area_len as int,
                        self.info.log_length as int,
                        addr - (log_start_addr + spec_log_area_pos()))
            },
            forall |i: int| log_start_addr <= i < log_start_addr + spec_log_area_pos() ==> !(#[trigger] is_writable_absolute_addr(i)),
            log_size == self.info.log_area_len + spec_log_area_pos(),
            log_start_addr < log_start_addr + spec_log_header_area_size() < log_start_addr + spec_log_area_pos(),
            bytes_to_append.len() <= self.info.log_area_len - self.info.log_plus_pending_length,
            self.info.head + self.info.log_plus_pending_length + bytes_to_append.len() <= u128::MAX,
            write_addr == relative_log_pos_to_log_area_offset(self.info.log_plus_pending_length as int,
                                self.info.head_log_area_offset as int, self.info.log_area_len as int),
            bytes_to_append.len() > 0,
            log_start_addr as int % const_persistence_chunk_size() == 0,
            log_size as int % const_persistence_chunk_size() == 0,
            forall |s| #[trigger] wrpm_region@.can_crash_as(s) ==> crash_pred(s),
            forall |s1: Seq<u8>, s2: Seq<u8>| {
                &&& s1.len() == s2.len() 
                &&& #[trigger] crash_pred(s1)
                &&& states_differ_only_in_log_region(s1, s2, log_start_addr as nat, log_size as nat)
                &&& Self::recover(s1, log_start_addr as nat, log_size as nat) == Some(self@.drop_pending_appends())
                &&& Self::recover(s2, log_start_addr as nat, log_size as nat) == Some(self@.drop_pending_appends())
            } ==> #[trigger] crash_pred(s2),
            forall |s| #[trigger] wrpm_region@.can_crash_as(s) ==> 
                UntrustedLogImpl::recover(s, log_start_addr as nat, log_size as nat) == Some(self.state@.drop_pending_appends()),
            ({
                ||| {
                        &&& self.info.log_plus_pending_length >= self.info.log_area_len - self.info.head_log_area_offset
                        &&& write_addr == self.info.log_plus_pending_length - (self.info.log_area_len - self.info.head_log_area_offset)
                    }
                ||| {
                        &&& bytes_to_append.len() <= self.info.log_area_len - self.info.head_log_area_offset - self.info.log_plus_pending_length
                        &&& write_addr == self.info.log_plus_pending_length + self.info.head_log_area_offset
                    }
            }),
        ensures 
            ({
                let log_area_start_addr = log_start_addr + spec_log_area_pos();
                let new_pm = wrpm_region@.write(log_area_start_addr + write_addr, bytes_to_append);
                &&& forall |s2| #[trigger] new_pm.can_crash_as(s2) ==> crash_pred(s2)
                &&& forall |s| #[trigger] new_pm.can_crash_as(s) ==> 
                        UntrustedLogImpl::recover(s, log_start_addr, log_size) == Some(self.state@.drop_pending_appends())
                &&& Self::can_only_crash_as_state(wrpm_region@, log_start_addr, log_size, self.state@.drop_pending_appends())
            })

    {
        let log_area_start_addr = log_start_addr + spec_log_area_pos();
        let new_pm = wrpm_region@.write(log_area_start_addr + write_addr, bytes_to_append);
        assert(views_differ_only_where_subregion_allows(wrpm_region@, new_pm, log_start_addr + spec_log_area_pos(),
                                                    self.info.log_area_len as nat, is_writable_absolute_addr));
        lemma_append_crash_states_do_not_modify_reachable_state(
            wrpm_region@, new_pm, log_start_addr, log_size, self.info, 
            self.state@, self.cdb, is_writable_absolute_addr
        );
        assert forall |s2| #[trigger] new_pm.can_crash_as(s2) implies crash_pred(s2) by {
            lemma_crash_state_differing_only_in_log_region_exists(wrpm_region@, new_pm, 
                log_area_start_addr + write_addr, bytes_to_append, log_start_addr, log_size);
            let witness = choose |s1: Seq<u8>| {
                &&& wrpm_region@.can_crash_as(s1)
                &&& #[trigger] s1.len() == s2.len()
                &&& states_differ_only_in_log_region(s1, s2, log_start_addr, log_size)
            };
            assert(wrpm_region@.can_crash_as(witness));
            assert(crash_pred(witness));
        }
    }

    pub exec fn setup<PM, K>(
        pm_region: &mut PM,
        log_start_addr: u64,
        log_size: u64, 
    ) -> (result: Result<(), crate::kv::kvimpl_t::KvError<K>>) 
        where 
            PM: PersistentMemoryRegion,
            K: std::fmt::Debug,
        requires 
            old(pm_region).inv(),
            log_start_addr + log_size <= old(pm_region)@.len() <= u64::MAX,
            old(pm_region)@.no_outstanding_writes_in_range(log_start_addr as int, log_start_addr + log_size),
            log_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE
        ensures 
            pm_region.inv(),
            ({
                // Bytes outside the specified log region have not changed
                let old_pm_bytes = old(pm_region)@.flush().committed();
                let new_pm_bytes = pm_region@.flush().committed();
                &&& extract_bytes(new_pm_bytes, 0, log_start_addr as nat) == extract_bytes(old_pm_bytes, 0, log_start_addr as nat)
                &&& extract_bytes(new_pm_bytes, (log_start_addr + log_size) as nat, (pm_region@.len() - (log_start_addr + log_size)) as nat) == 
                        extract_bytes(old_pm_bytes, (log_start_addr + log_size) as nat, (pm_region@.len() - (log_start_addr + log_size)) as nat)
            }),
            match result {
                Ok(()) => {
                    let pm = pm_region@.flush().committed();
                    let state = AbstractLogState::initialize(log_size - spec_log_area_pos());
                    &&& Self::recover(pm, log_start_addr as nat, log_size as nat) matches Some(recovered_state)
                    &&& state == recovered_state
                    &&& pm_region@.len() == old(pm_region)@.len()
                }
                Err(_) => false
            } 
    {
        // Initialize CDB and log metadata
        let log_metadata = LogMetadata {
            head: 0,
            log_length: 0
        };
        let log_crc = calculate_crc(&log_metadata);
        let log_cdb = CDB_FALSE;

        assert(spec_log_area_pos() >= spec_log_header_area_size()) by {
            reveal(spec_padding_needed);
        }

        // Write the CDB, metadata, and CRC to PM. Since PM isn't write restricted right now,
        // we don't have to prove that these updates are crash safe.
        pm_region.serialize_and_write(log_start_addr, &log_cdb);
        pm_region.serialize_and_write(log_start_addr + log_header_pos_cdb_false(), &log_metadata);
        pm_region.serialize_and_write(log_start_addr + log_header_pos_cdb_false() + size_of::<LogMetadata>() as u64, &log_crc);

        proof { 
            broadcast use pmcopy_axioms;

            // Prove that we have not modified any bytes that do not fall in the log region
            lemma_establish_extract_bytes_equivalence(old(pm_region)@.flush().committed(), pm_region@.flush().committed()); 

            // Prove that the resulting log, when recovered, is initialized
            let pm = pm_region@.flush().committed();
            let log_region = extract_bytes(pm, log_start_addr as nat, log_size as nat);
            let recovered_state = Self::recover(pm, log_start_addr as nat, log_size as nat);
            
            // Prove that we can recover a valid log
            // First, prove that the return value of recover is not None
            assert(log_region.len() > u64::spec_size_of());

            // Prove that we wrote a valid CDB
            let cdb_bytes = extract_bytes(pm, log_start_addr as nat, u64::spec_size_of());
            assert(cdb_bytes == log_cdb.spec_to_bytes());
            lemma_subrange_of_extract_bytes_equal(pm, log_start_addr as nat, log_start_addr as nat, log_size as nat, u64::spec_size_of());
            let cdb = if log_cdb == CDB_FALSE { false } else { true };

            // Prove that the CRC we wrote matches the metadata that we wrote
            let metadata = spec_get_active_log_metadata(pm, log_start_addr as nat, cdb);
            let metadata_bytes = extract_bytes(pm, (log_start_addr + spec_log_header_pos_cdb_false()) as nat, LogMetadata::spec_size_of());
            let crc = spec_get_active_log_crc(pm, log_start_addr as nat, cdb);
            let crc_bytes = extract_bytes(pm, (log_start_addr + spec_log_header_pos_cdb_false() + LogMetadata::spec_size_of()) as nat, u64::spec_size_of());
            assert(metadata_bytes == log_metadata.spec_to_bytes());
            lemma_subrange_of_extract_bytes_equal(pm, log_start_addr as nat, (log_start_addr + spec_log_header_pos_cdb_false()) as nat, log_size as nat, LogMetadata::spec_size_of());
            lemma_subrange_of_extract_bytes_equal(pm, 
                log_start_addr as nat, 
                (log_start_addr + spec_log_header_pos_cdb_false() + LogMetadata::spec_size_of()) as nat,
                log_size as nat, 
                u64::spec_size_of());
            assert(crc == metadata.spec_crc());

            // Once we have proven that the log recovers to a valid abstract state, extensional equality takes care of the rest of the proof
            assert(recovered_state is Some);
            assert(recovered_state.unwrap() =~= AbstractLogState::initialize(log_size - spec_log_area_pos()));
        }
    
        Ok(())
    }

    // TODO: rename TrustedKvPermission to TrustedPermission
    // or use a trait
    pub fn start<Perm, PM>(
        pm_region: &WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        log_start_addr: u64,
        log_size: u64, 
        Ghost(state): Ghost<AbstractLogState>,
    ) -> (result: Result<Self, LogErr>)
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires
            Self::recover(pm_region@.committed(), log_start_addr as nat, log_size as nat) == Some(state),
            pm_region.inv(),
            pm_region@.no_outstanding_writes(),
            log_start_addr + log_size <= pm_region@.len() <= u64::MAX,
            log_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
            state == state.drop_pending_appends(),
        ensures
            ({
                match result {
                    Ok(log_impl) => {
                        &&& log_impl@ == state
                        &&& log_impl.inv(pm_region@, log_start_addr as nat, log_size as nat)
                    }
                    Err(LogErr::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                    Err(e) => e == LogErr::PmemErr{ err: PmemError::AccessOutOfRange },
                }
            })   
    {
        // First, we read the corruption-detecting boolean and
        // return an error if that fails.

        let cdb = read_cdb(pm_region.get_pm_region_ref(), log_start_addr, log_size)?;

        let info = read_log_variables(pm_region.get_pm_region_ref(), log_start_addr, log_size, cdb)?;

        proof {
            // prove that we establish the part of the invariant that says that the only possible crash state is the one
            // with all pending appends dropped
            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(pm_region@);
            assert(forall |s| pm_region@.can_crash_as(s) ==> s == pm_region@.committed());
        }

        Ok(Self { cdb, info, state: Ghost(state) })
    }  

    // The `tentatively_append_to_log` method is called by
    // `tentatively_append` to perform writes to the log area.
    // It's passed a `subregion` that frames access to only that
    // log area, and only to offsets within that log area that are
    // unreachable during recovery.
    exec fn tentatively_append_to_log<Perm, PMRegion>(
        &self,
        wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        log_start_addr: u64,
        log_size: u64,
        bytes_to_append: &[u8],
        Ghost(crash_pred): Ghost<spec_fn(Seq<u8>) -> bool>,
        Tracked(perm): Tracked<&Perm>,
        Ghost(is_writable_absolute_addr): Ghost<spec_fn(int) -> bool>,
    ) -> (result: Result<u128, LogErr>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old(wrpm_region)@, log_start_addr as nat, log_size as nat),
            bytes_to_append.len() <= self.info.log_area_len - self.info.log_plus_pending_length,
            self.info.head + self.info.log_plus_pending_length + bytes_to_append.len() <= u128::MAX,
            old(wrpm_region).inv(),
            log_size == self.info.log_area_len + spec_log_area_pos(),
            metadata_consistent_with_info(old(wrpm_region)@, log_start_addr as nat, log_size as nat, self.cdb, self.info),
            info_consistent_with_log_area(old(wrpm_region)@, log_start_addr as nat, log_size as nat, self.info, self.state@),
            forall |addr: int|
                #[trigger] is_writable_absolute_addr(addr) <==> {
                    &&& log_start_addr + spec_log_area_pos() <= addr < log_start_addr + spec_log_area_pos() + log_size
                    &&& log_area_offset_unreachable_during_recovery(self.info.head_log_area_offset as int,
                            self.info.log_area_len as int,
                            self.info.log_length as int,
                            addr - (log_start_addr + spec_log_area_pos()))
                },
            log_start_addr < log_start_addr + spec_log_header_area_size() < log_start_addr + spec_log_area_pos(),
            no_outstanding_writes_to_metadata(old(wrpm_region)@, log_start_addr as nat),
            log_start_addr as int % const_persistence_chunk_size() == 0,
            log_size as int % const_persistence_chunk_size() == 0,
            forall |s| #[trigger] old(wrpm_region)@.can_crash_as(s) ==> crash_pred(s),
            forall |s| #[trigger] old(wrpm_region)@.can_crash_as(s) ==> 
                Self::recover(s, log_start_addr as nat, log_size as nat) == Some(self@.drop_pending_appends()),
            forall |s1: Seq<u8>, s2: Seq<u8>| {
                &&& s1.len() == s2.len() 
                &&& #[trigger] crash_pred(s1)
                &&& states_differ_only_in_log_region(s1, s2, log_start_addr as nat, log_size as nat)
                &&& Self::recover(s1, log_start_addr as nat, log_size as nat) == Some(self@.drop_pending_appends())
                &&& Self::recover(s2, log_start_addr as nat, log_size as nat) == Some(self@.drop_pending_appends())
            } ==> #[trigger] crash_pred(s2),
            forall |s| crash_pred(s) ==> perm.check_permission(s),
        ensures
            spec_check_log_cdb(wrpm_region@.committed(), log_start_addr as nat) == spec_check_log_cdb(old(wrpm_region)@.committed(), log_start_addr as nat),
            wrpm_region.inv(),
            no_outstanding_writes_to_metadata(wrpm_region@, log_start_addr as nat),
            log_start_addr + spec_log_area_pos() <= log_start_addr + log_size <= wrpm_region@.len() <= u64::MAX,
            wrpm_region.constants() == old(wrpm_region).constants(),
            wrpm_region@.len() == old(wrpm_region)@.len(),
            Self::recover(old(wrpm_region)@.committed(), log_start_addr as nat, log_size as nat) 
                == Self::recover(wrpm_region@.committed(), log_start_addr as nat, log_size as nat),
            views_differ_only_in_log_region(old(wrpm_region)@, wrpm_region@, 
                log_start_addr as nat, log_size as nat),
            Self::can_only_crash_as_state(wrpm_region@, log_start_addr as nat, log_size as nat, self@.drop_pending_appends()),
            forall |s| #[trigger] wrpm_region@.can_crash_as(s) ==> crash_pred(s),
            states_differ_only_in_log_region(old(wrpm_region)@.flush().committed(), wrpm_region@.flush().committed(), log_start_addr as nat, log_size as nat),
            match result {
                Ok(offset) => {
                    &&& offset == self.info.head + self.info.log_plus_pending_length
                    &&& info_consistent_with_log_area(
                        wrpm_region@,
                        log_start_addr as nat,
                        log_size as nat,
                        self.info.tentatively_append(bytes_to_append.len() as u64),
                        self.state@.tentatively_append(bytes_to_append@)
                    )
                    &&& metadata_consistent_with_info(wrpm_region@, log_start_addr as nat, log_size as nat, self.cdb, self.info)
                    &&& metadata_types_set(wrpm_region@.committed(), log_start_addr as nat)
                },
                Err(LogErr::InsufficientSpaceForAppend { available_space }) => {
                    &&& wrpm_region@ == old(wrpm_region)@
                    &&& available_space < bytes_to_append@.len()
                    &&& {
                            ||| available_space == self@.capacity - self@.log.len() - self@.pending.len()
                            ||| available_space == u128::MAX - self@.head - self@.log.len() - self@.pending.len()
                        }
                },
                _ => false
            }
    {
        let info = &self.info;
        let log_area_start_addr = log_start_addr + log_area_pos();
        let ghost old_wrpm_region = wrpm_region@;

        // writable fn should not allow changes to metadata
        assert(forall |i: int| log_start_addr <= i < log_start_addr + spec_log_area_pos() ==> !(#[trigger] is_writable_absolute_addr(i)));

        // Compute the current logical offset of the end of the
        // log, including any earlier pending appends. This is the
        // offset at which we'll be logically appending, and so is
        // the offset we're expected to return. After all, the
        // caller wants to know what virtual log position they
        // need to use to read this data in the future.

        let old_pending_tail: u128 = info.head + info.log_plus_pending_length as u128;

        // The simple case is that we're being asked to append the
        // empty string. If so, do nothing and return.

        let num_bytes: u64 = bytes_to_append.len() as u64;
        if num_bytes == 0 {
            return Ok(old_pending_tail);
        }

        let ghost state = self.state@;

        // If the number of bytes in the log plus pending appends
        // is at least as many bytes as are beyond the head in the
        // log area, there's obviously enough room to append all
        // the bytes without wrapping. So just write the bytes
        // there.

        if info.log_plus_pending_length >= info.log_area_len - info.head_log_area_offset {

            // We could compute the address to write to with:
            //
            // `write_addr = old_pending_tail % info.log_area_len;`
            //
            // But we can replace the expensive modulo operation above with two subtraction
            // operations as follows. This is somewhat subtle, but we have verification backing
            // us up and proving this optimization correct.

            let write_addr: u64 =
                info.log_plus_pending_length - (info.log_area_len - info.head_log_area_offset);
            assert(write_addr ==
                    relative_log_pos_to_log_area_offset(info.log_plus_pending_length as int,
                                                        info.head_log_area_offset as int,
                                                        info.log_area_len as int));

            proof {
                lemma_tentatively_append(wrpm_region@, bytes_to_append@, log_start_addr as nat, log_size as nat, self.info, self.state@);
                self.lemma_tentatively_append_is_crash_safe(*wrpm_region, log_start_addr as nat, log_size as nat, 
                    write_addr as int, bytes_to_append@, is_writable_absolute_addr, crash_pred);
            }
            wrpm_region.write(log_area_start_addr + write_addr, &bytes_to_append, Tracked(perm));
        }
        else {
            // We could compute the address to write to with:
            //
            // `write_addr = old_pending_tail % info.log_area_len`
            //
            // But we can replace the expensive modulo operation above with an addition
            // operation as follows. This is somewhat subtle, but we have verification backing
            // us up and proving this optimization correct.

            let write_addr: u64 = info.log_plus_pending_length + info.head_log_area_offset;
            assert(write_addr ==
                    relative_log_pos_to_log_area_offset(info.log_plus_pending_length as int,
                                                        info.head_log_area_offset as int,
                                                        info.log_area_len as int));

            // There's limited space beyond the pending bytes in the log area, so as we write
            // the bytes we may have to wrap around the end of the log area. So we must compute
            // how many bytes we can write without having to wrap:

            let max_len_without_wrapping: u64 =
                info.log_area_len - info.head_log_area_offset - info.log_plus_pending_length;
            assert(max_len_without_wrapping == info.log_area_len -
                    relative_log_pos_to_log_area_offset(info.log_plus_pending_length as int,
                                                        info.head_log_area_offset as int, info.log_area_len as int));

            if num_bytes <= max_len_without_wrapping {

                // If there's room for all the bytes we need to write, we just need one write.
                proof {
                    lemma_tentatively_append(wrpm_region@, bytes_to_append@, log_start_addr as nat, log_size as nat, self.info, self.state@);
                    self.lemma_tentatively_append_is_crash_safe(*wrpm_region, log_start_addr as nat, log_size as nat, 
                        write_addr as int, bytes_to_append@, is_writable_absolute_addr, crash_pred);
                }
                wrpm_region.write(log_area_start_addr + write_addr, &bytes_to_append, Tracked(perm));
            }
            else {

                // If there isn't room for all the bytes we need to write, we need two writes,
                // one writing the first `max_len_without_wrapping` bytes to address
                // `write_addr` and the other writing the remaining bytes to the beginning of
                // the log area.
                //
                // There are a lot of things we have to prove about these writes, like the fact
                // that they're both permitted by `perm`. We offload those proofs to a lemma in
                // `append_v.rs` that we invoke here.

                proof {
                    lemma_tentatively_append_wrapping(wrpm_region@, bytes_to_append@, log_start_addr as nat, log_size as nat, self.info, self.state@);

                    let new_pm1 = wrpm_region@.write(log_area_start_addr + write_addr, extract_bytes(bytes_to_append@, 
                        0, max_len_without_wrapping as nat));
                    let new_pm2 = new_pm1.write(log_area_start_addr as int, extract_bytes(bytes_to_append@, 
                        max_len_without_wrapping as nat, (bytes_to_append@.len() - max_len_without_wrapping) as nat));

                    lemma_append_crash_states_do_not_modify_reachable_state(
                        wrpm_region@, new_pm2, log_start_addr as nat, log_size as nat, 
                        self.info, self.state@, self.cdb, is_writable_absolute_addr
                    );
                    
                    assert forall |s2| #[trigger] new_pm1.can_crash_as(s2) implies crash_pred(s2) by {
                         lemma_append_crash_states_do_not_modify_reachable_state(
                            wrpm_region@, new_pm1, log_start_addr as nat, log_size as nat, 
                            self.info, self.state@, self.cdb, is_writable_absolute_addr
                        );
                        assert(Self::recover(s2, log_start_addr as nat, log_size as nat) == Some(self@.drop_pending_appends()));
                        lemma_crash_state_differing_only_in_log_region_exists(wrpm_region@, new_pm1, 
                            log_area_start_addr + write_addr, extract_bytes(bytes_to_append@, 0, max_len_without_wrapping as nat), 
                            log_start_addr as nat, log_size as nat);
                    }

                    assert forall |s2| #[trigger] new_pm2.can_crash_as(s2) implies crash_pred(s2) by {
                        assert(Self::recover(s2, log_start_addr as nat, log_size as nat) == Some(self@.drop_pending_appends()));
                        lemma_crash_state_differing_only_in_log_region_exists_wrapping(wrpm_region@, new_pm2, 
                            log_area_start_addr + write_addr, extract_bytes(bytes_to_append@, 0, max_len_without_wrapping as nat), 
                            log_area_start_addr as int, 
                            extract_bytes(bytes_to_append@, max_len_without_wrapping as nat, (bytes_to_append@.len() - max_len_without_wrapping) as nat), 
                            log_start_addr as nat, log_size as nat);
                    }
                }
                wrpm_region.write(log_area_start_addr + write_addr, slice_subrange(bytes_to_append, 0, max_len_without_wrapping as usize), Tracked(perm));
                wrpm_region.write(log_area_start_addr, slice_subrange(bytes_to_append, max_len_without_wrapping as usize, bytes_to_append.len()), Tracked(perm));
            }
        }

        proof {
            // Proves that the log metadata is unchanged by the tentative append
            lemma_establish_extract_bytes_equivalence(wrpm_region@.committed(), old_wrpm_region.committed());
        }

        Ok(old_pending_tail)
    }

    // The `tentatively_append` method tentatively appends
    // `bytes_to_append` to the end of the log. It's tentative in
    // that crashes will undo the appends, and reads aren't
    // allowed in the tentative part of the log. See `README.md` for
    // more documentation and examples of its use.
    //
    // This method is passed a write-restricted persistent memory
    // region `wrpm_region`. This restricts how it can write
    // `wrpm_region`. It's only given permission (in `perm`) to
    // write if it can prove that any crash after initiating the
    // write is safe. That is, any such crash must put the memory
    // in a state that recovers as the current abstract state with
    // all pending appends dropped.
    pub exec fn tentatively_append<Perm, PM>(
        &mut self,
        wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        log_start_addr: u64,
        log_size: u64,
        bytes_to_append: &[u8],
        Ghost(crash_pred): Ghost<spec_fn(Seq<u8>) -> bool>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<u128, LogErr>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires
            old(self).inv(old(wrpm_region)@, log_start_addr as nat, log_size as nat),
            old(wrpm_region).inv(),
            log_start_addr as int % const_persistence_chunk_size() == 0,
            log_size as int % const_persistence_chunk_size() == 0,
            forall |s| #[trigger] old(wrpm_region)@.can_crash_as(s) ==> crash_pred(s),
            forall |s| #[trigger] old(wrpm_region)@.can_crash_as(s) ==> 
                Self::recover(s, log_start_addr as nat, log_size as nat) == Some(old(self)@.drop_pending_appends()),
            forall |s1: Seq<u8>, s2: Seq<u8>| {
                &&& s1.len() == s2.len() 
                &&& #[trigger] crash_pred(s1)
                &&& states_differ_only_in_log_region(s1, s2, log_start_addr as nat, log_size as nat)
                &&& Self::recover(s1, log_start_addr as nat, log_size as nat) == Some(old(self)@.drop_pending_appends())
                &&& Self::recover(s2, log_start_addr as nat, log_size as nat) == Some(old(self)@.drop_pending_appends())
            } ==> #[trigger] crash_pred(s2),
            forall |s| crash_pred(s) ==> perm.check_permission(s),
            no_outstanding_writes_to_metadata(old(wrpm_region)@, log_start_addr as nat),
        ensures
            self.inv(wrpm_region@, log_start_addr as nat, log_size as nat),
            wrpm_region@.len() == old(wrpm_region)@.len(),
            wrpm_region.constants() == old(wrpm_region).constants(),
            wrpm_region.inv(),
            forall |s| #[trigger] wrpm_region@.can_crash_as(s) ==> crash_pred(s),
            Self::recover(old(wrpm_region)@.committed(), log_start_addr as nat, log_size as nat) 
                == Self::recover(wrpm_region@.committed(), log_start_addr as nat, log_size as nat),
            views_differ_only_in_log_region(old(wrpm_region)@, wrpm_region@, 
                log_start_addr as nat, log_size as nat),
            Self::can_only_crash_as_state(wrpm_region@, log_start_addr as nat, log_size as nat, self@.drop_pending_appends()),
            no_outstanding_writes_to_metadata(wrpm_region@, log_start_addr as nat),
            states_differ_only_in_log_region(old(wrpm_region)@.flush().committed(), wrpm_region@.flush().committed(), log_start_addr as nat, log_size as nat),
            match result {
                Ok(offset) => {
                    let state = old(self)@;
                    &&& offset == state.head + state.log.len() + state.pending.len()
                    &&& self@ == old(self)@.tentatively_append(bytes_to_append@)
                },
                Err(LogErr::InsufficientSpaceForAppend { available_space }) => {
                    &&& self@ == old(self)@
                    &&& wrpm_region@ == old(wrpm_region)@
                    &&& available_space < bytes_to_append@.len()
                    &&& {
                            ||| available_space == self@.capacity - self@.log.len() - self@.pending.len()
                            ||| available_space == u128::MAX - self@.head - self@.log.len() - self@.pending.len()
                        }
                },
                _ => false
            },
    {
        // One useful invariant implies that
        // `info.log_plus_pending_length <= info.log_area_len`, so
        // we know we can safely do the following subtraction
        // without underflow.

        let info = &self.info;
        let available_space: u64 = info.log_area_len - info.log_plus_pending_length as u64;

        // Check to make sure we have enough available space, and
        // return an error otherwise. There are two ways we might
        // not have available space. The first is that doing the
        // append would overfill the log area. The second (which
        // will probably never happen) is that doing this append
        // and a subsequent commit would make the logical tail
        // exceed u128::MAX.

        let num_bytes: u64 = bytes_to_append.len() as u64;
        if num_bytes > available_space {
            return Err(LogErr::InsufficientSpaceForAppend{ available_space })
        }
        if num_bytes as u128 > u128::MAX - info.log_plus_pending_length as u128 - info.head {
            return Err(LogErr::InsufficientSpaceForAppend{
                available_space: (u128::MAX - info.log_plus_pending_length as u128 - info.head) as u64
            })
        }

        // Create a closure that indicates which bytes in the log region we are allowed to write to.
        // We'll use this in the same way that subregions do to prove that the append is crash consistent.

        let ghost is_writable_absolute_addr_fn = |addr: int| {
            &&& log_start_addr + spec_log_area_pos() <= addr < log_start_addr + spec_log_area_pos() + log_size
            &&& log_area_offset_unreachable_during_recovery(self.info.head_log_area_offset as int,
                    self.info.log_area_len as int,
                    self.info.log_length as int,
                    addr - (log_start_addr + spec_log_area_pos()))
        };

        // Call `tentatively_append_to_log` to do the real work of this function,
        // providing it the subregion created above so it doesn't have to think
        // about anything but the log area and so it doesn't have to reason about
        // the overall recovery view to perform writes.
        let ghost old_wrpm_region = wrpm_region@;
        assert(spec_log_header_area_size() < spec_log_area_pos()) by { reveal(spec_padding_needed); }
        let result = self.tentatively_append_to_log(wrpm_region, log_start_addr, log_size, bytes_to_append, Ghost(crash_pred), Tracked(perm), Ghost(is_writable_absolute_addr_fn));

        // We now update our `info` field to reflect the new
        // `log_plus_pending_length` value.

        let num_bytes: u64 = bytes_to_append.len() as u64;
        self.info.log_plus_pending_length = (self.info.log_plus_pending_length + num_bytes) as u64;

        // We update our `state` field to reflect the tentative append.

        self.state = Ghost(self.state@.tentatively_append(bytes_to_append@));

        result
    }

    // This local helper method proves that we can read a portion of
    // the abstract log by reading a continuous range of the log area.
    // It requires that the position being read from is correct, and
    // that the read is short enough to not require wrapping around the
    // end of the log area.
    proof fn lemma_read_of_continuous_range(
        &self,
        pm_region_view: PersistentMemoryRegionView,
        log_start_addr: nat,
        log_size: nat,
        pos: nat,
        len: nat,
        addr: nat,
    )
        requires
            len > 0,
            metadata_consistent_with_info(pm_region_view, log_start_addr, log_size, self.cdb, self.info),
            info_consistent_with_log_area(pm_region_view, log_start_addr, log_size, self.info, self.state@),
            log_start_addr + spec_log_area_pos() + self.info.log_area_len <= pm_region_view.len(),
            log_start_addr + spec_log_area_pos() <= addr < addr + len <= pm_region_view.len(),
            addr + len <= log_start_addr + log_size,
            ({
                let info = self.info;
                let max_len_without_wrapping = info.log_area_len -
                    relative_log_pos_to_log_area_offset(pos - info.head,
                                                        info.head_log_area_offset as int,
                                                        info.log_area_len as int);
                &&& pos >= info.head
                &&& pos + len <= info.head + info.log_length
                &&& len <= max_len_without_wrapping
                &&& addr == log_start_addr + spec_log_area_pos() +
                        relative_log_pos_to_log_area_offset(pos - info.head as int,
                                                            info.head_log_area_offset as int,
                                                            info.log_area_len as int)
                &&& info.log_length < log_size
            })
        ensures
            ({
                let log = self@;
                &&& pm_region_view.no_outstanding_writes_in_range(addr as int, (addr + len) as int)
                &&& extract_bytes(pm_region_view.committed(), addr, len) == 
                        extract_bytes(log.log, (pos - log.head) as nat, len)
            })
    {
        let info = self.info;
        let s = self.state@;

        // The key to the proof is that we need to reason about how
        // addresses in the log area correspond to relative log
        // positions. This is because the invariant talks about
        // relative log positions but this lemma is proving things
        // about addresses in the log area.

        lemma_addresses_in_log_area_correspond_to_relative_log_positions(pm_region_view, log_start_addr, log_size, info);
        assert(extract_bytes(pm_region_view.committed(), addr, len) =~= extract_bytes(s.log, (pos - s.head) as nat, len));
    }

    // This lemma, used by `advance_head`, gives a mathematical
    // proof that one can compute `new_head % log_area_len`
    // using only linear math operations (`+` and `-`).
    proof fn lemma_check_fast_way_to_compute_head_mod_log_area_len(
        info: LogInfo,
        state: AbstractLogState,
        new_head: u128,
    )
        requires
            info.head <= new_head,
            new_head - info.head <= info.log_length as u128,
            info.log_area_len >= MIN_LOG_AREA_SIZE,
            info.log_length <= info.log_plus_pending_length <= info.log_area_len,
            info.head_log_area_offset == info.head as int % info.log_area_len as int,
        ensures
            ({
                let amount_of_advancement: u64 = (new_head - info.head) as u64;
                new_head as int % info.log_area_len as int ==
                    if amount_of_advancement < info.log_area_len - info.head_log_area_offset {
                        amount_of_advancement + info.head_log_area_offset
                    }
                    else {
                        amount_of_advancement - (info.log_area_len - info.head_log_area_offset)
                    }
            }),
    {
        let amount_of_advancement: u64 = (new_head - info.head) as u64;
        let new_head_log_area_offset =
            if amount_of_advancement < info.log_area_len - info.head_log_area_offset {
                amount_of_advancement + info.head_log_area_offset
            }
            else {
                amount_of_advancement - (info.log_area_len - info.head_log_area_offset)
            };

        let n = info.log_area_len as int;
        let advancement = amount_of_advancement as int;
        let head = info.head as int;
        let head_mod_n = info.head_log_area_offset as int;
        let supposed_new_head_mod_n = new_head_log_area_offset as int;

        // First, observe that `advancement` plus `head` is
        // congruent modulo n to `advancement` plus `head` % n.

        assert((advancement + head) % n == (advancement + head_mod_n) % n) by {
            assert(head == n * (head / n) + head % n) by {
                lemma_fundamental_div_mod(head, n);
            }
            assert((n * (head / n) + (advancement + head_mod_n)) % n == (advancement + head_mod_n) % n) by {
                lemma_mod_multiples_vanish(head / n, advancement + head_mod_n, n);
            }
        }

        // Next, observe that `advancement` + `head` % n is
        // congruent modulo n to itself minus n. This is
        // relevant because there are two cases for computing
        // `new_head_mod_log_area_offset`. In one case, it's
        // computed as `advancement` + `head` % n. In the
        // other case, it's that quantity minus n.

        assert((advancement + head % n) % n == (advancement + head_mod_n - n) % n) by {
            lemma_mod_sub_multiples_vanish(advancement + head_mod_n, n);
        }

        // So we know that in either case, `new_head` % n ==
        // `new_head_mod_log_area_offset` % n.

        assert(new_head as int % n == supposed_new_head_mod_n % n);

        // But what we want to prove is that `new_head` % n ==
        // `new_head_mod_log_area_offset`. So we need to show
        // that `new_head_mod_log_area_offset` % n ==
        // `new_head_mod_log_area_offset`.  We can deduce this
        // from the fact that 0 <= `new_head_mod_log_area_offset`
        // < n.

        assert(supposed_new_head_mod_n % n == supposed_new_head_mod_n) by {
            lemma_small_mod(supposed_new_head_mod_n as nat, n as nat);
        }
    }

    // The `advance_head` method advances the head of the log,
    // thereby making more space for appending but making log
    // entries before the new head unavailable for reading. Upon
    // return from this method, the head advancement is durable,
    // i.e., it will survive crashes. See `README.md` for more
    // documentation and examples of its use.
    //
    // This method is passed a write-restricted persistent memory
    // region `wrpm_region`. This restricts how it can write
    // `wrpm_region`. It's only given permission (in `perm`) to
    // write if it can prove that any crash after initiating the
    // write is safe. That is, any such crash must put the memory
    // in a state that recovers as either (1) the current abstract
    // state with all pending appends dropped, or (2) the state
    // after advancing the head and then dropping all pending
    // appends.
    pub exec fn advance_head<Perm, PM>(
        &mut self,
        wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        new_head: u128,
        log_start_addr: u64,
        log_size: u64,
        Ghost(crash_pred): Ghost<spec_fn(Seq<u8>) -> bool>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), LogErr>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires
            old(self).inv(old(wrpm_region)@, log_start_addr as nat, log_size as nat),
            old(wrpm_region).inv(),
            forall |s| #[trigger] old(wrpm_region)@.can_crash_as(s) ==> crash_pred(s),
            Self::recover(old(wrpm_region)@.committed(), log_start_addr as nat, log_size as nat) == Some(old(self)@.drop_pending_appends()),
            forall |s| #[trigger] old(wrpm_region)@.can_crash_as(s) ==> 
                Self::recover(s, log_start_addr as nat, log_size as nat) == Some(old(self)@.drop_pending_appends()),
            forall |s2: Seq<u8>| {
                let current_state = old(wrpm_region)@.flush().committed();
                &&& current_state.len() == s2.len() 
                &&& states_differ_only_in_log_region(s2, current_state, log_start_addr as nat, log_size as nat)
                &&& {
                        ||| Self::recover(s2, log_start_addr as nat, log_size as nat) == Some(old(self)@.drop_pending_appends())
                        ||| Self::recover(s2, log_start_addr as nat, log_size as nat) == Some(old(self)@.advance_head(new_head as int).drop_pending_appends())
                    }
            } ==> perm.check_permission(s2),
            forall |s1: Seq<u8>, s2: Seq<u8>| {
                &&& s1.len() == s2.len() 
                &&& #[trigger] crash_pred(s1)
                &&& states_differ_only_in_log_region(s1, s2, log_start_addr as nat, log_size as nat)
                &&& Self::recover(s1, log_start_addr as nat, log_size as nat) == Some(old(self)@.drop_pending_appends())
                &&& Self::recover(s2, log_start_addr as nat, log_size as nat) == Some(old(self)@.drop_pending_appends())
            } ==> #[trigger] crash_pred(s2),
            forall |s| crash_pred(s) ==> perm.check_permission(s),
            log_start_addr as int % const_persistence_chunk_size() == 0,
            log_size as int % const_persistence_chunk_size() == 0,
        ensures
            self.inv(wrpm_region@, log_start_addr as nat, log_size as nat),
            wrpm_region.inv(),
            wrpm_region@.len() == old(wrpm_region)@.len(),
            wrpm_region.constants() == old(wrpm_region).constants(),
            Self::can_only_crash_as_state(wrpm_region@, log_start_addr as nat, log_size as nat, self@.drop_pending_appends()),
            no_outstanding_writes_to_metadata(wrpm_region@, log_start_addr as nat),
            match result {
                Ok(()) => {
                    &&& old(self)@.head <= new_head <= old(self)@.head + old(self)@.log.len()
                    &&& self@ == old(self)@.advance_head(new_head as int)
                    &&& wrpm_region@.no_outstanding_writes()
                    &&& states_differ_only_in_log_region(old(wrpm_region)@.flush().committed(), wrpm_region@.committed(), 
                            log_start_addr as nat, log_size as nat)
                },
                Err(LogErr::CantAdvanceHeadPositionBeforeHead { head }) => {
                    &&& self@ == old(self)@
                    &&& head == self@.head
                    &&& new_head < head
                },
                Err(LogErr::CantAdvanceHeadPositionBeyondTail { tail }) => {
                    &&& self@ == old(self)@
                    &&& tail == self@.head + self@.log.len()
                    &&& new_head > tail
                },
                _ => false
            }
    {
        // Even if we return an error code, we still have to prove that
        // upon return the states we can crash into recover into valid
        // abstract states.

        proof {
            lemma_invariants_imply_crash_recover_forall(wrpm_region@, log_start_addr as nat, log_size as nat, self.cdb,
                                                        self.info, self.state@);
        }

        // Handle error cases due to improper parameters passed to the
        // function.
        if new_head < self.info.head {
            return Err(LogErr::CantAdvanceHeadPositionBeforeHead{ head: self.info.head })
        }
        if new_head - self.info.head > self.info.log_length as u128 {
            return Err(LogErr::CantAdvanceHeadPositionBeyondTail{
                tail: self.info.head + self.info.log_length as u128
            })
        }

        // To compute the new head mod n (where n is the log area
        // length), take the old head mod n, add the amount by
        // which the head is advancing, then subtract n if
        // necessary.

        let amount_of_advancement: u64 = (new_head - self.info.head) as u64;
        let new_head_log_area_offset =
            if amount_of_advancement < self.info.log_area_len - self.info.head_log_area_offset {
                amount_of_advancement + self.info.head_log_area_offset
            }
            else {
                // To compute `self.info.head_log_area_offset` [the old
                // head] plus `amount_of_advancement` [the amount
                // by which the head is advancing] minus
                // `self.info.log_area_len` [the log area length], we
                // do it in the following order that guarantees no
                // overflow/underflow.
                amount_of_advancement - (self.info.log_area_len - self.info.head_log_area_offset)
            };

        assert(new_head_log_area_offset == new_head as int % self.info.log_area_len as int) by {
            Self::lemma_check_fast_way_to_compute_head_mod_log_area_len(self.info, self.state@, new_head);
        }

        // Update `self.self.info` to reflect the change to the head
        // position. This necessitates updating all the fields
        // except the log area length.

        let ghost prev_info = self.info;
        self.info.head = new_head;
        self.info.head_log_area_offset = new_head_log_area_offset;
        self.info.log_length = self.info.log_length - amount_of_advancement;
        self.info.log_plus_pending_length = self.info.log_plus_pending_length - amount_of_advancement;

        // Update the abstract `self.state` to reflect the head update.

        let ghost prev_state = self.state@;
        self.state = Ghost(self.state@.advance_head(new_head as int));

        // To prove that the log area for log number `which_log` is
        // compatible with the new `self.infos` and `self.state`, we
        // need to reason about how addresses in the log area
        // correspond to relative log positions. That's because the
        // invariants we know about the log area talk about log
        // positions relative to the old head, but we want to know
        // things about log positions relative to the new head. What
        // connects those together is that they both talk about the
        // same addresses in the log area.

        proof {
            lemma_log_area_consistent_with_new_info_and_state_advance_head(wrpm_region@, log_start_addr as nat, log_size as nat, new_head as int,
                prev_info, self.info, prev_state, self.state@);
        }

        // Update the inactive metadata on all regions and flush, then
        // swap the CDB to its opposite. We have to update the metadata
        // on all regions, even though we're only advancing the head on
        // one, for the following reason. The only way available to us
        // to update the active metadata is to flip the CDB, but this
        // flips which metadata is active on *all* regions. So we have
        // to update the inactive metadata on all regions.

        self.update_log_metadata(wrpm_region, log_start_addr, log_size, Ghost(prev_info), Ghost(prev_state),
                                    Ghost(crash_pred), Tracked(perm));

        Ok(())
    }

    // The `read` method reads part of the log, returning a vector
    // containing the read bytes. It doesn't guarantee that those
    // bytes aren't corrupted by persistent memory corruption. See
    // `README.md` for more documentation and examples of its use.
    pub exec fn read<Perm, PM>(
        &self,
        pm_region: &WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        log_start_addr: u64,
        log_size: u64, 
        pos: u128,
        len: u64,
    ) -> (result: Result<(Vec<u8>, Ghost<Seq<int>>), LogErr>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires
            self.inv(pm_region@, log_start_addr as nat, log_size as nat),
            pm_region.inv(),
            pos + len <= u128::MAX,
            log_start_addr + spec_log_area_pos() <= pm_region@.len() <= u64::MAX,
        ensures
            ({
                let log = self@;
                match result {
                    Ok((bytes, addrs)) => {
                        let true_bytes = self@.read(pos as int, len as int);
                        &&& true_bytes == Seq::new(addrs@.len(), |i: int| pm_region@.committed()[addrs@[i] as int])
                        &&& true_bytes == extract_bytes(self@.log, (pos - self@.head) as nat, len as nat)
                        &&& pos >= log.head
                        &&& pos + len <= log.head + log.log.len()
                        &&& read_correct_modulo_corruption(bytes@, true_bytes, addrs@, pm_region.constants().impervious_to_corruption)
                        &&& addrs@.len() == len
                    },
                    Err(LogErr::CantReadBeforeHead{ head: head_pos }) => {
                        &&& pos < log.head
                        &&& head_pos == log.head
                    },
                    Err(LogErr::CantReadPastTail{ tail }) => {
                        &&& pos + len > log.head + log.log.len()
                        &&& tail == log.head + log.log.len()
                    },
                    _ => false,
                }
            })
    {        
        // Handle error cases due to improper parameters passed to the
        // function.

        let info = &self.info;
        if pos < info.head {
            return Err(LogErr::CantReadBeforeHead{ head: info.head })
        }
        if len > info.log_length { // We have to do this check first to avoid underflow in the next comparison
            return Err(LogErr::CantReadPastTail{ tail: info.head + info.log_length as u128 })
        }
        if pos - info.head > (info.log_length - len) as u128 { // we know `info.log_length - len` can't underflow
            return Err(LogErr::CantReadPastTail{ tail: info.head + info.log_length as u128 })
        }

        let ghost s = self.state@;
        // let ghost true_bytes = s.log.subrange(pos - s.head, pos + len - s.head);
        let ghost true_bytes = extract_bytes(s.log, (pos - s.head) as nat, len as nat);

        if len == 0 {
            // Case 0: The trivial case where we're being asked to read zero bytes.
            let ghost addrs = Seq::empty();
            assert(true_bytes =~= Seq::<u8>::empty());
            assert(true_bytes == Seq::new(addrs.len(), |i: int| pm_region@.committed()[addrs[i] as int]));
            assert(maybe_corrupted(Seq::<u8>::empty(), true_bytes, addrs));
            return Ok((Vec::<u8>::new(), Ghost(addrs)));
        }

        let log_area_len: u64 = info.log_area_len;
        let relative_pos: u64 = (pos - info.head) as u64;
        if relative_pos >= log_area_len - info.head_log_area_offset {

            // Case 1: The position we're being asked to read appears
            // in the log area before the log head. So the read doesn't
            // need to wrap.
            //
            // We could compute the address to write to with:
            //
            // `write_addr = ABSOLUTE_POS_OF_LOG_AREA + pos % info.log_area_len;`
            //
            // But we can replace the expensive modulo operation above with two subtraction
            // operations as follows. This is somewhat subtle, but we have verification backing
            // us up and proving this optimization correct.

            let addr: u64 = log_start_addr + log_area_pos() + relative_pos - (info.log_area_len - info.head_log_area_offset);
            proof { self.lemma_read_of_continuous_range(pm_region@, log_start_addr as nat, log_size as nat, pos as nat,
                                                        len as nat, addr as nat); }
            let bytes = match pm_region.get_pm_region_ref().read_unaligned(addr, len) {
                Ok(bytes) => bytes,
                Err(e) => {
                    assert(e == PmemError::AccessOutOfRange);
                    return Err(LogErr::PmemErr{ err: e });
                }
            };
            let ghost addrs = Seq::new(len as nat, |i: int| i + addr);
            proof {
                let true_bytes = Seq::new(addrs.len(), |i: int| pm_region@.committed()[addrs[i] as int]);
                let read_bytes = self@.read(pos as int, len as int);
                assert(true_bytes =~= read_bytes);
            }
            return Ok((bytes, Ghost(addrs)));
        }

        // The log area wraps past the point we're reading from, so we
        // need to compute the maximum length we can read without
        // wrapping to be able to figure out whether we need to wrap.

        let max_len_without_wrapping: u64 = log_area_len - info.head_log_area_offset - relative_pos;
        assert(max_len_without_wrapping == info.log_area_len -
                relative_log_pos_to_log_area_offset(pos - info.head,
                                                    info.head_log_area_offset as int, info.log_area_len as int));

        // Whether we need to wrap or not, we know the address where
        // our read should start, so we can compute that and put it in
        // `addr`.
        //
        // We could compute the address to write to with:
        //
        // `write_addr = ABSOLUTE_POS_OF_LOG_AREA + pos % info.log_area_len;`
        //
        // But we can replace the expensive modulo operation above with
        // one addition operation as follows. This is somewhat subtle,
        // but we have verification backing us up and proving this
        // optimization correct.

        let addr: u64 = log_start_addr + log_area_pos() + relative_pos + info.head_log_area_offset;
        assert(addr == log_start_addr + spec_log_area_pos() +
                relative_log_pos_to_log_area_offset(pos - info.head,
                                                    info.head_log_area_offset as int,
                                                    info.log_area_len as int));

        if len <= max_len_without_wrapping {

            // Case 2: We're reading few enough bytes that we don't have to wrap.

            proof { self.lemma_read_of_continuous_range(pm_region@, log_start_addr as nat, log_size as nat, pos as nat,
                                                        len as nat, addr as nat); }
            let bytes = match pm_region.get_pm_region_ref().read_unaligned(addr, len) {
                Ok(bytes) => bytes,
                Err(e) => {
                    assert(e == PmemError::AccessOutOfRange);
                    return Err(LogErr::PmemErr{ err: e });
                }
            };
            let ghost addrs = Seq::new(len as nat, |i: int| i + addr);
            proof {
                let true_bytes = Seq::new(addrs.len(), |i: int| pm_region@.committed()[addrs[i] as int]);
                let read_bytes = self@.read(pos as int, len as int);
                assert(true_bytes =~= read_bytes);
            }
            return Ok((bytes, Ghost(addrs)));
        }

        // Case 3: We're reading enough bytes that we have to wrap.
        // That necessitates doing two contiguous reads, one from the
        // end of the log area and one from the beginning, and
        // concatenating the results.

        proof {
            self.lemma_read_of_continuous_range(pm_region@, log_start_addr as nat, log_size as nat, pos as nat,
                                                max_len_without_wrapping as nat, addr as nat);
        }

        let mut part1 = match pm_region.get_pm_region_ref().read_unaligned(addr, max_len_without_wrapping) {
            Ok(part1) => part1,
            Err(e) => {
                assert(e == PmemError::AccessOutOfRange);
                return Err(LogErr::PmemErr{ err: e });
            }
        };
        let ghost addrs_part1 = Seq::<int>::new(max_len_without_wrapping as nat, |i: int| i + addr);
        proof {
            let true_bytes = Seq::new(addrs_part1.len(), |i: int| pm_region@.committed()[addrs_part1[i] as int]);
            let read_bytes = self@.read(pos as int, max_len_without_wrapping as int);
            assert(true_bytes =~= read_bytes);
        }

        proof {
            self.lemma_read_of_continuous_range(pm_region@, log_start_addr as nat,
                                                log_size as nat,
                                                (pos + max_len_without_wrapping) as nat,
                                                (len - max_len_without_wrapping) as nat,
                                                (log_start_addr + spec_log_area_pos()) as nat);
        }

        let mut part2 = match pm_region.get_pm_region_ref().read_unaligned(log_start_addr + log_area_pos(), len - max_len_without_wrapping) {
            Ok(part2) => part2,
            Err(e) => {
                assert(e == PmemError::AccessOutOfRange);
                return Err(LogErr::PmemErr{ err: e });
            }
        };
        let ghost addrs_part2 = Seq::<int>::new((len - max_len_without_wrapping) as nat, |i: int| i + log_start_addr + spec_log_area_pos());

        // Now, prove that concatenating them produces the correct
        // bytes to return. The subtle thing in this argument is that
        // the bytes are only correct modulo corruption. And the
        // "correct modulo corruption" specification function talks
        // about the concrete addresses the bytes were read from and
        // demands that those addresses all be distinct.

        proof {
            let true_part1 = extract_bytes(s.log, (pos - s.head) as nat, max_len_without_wrapping as nat);
            let true_part2 = extract_bytes(s.log, (pos + max_len_without_wrapping - s.head) as nat, (len - max_len_without_wrapping) as nat);
            
            assert(true_part1 + true_part2 =~= s.log.subrange(pos - s.head, pos + len - s.head));

            let addrs = addrs_part1 + addrs_part2;
            assert(true_part1 + true_part2 == Seq::new(len as nat, |i: int| pm_region@.committed()[addrs[i]]));

            if !pm_region.constants().impervious_to_corruption {
                assert(maybe_corrupted(part1@ + part2@, true_part1 + true_part2, addrs));
                assert(all_elements_unique(addrs_part1 + addrs_part2));
            }
        }

        // Append the two byte vectors together and return the result.
        part1.append(&mut part2);
        let addrs = Ghost(addrs_part1 + addrs_part2);
        Ok((part1, addrs))
    }

    // This local helper method updates the log metadata on
    // persistent memory to be consistent with `self.info` and
    // `self.state`. It does so in the following steps: (1) update
    // the log metadata corresponding to the inactive CDB; (2)
    // flush; (3) swap the CDB in region #0; (4) flush again.
    //
    // The first of these steps only writes to inactive metadata, i.e.,
    // metadata that's ignored during recovery. So even if a crash
    // happens during or immediately after this call, recovery will be
    // unaffected.
    //
    // Before calling this function, the caller should make sure that
    // `self.info` and `self.state` contain the data that the inactive
    // log metadata should reflect. But, since this function has to
    // reason about crashes, it also needs to know things about the
    // *previous* values of `self.info` and `self.state`, since those
    // are the ones that the active log metadata is consistent with
    // and will stay consistent with until we write the new CDB. These
    // previous values are passed as ghost parameters since they're
    // only needed for proving things.
    //
    // The caller of this function is responsible for making sure that
    // the contents of the log area are compatible with both the old
    // and the new `info` and `state`. However, the log area contents
    // only need to be compatible with the new `info` and `state`
    // after the next flush, since we're going to be doing a flush.
    // This weaker requirement allows a performance optimization: the
    // caller doesn't have to flush before calling this function.
    exec fn update_log_metadata<Perm, PM>(
        &mut self,
        wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        log_start_addr: u64,
        log_size: u64,
        Ghost(prev_info): Ghost<LogInfo>,
        Ghost(prev_state): Ghost<AbstractLogState>,
        Ghost(crash_pred): Ghost<spec_fn(Seq<u8>) -> bool>,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion
        requires
            old(wrpm_region).inv(),
            log_start_addr as int % const_persistence_chunk_size() == 0,
            log_size as int % const_persistence_chunk_size() == 0,
            memory_matches_deserialized_cdb(old(wrpm_region)@, log_start_addr as nat, old(self).cdb),
            no_outstanding_writes_to_metadata(old(wrpm_region)@, log_start_addr as nat),
            metadata_consistent_with_info(old(wrpm_region)@, log_start_addr as nat, log_size as nat, old(self).cdb, prev_info),
            info_consistent_with_log_area(old(wrpm_region)@.flush(), log_start_addr as nat, log_size as nat, old(self).info, old(self).state@),
            info_consistent_with_log_area(old(wrpm_region)@, log_start_addr as nat, log_size as nat, prev_info, prev_state),
            old(self).info.log_area_len == prev_info.log_area_len,
            Self::recover(old(wrpm_region)@.committed(), log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends()),
            forall |s| #[trigger] old(wrpm_region)@.can_crash_as(s) ==> 
                Self::recover(s, log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends()),
            forall |s| #[trigger] old(wrpm_region)@.can_crash_as(s) ==> crash_pred(s),
            forall |s1: Seq<u8>, s2: Seq<u8>| {
                &&& s1.len() == s2.len() 
                &&& #[trigger] crash_pred(s1)
                &&& states_differ_only_in_log_region(s1, s2, log_start_addr as nat, log_size as nat)
                &&& Self::recover(s1, log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends())
                &&& Self::recover(s2, log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends())
            } ==> #[trigger] crash_pred(s2),
            forall |s| crash_pred(s) ==> perm.check_permission(s),
            forall |s2: Seq<u8>| {
                let flushed_state = old(wrpm_region)@.flush().committed();
                &&& flushed_state.len() == s2.len() 
                &&& states_differ_only_in_log_region(flushed_state, s2, log_start_addr as nat, log_size as nat)
                &&& {
                        ||| Self::recover(s2, log_start_addr as nat, log_size as nat) == Some(old(self).state@.drop_pending_appends())
                        ||| Self::recover(s2, log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends())
                }
            } ==> perm.check_permission(s2),

            metadata_types_set(old(wrpm_region)@.committed(), log_start_addr as nat),
            log_start_addr < log_start_addr + log_size <= old(wrpm_region)@.len() <= u64::MAX,
            log_start_addr as int % const_persistence_chunk_size() == 0,
        ensures
            self.inv(wrpm_region@, log_start_addr as nat, log_size as nat),
            wrpm_region.inv(),
            wrpm_region.constants() == old(wrpm_region).constants(),
            wrpm_region@.len() == old(wrpm_region)@.len(),
            self.state == old(self).state,
            wrpm_region@.no_outstanding_writes(),
            Self::recover(wrpm_region@.committed(), log_start_addr as nat, log_size as nat) == Some(self@.drop_pending_appends()),
            states_differ_only_in_log_region(old(wrpm_region)@.flush().committed(), wrpm_region@.committed(), 
                log_start_addr as nat, log_size as nat),
    {
        broadcast use pmcopy_axioms;

        // Set the `unused_metadata_pos` to be the position corresponding to !self.cdb
        // since we're writing in the inactive part of the metadata.

        let ghost old_wrpm = wrpm_region@;
        let unused_metadata_pos = get_inactive_log_metadata_pos(self.cdb);
        assert(unused_metadata_pos == spec_get_active_log_metadata_pos(!self.cdb));

        let ghost inactive_metadata_pos = spec_get_inactive_log_metadata_pos(self.cdb) + log_start_addr;
        let ghost is_writable_absolute_addr = |addr: int| {
            // either the address is in the unreachable log area
            ||| {
                &&& log_start_addr + spec_log_area_pos() <= addr < log_start_addr + spec_log_area_pos() + log_size
                &&& log_area_offset_unreachable_during_recovery(prev_info.head_log_area_offset as int,
                        prev_info.log_area_len as int,
                        prev_info.log_length as int,
                        addr - (log_start_addr + spec_log_area_pos()))
            }
            // or it's in the inactive metadata
            ||| inactive_metadata_pos <= addr < inactive_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()
        };

        assert(Self::recover(wrpm_region@.committed(), log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends()));
        assert(spec_log_header_area_size() < spec_log_area_pos()) by (compute);

        self.update_inactive_log_metadata(wrpm_region, log_start_addr, log_size, 
            Ghost(prev_info), Ghost(prev_state), Ghost(is_writable_absolute_addr), Ghost(crash_pred), Tracked(perm));

        // Prove that after the flush we're about to do, all our
        // invariants will continue to hold (using the still-unchanged
        // CDB and the old metadata, infos, and state).
        // Also prove that after the flush, there is only one possible
        // crash state.
        proof {
            lemma_flushing_metadata_maintains_invariants(wrpm_region@, log_start_addr as nat, log_size as nat, self.cdb, prev_info, prev_state);
        
            assert(wrpm_region@.can_crash_as(wrpm_region@.flush().committed()));
            assert(forall |s| #[trigger] wrpm_region@.flush().can_crash_as(s) ==> s == wrpm_region@.flush().committed()) by {
                lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(wrpm_region@.flush());
            }
        }

        // Next, flush all outstanding writes to memory. This is
        // necessary so that those writes are ordered before the update
        // to the CDB.
        wrpm_region.flush();

        // Next, compute the new encoded CDB to write.
        let new_cdb = if self.cdb { CDB_FALSE } else { CDB_TRUE };
        let ghost new_cdb_bytes = new_cdb.spec_to_bytes();

        // Show that after writing and flushing, the CDB will be !self.cdb
        let ghost pm_region_after_write = wrpm_region@.write(log_start_addr as int, new_cdb_bytes);
        let ghost flushed_mem_after_write = pm_region_after_write.flush();
        assert(memory_matches_deserialized_cdb(flushed_mem_after_write, log_start_addr as nat, !self.cdb)) by {
            let flushed_region = pm_region_after_write.flush();
            lemma_write_reflected_after_flush_committed(wrpm_region@, log_start_addr as int,
                                                        new_cdb_bytes);
        }

        // Show that after writing and flushing, our invariants will
        // hold for each log if we flip `self.cdb`.

        let ghost pm_region_after_flush = pm_region_after_write.flush();
        assert ({
            &&& metadata_consistent_with_info(pm_region_after_flush, log_start_addr as nat, log_size as nat, !self.cdb, self.info)
            &&& info_consistent_with_log_area(pm_region_after_flush, log_start_addr as nat, log_size as nat, self.info, self.state@)
            &&& metadata_types_set(pm_region_after_flush.committed(), log_start_addr as nat)
        }) by {
            lemma_establish_extract_bytes_equivalence(wrpm_region@.committed(),
                                                    pm_region_after_flush.committed());

            lemma_metadata_consistent_with_info_after_cdb_update(
                wrpm_region@,
                pm_region_after_flush,
                log_start_addr as nat, 
                log_size as nat,
                new_cdb_bytes,
                !self.cdb,
                self.info
            );
            lemma_metadata_types_set_after_cdb_update(
                wrpm_region@,
                pm_region_after_flush,
                log_start_addr as nat, 
                log_size as nat,
                new_cdb_bytes,
                self.cdb
            );
        }

        assert(memory_matches_deserialized_cdb(pm_region_after_flush, log_start_addr as nat, !self.cdb));

        // Show that if we crash after the write and flush, we recover
        // to an abstract state corresponding to `self.state@` after
        // dropping pending appends.

        proof {
            lemma_invariants_imply_crash_recover_forall(pm_region_after_flush, log_start_addr as nat, log_size as nat,
                                                        !self.cdb, self.info, self.state@);
        }

        // Show that if we crash after initiating the write of the CDB,
        // we'll recover to a permissible state. There are two cases:
        //
        // If we crash without any updating, then we'll recover to
        // state `prev_state.drop_pending_appends()` with the current
        // CDB.
        //
        // If we crash after writing, then we'll recover to state
        // `self.state@.drop_pending_appends()` with the flipped CDB.
        //
        // Because we're only writing within the persistence
        // granularity of the persistent memory, a crash in the middle
        // will either leave the persistent memory in the pre-state or
        // the post-state.
        //
        // This means we're allowed to do the write because if we
        // crash, we'll either be in state wrpm_region@.committed() or
        // pm_region_after_write.flush().committed(). In the former
        // case, we'll be in state `prev_state.drop_pending_appends()`
        // and in the latter case, as shown above, we'll be in state
        // `self.state@.drop_pending_appends()`.

        assert forall |s| pm_region_after_write.can_crash_as(s) implies
                    #[trigger] perm.check_permission(s) by {
            lemma_invariants_imply_crash_recover_forall(wrpm_region@, log_start_addr as nat, log_size as nat,
                                                        self.cdb, prev_info, prev_state);
            lemma_single_write_crash_effect_on_pm_region_view(wrpm_region@, log_start_addr as int,
                                                                new_cdb_bytes);
            if s == wrpm_region@.committed() {
                // This case is trivial -- we already know that this is a legal crash state
            } else {
                assert(pm_region_after_flush.can_crash_as(s));
            }
        }

        // Finally, update the CDB, then flush, then flip `self.cdb`.
        // There's no need to flip `self.cdb` atomically with the write
        // since the flip of `self.cdb` is happening in local
        // non-persistent memory so if we crash it'll be lost anyway.
        wrpm_region.serialize_and_write(log_start_addr, &new_cdb, Tracked(perm));
        wrpm_region.flush();
        self.cdb = !self.cdb;

        assert(Self::recover(wrpm_region@.committed(), log_start_addr as nat, log_size as nat) == Some(self@.drop_pending_appends()));
    }

    // This local helper method updates the inactive log metadata
    // on persistent memory to be consistent with `self.info` and
    // `self.state`. It's passed a subregion that gives it permission
    // to do arbitrary writes to the inactive log metadata portion
    // of the persistent memory.
    exec fn update_inactive_log_metadata<Perm, PM>(
        &self,
        wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        log_start_addr: u64,
        log_size: u64,
        Ghost(prev_info): Ghost<LogInfo>,
        Ghost(prev_state): Ghost<AbstractLogState>,
        Ghost(is_writable_absolute_addr): Ghost<spec_fn(int) -> bool>,
        Ghost(crash_pred): Ghost<spec_fn(Seq<u8>) -> bool>,
        Tracked(perm): Tracked<&Perm>,
    )
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires 
            old(wrpm_region).inv(),
            log_start_addr as int % const_persistence_chunk_size() == 0,
            log_size as int % const_persistence_chunk_size() == 0,
            info_consistent_with_log_area(old(wrpm_region)@.flush(), log_start_addr as nat, log_size as nat, self.info, self.state@),
            info_consistent_with_log_area(old(wrpm_region)@, log_start_addr as nat, log_size as nat, prev_info, prev_state),
            no_outstanding_writes_to_metadata(old(wrpm_region)@, log_start_addr as nat),
            metadata_consistent_with_info(old(wrpm_region)@, log_start_addr as nat, log_size as nat, self.cdb, prev_info),
            memory_matches_deserialized_cdb(old(wrpm_region)@, log_start_addr as nat, self.cdb),
            metadata_types_set(old(wrpm_region)@.committed(), log_start_addr as nat),
            log_size == prev_info.log_area_len + spec_log_area_pos(),
            prev_info.log_area_len == self.info.log_area_len,
            log_start_addr + spec_log_area_pos() + prev_info.log_area_len <= old(wrpm_region)@.len(),
            log_start_addr + spec_get_inactive_log_metadata_pos(self.cdb) < log_start_addr + spec_log_area_pos() < old(wrpm_region)@.len() <= u64::MAX,
            ({
                let inactive_metadata_pos = spec_get_inactive_log_metadata_pos(self.cdb) + log_start_addr;
                // the writable closure should allow both inactive metadata and unreachable log bytes to be updated.
                // we won't update unreachable log bytes in this function, but there may be outstanding writes to them,
                // so we need to allow for them to differ from the original state in crash states
                &&& forall |addr: int| #[trigger] is_writable_absolute_addr(addr) <==> {
                        // either the address is in the unreachable log area
                        ||| {
                            &&& log_start_addr + spec_log_area_pos() <= addr < log_start_addr + spec_log_area_pos() + log_size
                            &&& log_area_offset_unreachable_during_recovery(prev_info.head_log_area_offset as int,
                                    prev_info.log_area_len as int,
                                    prev_info.log_length as int,
                                    addr - (log_start_addr + spec_log_area_pos()))
                        }
                        // or it's in the inactive metadata
                        ||| inactive_metadata_pos <= addr < inactive_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()
                    }
            }),
            log_start_addr < log_start_addr + spec_log_header_area_size() < log_start_addr + spec_log_area_pos() < old(wrpm_region)@.len(),

            forall |s| #[trigger] old(wrpm_region)@.can_crash_as(s) ==> 
                Self::recover(s, log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends()),
            forall |s| #[trigger] old(wrpm_region)@.can_crash_as(s) ==> crash_pred(s),
            forall |s1: Seq<u8>, s2: Seq<u8>| {
                &&& s1.len() == s2.len() 
                &&& #[trigger] crash_pred(s1)
                &&& states_differ_only_in_log_region(s1, s2, log_start_addr as nat, log_size as nat)
                &&& Self::recover(s1, log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends()) 
                &&& Self::recover(s2, log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends()) // or committed?
            } ==> #[trigger] crash_pred(s2),
            forall |s| crash_pred(s) ==> perm.check_permission(s),
            Self::recover(old(wrpm_region)@.committed(), log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends())
        ensures
            wrpm_region.inv(),
            wrpm_region@.len() == old(wrpm_region)@.len(),
            wrpm_region.constants() == old(wrpm_region).constants(),
            ({
                let state_after_flush = wrpm_region@.flush().committed();
                let inactive_metadata_pos = spec_get_inactive_log_metadata_pos(self.cdb) + log_start_addr;
                let log_metadata_bytes = extract_bytes(state_after_flush, inactive_metadata_pos as nat, LogMetadata::spec_size_of());
                let log_crc_bytes = extract_bytes(state_after_flush, inactive_metadata_pos as nat + LogMetadata::spec_size_of(), u64::spec_size_of());
                let log_metadata = LogMetadata::spec_from_bytes(log_metadata_bytes);
                let log_crc = u64::spec_from_bytes(log_crc_bytes);
                let new_metadata = LogMetadata {
                    head: self.info.head,
                    log_length: self.info.log_length,
                };
                let new_crc = new_metadata.spec_crc();

                &&& log_crc == log_metadata.spec_crc()
                &&& log_metadata.head == self.info.head
                &&& log_metadata.log_length == self.info.log_length

                &&& log_metadata_bytes == new_metadata.spec_to_bytes()
                &&& log_crc_bytes == new_crc.spec_to_bytes()
                &&& inactive_metadata_types_set(state_after_flush, log_start_addr as nat)
            }),
            metadata_types_set(wrpm_region@.committed(), log_start_addr as nat),
            memory_matches_deserialized_cdb(wrpm_region@, log_start_addr as nat, self.cdb),
            metadata_consistent_with_info(wrpm_region@, log_start_addr as nat, log_size as nat, self.cdb, prev_info),
            info_consistent_with_log_area(wrpm_region@, log_start_addr as nat, log_size as nat, prev_info, prev_state),
            info_consistent_with_log_area(wrpm_region@.flush(), log_start_addr as nat, log_size as nat, self.info, self.state@),
            metadata_consistent_with_info(wrpm_region@.flush(), log_start_addr as nat, log_size as nat, !self.cdb, self.info),
            forall |s| #[trigger] wrpm_region@.can_crash_as(s) ==> perm.check_permission(s),
            views_differ_only_in_log_region(old(wrpm_region)@.flush(), wrpm_region@.flush(), log_start_addr as nat, log_size as nat),
    {
        // Encode the log metadata as bytes, and compute the CRC of those bytes
        let info = &self.info;
        let log_metadata = LogMetadata {
            head: info.head,
            log_length: info.log_length
        };
        let log_crc = calculate_crc(&log_metadata);

        let inactive_metadata_pos = get_inactive_log_metadata_pos(self.cdb) + log_start_addr;

        proof {
            broadcast use pmcopy_axioms;
            lemma_metadata_fits_in_log_header_area();

            let new_pm1 = wrpm_region@.write(inactive_metadata_pos as int, log_metadata.spec_to_bytes());
            let new_pm2 = new_pm1.write(inactive_metadata_pos + LogMetadata::spec_size_of(), log_crc.spec_to_bytes());

            self.lemma_update_inactive_metadata_and_crc_crash_states_allowed_by_perm(wrpm_region@, new_pm1, new_pm2, log_metadata, inactive_metadata_pos as int,
                log_crc, inactive_metadata_pos + LogMetadata::spec_size_of(), log_start_addr as nat, log_size as nat, prev_info, prev_state, perm, crash_pred);
        } 

        // Write the new metadata and CRC
        wrpm_region.serialize_and_write(inactive_metadata_pos, &log_metadata, Tracked(perm));
        wrpm_region.serialize_and_write(inactive_metadata_pos + size_of::<LogMetadata>() as u64, &log_crc, Tracked(perm));

        // Prove that after the flush, the log metadata will be reflected in the subregion's
        // state.
        proof {
            // metadata types are set in both the old and new wrpm committed state; we haven't done any flushes,
            // so the two wrpms have the same committed state
            assert(metadata_types_set(old(wrpm_region)@.committed(), log_start_addr as nat));
            assert(old(wrpm_region)@.committed() == wrpm_region@.committed());

            let state_after_flush = wrpm_region@.flush().committed();
            assert(extract_bytes(state_after_flush, log_start_addr as nat, u64::spec_size_of()) == extract_bytes(old(wrpm_region)@.committed(), log_start_addr as nat, u64::spec_size_of()));
            assert(extract_bytes(state_after_flush, inactive_metadata_pos as nat, LogMetadata::spec_size_of()) =~= log_metadata.spec_to_bytes());
            assert(extract_bytes(state_after_flush, inactive_metadata_pos as nat + LogMetadata::spec_size_of(), u64::spec_size_of()) =~= log_crc.spec_to_bytes());
        }
    }

    // The `commit` method commits all tentative appends that have been
    // performed since the last one. See `README.md` for more
    // documentation and examples of its use.
    //
    // This method is passed a write-restricted persistent memory
    // region `wrpm_region`. This restricts how it can write
    // `wrpm_region`. It's only given permission (in `perm`) to
    // write if it can prove that any crash after initiating the
    // write is safe. That is, any such crash must put the memory
    // in a state that recovers as either (1) the current abstract
    // state with all pending appends dropped, or (2) the abstract
    // state after all pending appends are committed.
    pub exec fn commit<Perm, PM>(
        &mut self,
        wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        log_start_addr: u64,
        log_size: u64,
        Ghost(crash_pred): Ghost<spec_fn(Seq<u8>) -> bool>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), LogErr>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion
        requires
            old(self).inv(old(wrpm_region)@, log_start_addr as nat, log_size as nat),
            old(wrpm_region).inv(),
            log_start_addr as int % const_persistence_chunk_size() == 0,
            log_size as int % const_persistence_chunk_size() == 0,
            Self::recover(old(wrpm_region)@.committed(), log_start_addr as nat, log_size as nat) == Some(old(self)@.drop_pending_appends()),
            forall |s| #[trigger] old(wrpm_region)@.can_crash_as(s) ==> 
                Self::recover(s, log_start_addr as nat, log_size as nat) == Some(old(self)@.drop_pending_appends()),
            forall |s| #[trigger] old(wrpm_region)@.can_crash_as(s) ==> crash_pred(s),
            forall |s2: Seq<u8>| {
                let flushed_state = old(wrpm_region)@.flush().committed();
                &&& flushed_state.len() == s2.len() 
                &&& states_differ_only_in_log_region(flushed_state, s2, log_start_addr as nat, log_size as nat)
                &&& {
                        ||| Self::recover(s2, log_start_addr as nat, log_size as nat) == Some(old(self)@.commit())
                        ||| Self::recover(s2, log_start_addr as nat, log_size as nat) == Some(old(self)@.drop_pending_appends())
                }
            } ==> perm.check_permission(s2),
            forall |s1: Seq<u8>, s2: Seq<u8>| {
                &&& s1.len() == s2.len() 
                &&& #[trigger] crash_pred(s1)
                &&& states_differ_only_in_log_region(s1, s2, log_start_addr as nat, log_size as nat)
                &&& Self::recover(s2, log_start_addr as nat, log_size as nat) == Some(old(self)@.drop_pending_appends())
            } ==> #[trigger] crash_pred(s2),
            forall |s| crash_pred(s) ==> perm.check_permission(s),
            log_start_addr as int % const_persistence_chunk_size() == 0,
            log_start_addr < log_start_addr + log_size <= old(wrpm_region)@.len() <= u64::MAX
        ensures
            self.inv(wrpm_region@, log_start_addr as nat, log_size as nat),
            wrpm_region.constants() == old(wrpm_region).constants(),
            wrpm_region@.len() == old(wrpm_region)@.len(),
            wrpm_region@.no_outstanding_writes(),
            Self::can_only_crash_as_state(wrpm_region@, log_start_addr as nat, log_size as nat, self@.drop_pending_appends()),
            result is Ok,
            self@ == old(self)@.commit(),
            Self::recover(wrpm_region@.committed(), log_start_addr as nat, log_size as nat) == Some(self@),
    {
        let ghost prev_info = self.info;
        let ghost prev_state = self.state@;

        self.state = Ghost(self.state@.commit());

        self.info.log_length = self.info.log_plus_pending_length;

        assert(memory_matches_deserialized_cdb(wrpm_region@, log_start_addr as nat, self.cdb));
        assert(metadata_consistent_with_info(wrpm_region@, log_start_addr as nat, log_size as nat, self.cdb, prev_info));
        assert(info_consistent_with_log_area(wrpm_region@, log_start_addr as nat, log_size as nat, prev_info, prev_state));
        assert(self.state@ == prev_state.commit());
        assert(info_consistent_with_log_area(wrpm_region@.flush(), log_start_addr as nat, log_size as nat, self.info, self.state@));

        // Update the inactive metadata on all regions and flush, then
        // swap the CDB to its opposite.

        self.update_log_metadata(wrpm_region, log_start_addr, log_size, Ghost(prev_info), Ghost(prev_state), Ghost(crash_pred), Tracked(perm));

        Ok(())
    }

    // The `get_head_tail_and_capacity` method returns the head,
    // tail, and capacity of the log. See `README.md` for more
    // documentation and examples of its use.
    #[allow(unused_variables)]
    pub exec fn get_head_tail_and_capacity<Perm, PM>(
        &self,
        pm_region: &WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        log_start_addr: u64,
        log_size: u64, 
    ) -> (result: Result<(u128, u128, u64), LogErr>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires
            self.inv(pm_region@, log_start_addr as nat, log_size as nat)
        ensures
            ({
                let log = self@;
                match result {
                    Ok((result_head, result_tail, result_capacity)) => {
                        &&& result_head == log.head
                        &&& result_tail == log.head + log.log.len()
                        &&& result_capacity == log.capacity
                        &&& result_capacity >= result_tail - result_head
                        &&& result_capacity <= pm_region@.len()
                    },
                    _ => false
                }
            })
    {
        // We cache information in `self.info` that lets us easily
        // compute the return values.

        let info = &self.info;
        Ok((info.head, info.head + info.log_length as u128, info.log_area_len))
    }

    // This function aborts a transaction by removing all pending appends.
    // It also flushes the PM device in order to ensure that the bytes beyond the 
    // end of the log are writable the next time we want to append.
    pub exec fn abort_pending_appends<Perm, PM>(
        &mut self,
        pm_region: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        log_start_addr: u64,
        log_size: u64, 
    ) 
        where
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires 
            old(self).inv(old(pm_region)@, log_start_addr as nat, log_size as nat),
            old(pm_region).inv(),
            log_start_addr as int % const_persistence_chunk_size() == 0,
            no_outstanding_writes_to_metadata(old(pm_region)@, log_start_addr as nat),
        ensures
            self.inv(pm_region@, log_start_addr as nat, log_size as nat),
            Self::recover(pm_region@.committed(), log_start_addr as nat, log_size as nat) 
                == Some(self@.drop_pending_appends()),
            pm_region.inv(),
            pm_region@.no_outstanding_writes(),
            pm_region@.len() == old(pm_region)@.len(),
            pm_region.constants() == old(pm_region).constants(),
            self@.pending == Seq::<u8>::empty(),
            self@.log == old(self)@.log,
            self@.head == old(self)@.head,
            self@.capacity == old(self)@.capacity,
            forall |s| #[trigger] pm_region@.can_crash_as(s) ==>
                Self::recover(s, log_start_addr as nat, log_size as nat) == Some(self@),
            pm_region@ == old(pm_region)@.flush(),
    {
        // remove pending bytes from the log length in the concrete state
        self.info.log_plus_pending_length = self.info.log_length;
        assert(self.state@.log == self.state@.drop_pending_appends().log);

        // and remove them from the abstract state as well
        self.state = Ghost(self.state@.drop_pending_appends());

        // We have to flush before we return in order to maintain the invariant that each 
        // byte has at most one outstanding write at a time. Otherwise, the next time we try to append, 
        // there will already be outstanding writes where we want to write.
        // TODO: could we somehow just drop these outstanding writes, rather than flushing them,
        // since we know they don't matter? This would also benefit from a more relaxed write model
        pm_region.flush();

        proof {
            broadcast use pmcopy_axioms;

            lemma_establish_extract_bytes_equivalence(old(pm_region)@.committed(), pm_region@.committed());
            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(pm_region@);

            assert forall |s| #[trigger] pm_region@.can_crash_as(s) implies {
                UntrustedLogImpl::recover(s, log_start_addr as nat, log_size as nat) == Some(self.state@)
            } by {
                let recovery_state = UntrustedLogImpl::recover(s, log_start_addr as nat, log_size as nat);
                let regular_state = UntrustedLogImpl::recover(pm_region@.committed(), log_start_addr as nat, log_size as nat);
                assert(pm_region@.no_outstanding_writes());
                assert(s == pm_region@.committed());
                assert(regular_state.unwrap() == self.state@.drop_pending_appends());
            }

            assert(self@ == self@.drop_pending_appends());
            assert(pm_region@.can_crash_as(pm_region@.committed()));
        }  
    }
}
    
}
