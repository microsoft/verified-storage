use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::slice::*;

use crate::kv::durable::inv_v::lemma_subrange_of_extract_bytes_equal;
use crate::kv::kvimpl_t::KvError;
use crate::pmem::{pmemspec_t::*, pmcopy_t::*, pmemutil_v::*, wrpm_t::*, subregion_v::*, traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe}};
use crate::log2::{append_v::*, layout_v::*, logspec_t::*, start_v::*, inv_v::*};
use crate::pmem::wrpm_t::WriteRestrictedPersistentMemoryRegion;

verus! {

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
    pub open spec fn recover(mem: Seq<u8>, log_start_addr: nat, log_size: nat) -> Option<AbstractLogState> 
    {
        if !metadata_types_set(mem, log_start_addr) {
            None
        } else {
            recover_state(mem, log_start_addr, log_size)
        }
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

    pub closed spec fn inv<Perm, PM>(self, pm: WriteRestrictedPersistentMemoryRegion<Perm, PM>, log_start_addr: nat, log_size: nat) -> bool
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion
    {
        &&& pm.inv()
        &&& self@.capacity >= self@.log.len()
        // &&& no_outstanding_writes_to_metadata(pm@)
        &&& memory_matches_deserialized_cdb(pm@, log_start_addr, self.cdb)
        &&& self.info.log_area_len + spec_log_area_pos() == log_size
        &&& log_start_addr + spec_log_area_pos() <= log_start_addr + log_size <= pm@.len() <= u64::MAX
        &&& metadata_consistent_with_info(pm@, log_start_addr, log_size, self.cdb, self.info)
        &&& info_consistent_with_log_area(pm@, log_start_addr, log_size, self.info, self.state@)
        &&& Self::can_only_crash_as_state(pm@, log_start_addr, log_size, self.state@.drop_pending_appends())
        &&& metadata_types_set(pm@.committed(), log_start_addr)
    }

    // This lemma makes some facts about non-private fields of self visible
    pub proof fn lemma_reveal_log_inv<Perm, PM>(self, pm: WriteRestrictedPersistentMemoryRegion<Perm, PM>, log_start_addr: nat, log_size: nat) 
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires
            self.inv(pm, log_start_addr, log_size),
        ensures
            log_start_addr + spec_log_area_pos() <= log_start_addr + log_size <= pm@.len() <= u64::MAX,
            metadata_types_set(pm@.committed(), log_start_addr)
    {}

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
                        &&& log_impl.inv(*pm_region, log_start_addr as nat, log_size as nat)
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
        Tracked(perm): Tracked<&Perm>,
        Ghost(is_writable_absolute_addr): Ghost<spec_fn(int) -> bool>,
    ) -> (result: Result<u128, LogErr>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(*old(wrpm_region), log_start_addr as nat, log_size as nat),
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
            forall |s| #[trigger] perm.check_permission(s) <==>
                    Self::recover(s, log_start_addr as nat, log_size as nat) == Some(self@.drop_pending_appends()),
        ensures
            spec_check_log_cdb(wrpm_region@.committed(), log_start_addr as nat) == spec_check_log_cdb(old(wrpm_region)@.committed(), log_start_addr as nat),
            wrpm_region.inv(),
            log_start_addr + spec_log_area_pos() <= log_start_addr + log_size <= wrpm_region@.len() <= u64::MAX,
            wrpm_region.constants() == old(wrpm_region).constants(),
            Self::can_only_crash_as_state(wrpm_region@, log_start_addr as nat, log_size as nat, self@.drop_pending_appends()),
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

        // Prove that any write allowed by `is_writable_absolute_addr` does not change the recovery state
        // and is thus crash safe
        assert forall |alt_region_view: PersistentMemoryRegionView, crash_state: Seq<u8>| {
            &&& #[trigger] alt_region_view.can_crash_as(crash_state)
            &&& wrpm_region@.len() == alt_region_view.len()
            &&& views_differ_only_where_subregion_allows(wrpm_region@, alt_region_view,
                                                        (log_start_addr + spec_log_area_pos()) as nat,
                                                        info.log_area_len as nat,
                                                        is_writable_absolute_addr)
        } implies perm.check_permission(crash_state) by {
            broadcast use pmcopy_axioms;
            lemma_if_view_differs_only_in_log_area_parts_not_accessed_by_recovery_then_recover_state_matches(
                wrpm_region@, alt_region_view, crash_state, log_start_addr as nat, log_size as nat, self.cdb, 
                self.info, self.state@, is_writable_absolute_addr
            );
            lemma_establish_extract_bytes_equivalence(wrpm_region@.committed(), alt_region_view.committed());
            lemma_header_bytes_equal_implies_active_metadata_bytes_equal(wrpm_region@.committed(), alt_region_view.committed(), log_start_addr as nat, log_size as nat);
            lemma_metadata_matches_implies_metadata_types_set(wrpm_region@, alt_region_view, log_start_addr as nat, self.cdb);
            lemma_metadata_set_after_crash(alt_region_view, log_start_addr as nat, self.cdb);
            assert(Self::recover(crash_state, log_start_addr as nat, log_size as nat) == Some(self@.drop_pending_appends()));
        }

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
            assert(forall |a: Seq<u8>, b: Seq<u8>| b == Seq::<u8>::empty() ==> a + b == a);
            assert(bytes_to_append@ =~= Seq::<u8>::empty());
            assert(self.info.tentatively_append(bytes_to_append.len() as u64) =~= self.info);
            assert(self.state@.tentatively_append(bytes_to_append@) =~= self.state@);
            assert(info_consistent_with_log_area(
                wrpm_region@,
                log_start_addr as nat,
                log_size as nat,
                self.info.tentatively_append(bytes_to_append.len() as u64),
                self.state@.tentatively_append(bytes_to_append@)
            ));
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
        Ghost(log_id): Ghost<u128>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<u128, LogErr>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires
            old(self).inv(*old(wrpm_region), log_start_addr as nat, log_size as nat),
            forall |s| #[trigger] perm.check_permission(s) <==>
                Self::recover(s, log_start_addr as nat, log_size as nat) == Some(old(self)@.drop_pending_appends()),
            no_outstanding_writes_to_metadata(old(wrpm_region)@, log_start_addr as nat),
        ensures
            self.inv(*wrpm_region, log_start_addr as nat, log_size as nat),
            wrpm_region.constants() == old(wrpm_region).constants(),
            Self::can_only_crash_as_state(wrpm_region@, log_start_addr as nat, log_size as nat, self@.drop_pending_appends()),
            match result {
                Ok(offset) => {
                    let state = old(self)@;
                    &&& offset == state.head + state.log.len() + state.pending.len()
                    &&& self@ == old(self)@.tentatively_append(bytes_to_append@)
                },
                Err(LogErr::InsufficientSpaceForAppend { available_space }) => {
                    &&& self@ == old(self)@
                    &&& available_space < bytes_to_append@.len()
                    &&& {
                            ||| available_space == self@.capacity - self@.log.len() - self@.pending.len()
                            ||| available_space == u128::MAX - self@.head - self@.log.len() - self@.pending.len()
                        }
                },
                _ => false
            },
    {
        reveal(spec_padding_needed);
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
        let result = self.tentatively_append_to_log(wrpm_region, log_start_addr, log_size, bytes_to_append, Tracked(perm), Ghost(is_writable_absolute_addr_fn));

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
            self.inv(*pm_region, log_start_addr as nat, log_size as nat),
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
        Tracked(perm): Tracked<&Perm>,
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion
        requires
            old(wrpm_region).inv(),
            memory_matches_deserialized_cdb(old(wrpm_region)@, log_start_addr as nat, old(self).cdb),
            no_outstanding_writes_to_metadata(old(wrpm_region)@, log_start_addr as nat),
            metadata_consistent_with_info(old(wrpm_region)@, log_start_addr as nat, log_size as nat, old(self).cdb, prev_info),
            info_consistent_with_log_area(old(wrpm_region)@.flush(), log_start_addr as nat, log_size as nat, old(self).info, old(self).state@),
            info_consistent_with_log_area(old(wrpm_region)@, log_start_addr as nat, log_size as nat, prev_info, prev_state),
            old(self).info.log_area_len == prev_info.log_area_len,
            forall |s| {
                        ||| Self::recover(s, log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends())
                        ||| Self::recover(s, log_start_addr as nat, log_size as nat) == Some(old(self).state@.drop_pending_appends())
                    } ==> #[trigger] perm.check_permission(s),
            metadata_types_set(old(wrpm_region)@.committed(), log_start_addr as nat),
            log_start_addr < log_start_addr + log_size < old(wrpm_region)@.len() <= u64::MAX,
            log_start_addr as int % const_persistence_chunk_size() == 0,
        ensures
            self.inv(*wrpm_region, log_start_addr as nat, log_size as nat),
            wrpm_region.constants() == old(wrpm_region).constants(),
            self.state == old(self).state,
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
            Ghost(prev_info), Ghost(prev_state), Ghost(is_writable_absolute_addr), Tracked(perm));

        // Prove that after the flush we're about to do, all our
        // invariants will continue to hold (using the still-unchanged
        // CDB and the old metadata, infos, and state).
        // assert(false);
        proof {
            lemma_flushing_metadata_maintains_invariants(wrpm_region@, log_start_addr as nat, log_size as nat, self.cdb, prev_info, prev_state);
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

        assert forall |crash_bytes| pm_region_after_write.can_crash_as(crash_bytes) implies
                    #[trigger] perm.check_permission(crash_bytes) by {
            lemma_invariants_imply_crash_recover_forall(wrpm_region@, log_start_addr as nat, log_size as nat,
                                                        self.cdb, prev_info, prev_state);
            lemma_single_write_crash_effect_on_pm_region_view(wrpm_region@, log_start_addr as int,
                                                                new_cdb_bytes);
            if crash_bytes == wrpm_region@.committed() {
                assert(wrpm_region@.can_crash_as(crash_bytes));
            }
            else {
                assert(pm_region_after_flush.can_crash_as(crash_bytes));
            }
        }

        // Finally, update the CDB, then flush, then flip `self.cdb`.
        // There's no need to flip `self.cdb` atomically with the write
        // since the flip of `self.cdb` is happening in local
        // non-persistent memory so if we crash it'll be lost anyway.
        wrpm_region.serialize_and_write(log_start_addr, &new_cdb, Tracked(perm));
        wrpm_region.flush();
        self.cdb = !self.cdb;
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
        Tracked(perm): Tracked<&Perm>,
    )
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires 
            old(wrpm_region).inv(),
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
            forall |s| {
                    ||| Self::recover(s, log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends())
                    ||| Self::recover(s, log_start_addr as nat, log_size as nat) == Some(self.state@.drop_pending_appends())
                } ==> #[trigger] perm.check_permission(s),
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
    {
        // broadcast use pmcopy_axioms;

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
            // To prove that there are no outstanding updates to inactive metadata, we have to prove that it doesn't run into the log area.
            // We have to do this by compute; since there are two possible inactive metadata positions, we have to do case analysis
            assert(spec_get_inactive_log_metadata_pos(self.cdb) == spec_log_header_pos_cdb_false() || spec_get_inactive_log_metadata_pos(self.cdb) == spec_log_header_pos_cdb_true());
            if spec_get_inactive_log_metadata_pos(self.cdb) == spec_log_header_pos_cdb_false() {
                assert(spec_log_header_pos_cdb_false() + LogMetadata::spec_size_of() + u64::spec_size_of() <= spec_log_area_pos()) by (compute_only);
            } else {
                assert(spec_log_header_pos_cdb_true() + LogMetadata::spec_size_of() + u64::spec_size_of() <= spec_log_area_pos()) by (compute_only);
            }
            assert(spec_get_inactive_log_metadata_pos(self.cdb) + LogMetadata::spec_size_of() + u64::spec_size_of() <= spec_log_area_pos());
            assert(inactive_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of() <= log_start_addr + spec_log_area_pos());

            assert(wrpm_region@.no_outstanding_writes_in_range(inactive_metadata_pos as int, inactive_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()));
        } 

        // Prove that all crash states are legal by invoking the lemma that proves that if we only
        // modify inactive metadata and unreachable log bytes, the recovery state of all possible
        // crash states matches the original recovery state.
        assert forall |alt_region_view: PersistentMemoryRegionView, crash_state: Seq<u8>| {
            &&& #[trigger] alt_region_view.can_crash_as(crash_state)
            &&& wrpm_region@.len() == alt_region_view.len()
            &&& views_differ_only_where_subregion_allows(wrpm_region@, 
                alt_region_view, log_start_addr as nat, log_size as nat, is_writable_absolute_addr)
        } implies perm.check_permission(crash_state) by {
            lemma_if_view_differs_only_in_inactive_metadata_and_unreachable_log_area_then_recovery_state_matches(
                wrpm_region@, alt_region_view, crash_state, log_start_addr as nat, log_size as nat, self.cdb, 
                prev_info, prev_state, is_writable_absolute_addr
            );
            lemma_establish_extract_bytes_equivalence(wrpm_region@.committed(), alt_region_view.committed());
            lemma_metadata_matches_implies_metadata_types_set(wrpm_region@, alt_region_view, log_start_addr as nat, self.cdb);
            lemma_metadata_set_after_crash(alt_region_view, log_start_addr as nat, self.cdb);
            assert(Self::recover(crash_state, log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends()));
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

    // // The `commit` method commits all tentative appends that have been
    // // performed since the last one. See `README.md` for more
    // // documentation and examples of its use.
    // //
    // // This method is passed a write-restricted persistent memory
    // // region `wrpm_region`. This restricts how it can write
    // // `wrpm_region`. It's only given permission (in `perm`) to
    // // write if it can prove that any crash after initiating the
    // // write is safe. That is, any such crash must put the memory
    // // in a state that recovers as either (1) the current abstract
    // // state with all pending appends dropped, or (2) the abstract
    // // state after all pending appends are committed.
    // pub exec fn commit<Perm, PM>(
    //     &mut self,
    //     wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
    //     log_start_addr: u64,
    //     log_size: u64,
    //     Tracked(perm): Tracked<&Perm>,
    // ) -> (result: Result<(), LogErr>)
    //     where
    //         Perm: CheckPermission<Seq<u8>>,
    //         PM: PersistentMemoryRegion
    //     requires
    //         old(self).inv(*old(wrpm_region), log_start_addr as nat, log_size as nat),
    //         forall |s| #[trigger] perm.check_permission(s) <==> {
    //             ||| Self::recover(s, log_start_addr as nat, log_size as nat) == Some(old(self)@.drop_pending_appends())
    //             ||| Self::recover(s, log_start_addr as nat, log_size as nat) == Some(old(self)@.commit().drop_pending_appends())
    //         },
    //     ensures
    //         self.inv(*wrpm_region, log_start_addr as nat, log_size as nat),
    //         wrpm_region.constants() == old(wrpm_region).constants(),
    //         Self::can_only_crash_as_state(wrpm_region@, log_start_addr as nat, log_size as nat, self@.drop_pending_appends()),
    //         result is Ok,
    //         self@ == old(self)@.commit(),
    // {
    //     let ghost prev_info = self.info;
    //     let ghost prev_state = self.state@;

    //     self.state = Ghost(self.state@.commit());

    //     self.info.log_length = self.info.log_plus_pending_length;

    //     assert(memory_matches_deserialized_cdb(wrpm_region@, log_start_addr as nat, self.cdb));
    //     assert(metadata_consistent_with_info(wrpm_region@, log_start_addr as nat, log_size as nat, self.cdb, prev_info));
    //     assert(info_consistent_with_log_area(wrpm_region@, log_start_addr as nat, log_size as nat, prev_info, prev_state));
    //     assert(self.state@ == prev_state.commit());
    //     assert(info_consistent_with_log_area(wrpm_region@.flush(), log_start_addr as nat, log_size as nat, self.info, self.state@));

    //     // Update the inactive metadata on all regions and flush, then
    //     // swap the CDB to its opposite.

    //     self.update_log_metadata(wrpm_region, Ghost(prev_info), Ghost(prev_state), Tracked(perm));

    //     Ok(())
    // }

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
            self.inv(*pm_region, log_start_addr as nat, log_size as nat)
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
}
    
}

/*
        // this is how the original implementation uses subregions
        // // Update the inactive log metadata by creating a
        // // subregion and invoking `update_inactive_log_metadata`.
        // // The main interesting part of creating the subregion is
        // // establishing a condition `condition` such that (1)
        // // `condition(crash_state) ==>
        // // perm.check_permission(crash_state)` and (2) `condition`
        // // is preserved by updating writable addresses within the
        // // subregion.

        // // // let ghost is_writable_absolute_addr_fn = |addr: int| true;
        // let ghost condition = |mem: Seq<u8>| {
        //     &&& mem.len() >= log_start_addr + log_size
        //     &&& recover_cdb(mem, log_start_addr as nat) == Some(self.cdb)
        //     &&& recover_state(mem, log_start_addr as nat, log_size as nat) == Some(prev_state.drop_pending_appends())
        //     &&& metadata_types_set(mem, log_start_addr as nat)
        // };
        // assert forall |s1: Seq<u8>, s2: Seq<u8>| {
        //     &&& condition(s1)
        //     &&& s1.len() == s2.len() == wrpm_region@.len()
        //     &&& #[trigger] memories_differ_only_where_subregion_allows(s1, s2, inactive_metadata_pos as nat,
        //         LogMetadata::spec_size_of() + u64::spec_size_of(), is_writable_absolute_addr)
        // } implies condition(s2) by {
        //     assume(false);
        //     lemma_if_only_differences_in_memory_are_inactive_metadata_then_recover_state_matches(
        //         s1, s2, log_start_addr as nat, log_size as nat, self.cdb
        //     );
        // }
        // assert forall |crash_state: Seq<u8>| wrpm_region@.can_crash_as(crash_state) implies condition(crash_state) by {
        //     assume(false);
        //     // lemma_invariants_imply_crash_recover_forall(wrpm_region@, log_id, self.cdb, prev_info, prev_state);
        // }

        // wrpm_region.flush(); // this might be helpful?

        // // Since we aren't using real subregions, we need to include a proof here that addresses allowed by the 
        // // is_writable_absolute_addr closure are safe to write to
        assert forall |alt_region_view: PersistentMemoryRegionView, crash_state: Seq<u8>| {
            &&& #[trigger] alt_region_view.can_crash_as(crash_state)
            &&& wrpm_region@.len() == alt_region_view.len()
            &&& views_differ_only_where_subregion_allows(wrpm_region@, alt_region_view,
                                                        inactive_metadata_pos as nat,
                                                        LogMetadata::spec_size_of() + u64::spec_size_of(),
                                                        is_writable_absolute_addr)
        } implies perm.check_permission(crash_state) by {

            // The challenge here is that we don't have subregions, so we have to reason about the entire state,
            // which may include other tentative updates in unreachable parts of the log area. This means 
            // that a lot of our existing lemmas are not very helpful, because they assume that we know exactly
            // where all the differences in memory are.

            // we could take a different approach -- as long as there are no outstanding updates to live/active bytes,
            // then the crash state will always be the same.
            // assert(no_outstanding_writes_to_active_metadata(alt_region_view, log_start_addr as nat, self.cdb));
            // assert(alt_region_view.no_outstanding_writes_in_range(log_start_addr as int, log_start_addr + u64::spec_size_of()));

        //     lemma_if_only_differences_in_memory_are_inactive_metadata_then_recover_state_matches(wrpm_region@.committed(), alt_region_view.committed(),
        //         log_start_addr as nat, log_size as nat, self.cdb);

        //     lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(alt_region_view);

        // //     // assert(wrpm_region@.no_outstanding_writes_in_range(0, inactive_metadata_pos as int));
        // //     // assert(wrpm_region@.no_outstanding_writes_in_range(log_start_addr + log_size, wrpm_region@.len() as int));
            
        // //     // assert(alt_region_view.no_outstanding_writes_in_range(0, inactive_metadata_pos as int));
        // //     // assert(alt_region_view.no_outstanding_writes_in_range(log_start_addr + log_size, alt_region_view.len() as int));

        //     // There may be differences in the inactive log, but they would have been lost in a crash...? not necessarily
        //     lemma_if_only_differences_in_memory_are_inactive_metadata_then_recover_state_matches(wrpm_region@.committed(), crash_state,
        //         log_start_addr as nat, log_size as nat, self.cdb);
            

            // // from views_differ_only_where_subregion_allows
            // assert(forall |addr: int| {
            //     ||| 0 <= addr < inactive_metadata_pos
            //     ||| inactive_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of() <= addr < alt_region_view.len()
            //     ||| inactive_metadata_pos <= addr < inactive_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of() && !is_writable_absolute_addr(addr)
            // } ==> {
            //     wrpm_region@.committed()[addr] == #[trigger] alt_region_view.committed()[addr]
            // });

            // assert(forall |addr: int| {
            //     &&& 0 <= addr < wrpm_region@.len()
            //     &&& wrpm_region@.committed()[addr] == #[trigger] alt_region_view.committed()[addr]
            // } ==> wrpm_region@.committed()[addr] == crash_state[addr]);

        //     // assert(forall |addr: int| 0 <= addr < crash_state.len() && !(inactive_metadata_pos <= addr < inactive_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()) ==> 
        //     //     wrpm_region@.committed()[addr] == #[trigger] crash_state[addr]);

        //     // lemma_if_only_differences_in_memory_are_inactive_metadata_then_recover_state_matches2(wrpm_region@, alt_region_view, crash_state,
        //     //     log_start_addr as nat, log_size as nat, self.cdb, self.info, self.state@, is_writable_absolute_addr);
        //     lemma_establish_extract_bytes_equivalence(wrpm_region@.committed(), alt_region_view.committed());
        //     // lemma_header_bytes_equal_implies_active_metadata_bytes_equal(wrpm_region@.committed(), alt_region_view.committed(), log_start_addr as nat, log_size as nat);
            
        //     assert(no_outstanding_writes_to_active_metadata(alt_region_view, log_start_addr as nat, self.cdb));
        //     assert(active_metadata_is_equal(wrpm_region@, alt_region_view, log_start_addr as nat));
        //     assert(memory_matches_deserialized_cdb(wrpm_region@, log_start_addr as nat, self.cdb));

        //     lemma_metadata_matches_implies_metadata_types_set(wrpm_region@, alt_region_view, log_start_addr as nat, self.cdb);
        //     lemma_metadata_set_after_crash(alt_region_view, log_start_addr as nat, self.cdb);

        //     // assert(spec_get_active_log_metadata(wrpm_region@.committed(), log_start_addr as nat, self.cdb) == spec_get_active_log_metadata(crash_state, log_start_addr as nat, self.cdb));
        //     // assume(false);

            
        //     // proving this is sufficient to prove the assertion
        //     assert(Self::recover(wrpm_region@.committed(), log_start_addr as nat, log_size as nat) == Some(self@.drop_pending_appends()));
        //     assert(Self::recover(crash_state, log_start_addr as nat, log_size as nat) is Some);
            assert(Self::recover(crash_state, log_start_addr as nat, log_size as nat) == Some(self@.drop_pending_appends()));
        }

 */