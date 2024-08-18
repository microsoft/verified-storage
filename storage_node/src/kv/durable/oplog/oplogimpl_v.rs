use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::{
    kv::{durable::{metadata::layout_v::*, oplog::{logentry_v::*, oplogspec_t::*}},
            kvimpl_t::*, layout_v::*},
    log2::{logimpl_v::*, logspec_t::*, layout_v::*, inv_v::*},
    pmem::{pmemspec_t::*, wrpm_t::*, pmemutil_v::*, pmcopy_t::*, traits_t, crc_t::*},
};
use vstd::bytes::*;

use super::inv_v::*;

verus! {
    pub struct UntrustedOpLog<K, L>
        where 
            L: PmCopy + std::fmt::Debug + Copy,
    {
        log: UntrustedLogImpl,
        overall_metadata: OverallMetadata,
        state: Ghost<AbstractOpLogState>,
        current_transaction_crc: CrcDigest,
        _phantom: Option<(K, L)>
    }

    impl<K, L> UntrustedOpLog<K, L>
        where 
            L: PmCopy + std::fmt::Debug + Copy,
            K: std::fmt::Debug,
    {

        pub closed spec fn log_start_addr(self) -> u64 {
            self.overall_metadata.log_area_addr
        }

        pub closed spec fn log_size(self) -> u64 {
            self.overall_metadata.log_area_size
        }

        pub closed spec fn overall_metadata(self) -> OverallMetadata {
            self.overall_metadata
        }

        pub closed spec fn base_log_capacity(self) -> int {
            self.log@.capacity
        }

        pub closed spec fn base_log_view(self) -> AbstractLogState {
            self.log@
        }

        pub closed spec fn log_entry_valid(self, pm_region: PersistentMemoryRegionView, op: AbstractPhysicalOpLogEntry) -> bool {
            // all addrs are within the bounds of the device
            &&& 0 <= op.absolute_addr < op.absolute_addr + op.len < pm_region.len() <= u64::MAX
            // no logged ops change bytes belonging to the log itself
            &&& (op.absolute_addr + op.len < self.overall_metadata.log_area_addr || self.overall_metadata.log_area_addr + self.overall_metadata.log_area_size <= op.absolute_addr)
            &&& op.bytes.len() <= u64::MAX
        }

        pub closed spec fn crc_invariant(self) -> bool {
            &&& !self@.op_list_committed && self.log@.pending.len() > 0 ==> self.current_transaction_crc.bytes_in_digest().flatten() == self.log@.pending
            &&& self.log@.pending.len() == 0 ==> self.current_transaction_crc.bytes_in_digest().len() == 0
        }

        pub closed spec fn inv<Perm, PM>(self, pm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>) -> bool
            where 
                Perm: CheckPermission<Seq<u8>>,
                PM: PersistentMemoryRegion,
        {
            &&& self.log.inv(pm_region, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat)
            &&& ({
                    // either the base log is empty or the op log is committed and non-empty
                    ||| self.log@.log.len() == 0
                    ||| (self@.op_list_committed && self@.physical_op_list.len() > 0)
                })
            &&& self.crc_invariant()
            &&& !self@.op_list_committed ==> {
                // if we aren't committed, then parsing the pending bytes (ignoring crc check,
                // since we haven't written the CRC yet) should give us the current abstract log op list
                let pending_bytes = self.log@.pending;
                let log_ops = Self::parse_log_ops(pending_bytes, self.overall_metadata.log_area_addr as nat, 
                    self.overall_metadata.log_area_size as nat, self.overall_metadata.region_size as nat);
                ||| {
                        &&& log_ops is Some 
                        &&& log_ops.unwrap() == self@.physical_op_list
                    }
            }
            &&& self@.op_list_committed ==> {
                let log_contents = Self::get_log_contents(self.log@);
                let log_ops = Self::parse_log_ops(log_contents.unwrap(), self.log_start_addr() as nat, 
                    self.log_size() as nat, self.overall_metadata.region_size as nat);
                &&& log_contents is Some
                &&& log_ops is Some
                &&& log_ops.unwrap() == self@.physical_op_list
                &&& self.log@.log.len() > 0
            }
            &&& forall |i: int| 0 <= i < self@.physical_op_list.len() ==> {
                    let op = #[trigger] self@.physical_op_list[i];
                    self.log_entry_valid(pm_region@, op)
            } 
            &&& self.overall_metadata.log_area_addr < self.overall_metadata.log_area_addr + self.overall_metadata.log_area_size <= pm_region@.len() <= u64::MAX
            &&& self.overall_metadata.log_area_addr as int % const_persistence_chunk_size() == 0
            &&& no_outstanding_writes_to_metadata(pm_region@, self.overall_metadata.log_area_addr as nat)
        }

        pub closed spec fn view(self) -> AbstractOpLogState
        {
            self.state@
        }

        pub closed spec fn log_len(self) -> nat {
            self.log@.log.len()
        }

        pub open spec fn recover(mem: Seq<u8>, overall_metadata: OverallMetadata) -> Option<AbstractOpLogState>
        {
            // use log's recover method to recover the log state, then parse it into operations
            match UntrustedLogImpl::recover(mem, overall_metadata.log_area_addr as nat,
                                            overall_metadata.log_area_size as nat) {
                Some(log) => {
                    if log.log.len() == 0 {
                        Some(AbstractOpLogState::initialize())
                    } else {
                        if let Some(log_contents) = Self::get_log_contents(log) {
                            // parsing the log only obtains physical entries, but we (should) know that there is a corresponding logical op log (even
                            // if we don't know exactly what it is)
                            if let Some(physical_log_entries) =  Self::parse_log_ops(
                                log_contents, 
                                overall_metadata.log_area_addr as nat, 
                                overall_metadata.log_area_size as nat,
                                overall_metadata.region_size as nat
                            ) {
                                    Some(AbstractOpLogState {
                                        physical_op_list: physical_log_entries,
                                        op_list_committed: true
                                    })
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    }
                }
                None => None
            }
        }

        // This helper function obtains committed contents of the op log as bytes, reads the CRC, and checks
        // that the CRC matches the rest of the log 
        pub open spec fn get_log_contents(log: AbstractLogState) -> Option<Seq<u8>>
        {
            let log_contents = extract_bytes(log.log, 0, (log.log.len() - u64::spec_size_of()) as nat);
            let crc_bytes = extract_bytes(log.log, (log.log.len() - u64::spec_size_of()) as nat, u64::spec_size_of());
            let crc = u64::spec_from_bytes(crc_bytes);
            // if the crc written at the end of the transaction does not match the crc of the rest of the log contents, the log is invalid
            if !u64::bytes_parseable(crc_bytes) {
                None
            } else if crc != spec_crc_u64(log_contents) {
                None
            } else {
                Some(log_contents)
            }
        }

        proof fn lemma_parse_up_to_offset_succeeds(
            offset: nat,
            pm_region: PersistentMemoryRegionView,
            log_contents: Seq<u8>,
            overall_metadata: OverallMetadata,
        )
            requires 
                UntrustedOpLog::<K, L>::recover(pm_region.committed(), overall_metadata) is Some,
                ({
                    let base_log = UntrustedLogImpl::recover(pm_region.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat);
                    &&& base_log matches Some(base_log)
                    &&& base_log.log.len() > 0
                    &&& log_contents == extract_bytes(base_log.log, 0, (base_log.log.len() - u64::spec_size_of()) as nat)
                }),
                Self::parse_log_ops_helper(0, offset, log_contents, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat) is Some,
                offset < log_contents.len(),
                u64::spec_size_of() < log_contents.len(),
            ensures 
                Self::parse_log_op(offset, log_contents, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat) is Some
        {
            // Proof by contradiction: if the op at offset cannot be parsed, then the whole op log cannot be parsed;
            // but the precondition says it can, so the op log must be valid/parseable.
            if Self::parse_log_op(offset, log_contents, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat) is None {
                assert(Self::parse_log_ops_helper(offset, log_contents.len(), log_contents, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat) is None);
                Self::lemma_partial_parse_fails_implies_full_parse_fails(0, offset, log_contents.len(), log_contents, 
                    overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat);
                assert(false);
            }
        }

        // This inductive lemma proves that if a prefix of the log can be parsed successfully
        // but the rest of the log cannot be parsed, attempting to parse the entire log will fail.
        // We use this in a proof by contradiction in `lemma_parse_up_to_offset_succeeds`
        proof fn lemma_partial_parse_fails_implies_full_parse_fails(
            start: nat,
            mid: nat,
            end: nat,
            log_contents: Seq<u8>,
            log_start_addr: nat, 
            log_size: nat,
            region_size: nat,
        )
            requires 
                start <= mid <= end <= log_contents.len(),
                Self::parse_log_ops_helper(mid, end, log_contents, log_start_addr, log_size, region_size) is None,
                Self::parse_log_ops_helper(start, mid, log_contents, log_start_addr, log_size, region_size) is Some,
                end == log_contents.len(),
            ensures 
                Self::parse_log_ops_helper(start, end, log_contents, log_start_addr, log_size, region_size) is None,
            decreases end - start
        {
            if start == mid {
                // trivial 
            } else {
                let next_op = Self::parse_log_op(start, log_contents, log_start_addr, log_size, region_size).unwrap();
                let next_start = start + u64::spec_size_of() * 2 + next_op.len;
                Self::lemma_partial_parse_fails_implies_full_parse_fails(next_start, mid, end, log_contents, log_start_addr, log_size, region_size);
            }
        }

        // This lemma helps us prove that recursively parsing the physical log (which, due to the 
        // structure of the log, can only be specified in one direction, which happens to 
        // be opposite of the direction we want) is equivalent to iteratively parsing it. We invoke
        // this lemma to maintain the loop invariant of `parse_phys_op_log` which states that 
        // iteratively parsing the log up to the current offset is equivalent to recursively
        // parsing it up to that same offset.
        proof fn lemma_op_log_parse_equal(
            start: nat,
            mid: nat,
            end: nat,
            log_contents: Seq<u8>,
            log_start_addr: nat, 
            log_size: nat,
            region_size: nat,
        )
        requires
            start <= mid <= end <= log_contents.len(),
            Self::parse_log_ops_helper(start, mid, log_contents, log_start_addr, log_size, region_size) is Some,
            Self::parse_log_op(mid, log_contents, log_start_addr, log_size, region_size) is Some,
            ({
                let last_op = Self::parse_log_op(mid, log_contents, log_start_addr, log_size, region_size);
                &&& last_op matches Some(last_op)
                &&& end == mid + u64::spec_size_of() * 2 + last_op.len
            })
        ensures 
            Self::parse_log_ops_helper(start, end, log_contents, log_start_addr, log_size, region_size) is Some,
            ({
                let old_seq = Self::parse_log_ops_helper(start, mid, log_contents, log_start_addr, log_size, region_size).unwrap();
                let new_seq = Self::parse_log_ops_helper(start, end, log_contents, log_start_addr, log_size, region_size).unwrap();
                let last_op = Self::parse_log_op(mid, log_contents, log_start_addr, log_size, region_size).unwrap();
                new_seq == old_seq + seq![last_op]
            }),
        decreases end - start
        {
            let old_seq = Self::parse_log_ops_helper(start, mid,log_contents, log_start_addr, log_size, region_size).unwrap();
            let last_op = Self::parse_log_op(mid, log_contents, log_start_addr, log_size, region_size).unwrap();

            if mid == start {
                // Base case: old_seq is empty.
                // This case is not trivial; Verus needs some help reasoning about the end point as well
                assert(Some(Seq::<AbstractPhysicalOpLogEntry>::empty()) == Self::parse_log_ops_helper(end, end, log_contents, log_start_addr, log_size, region_size));
                return;
            }
            // first_op + middle_section == parse_log_ops_helper(start, mid, ...) by the definition of parse (which prepends earlier entries
            // onto the sequence of parsed ops)
            let first_op = Self::parse_log_op(start, log_contents, log_start_addr, log_size, region_size).unwrap();
            let next_start = start + u64::spec_size_of() * 2 + first_op.len;
            let middle_section = Self::parse_log_ops_helper(next_start, mid, log_contents, log_start_addr, log_size, region_size).unwrap();

            // associativity 
            assert((seq![first_op] + middle_section) + seq![last_op] == seq![first_op] + (middle_section + seq![last_op]));

            Self::lemma_op_log_parse_equal(next_start, mid, end, log_contents, log_start_addr, log_size, region_size);  
        }

        // This lemma proves that if one sequence is a prefix of another sequence and the shorter sequence
        // can be successfully parsed as an operation log, then the matching subrange/prefix of the longer
        // sequence can also be parsed as an operation log. This lemma is a wrapper around an an inductive
        // proof function that does all of the actual work.
        proof fn lemma_parsing_same_range_equal(
            mem1: Seq<u8>,
            mem2: Seq<u8>,
            log_start_addr: nat,
            log_size: nat,
            region_size: nat,
        )
            requires 
                extract_bytes(mem2, 0, mem1.len()) == mem1,
                mem2.len() > mem1.len(),
                Self::parse_log_ops_helper(0, mem1.len(), mem1, log_start_addr, log_size, region_size) is Some,
            ensures 
                Self::parse_log_ops_helper(0, mem1.len(), mem1, log_start_addr, log_size, region_size) =~=
                    Self::parse_log_ops_helper(0, mem1.len(), mem2, log_start_addr, log_size, region_size)
        {
            let mem2_prefix = extract_bytes(mem2, 0, mem1.len());
            assert(Self::parse_log_ops_helper(0, mem1.len(), mem1, log_start_addr, log_size, region_size) =~=
                Self::parse_log_ops_helper(0, mem2_prefix.len(), mem2_prefix, log_start_addr, log_size, region_size));
            Self::lemma_inductive_parsing_same_range_equal(0, mem1.len(), mem1, mem2, log_start_addr, log_size, region_size);
        }

        // This helper lemma does the key work to prove lemma_parsing_same_range_equal.
        // It inductively proves that each parsed operation in the longer sequence's prefix
        // is equivalent to the corresponding parsed operation in the shorter sequence.
        proof fn lemma_inductive_parsing_same_range_equal(
            current_offset: nat,
            target_offset: nat,
            mem1: Seq<u8>,
            mem2: Seq<u8>,
            log_start_addr: nat,
            log_size: nat,
            region_size: nat,
        )
            requires 
                current_offset <= target_offset <= mem1.len() <= mem2.len(),
                target_offset == mem1.len(),
                extract_bytes(mem2, 0, mem1.len()) == mem1,
                Self::parse_log_ops_helper(current_offset, target_offset, mem1, log_start_addr, log_size, region_size) is Some,
            ensures 
                Self::parse_log_ops_helper(current_offset, target_offset, mem1, log_start_addr, log_size, region_size) =~=
                    Self::parse_log_ops_helper(current_offset, target_offset, mem2, log_start_addr, log_size, region_size)
            decreases target_offset - current_offset 
        {
            if target_offset == current_offset {
                // trivial
            } else {
                lemma_establish_extract_bytes_equivalence(mem1, mem2);
                let mem1_op = Self::parse_log_op(current_offset, mem1, log_start_addr, log_size, region_size);
                let entry_size = u64::spec_size_of() * 2 + mem1_op.unwrap().len;
                let next_offset = current_offset + entry_size;
                Self::lemma_inductive_parsing_same_range_equal(
                    next_offset,
                    target_offset,
                    mem1,
                    mem2, 
                    log_start_addr,
                    log_size,
                    region_size
                );
            }
        }

        // This spec function parses an individual op log entry at the given offset. It returns None
        // if the log entry is invalid, i.e., its address and length don't fit within the log area or 
        // if the length is 0.
        pub open spec fn parse_log_op(
            offset: nat,
            log_contents: Seq<u8>,
            log_start_addr: nat, 
            log_size: nat,
            region_size: nat,
        ) -> Option<AbstractPhysicalOpLogEntry>
        {
            // 1. Read the absolute addr and log entry size
            let absolute_addr = u64::spec_from_bytes(extract_bytes(log_contents, offset, u64::spec_size_of()));
            let len = u64::spec_from_bytes(extract_bytes(log_contents, offset + u64::spec_size_of(), u64::spec_size_of()));
            if {
                ||| offset + u64::spec_size_of() * 2 > u64::MAX
                ||| offset + u64::spec_size_of() * 2 + len > u64::MAX
                ||| absolute_addr + len > u64::MAX
                ||| absolute_addr + len > region_size
                ||| offset + u64::spec_size_of() * 2 > log_contents.len()
                ||| offset + u64::spec_size_of() * 2 + len > log_contents.len()
                ||| !({
                    ||| absolute_addr < absolute_addr + len <= log_start_addr // region end before log area
                    ||| log_start_addr + log_size <= absolute_addr < absolute_addr + len // region ends after log area
                })
                ||| len == 0
                ||| log_contents.len() - u64::spec_size_of() * 2 < len
            } {
                // if the entry contains invalid values, recovery fails
                None 
            } else {
                // 2. Read the log entry contents
                let log_entry_contents = extract_bytes(log_contents, offset + u64::spec_size_of() * 2, len as nat);

                // 3. Construct the physical log entry
                // let new_op = AbstractPhysicalOpLogEntry { offset, absolute_addr: entry_header.absolute_addr as nat, len: entry_header.len as nat, bytes: log_entry_contents };
                let new_op = AbstractPhysicalOpLogEntry { absolute_addr: absolute_addr as nat, len: len as nat, bytes: log_entry_contents };

                Some(new_op)
            }
        }

        pub open spec fn parse_log_ops(
            log_contents: Seq<u8>,
            log_start_addr: nat, 
            log_size: nat,
            region_size: nat,
        ) -> Option<Seq<AbstractPhysicalOpLogEntry>>
        {
            Self::parse_log_ops_helper(0, log_contents.len(),  log_contents, log_start_addr, log_size, region_size)
        }

        pub open spec fn parse_log_ops_helper(
            current_offset: nat,
            target_offset: nat,
            log_contents: Seq<u8>,
            log_start_addr: nat, 
            log_size: nat,
            region_size: nat,
        ) -> Option<Seq<AbstractPhysicalOpLogEntry>>
            decreases target_offset - current_offset
        {
            if target_offset == current_offset {
                Some(Seq::empty())
            } else {
                // parse the log entry at the current offset
                let op = Self::parse_log_op(current_offset, log_contents, log_start_addr, log_size, region_size);
                if let Some(op) = op {
                    let entry_size = u64::spec_size_of() * 2 + op.len;
                    if target_offset < current_offset + entry_size {
                        None
                    } else {
                        let seq = Self::parse_log_ops_helper(
                            current_offset + entry_size,
                            target_offset, 
                            log_contents, 
                            log_start_addr,
                            log_size,
                            region_size
                        );
                        if let Some(seq) = seq {
                            Some(seq![op] + seq)
                        } else {
                            None
                        }
                    }
                } else {
                    None
                }
            }
        }

        // This lemma proves that if we can parse the given log area from `current_offset`
        // to `target_offset` as a valid operation log, then certain invariants hold
        // about the resulting parsed log.
        pub proof fn lemma_successful_log_ops_parse_implies_inv(
            current_offset: nat,
            target_offset: nat,
            log_contents: Seq<u8>,
            overall_metadata: OverallMetadata,
        )
            requires 
                Self::parse_log_ops_helper(current_offset, target_offset, log_contents, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat) is Some 
            ensures 
                ({
                    let parsed_log = Self::parse_log_ops_helper(current_offset, target_offset, log_contents, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat).unwrap();
                    AbstractPhysicalOpLogEntry::log_inv(parsed_log, overall_metadata)
                })
            decreases target_offset - current_offset
        {
            if target_offset == current_offset {
                // trivial
            } else {
                let op = Self::parse_log_op(current_offset, log_contents, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat);
                assert(op is Some); // inv holds when op can be parsed
                let entry_size = u64::spec_size_of() * 2 + op.unwrap().len;
                Self::lemma_successful_log_ops_parse_implies_inv(
                    current_offset + entry_size,
                    target_offset,
                    log_contents,
                    overall_metadata
                );
            }
        }

        // This executable function parses the entire operation log iteratively
        // and returns a vector of `PhysicalOpLogEntry`. This operation will fail 
        // if the CRC for the op log does not match the rest of the log body or 
        // if any of the log entries themselves are invalid.
        pub exec fn parse_phys_op_log<Perm, PM>(
            pm_region: &WriteRestrictedPersistentMemoryRegion<Perm, PM>,
            log_bytes: Vec<u8>,
            overall_metadata: OverallMetadata
        ) -> (result: Result<Vec<PhysicalOpLogEntry>, KvError<K>>)
            where 
                Perm: CheckPermission<Seq<u8>>,
                PM: PersistentMemoryRegion,
            requires
                pm_region.inv(),
                pm_region@.no_outstanding_writes(),
                overall_metadata.log_area_addr + overall_metadata.log_area_size <= pm_region@.len() <= u64::MAX,
                overall_metadata.log_area_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
                Self::recover(pm_region@.committed(), overall_metadata) is Some,
                pm_region@.len() == overall_metadata.region_size,
                ({
                    let base_log_state = UntrustedLogImpl::recover(pm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat);
                    &&& base_log_state matches Some(base_log_state)
                    &&& log_bytes@ == extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat)
                }),
                ({
                    let base_log_state = UntrustedLogImpl::recover(pm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
                    let phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
                    let abstract_op_log = Self::parse_log_ops(phys_op_log_buffer, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat);
                    &&& abstract_op_log matches Some(abstract_log)
                    &&& 0 < abstract_log.len() <= u64::MAX
                }),
                ({
                    let recovered_log = UntrustedOpLog::<K, L>::recover(pm_region@.committed(), overall_metadata);
                    let parsed_ops = Self::parse_log_ops(log_bytes@, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat);
                    &&& recovered_log matches Some(recovered_log)
                    &&& parsed_ops matches Some(parsed_ops)
                    &&& recovered_log.physical_op_list == parsed_ops
                }),
                u64::spec_size_of() * 2 <= log_bytes.len() <= u64::MAX,
                overall_metadata.log_area_addr + overall_metadata.log_area_size <= u64::MAX
            ensures 
                match result {
                    Ok(phys_log) => {
                        ||| {
                            let abstract_op_log = UntrustedOpLog::<K, L>::recover(pm_region@.committed(), overall_metadata);
                            &&& abstract_op_log matches Some(abstract_op_log)
                            &&& phys_log.len() == 0
                            &&& abstract_op_log.physical_op_list.len() == 0
                        }
                        ||| {
                            let abstract_op_log = UntrustedOpLog::<K, L>::recover(pm_region@.committed(), overall_metadata);
                            let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                            &&& abstract_op_log matches Some(abstract_op_log)
                            &&& abstract_op_log.physical_op_list == phys_log_view
                            &&& AbstractPhysicalOpLogEntry::log_inv(phys_log_view, overall_metadata)
                        }
                    }
                    Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                    Err(KvError::LogErr{log_err}) => {
                        &&& log_err matches LogErr::PmemErr{err}
                        &&& err matches PmemError::AccessOutOfRange
                    }
                    Err(_) => false
                }
    {
        let log_start_addr = overall_metadata.log_area_addr;
        let log_size = overall_metadata.log_area_size;
        let region_size = overall_metadata.region_size;

        let ghost base_log_state = UntrustedLogImpl::recover(pm_region@.committed(), log_start_addr as nat, log_size as nat).unwrap();
        let ghost phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
        let ghost abstract_op_log = Self::parse_log_ops(phys_op_log_buffer, log_start_addr as nat, log_size as nat, region_size as nat).unwrap();

        let mut offset = 0;
        let mut ops = Vec::<PhysicalOpLogEntry>::new();

        proof {
            // Before the loop, we haven't parsed anything
            let phys_log_view = Seq::new(ops@.len(), |i: int| ops[i]@);
            assert(phys_log_view == Seq::<AbstractPhysicalOpLogEntry>::empty());
            assert(Some(phys_log_view) == Self::parse_log_ops_helper(0, 0, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat))
        }

        let ghost old_overall_metadata = overall_metadata;

        while offset < log_bytes.len()
            invariant
                u64::spec_size_of() * 2 <= log_bytes.len() <= u64::MAX,
                0 < abstract_op_log.len() <= u64::MAX,
                Self::parse_log_ops(log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat) is Some,
                ({
                    let phys_log_view = Seq::new(ops@.len(), |i: int| ops[i]@);
                    &&& Self::parse_log_ops_helper(0, offset as nat, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat) matches Some(abstract_log_view)
                    &&& phys_log_view == abstract_log_view
                    &&& AbstractPhysicalOpLogEntry::log_inv(phys_log_view, overall_metadata)
                }),
                ({
                    let recovered_log = UntrustedOpLog::<K, L>::recover(pm_region@.committed(), overall_metadata);
                    let parsed_ops = Self::parse_log_ops(log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat);
                    &&& recovered_log matches Some(recovered_log)
                    &&& parsed_ops matches Some(parsed_ops)
                    &&& recovered_log.physical_op_list == parsed_ops
                }),
                ({
                    let base_log_state = UntrustedLogImpl::recover(pm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat);
                    &&& base_log_state matches Some(base_log_state)
                    &&& log_bytes@ == extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat)
                }),
                log_start_addr + log_size <= u64::MAX,
                offset <= log_bytes.len(),
                old_overall_metadata == overall_metadata,
                log_start_addr == overall_metadata.log_area_addr,
                log_size == overall_metadata.log_area_size,
                region_size == overall_metadata.region_size,
        {
            broadcast use pmcopy_axioms;

            proof {
                assert(Self::parse_log_ops_helper(0, offset as nat, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat) is Some);
                assert(UntrustedOpLog::<K, L>::recover(pm_region@.committed(), overall_metadata) is Some);
                let recovered_base_log = UntrustedLogImpl::recover(pm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();

                let log_contents = Self::get_log_contents(recovered_base_log).unwrap();
                assert(log_contents == extract_bytes(recovered_base_log.log, 0, (recovered_base_log.log.len() - u64::spec_size_of()) as nat));
                assert(log_contents == log_bytes@);
                // the full op log, as well as the op log up to offset, both recover correctly.
                // this should imply that there is either a valid entry at offset, or that offset is 
                // is at the end 
                Self::lemma_parse_up_to_offset_succeeds(offset as nat, pm_region@, log_contents, overall_metadata);

                assert(offset <= log_contents.len());
                let current_op = Self::parse_log_op(offset as nat, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat);
                assert(current_op is Some);
            }

            if offset > log_bytes.len() - traits_t::size_of::<u64>() * 2 {
                assert(false);
                return Err(KvError::InternalError);
            }

            // parse the log entry
            let addr_bytes = slice_range(&log_bytes, offset, traits_t::size_of::<u64>());
            let len_bytes = slice_range(&log_bytes, offset + traits_t::size_of::<u64>(), traits_t::size_of::<u64>());
            let addr = u64_from_le_bytes(addr_bytes);
            let len = u64_from_le_bytes(len_bytes);

            // Check that the log entry is valid. 
            if {
                ||| offset + traits_t::size_of::<u64>() * 2 > u64::MAX as usize
                ||| offset + traits_t::size_of::<u64>() * 2 > (u64::MAX - len) as usize
                ||| addr > u64::MAX - len
                ||| addr + len > region_size 
                ||| offset + traits_t::size_of::<u64>() * 2 > log_bytes.len()
                ||| offset + traits_t::size_of::<u64>() * 2 + len as usize > log_bytes.len()
                ||| !({
                    ||| addr + len <= log_start_addr // region end before log area
                    ||| log_start_addr + log_size <= addr // region ends after log area
                })
                ||| len == 0
                ||| log_bytes.len() < traits_t::size_of::<u64>() * 2 + len as usize
                ||| offset > log_bytes.len() - (traits_t::size_of::<u64>() * 2 + len as usize)
            } {
                assert(false);
                return Err(KvError::InternalError);
            }

            let entry_size = traits_t::size_of::<u64>() * 2 + len as usize;

            let bytes = slice_range_to_vec(&log_bytes, offset + traits_t::size_of::<u64>() * 2, len as usize);

            let phys_log_entry = PhysicalOpLogEntry {
                absolute_addr: addr,
                len,
                bytes
            };
            ops.push(phys_log_entry);

            let ghost old_offset = offset;
            offset += entry_size;

            proof {
                let phys_log_view = Seq::new(ops@.len(), |i: int| ops[i]@);
                assert(Self::parse_log_op(old_offset as nat, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat) is Some);
                Self::lemma_op_log_parse_equal(0, old_offset as nat, offset as nat, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat);      
                
                let abstract_partial_log = Self::parse_log_ops_helper(0, offset as nat, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat);
                assert(abstract_partial_log is Some);
                let abstract_partial_log = abstract_partial_log.unwrap();
                assert(abstract_partial_log == phys_log_view);

                Self::lemma_successful_log_ops_parse_implies_inv(0, offset as nat, log_bytes@, overall_metadata);
            }
        }
        Ok(ops)
    }
    
    // This function starts the operation log, given a WRPM region that already has a base log
    // set up at the address specified in the `overall_metadata` argument.
    // If log is not empty, it parses it and returns the contents so that they can be used
    // to recover other regions.
    // Note that the op log is given the entire PM device, but only deals with the log region.
    pub exec fn start<Perm, PM>(
        pm_region: &WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        overall_metadata: OverallMetadata
    ) -> (result: Result<(Self, Vec<PhysicalOpLogEntry>), KvError<K>>)
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires
            pm_region.inv(),
            pm_region@.no_outstanding_writes(),
            overall_metadata.log_area_addr + overall_metadata.log_area_size <= pm_region@.len() <= u64::MAX,
            overall_metadata.log_area_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
            Self::recover(pm_region@.committed(), overall_metadata) is Some,
            pm_region@.len() == overall_metadata.region_size,
            ({
                let base_log_state = UntrustedLogImpl::recover(pm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
                let phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
                let abstract_op_log = Self::parse_log_ops(phys_op_log_buffer, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat);
                &&& abstract_op_log matches Some(abstract_log)
                &&& 0 < abstract_log.len() <= u64::MAX
            }),
            overall_metadata.log_area_addr + overall_metadata.log_area_size <= u64::MAX,
            overall_metadata.log_area_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
        ensures
            match result {
                Ok((op_log_impl, phys_log)) => {
                    ||| {
                        let abstract_op_log = UntrustedOpLog::<K, L>::recover(pm_region@.committed(), overall_metadata);
                        &&& abstract_op_log matches Some(abstract_op_log)
                        &&& phys_log.len() == 0
                        &&& abstract_op_log.physical_op_list.len() == 0
                    }
                    ||| {
                        let abstract_op_log = UntrustedOpLog::<K, L>::recover(pm_region@.committed(), overall_metadata);
                        let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                        &&& abstract_op_log matches Some(abstract_op_log)
                        &&& abstract_op_log.physical_op_list == phys_log_view
                        &&& AbstractPhysicalOpLogEntry::log_inv(phys_log_view, overall_metadata)
                    }
                }
                Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                Err(KvError::LogErr{log_err}) => {
                    &&& log_err matches LogErr::PmemErr{err}
                    &&& err matches PmemError::AccessOutOfRange
                }
                Err(KvError::InternalError) => {
                    let log = UntrustedLogImpl::recover(pm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
                    let tail = log.head + log.log.len();
                    ||| tail - log.head < u64::spec_size_of() as u128
                    ||| UntrustedOpLog::<K, L>::recover(pm_region@.committed(), overall_metadata) is None
                }
                Err(_) => false
            }
    {
        let log_start_addr = overall_metadata.log_area_addr;
        let log_size = overall_metadata.log_area_size;

        // Start the base log
        let ghost base_log_state = UntrustedLogImpl::recover(pm_region@.committed(), log_start_addr as nat, log_size as nat).unwrap();
        let log = match UntrustedLogImpl::start(pm_region, log_start_addr, log_size, Ghost(base_log_state)) {
            Ok(log) => log,
            Err(LogErr::CRCMismatch) => return Err(KvError::CRCMismatch),
            Err(e) => {
                return Err(KvError::LogErr { log_err: e });
            }
        };
        let ghost op_log_state = Self::recover(pm_region@.committed(), overall_metadata);

        // Read the entire log and its CRC and check for corruption. we have to do this before we can parse the bytes.
        // Obtain the head and tail of the log so that we know the region to read to get the log contents and the CRC
        let (head, tail, capacity) = match log.get_head_tail_and_capacity(pm_region, log_start_addr, log_size) {
            Ok((head, tail, capacity)) => (head, tail, capacity),
            Err(e) => return Err(KvError::LogErr { log_err: e }),
        };

        if tail == head {
            return Ok((
                Self {
                    log,
                    overall_metadata,
                    state: Ghost(op_log_state.unwrap()),
                    current_transaction_crc: CrcDigest::new(),
                    _phantom: None
                },
                Vec::new(),
            ));
        } else if tail < head || tail - head < traits_t::size_of::<u64>() as u128 {
            // Tail must be greater than head, and the log must be at least 8 bytes long
            // to avoid underflow later.
            return Err(KvError::InternalError); 
        }
        let len = (tail - head) as u64 - traits_t::size_of::<u64>() as u64;
        
        let (log_bytes, log_addrs) = match log.read(pm_region, log_start_addr, log_size, head, len) {
            Ok(bytes) => bytes,
            Err(e) => {
                assert(head == log@.head);
                assert(head + len < log@.head + log@.log.len());
                return Err(KvError::LogErr { log_err: e });
            }
        };
        let (crc_bytes, crc_addrs) = match log.read(pm_region, log_start_addr, log_size, tail - traits_t::size_of::<u64>() as u128, traits_t::size_of::<u64>() as u64) {
            Ok(bytes) => bytes,
            Err(e) => {
                proof {
                    let log_tail = log@.head + log@.log.len() as int;
                    assert(tail - u64::spec_size_of() >= log@.head);
                    assert(tail == log_tail);
                }
                return Err(KvError::LogErr { log_err: e });
            }
        };

        if !check_crc(log_bytes.as_slice(), crc_bytes.as_slice(), Ghost(pm_region@.committed()),
            Ghost(pm_region.constants().impervious_to_corruption), log_addrs, crc_addrs) 
        {
            return Err(KvError::CRCMismatch);
        }

        let phys_op_log = Self::parse_phys_op_log(pm_region, log_bytes, overall_metadata)?;

        let op_log_impl = Self {
            log,
            overall_metadata,
            state: Ghost(op_log_state.unwrap()),
            current_transaction_crc: CrcDigest::new(),
            _phantom: None
        };

        Ok((
            op_log_impl,
            phys_op_log
        ))
    }

    // This helper lemma helps us prove that flattening a 2D sequence
    // is equivalent to concatenating the last sequence to all prior
    // sequences after flattening them. We use this to prove that 
    // the op log's CRC digest (which is a sequence of sequences) is 
    // equivalent to the base log's pending bytes (which is a sequence).
    proof fn lemma_seqs_flatten_equal_suffix(s: Seq<Seq<u8>>)
        requires
            s.len() >= 1
        ensures 
            ({
                let last = s[s.len() - 1];
                let prefix = s.subrange(0, s.len() - 1);
                s.flatten() == prefix.flatten() + last
            })
        decreases s.len()
    {
        if s.len() == 1 {
            let last = s[0];
            assert(s == seq![last]);
            seq![last].lemma_flatten_one_element();
            assert(seq![last].flatten() == last);
        }
        else {
            let first = s[0];
            let last = s[s.len() - 1];
            let middle = s.subrange(0, s.len() - 1).drop_first();
            let suffix = s.drop_first();

            assert(middle == suffix.subrange(0, suffix.len() - 1));

            Self::lemma_seqs_flatten_equal_suffix(suffix);
            assert(suffix.flatten() == middle.flatten() + last);
            assert(first + suffix.flatten() == first + middle.flatten() + last);
        }
    }

    // This lemma proves that if we append a log entry to the current op log,
    // and append the same log entry as a sequence of bytes to the current 
    // base log, then parsing the log in the base log will return the 
    // current op log.
    proof fn lemma_appending_log_entry_bytes_appends_op_to_list(
        self,
        pm_region: PersistentMemoryRegionView,
        log_entry: PhysicalOpLogEntry,
    )
        requires
            ({
                let pending_bytes = self.log@.pending;
                let log_ops = Self::parse_log_ops(pending_bytes, self.overall_metadata.log_area_addr as nat, 
                    self.overall_metadata.log_area_size as nat, self.overall_metadata.region_size as nat);
                &&& log_ops is Some 
                &&& log_ops.unwrap() == self@.physical_op_list
                &&& pending_bytes.len() + u64::spec_size_of() * 2 <= u64::MAX
                &&& pending_bytes.len() + u64::spec_size_of() * 2 + log_entry.len <= u64::MAX
            }),
            // log entry is valid
            0 <= log_entry.absolute_addr < log_entry.absolute_addr + log_entry.len < pm_region.len() <= u64::MAX,
            log_entry.absolute_addr + log_entry.len < self.overall_metadata.log_area_addr || self.overall_metadata.log_area_addr + self.overall_metadata.log_area_size <= log_entry.absolute_addr,
            log_entry.bytes@.len() <= u64::MAX,
            log_entry.len != 0,
            log_entry.len == log_entry.bytes@.len(),
            log_entry.absolute_addr + log_entry.len <= self.overall_metadata.region_size,
        ensures 
            ({
                let pending_bytes = self.log@.pending;
                let bytes = log_entry.bytes@;
                let new_pending_bytes = pending_bytes + log_entry.absolute_addr.spec_to_bytes() + (log_entry.bytes.len() as u64).spec_to_bytes() + bytes;
                let new_log_ops = Self::parse_log_ops(new_pending_bytes, self.overall_metadata.log_area_addr as nat, 
                    self.overall_metadata.log_area_size as nat, self.overall_metadata.region_size as nat);
                &&& new_log_ops is Some 
                &&& new_log_ops.unwrap() == self@.physical_op_list.push(log_entry@)

            })
    {
        broadcast use pmcopy_axioms;

        let log_start_addr = self.overall_metadata.log_area_addr as nat;
        let log_size = self.overall_metadata.log_area_size as nat;
        let region_size = self.overall_metadata.region_size as nat;

        let pending_bytes = self.log@.pending;
        let bytes = log_entry.bytes@;
        let new_pending_bytes = pending_bytes + log_entry.absolute_addr.spec_to_bytes() + (log_entry.bytes.len() as u64).spec_to_bytes() + bytes;
        let old_log_ops = Self::parse_log_ops(pending_bytes, self.overall_metadata.log_area_addr as nat, 
            self.overall_metadata.log_area_size as nat, self.overall_metadata.region_size as nat).unwrap();

        // parsing just the new operation's bytes succeeds
        let new_op = Self::parse_log_op(pending_bytes.len(), new_pending_bytes, log_start_addr, log_size, region_size);
        assert(new_op is Some && new_op.unwrap() == log_entry@) by {
            let addr_bytes = extract_bytes(new_pending_bytes, pending_bytes.len(), u64::spec_size_of());
            let len_bytes = extract_bytes(new_pending_bytes, pending_bytes.len() + u64::spec_size_of(), u64::spec_size_of());
            let addr = u64::spec_from_bytes(addr_bytes);
            let len = u64::spec_from_bytes(len_bytes);
            assert(log_entry.absolute_addr.spec_to_bytes() == addr_bytes);
            assert((log_entry.bytes.len() as u64).spec_to_bytes() == len_bytes);
            let read_entry_bytes = extract_bytes(new_pending_bytes, pending_bytes.len() + u64::spec_size_of() * 2, len as nat);
            assert(read_entry_bytes == bytes);
        }
        
        // Parsing the pending_bytes prefix of new_pending_bytes gives the same op log as parsing pending_bytes
        assert(extract_bytes(new_pending_bytes, 0, pending_bytes.len()) == pending_bytes);
        Self::lemma_parsing_same_range_equal(pending_bytes, new_pending_bytes, log_start_addr, log_size, region_size);

        // Appending the new op to the pending_bytes op log is equivalent to parsing all of new_pending_bytes
        Self::lemma_op_log_parse_equal(0, pending_bytes.len(), new_pending_bytes.len(), new_pending_bytes, log_start_addr, log_size, region_size);
        let new_log_ops = Self::parse_log_ops(new_pending_bytes, self.overall_metadata.log_area_addr as nat, 
            self.overall_metadata.log_area_size as nat, self.overall_metadata.region_size as nat);
        
        assert(new_log_ops.unwrap() == old_log_ops.push(new_op.unwrap()));
    }

    // This function tentatively appends a log entry to the operation log. It does so 
    // by casting the log entry to byte slices and tentatively appending them to the 
    // base log, then updating the op log's current CRC digest to include these new bytes.
    // We perform three separate tentative appends to the underlying base log in this 
    // function, as it is easier to treat each part of the log entry (absolute address, 
    // len, and bytes) as separate updates when it comes to proving correctness. If 
    // any of these three appends returns an error, the transaction is aborted.
    pub exec fn tentatively_append_log_entry<Perm, PM>(
        &mut self,
        log_wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        log_entry: PhysicalOpLogEntry,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), KvError<K>>)
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires 
            old(self).inv(*old(log_wrpm)),
            old(self).log_entry_valid(old(log_wrpm)@, log_entry@),
            !old(self)@.op_list_committed,
            Self::parse_log_ops(old(self).base_log_view().pending, old(self).log_start_addr() as nat, 
                old(self).log_size() as nat, old(self).overall_metadata().region_size as nat) is Some,
            forall |s| #[trigger] perm.check_permission(s) <==> 
                Self::recover(s, old(self).overall_metadata()) == Some(AbstractOpLogState::initialize()),
            log_entry.len == log_entry.bytes@.len(),
            log_entry.absolute_addr + log_entry.len <= old(self).overall_metadata().region_size,
            ({
                let pending_bytes = old(self).base_log_view().pending;
                let log_ops = Self::parse_log_ops(pending_bytes, old(self).log_start_addr() as nat, 
                    old(self).log_size() as nat, old(self).overall_metadata().region_size as nat);
                &&& log_ops is Some 
                &&& log_ops.unwrap() == old(self)@.physical_op_list
                &&& pending_bytes.len() + u64::spec_size_of() * 2 <= u64::MAX
                &&& pending_bytes.len() + u64::spec_size_of() * 2 + log_entry.len <= u64::MAX
            }),
        ensures 
            match result {
                Ok(()) => {
                    // We only maintain the invariant in the success case because an error appending to 
                    // the log should abort the transaction, since we may not have appended a full log entry
                    // and even if we did (or did not append anything), the error likely indicates we won't 
                    // be able to commit it later anyway.
                    &&& self.inv(*log_wrpm)
                    &&& self@ == old(self)@.tentatively_append_log_entry(log_entry@)
                }
                Err(KvError::LogErr { log_err: e }) => {
                    &&& self.base_log_view().pending.len() == 0
                    &&& self.base_log_view().log == old(self).base_log_view().log
                    &&& self.base_log_view().head == old(self).base_log_view().head
                    &&& self.base_log_view().capacity == old(self).base_log_view().capacity
                    &&& log_wrpm@.no_outstanding_writes()
                    &&& self@.physical_op_list.len() == 0
                }
                Err(_) => false 
            }
    {
        // this assert is sufficient to hit the triggers we need to prove that the log entries
        // are all valid after appending the new one
        assert(forall |i: int| 0 <= i < self@.physical_op_list.len() ==> {
            let op = #[trigger] self@.physical_op_list[i];
            self.log_entry_valid(log_wrpm@, op)
        });

        proof {
            // before we append anything, prove that appending this entry will maintain the loop invariant
            self.lemma_appending_log_entry_bytes_appends_op_to_list(log_wrpm@, log_entry);
        }

        let absolute_addr = log_entry.absolute_addr;

        let ghost old_digest = self.current_transaction_crc.bytes_in_digest();
        let ghost old_pending = self.log@.pending;

        let result = self.log.tentatively_append(
            log_wrpm,
            self.overall_metadata.log_area_addr, 
            self.overall_metadata.log_area_size, 
            absolute_addr.as_byte_slice(),
            Tracked(perm)
        );
        match result {
            Ok(_) => {}
            Err(e) => {
                self.log.abort_pending_appends(log_wrpm, self.overall_metadata.log_area_addr, self.overall_metadata.log_area_size);
                self.current_transaction_crc = CrcDigest::new();
                self.state = Ghost(AbstractOpLogState {
                    physical_op_list: Seq::empty(),
                    op_list_committed: false
                });
                return Err(KvError::LogErr { log_err: e });
            }
        }
        self.current_transaction_crc.write_bytes(absolute_addr.as_byte_slice());

        proof {
            // This proves that the CRC digest bytes and log pending bytes are the same
            let current_digest = self.current_transaction_crc.bytes_in_digest();
            let bytes = absolute_addr.spec_to_bytes();
            assert(current_digest == old_digest.push(bytes));
            assert(self.log@.pending == old_pending + bytes);
            // The proof is slightly different if the log was empty before this operation.
            // The other proofs about CRC digest bytes for the other appends don't need 
            // to consider this because we will have appended to the log by then.
            if old_pending.len() > 0 {
                assert(old_digest.flatten() == old_pending);
                Self::lemma_seqs_flatten_equal_suffix(current_digest);
                assert(current_digest[current_digest.len() - 1] == bytes);
                assert(current_digest.subrange(0, current_digest.len() - 1) == old_digest);
            } else {
                assert(current_digest.len() == 1);
                current_digest.lemma_flatten_one_element();
            }
            assert(current_digest.flatten() == old_digest.flatten() + bytes);
        }

        let len = log_entry.bytes.len() as u64;

        let ghost old_digest = self.current_transaction_crc.bytes_in_digest();
        let ghost old_pending = self.log@.pending;

        let result = self.log.tentatively_append(
            log_wrpm,
            self.overall_metadata.log_area_addr, 
            self.overall_metadata.log_area_size, 
            len.as_byte_slice(),
            Tracked(perm)
        );
        match result {
            Ok(_) => {}
            Err(e) => {
                self.log.abort_pending_appends(log_wrpm, self.overall_metadata.log_area_addr, self.overall_metadata.log_area_size);
                self.current_transaction_crc = CrcDigest::new();
                self.state = Ghost(AbstractOpLogState {
                    physical_op_list: Seq::empty(),
                    op_list_committed: false
                });
                return Err(KvError::LogErr { log_err: e });
            }
        }
        self.current_transaction_crc.write_bytes(len.as_byte_slice());

        proof {
            // This proves that the CRC digest bytes and log pending bytes are the same
            let current_digest = self.current_transaction_crc.bytes_in_digest();
            let bytes = len.spec_to_bytes();
            assert(current_digest == old_digest.push(bytes));
            assert(self.log@.pending == old_pending + bytes);
            assert(old_digest.flatten() == old_pending);
            Self::lemma_seqs_flatten_equal_suffix(current_digest);
            assert(current_digest[current_digest.len() - 1] == bytes);
            assert(current_digest.subrange(0, current_digest.len() - 1) == old_digest);
            assert(current_digest.flatten() == old_digest.flatten() + bytes);
        }
        
        assert(self.current_transaction_crc.bytes_in_digest().flatten() == self.log@.pending);

        let ghost old_digest = self.current_transaction_crc.bytes_in_digest();
        let ghost old_pending = self.log@.pending;

        let bytes = log_entry.bytes.as_slice();
        let result = self.log.tentatively_append(
            log_wrpm, 
            self.overall_metadata.log_area_addr, 
            self.overall_metadata.log_area_size, 
            bytes,
            Tracked(perm)
        );
        match result {
            Ok(_) => {}
            Err(e) => {
                self.log.abort_pending_appends(log_wrpm, self.overall_metadata.log_area_addr, self.overall_metadata.log_area_size);
                self.current_transaction_crc = CrcDigest::new();
                self.state = Ghost(AbstractOpLogState {
                    physical_op_list: Seq::empty(),
                    op_list_committed: false
                });
                return Err(KvError::LogErr { log_err: e });
            }
        }
        // update the op log's CRC digest
        self.current_transaction_crc.write_bytes(bytes);

        proof {
            let current_digest = self.current_transaction_crc.bytes_in_digest();
            let bytes = bytes@;
            assert(current_digest == old_digest.push(bytes));
            assert(self.log@.pending == old_pending + bytes);
            assert(old_digest.flatten() == old_pending);
            Self::lemma_seqs_flatten_equal_suffix(current_digest);
            assert(current_digest[current_digest.len() - 1] == bytes);
            assert(current_digest.subrange(0, current_digest.len() - 1) == old_digest);
            assert(current_digest.flatten() == old_digest.flatten() + bytes);
        }

        // update the ghost state to reflect the new entry
        let ghost new_state = self.state@.tentatively_append_log_entry(log_entry@);
        self.state = Ghost(new_state);

        proof {
            // We need to prove that we maintain the invariant that parsing the pending log bytes
            // gives us the current abstract op log
            let old_pending_bytes = old(self).log@.pending;
            let new_pending_bytes = self.log@.pending;

            assert(new_pending_bytes == old_pending_bytes + absolute_addr.spec_to_bytes() + len.spec_to_bytes() + bytes@);

            let old_log_ops = Self::parse_log_ops(old_pending_bytes, self.overall_metadata.log_area_addr as nat, 
                self.overall_metadata.log_area_size as nat, self.overall_metadata.region_size as nat);
            let new_log_ops = Self::parse_log_ops(new_pending_bytes, self.overall_metadata.log_area_addr as nat, 
                self.overall_metadata.log_area_size as nat, self.overall_metadata.region_size as nat);
            assert(old_log_ops is Some);
            assert(new_log_ops is Some);
            assert(new_log_ops.unwrap() == self@.physical_op_list);
        }
        
        Ok(())
    }

    // This function commits the operation log. It first appends the CRC of the current
    // digest, then commits the base log. If either the append or the base log commit 
    // operation fail, then the transaction is aborted.
    pub exec fn commit_log<Perm, PM>(
        &mut self, 
        log_wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), KvError<K>>)
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires 
            old(self).inv(*old(log_wrpm)),
            old(self)@.physical_op_list.len() > 0,
            !old(self)@.op_list_committed,
            old(log_wrpm).inv(),
            old(self).log_start_addr() + spec_log_area_pos() <= old(log_wrpm)@.len(),
            forall |s| #[trigger] perm.check_permission(s) <==> {
                ||| Self::recover(s, old(self).overall_metadata()) == Some(AbstractOpLogState::initialize())
                ||| Self::recover(s, old(self).overall_metadata()) == Some(old(self)@.commit_op_log())
            }
        ensures 
            self.inv(*log_wrpm),
            log_wrpm@.len() == old(log_wrpm)@.len(),
            log_wrpm.constants() == old(log_wrpm).constants(),
            self.overall_metadata() == old(self).overall_metadata(),
            match result {
                Ok(()) => {
                    &&& self@ == old(self)@.commit_op_log()
                }
                Err(KvError::LogErr{log_err}) => {
                    &&& self.base_log_view().pending.len() == 0
                    &&& self.base_log_view().log == old(self).base_log_view().log
                    &&& self.base_log_view().head == old(self).base_log_view().head
                    &&& self.base_log_view().capacity == old(self).base_log_view().capacity
                    &&& log_wrpm@.no_outstanding_writes()
                    &&& self@.physical_op_list.len() == 0
                }
                Err(_) => false 
            }
    {
        let transaction_crc = self.current_transaction_crc.sum64();
        let bytes = transaction_crc.as_byte_slice();

        proof {
            broadcast use pmcopy_axioms;
            // All base log crash states that result in self.base_log_view.drop_pending_appends() will result in 
            // an op log state that is allowed by `perm`. The base log's `tentatively_append` requires that perm
            // allow base log states that recover to self.base_log_view.drop_pending_appends(), so this 
            // assertion tells us that all crash states considered legal in the base log's `tentatively_append` 
            // also recover to a legal op log state
            assert forall |s| UntrustedLogImpl::recover(s, self.log_start_addr() as nat, self.log_size() as nat) == 
                    Some(self.base_log_view().drop_pending_appends())
                implies #[trigger] Self::recover(s, self.overall_metadata()) == Some(AbstractOpLogState::initialize()) 
            by {
                let base_log_recovery_state = UntrustedLogImpl::recover(s, self.log_start_addr() as nat, self.log_size() as nat);
                assert(base_log_recovery_state is Some);
                assert(base_log_recovery_state.unwrap().log.len() == 0);
            }
            assert(bytes.len() > 0);
        }

        let ghost old_pending_bytes = self.log@.pending;

        match self.log.tentatively_append(log_wrpm, self.overall_metadata.log_area_addr, self.overall_metadata.log_area_size, bytes, Tracked(perm)) {
            Ok(_) => {}
            Err(e) => {
                self.log.abort_pending_appends(log_wrpm, self.overall_metadata.log_area_addr, self.overall_metadata.log_area_size);
                self.current_transaction_crc = CrcDigest::new();
                self.state = Ghost(AbstractOpLogState {
                    physical_op_list: Seq::empty(),
                    op_list_committed: false
                });
                return Err(KvError::LogErr { log_err: e });
            }
        }

        proof {
            // The u64 we just appended is the CRC of all of the other bytes in the pending log. This should be obvious, but including 
            // these assertions here helps Verus prove that the commit operation is crash consistent later
            let current_pending_bytes = self.log@.pending;
            let log_contents = extract_bytes(current_pending_bytes, 0, (current_pending_bytes.len() - u64::spec_size_of()) as nat);
            let crc_bytes = extract_bytes(current_pending_bytes, (current_pending_bytes.len() - u64::spec_size_of()) as nat, u64::spec_size_of());
            let crc = u64::spec_from_bytes(crc_bytes);
            assert(log_contents == old_pending_bytes);
            assert(crc_bytes == bytes@);
            assert(crc == spec_crc_u64(log_contents));
            assert(u64::bytes_parseable(crc_bytes));
        }

        proof {
            // To prove that committing the base log is crash safe, we need to prove that all possible base log crash states
            // imply a legal op log crash state. The crash state in which the base log loses all pending appends corresponds 
            // to the crash state in which the op log is empty, and the crash state in which the base log commits is equivalent
            // to the crash state in which the op log is also committed.
            assert forall |s| UntrustedLogImpl::recover(s, self.log_start_addr() as nat, self.log_size() as nat) == 
                    Some(self.base_log_view().drop_pending_appends())
                implies #[trigger] Self::recover(s, self.overall_metadata()) == Some(AbstractOpLogState::initialize()) 
            by {
                // In this crash state, the base log is empty, so the op log is also empty
                let base_log_recovery_state = UntrustedLogImpl::recover(s, self.log_start_addr() as nat, self.log_size() as nat);
                assert(base_log_recovery_state is Some);
                assert(base_log_recovery_state.unwrap().log.len() == 0);
            }

            assert forall |s| UntrustedLogImpl::recover(s, self.log_start_addr() as nat, self.log_size() as nat) == 
                    Some(self.base_log_view().commit().drop_pending_appends())
                implies #[trigger] Self::recover(s, self.overall_metadata()) == Some(self@.commit_op_log()) 
            by {
                let base_log_recovery_state = UntrustedLogImpl::recover(s, self.log_start_addr() as nat, self.log_size() as nat).unwrap();
                
                // Prove that recovering the op log from this base log -- getting its log contents, checking their CRC, and parsing it -- 
                // results in the current abstract op log state.
                let log_contents = extract_bytes(base_log_recovery_state.log, 0, (base_log_recovery_state.log.len() - u64::spec_size_of()) as nat);
                let crc_bytes = extract_bytes(base_log_recovery_state.log, (base_log_recovery_state.log.len() - u64::spec_size_of()) as nat, u64::spec_size_of());
                assert(crc_bytes == bytes@); // the CRC is the one we appended earlier
                assert(u64::bytes_parseable(crc_bytes));
                assert(crc_bytes == spec_crc_bytes(log_contents));

                // if we get the log contents and parse them, we will get the desired op log
                let base_log_contents = Self::get_log_contents(base_log_recovery_state);
                assert(base_log_contents is Some);
                let parsed_log_ops = Self::parse_log_ops(base_log_contents.unwrap(), self.log_start_addr() as nat, self.log_size() as nat, self.overall_metadata.region_size as nat);
                
                assert(parsed_log_ops is Some);
                assert(parsed_log_ops.unwrap() == self@.physical_op_list);
            }
        }
        
        match self.log.commit(log_wrpm, self.overall_metadata.log_area_addr, self.overall_metadata.log_area_size, Tracked(perm)) {
            Ok(_) => {}
            Err(e) => {
                assert(false);
                return Err(KvError::LogErr { log_err: e });
            } 
        }

        // update the op log's ghost state to indicate that it has been committed
        self.state = Ghost(self.state@.commit_op_log());
        // and clear its CRC digest
        self.current_transaction_crc = CrcDigest::new();

        Ok(())
    }

    // This function clears the operation log by advancing the base log's 
    // head to its tail position. Failing this operation does not have to 
    // abort the transaction, since a failure cannot put the op log in 
    // an inconsistent state, but it does prevent any further transactions 
    // from taking place.
    pub exec fn clear_log<Perm, PM>(
        &mut self,
        log_wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), KvError<K>>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires 
            old(self).inv(*old(log_wrpm)),
            old(self)@.op_list_committed,
            old(self).log_start_addr() + spec_log_area_pos() <= old(log_wrpm)@.len(),
            old(self).base_log_view().pending.len() == 0,
            // legal crash states are the current op log state, or a cleared op log state
            forall |s| #[trigger] perm.check_permission(s) <==> {
                ||| Self::recover(s, old(self).overall_metadata()) == Some(old(self)@)
                ||| Self::recover(s, old(self).overall_metadata()) == Some(old(self)@.clear_log().unwrap())
            }
        ensures 
            self.inv(*log_wrpm),
            log_wrpm@.len() == old(log_wrpm)@.len(),
            log_wrpm.constants() == old(log_wrpm).constants(),
            self.overall_metadata() == old(self).overall_metadata(),
            match result {
                Ok(()) => {
                    Ok::<_, ()>(self@) == old(self)@.clear_log()
                }
                Err(_) => false 
            }
    {
        let log_start_addr = self.overall_metadata.log_area_addr;
        let log_size = self.overall_metadata.log_area_size;

        // To clear the log, we'll look up its head and tail, then advance the head to the tail
        let (head, tail, capacity) = match self.log.get_head_tail_and_capacity(log_wrpm, log_start_addr, log_size) {
            Ok((head, tail, capacity)) => (head, tail, capacity),
            Err(e) => {
                assert(false);
                return Err(KvError::LogErr{log_err: e});
            }
        };

        // Now, advance the head to the tail. Verus is able to prove the required crash preconditions on its own
        match self.log.advance_head(log_wrpm, tail, log_start_addr, log_size, Tracked(perm)) {
            Ok(()) => {}
            Err(e) => {
                assert(false);
                return Err(KvError::LogErr{log_err: e});
            }
        }

        // update the op log's state -- it is now empty and is not committed
        self.state = Ghost(self.state@.clear_log().unwrap());

        assert(self.log@.pending.len() == 0);
        assert(self.current_transaction_crc.bytes_in_digest().len() == 0);
        Ok(())
    }
}
}
