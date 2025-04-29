use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::{
    util_v::*,
    kv::{durable::{maintablelayout_v::*, oplog::logentry_v::*, inv_v::*}, kvimpl_t::*, layout_v::*},
    log2::{logimpl_v::*, layout_v::*, inv_v::*},
    pmem::{pmemspec_t::*, power_t::*, pmemutil_v::*, pmcopy_t::*, traits_t, crc_t::*, subregion_v::*},
};
use vstd::bytes::*;

verus! {

    #[verifier::ext_equal]
    pub struct AbstractPhysicalOpLogEntry
    {
        pub absolute_addr: nat,
        pub len: nat,
        pub bytes: Seq<u8>,
    }

    impl AbstractPhysicalOpLogEntry
    {
        pub open spec fn inv(self, version_metadata: VersionMetadata, overall_metadata: OverallMetadata) -> bool
        {
            &&& self.len > 0
            &&& 0 <= self.absolute_addr
            &&& self.absolute_addr + self.len <= overall_metadata.region_size
            &&& ({
                ||| self.absolute_addr + self.len <= overall_metadata.log_area_addr
                ||| overall_metadata.log_area_addr + overall_metadata.log_area_size <= self.absolute_addr
            })
            &&& VersionMetadata::spec_size_of() + u64::spec_size_of() < self.absolute_addr
            &&& version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() + u64::spec_size_of() <= self.absolute_addr
            &&& self.len == self.bytes.len()
        }

        pub open spec fn log_inv(log: Seq<Self>, version_metadata: VersionMetadata, overall_metadata: OverallMetadata) -> bool {
            forall |i: int| 0 <= i < log.len() ==> (#[trigger] log[i]).inv(version_metadata, overall_metadata)
        }
    }

    // Abstract state of the log as it is used in the KV store.
    // There is a small set of legal log entry types, and the only
    // way to free up space is to completely clear the log by moving
    // the head pointer to the tail. Once the log has been committed
    // it is illegal to perform any additional appends until it has
    // been cleared.
    pub struct AbstractOpLogState
    {
        pub physical_op_list: Seq<AbstractPhysicalOpLogEntry>,
        pub op_list_committed: bool,
    }

    impl AbstractOpLogState
    {
        pub open spec fn initialize() -> Self {
            Self {
                physical_op_list: Seq::empty(),
                op_list_committed: false,
            }
        }

        pub open spec fn drop_pending_appends(self) -> Self 
        {
            Self {
                physical_op_list: Seq::empty(),
                op_list_committed: false,
            }
        }

        pub open spec fn tentatively_append_log_entry(
            self,
            physical_log_entry: AbstractPhysicalOpLogEntry,
        ) -> Self {
            Self {
                physical_op_list: self.physical_op_list.push(physical_log_entry),
                op_list_committed: false
            }
        }

        pub open spec fn commit_op_log(self) -> Self
        {
            if self.physical_op_list.len() == 0 {
                self
            } else {
                Self {
                    physical_op_list: self.physical_op_list,
                    op_list_committed: true,
                }
            }
        }

        // TODO: use a more informative error code?
        pub open spec fn clear_log(self) -> Result<Self, ()>
        {
            if !self.op_list_committed {
                Err(())
            } else {
                Ok(Self {
                    physical_op_list: Seq::empty(),
                    op_list_committed: false,
                })
            }
        }
    }

    pub struct UntrustedOpLog<K, L>
        where 
            L: PmCopy + std::fmt::Debug + Copy,
    {
        log: UntrustedLogImpl,
        state: Ghost<AbstractOpLogState>,
        current_transaction_crc: CrcDigest,
        _phantom: Option<(K, L)>
    }

    impl<K, L> UntrustedOpLog<K, L>
        where 
            L: PmCopy + std::fmt::Debug + Copy,
            K: std::fmt::Debug,
    {

        pub closed spec fn base_log_capacity(self) -> int {
            self.log@.capacity
        }

        pub closed spec fn base_log_view(self) -> AbstractLogState {
            self.log@
        }

        pub closed spec fn spec_base_log(self) -> UntrustedLogImpl {
            self.log
        }

        pub closed spec fn crc_invariant(self) -> bool {
            self.current_transaction_crc.bytes_in_digest().flatten() == self.log@.pending
        }

        pub closed spec fn inv(self, pm_region: PersistentMemoryRegionView, version_metadata: VersionMetadata, overall_metadata: OverallMetadata) -> bool
        {
            &&& self.log.inv(pm_region, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
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
                let log_ops = Self::parse_log_ops(pending_bytes, overall_metadata.log_area_addr as nat, 
                    overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
                &&& log_ops is Some 
                &&& log_ops.unwrap() == self@.physical_op_list
                &&& Self::recover(pm_region.durable_state, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize())
                &&& Self::recover(pm_region.read_state, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize())
            }
            &&& self@.op_list_committed ==> {
                let log_contents = Self::get_log_contents(self.log@);
                let log_ops = Self::parse_log_ops(log_contents.unwrap(), overall_metadata.log_area_addr as nat, 
                    overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
                &&& log_contents is Some
                &&& log_ops is Some
                &&& log_ops.unwrap() == self@.physical_op_list
                &&& self.log@.log.len() > 0
                &&& Self::recover(pm_region.durable_state, version_metadata, overall_metadata) == Some(self@)
                &&& Self::recover(pm_region.read_state, version_metadata, overall_metadata) == Some(self@)
            }
            &&& forall |i: int| 0 <= i < self@.physical_op_list.len() ==> {
                    let op = #[trigger] self@.physical_op_list[i];
                    op.inv(version_metadata, overall_metadata)
            } 
            &&& overall_metadata.log_area_addr + overall_metadata.log_area_size <= pm_region.len() <= u64::MAX
            &&& overall_metadata.log_area_addr as int % const_persistence_chunk_size() == 0
            &&& overall_metadata.log_area_size as int % const_persistence_chunk_size() == 0
            &&& no_outstanding_writes_to_metadata(pm_region, overall_metadata.log_area_addr as nat)
            &&& AbstractPhysicalOpLogEntry::log_inv(self@.physical_op_list, version_metadata, overall_metadata)
        }

        pub proof fn lemma_reveal_opaque_op_log_inv<Perm, PM>(
            self, 
            pm_region: PoWERPersistentMemoryRegion<Perm, PM>, 
            version_metadata: VersionMetadata, 
            overall_metadata: OverallMetadata
        )
            where 
                Perm: CheckPermission<Seq<u8>>,
                PM: PersistentMemoryRegion,
            requires
                self.inv(pm_region@, version_metadata, overall_metadata)
            ensures 
                AbstractPhysicalOpLogEntry::log_inv(self@.physical_op_list, version_metadata, overall_metadata),
                !self@.op_list_committed ==> {
                    let pending_bytes = self.base_log_view().pending;
                    let log_ops = Self::parse_log_ops(pending_bytes, overall_metadata.log_area_addr as nat, 
                            overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
                    &&& log_ops is Some 
                    &&& log_ops.unwrap() == self@.physical_op_list
                    &&& Self::recover(pm_region@.durable_state, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize())
                    &&& Self::recover(pm_region@.read_state, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize())
                },
                self@.op_list_committed ==> {
                    let log_contents = Self::get_log_contents(self.base_log_view());
                    let log_ops = Self::parse_log_ops(log_contents.unwrap(), overall_metadata.log_area_addr as nat, 
                                                      overall_metadata.log_area_size as nat,
                                                      overall_metadata.region_size as nat,
                                                      version_metadata.overall_metadata_addr as nat);
                    &&& log_contents is Some
                    &&& log_ops is Some
                    &&& log_ops.unwrap() == self@.physical_op_list
                    &&& self.base_log_view().log.len() > 0
                    &&& Self::recover(pm_region@.durable_state, version_metadata, overall_metadata) == Some(self@)
                    &&& Self::recover(pm_region@.read_state, version_metadata, overall_metadata) == Some(self@)
                },
                self.spec_base_log().inv(pm_region@, overall_metadata.log_area_addr as nat,
                    overall_metadata.log_area_size as nat),
                no_outstanding_writes_to_metadata(pm_region@, overall_metadata.log_area_addr as nat),
        {
//            lemma_persistent_memory_view_can_crash_as_committed(pm_region@);
        }

        pub closed spec fn view(self) -> AbstractOpLogState
        {
            self.state@
        }

        pub closed spec fn log_len(self) -> nat {
            self.log@.log.len()
        }

        pub open spec fn recover(mem: Seq<u8>, version_metadata: VersionMetadata, overall_metadata: OverallMetadata) -> Option<AbstractOpLogState>
        {
            // use log's recover method to recover the log state, then parse it into operations
            match UntrustedLogImpl::recover(mem, overall_metadata.log_area_addr as nat,
                                            overall_metadata.log_area_size as nat) {
                Some(log) => {
                    if log.log.len() == 0 {
                        Some(AbstractOpLogState::initialize())
                    } else {
                        if let Some(log_contents) = Self::get_log_contents(log) {
                            if let Some(physical_log_entries) =  Self::parse_log_ops(
                                log_contents, 
                                overall_metadata.log_area_addr as nat, 
                                overall_metadata.log_area_size as nat,
                                overall_metadata.region_size as nat, 
                                version_metadata.overall_metadata_addr as nat
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
            // log must be large enough for the following extract_bytes calls to make sense
            if log.log.len() < u64::spec_size_of() * 2 {
                None
            } else {
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
            
        }

        pub proof fn lemma_if_not_committed_recovery_equals_drop_pending_appends<Perm, PM>(
            self, 
            pm_region: PoWERPersistentMemoryRegion<Perm, PM>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
        )
            where 
                Perm: CheckPermission<Seq<u8>>,
                PM: PersistentMemoryRegion,
            requires
                self.inv(pm_region@, version_metadata, overall_metadata),
                UntrustedOpLog::<K, L>::recover(pm_region@.durable_state, version_metadata, overall_metadata) is Some,
                !self@.op_list_committed,
            ensures 
                self@.drop_pending_appends() == UntrustedOpLog::<K, L>::recover(pm_region@.durable_state, version_metadata, overall_metadata).unwrap()
        {
            // The base log is empty
            assert(self.log@.log.len() == 0);
            let base_log_recover_state = UntrustedLogImpl::recover(pm_region@.durable_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat);
            assert(base_log_recover_state is Some);
            self.log.lemma_all_crash_states_recover_to_drop_pending_appends(pm_region, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat);
            assert(base_log_recover_state.unwrap() == self.log@.drop_pending_appends());
        }

        proof fn lemma_parse_up_to_offset_succeeds(
            offset: nat,
            pm_region: PersistentMemoryRegionView,
            log_contents: Seq<u8>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
        )
            requires 
                UntrustedOpLog::<K, L>::recover(pm_region.durable_state, version_metadata, overall_metadata) is Some,
                ({
                    let base_log = UntrustedLogImpl::recover(pm_region.durable_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat);
                    &&& base_log matches Some(base_log)
                    &&& base_log.log.len() > 0
                    &&& log_contents == extract_bytes(base_log.log, 0, (base_log.log.len() - u64::spec_size_of()) as nat)
                }),
                Self::parse_log_ops_helper(0, offset, log_contents, overall_metadata.log_area_addr as nat, 
                    overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat) is Some,
                offset < log_contents.len(),
                u64::spec_size_of() < log_contents.len(),
            ensures 
                Self::parse_log_op(offset, log_contents, overall_metadata.log_area_addr as nat, 
                    overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat) is Some
        {
            // Proof by contradiction: if the op at offset cannot be parsed, then the whole op log cannot be parsed;
            // but the precondition says it can, so the op log must be valid/parseable.
            if Self::parse_log_op(offset, log_contents, overall_metadata.log_area_addr as nat, 
                    overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat) is None {
                assert(Self::parse_log_ops_helper(offset, log_contents.len(), log_contents, overall_metadata.log_area_addr as nat, 
                    overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat) is None);
                Self::lemma_partial_parse_fails_implies_full_parse_fails(0, offset, log_contents.len(), log_contents, 
                    overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
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
            overall_metadata_addr: nat,
        )
            requires 
                start <= mid <= end <= log_contents.len(),
                Self::parse_log_ops_helper(mid, end, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr) is None,
                Self::parse_log_ops_helper(start, mid, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr) is Some,
                end == log_contents.len(),
            ensures 
                Self::parse_log_ops_helper(start, end, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr) is None,
            decreases end - start
        {
            if start == mid {
                // trivial 
            } else {
                let next_op = Self::parse_log_op(start, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr).unwrap();
                let next_start = start + u64::spec_size_of() * 2 + next_op.len;
                Self::lemma_partial_parse_fails_implies_full_parse_fails(next_start, mid, end, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr);
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
            overall_metadata_addr: nat,
        )
        requires
            start <= mid <= end <= log_contents.len(),
            Self::parse_log_ops_helper(start, mid, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr) is Some,
            Self::parse_log_op(mid, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr) is Some,
            ({
                let last_op = Self::parse_log_op(mid, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr);
                &&& last_op matches Some(last_op)
                &&& end == mid + u64::spec_size_of() * 2 + last_op.len
            })
        ensures 
            Self::parse_log_ops_helper(start, end, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr) is Some,
            ({
                let old_seq = Self::parse_log_ops_helper(start, mid, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr).unwrap();
                let new_seq = Self::parse_log_ops_helper(start, end, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr).unwrap();
                let last_op = Self::parse_log_op(mid, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr).unwrap();
                new_seq == old_seq + seq![last_op]
            }),
        decreases end - start
        {
            let old_seq = Self::parse_log_ops_helper(start, mid,log_contents, log_start_addr, log_size, region_size, overall_metadata_addr).unwrap();
            let last_op = Self::parse_log_op(mid, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr).unwrap();

            if mid == start {
                // Base case: old_seq is empty.
                // This case is not trivial; Verus needs some help reasoning about the end point as well
                assert(Some(Seq::<AbstractPhysicalOpLogEntry>::empty()) == Self::parse_log_ops_helper(end, end, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr));
                return;
            }
            // first_op + middle_section == parse_log_ops_helper(start, mid, ...) by the definition of parse (which prepends earlier entries
            // onto the sequence of parsed ops)
            let first_op = Self::parse_log_op(start, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr).unwrap();
            let next_start = start + u64::spec_size_of() * 2 + first_op.len;
            let middle_section = Self::parse_log_ops_helper(next_start, mid, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr).unwrap();

            // associativity 
            assert((seq![first_op] + middle_section) + seq![last_op] == seq![first_op] + (middle_section + seq![last_op]));

            Self::lemma_op_log_parse_equal(next_start, mid, end, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr);  
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
            overall_metadata_addr: nat
        )
            requires 
                extract_bytes(mem2, 0, mem1.len()) == mem1,
                mem2.len() > mem1.len(),
                Self::parse_log_ops_helper(0, mem1.len(), mem1, log_start_addr, log_size, region_size, overall_metadata_addr) is Some,
            ensures 
                Self::parse_log_ops_helper(0, mem1.len(), mem1, log_start_addr, log_size, region_size, overall_metadata_addr) =~=
                    Self::parse_log_ops_helper(0, mem1.len(), mem2, log_start_addr, log_size, region_size, overall_metadata_addr)
        {
            let mem2_prefix = extract_bytes(mem2, 0, mem1.len());
            assert(Self::parse_log_ops_helper(0, mem1.len(), mem1, log_start_addr, log_size, region_size, overall_metadata_addr) =~=
                Self::parse_log_ops_helper(0, mem2_prefix.len(), mem2_prefix, log_start_addr, log_size, region_size, overall_metadata_addr));
            Self::lemma_inductive_parsing_same_range_equal(0, mem1.len(), mem1, mem2, log_start_addr, log_size, region_size, overall_metadata_addr);
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
            overall_metadata_addr: nat
        )
            requires 
                current_offset <= target_offset <= mem1.len() <= mem2.len(),
                target_offset == mem1.len(),
                extract_bytes(mem2, 0, mem1.len()) == mem1,
                Self::parse_log_ops_helper(current_offset, target_offset, mem1, log_start_addr, log_size, region_size, overall_metadata_addr) is Some,
            ensures 
                Self::parse_log_ops_helper(current_offset, target_offset, mem1, log_start_addr, log_size, region_size, overall_metadata_addr) =~=
                    Self::parse_log_ops_helper(current_offset, target_offset, mem2, log_start_addr, log_size, region_size, overall_metadata_addr)
            decreases target_offset - current_offset 
        {
            if target_offset == current_offset {
                // trivial
            } else {
                lemma_establish_extract_bytes_equivalence(mem1, mem2);
                let mem1_op = Self::parse_log_op(current_offset, mem1, log_start_addr, log_size, region_size, overall_metadata_addr);
                let entry_size = u64::spec_size_of() * 2 + mem1_op.unwrap().len;
                let next_offset = current_offset + entry_size;
                Self::lemma_inductive_parsing_same_range_equal(
                    next_offset,
                    target_offset,
                    mem1,
                    mem2, 
                    log_start_addr,
                    log_size,
                    region_size, 
                    overall_metadata_addr
                );
            }
        }

        pub proof fn lemma_num_log_entries_less_than_or_equal_to_log_bytes_len(
            current_offset: nat,
            target_offset: nat,
            mem: Seq<u8>,
            log_start_addr: nat,
            log_size: nat,
            region_size: nat,
            overall_metadata_addr: nat
        )
            requires 
                current_offset <= target_offset <= mem.len(),
                target_offset == mem.len(),
                Self::parse_log_ops_helper(current_offset, target_offset, mem, 
                    log_start_addr, log_size, region_size, overall_metadata_addr) is Some,
            ensures 
                ({
                    &&& Self::parse_log_ops_helper(current_offset, target_offset, mem, 
                            log_start_addr, log_size, region_size, overall_metadata_addr) matches Some(log)
                    &&& log.len() <= target_offset - current_offset
                })
            decreases target_offset - current_offset
        {
            broadcast use pmcopy_axioms;

            if target_offset == current_offset {
                // trivial
            } else {
                let op = Self::parse_log_op(current_offset, mem, log_start_addr, log_size, region_size, overall_metadata_addr);
                assert(op is Some);
                let entry_size = u64::spec_size_of() * 2 + op.unwrap().len;
                assert(entry_size > 1);
                let next_offset = current_offset + entry_size;
                Self::lemma_num_log_entries_less_than_or_equal_to_log_bytes_len(
                    next_offset, target_offset, mem, log_start_addr, log_size, region_size, overall_metadata_addr);
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
            overall_metadata_addr: nat,
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
                    ||| absolute_addr + len <= log_start_addr // region end before log area
                    ||| log_start_addr + log_size <= absolute_addr // region ends after log area
                })
                ||| absolute_addr < overall_metadata_addr + OverallMetadata::spec_size_of()
                ||| len == 0
                ||| log_contents.len() - u64::spec_size_of() * 2 < len
                ||| absolute_addr <= VersionMetadata::spec_size_of() + u64::spec_size_of()
                ||| absolute_addr < overall_metadata_addr + OverallMetadata::spec_size_of() + u64::spec_size_of()
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
            overall_metadata_addr: nat,
        ) -> Option<Seq<AbstractPhysicalOpLogEntry>>
        {
            Self::parse_log_ops_helper(0, log_contents.len(),  log_contents, log_start_addr, log_size, region_size, overall_metadata_addr)
        }

        pub open spec fn parse_log_ops_helper(
            current_offset: nat,
            target_offset: nat,
            log_contents: Seq<u8>,
            log_start_addr: nat, 
            log_size: nat,
            region_size: nat,
            overall_metadata_addr: nat,
        ) -> Option<Seq<AbstractPhysicalOpLogEntry>>
            decreases target_offset - current_offset
        {
            if target_offset == current_offset {
                Some(Seq::empty())
            } else {
                // parse the log entry at the current offset
                let op = Self::parse_log_op(current_offset, log_contents, log_start_addr, log_size, region_size, overall_metadata_addr);
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
                            region_size,
                            overall_metadata_addr
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
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
        )
            requires 
                Self::parse_log_ops_helper(current_offset, target_offset, log_contents, overall_metadata.log_area_addr as nat, 
                    overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat) is Some 
            ensures 
                ({
                    let parsed_log = Self::parse_log_ops_helper(current_offset, target_offset, log_contents, overall_metadata.log_area_addr as nat, 
                        overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat).unwrap();
                    AbstractPhysicalOpLogEntry::log_inv(parsed_log, version_metadata, overall_metadata)
                })
            decreases target_offset - current_offset
        {
            if target_offset == current_offset {
                // trivial
            } else {
                let op = Self::parse_log_op(current_offset, log_contents, overall_metadata.log_area_addr as nat, 
                    overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
                assert(op is Some); // inv holds when op can be parsed
                let entry_size = u64::spec_size_of() * 2 + op.unwrap().len;
                Self::lemma_successful_log_ops_parse_implies_inv(
                    current_offset + entry_size,
                    target_offset,
                    log_contents,
                    version_metadata,
                    overall_metadata
                );
            }
        }

        pub proof fn lemma_same_bytes_preserve_op_log_invariant<Perm, PM>(
            self,
            powerpm1: PoWERPersistentMemoryRegion<Perm, PM>,
            powerpm2: PoWERPersistentMemoryRegion<Perm, PM>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata
        )
            where 
                Perm: CheckPermission<Seq<u8>>,
                PM: PersistentMemoryRegion,
            requires 
                powerpm1@.len() == overall_metadata.region_size,
                powerpm1@.len() == powerpm2@.len(),
                powerpm1.inv(),
                powerpm2.inv(),
                self.inv(powerpm1@, version_metadata, overall_metadata),
                self.base_log_view() == self.base_log_view().drop_pending_appends(),
                powerpm1@.flush_predicted(),
                powerpm2@.flush_predicted(),
                extract_bytes(powerpm1@.durable_state, overall_metadata.log_area_addr as nat,
                              overall_metadata.log_area_size as nat) == 
                    extract_bytes(powerpm2@.durable_state, overall_metadata.log_area_addr as nat,
                                  overall_metadata.log_area_size as nat),
                0 <= overall_metadata.log_area_addr <
                    overall_metadata.log_area_addr + overall_metadata.log_area_size <= overall_metadata.region_size,
                0 < spec_log_header_area_size() <= spec_log_area_pos() < overall_metadata.log_area_size,
            ensures 
                self.inv(powerpm2@, version_metadata, overall_metadata),
        {
            let mem1 = powerpm1@.durable_state;
            let mem2 = powerpm2@.durable_state;
            lemma_same_log_bytes_recover_to_same_state(mem1, mem2, overall_metadata.log_area_addr as nat,
                overall_metadata.log_area_size as nat, overall_metadata.region_size as nat);
            self.log.lemma_same_bytes_preserve_log_invariant(powerpm1, powerpm2, 
                overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat,
                overall_metadata.region_size as nat);
        }

        pub proof fn lemma_same_bytes_recover_to_same_state(
            s1: Seq<u8>,
            s2: Seq<u8>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata
        )
            requires 
                s1.len() == overall_metadata.region_size,
                s1.len() == s2.len(),
                extract_bytes(s1, overall_metadata.log_area_addr as nat,
                              overall_metadata.log_area_size as nat) == 
                    extract_bytes(s2, overall_metadata.log_area_addr as nat,
                                  overall_metadata.log_area_size as nat),
                0 <= overall_metadata.log_area_addr <
                    overall_metadata.log_area_addr + overall_metadata.log_area_size <=
                    overall_metadata.region_size,
                0 < spec_log_header_area_size() <= spec_log_area_pos() < overall_metadata.log_area_size,
            ensures
                Self::recover(s1, version_metadata, overall_metadata) ==
                    Self::recover(s2, version_metadata, overall_metadata)
        {
            lemma_same_log_bytes_recover_to_same_state(s1, s2, overall_metadata.log_area_addr as nat,
                                                       overall_metadata.log_area_size as nat,
                                                       overall_metadata.region_size as nat);
        }

        pub proof fn lemma_same_op_log_view_preserves_invariant<Perm, PM>(
            self,
            powerpm1: PoWERPersistentMemoryRegion<Perm, PM>,
            powerpm2: PoWERPersistentMemoryRegion<Perm, PM>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata
        )
            where 
                Perm: CheckPermission<Seq<u8>>,
                PM: PersistentMemoryRegion,
            requires
                powerpm1@.len() == overall_metadata.region_size,
                powerpm1@.len() == powerpm2@.len(),
                powerpm1.inv(),
                powerpm2.inv(),
                self.inv(powerpm1@, version_metadata, overall_metadata),
                get_subregion_view(powerpm1@, overall_metadata.log_area_addr as nat,
                                   overall_metadata.log_area_size as nat) == 
                    get_subregion_view(powerpm2@, overall_metadata.log_area_addr as nat,
                                       overall_metadata.log_area_size as nat),
                0 <= overall_metadata.log_area_addr <
                    overall_metadata.log_area_addr + overall_metadata.log_area_size <= overall_metadata.region_size,
                0 < spec_log_header_area_size() <= spec_log_area_pos() < overall_metadata.log_area_size,
            ensures 
                self.inv(powerpm2@, version_metadata, overall_metadata)
        {
            powerpm1.lemma_inv_implies_view_valid();
            powerpm2.lemma_inv_implies_view_valid();

            self.log.lemma_same_log_view_preserves_invariant(powerpm1, powerpm2, overall_metadata.log_area_addr as nat,
                overall_metadata.log_area_size as nat, overall_metadata.region_size as nat);
            lemma_bytes_match_in_equal_subregions(powerpm1@, powerpm2@, overall_metadata.log_area_addr as nat,
                overall_metadata.log_area_size as nat);
            if !self@.op_list_committed {
                // If the log is not committed, we have to prove that all possible crash states recover to an empty log.
                assert(Self::recover(powerpm2@.durable_state, version_metadata, overall_metadata) ==
                       Some(AbstractOpLogState::initialize()))
                by {
                    let views_must_match_at_addr = |addr: int| overall_metadata.log_area_addr <= addr <
                        overall_metadata.log_area_addr + overall_metadata.log_area_size;
                    assert forall |addr: int| overall_metadata.log_area_addr <= addr <
                        overall_metadata.log_area_addr + overall_metadata.log_area_size 
                        implies powerpm1@.durable_state[addr] == powerpm2@.durable_state[addr] 
                    by { assert(views_must_match_at_addr(addr)); }
                    assert(extract_bytes(powerpm1@.durable_state, overall_metadata.log_area_addr as nat,
                                         overall_metadata.log_area_size as nat) == 
                        extract_bytes(powerpm2@.durable_state, overall_metadata.log_area_addr as nat,
                                      overall_metadata.log_area_size as nat));
                    UntrustedLogImpl::lemma_same_log_bytes_recover_to_same_state(
                        powerpm2@.durable_state,
                        powerpm1@.durable_state,
                        overall_metadata.log_area_addr as nat,
                        overall_metadata.log_area_size as nat
                    );
                }

                assert(Self::recover(powerpm2@.read_state, version_metadata, overall_metadata) ==
                       Some(AbstractOpLogState::initialize()))
                by {
                    // TODO: refactor this proof -- it's exactly the same as above
                    let views_must_match_at_addr = |addr: int| overall_metadata.log_area_addr <= addr <
                        overall_metadata.log_area_addr + overall_metadata.log_area_size;
                    assert forall |addr: int| overall_metadata.log_area_addr <= addr <
                        overall_metadata.log_area_addr + overall_metadata.log_area_size 
                        implies powerpm1@.read_state[addr] == powerpm2@.read_state[addr] 
                    by { assert(views_must_match_at_addr(addr)); }
                    assert(extract_bytes(powerpm1@.read_state, overall_metadata.log_area_addr as nat,
                                         overall_metadata.log_area_size as nat) == 
                        extract_bytes(powerpm2@.read_state, overall_metadata.log_area_addr as nat,
                                      overall_metadata.log_area_size as nat));
                    UntrustedLogImpl::lemma_same_log_bytes_recover_to_same_state(
                        powerpm2@.read_state,
                        powerpm1@.read_state,
                        overall_metadata.log_area_addr as nat,
                        overall_metadata.log_area_size as nat
                    );
                }
            } else {
                // If the op list is the same, we the proof is the same, but we are instead proving that 
                // the log always recovers to the current abstract state.
                assert(Self::recover(powerpm2@.durable_state, version_metadata, overall_metadata) == Some(self@))
                by {
                    // TODO: refactor this proof -- it's exactly the same as above
                    let views_must_match_at_addr = |addr: int| overall_metadata.log_area_addr <= addr <
                        overall_metadata.log_area_addr + overall_metadata.log_area_size;
                    assert forall |addr: int| overall_metadata.log_area_addr <= addr <
                        overall_metadata.log_area_addr + overall_metadata.log_area_size 
                        implies powerpm1@.durable_state[addr] == powerpm2@.durable_state[addr] 
                    by { assert(views_must_match_at_addr(addr)); }
                    assert(extract_bytes(powerpm1@.durable_state, overall_metadata.log_area_addr as nat,
                                         overall_metadata.log_area_size as nat) == 
                           extract_bytes(powerpm2@.durable_state, overall_metadata.log_area_addr as nat,
                                         overall_metadata.log_area_size as nat));
                    UntrustedLogImpl::lemma_same_log_bytes_recover_to_same_state(
                        powerpm2@.durable_state,
                        powerpm1@.durable_state,
                        overall_metadata.log_area_addr as nat,
                        overall_metadata.log_area_size as nat
                    );
                }

                assert(Self::recover(powerpm2@.read_state, version_metadata, overall_metadata) == Some(self@))
                by {
                    // TODO: refactor this proof -- it's exactly the same as above
                    let views_must_match_at_addr = |addr: int| overall_metadata.log_area_addr <= addr <
                        overall_metadata.log_area_addr + overall_metadata.log_area_size;
                    assert forall |addr: int| overall_metadata.log_area_addr <= addr <
                        overall_metadata.log_area_addr + overall_metadata.log_area_size 
                        implies powerpm1@.read_state[addr] == powerpm2@.read_state[addr] 
                    by { assert(views_must_match_at_addr(addr)); }
                    assert(extract_bytes(powerpm1@.read_state, overall_metadata.log_area_addr as nat,
                                         overall_metadata.log_area_size as nat) == 
                           extract_bytes(powerpm2@.read_state, overall_metadata.log_area_addr as nat,
                                         overall_metadata.log_area_size as nat));
                    UntrustedLogImpl::lemma_same_log_bytes_recover_to_same_state(
                        powerpm2@.read_state,
                        powerpm1@.read_state,
                        overall_metadata.log_area_addr as nat,
                        overall_metadata.log_area_size as nat
                    );
                }
            }
        }

        // This executable function parses the entire operation log iteratively
        // and returns a vector of `PhysicalOpLogEntry`. This operation will fail 
        // if the CRC for the op log does not match the rest of the log body or 
        // if any of the log entries themselves are invalid.
        pub exec fn parse_phys_op_log<Perm, PM>(
            pm_region: &PoWERPersistentMemoryRegion<Perm, PM>,
            log_bytes: Vec<u8>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata
        ) -> (result: Result<Vec<PhysicalOpLogEntry>, KvError<K>>)
            where 
                Perm: CheckPermission<Seq<u8>>,
                PM: PersistentMemoryRegion,
            requires
                pm_region.inv(),
                pm_region@.flush_predicted(),
                overall_metadata.log_area_addr + overall_metadata.log_area_size <= pm_region@.len() <= u64::MAX,
                overall_metadata.log_area_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
                Self::recover(pm_region@.durable_state, version_metadata, overall_metadata) is Some,
                pm_region@.len() == overall_metadata.region_size,
                ({
                    let base_log_state = UntrustedLogImpl::recover(pm_region@.durable_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat);
                    &&& base_log_state matches Some(base_log_state)
                    &&& log_bytes@ == extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat)
                }),
                ({
                    let base_log_state = UntrustedLogImpl::recover(pm_region@.durable_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
                    let phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
                    let abstract_op_log = Self::parse_log_ops(phys_op_log_buffer, overall_metadata.log_area_addr as nat, 
                            overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
                    &&& abstract_op_log matches Some(abstract_log)
                    &&& 0 < abstract_log.len() <= u64::MAX
                }),
                ({
                    let recovered_log = UntrustedOpLog::<K, L>::recover(pm_region@.durable_state, version_metadata, overall_metadata);
                    let parsed_ops = Self::parse_log_ops(log_bytes@, overall_metadata.log_area_addr as nat, 
                            overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
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
                            let abstract_op_log = UntrustedOpLog::<K, L>::recover(pm_region@.durable_state, version_metadata, overall_metadata);
                            &&& abstract_op_log matches Some(abstract_op_log)
                            &&& phys_log.len() == 0
                            &&& abstract_op_log.physical_op_list.len() == 0
                        }
                        ||| {
                            let abstract_op_log = UntrustedOpLog::<K, L>::recover(pm_region@.durable_state, version_metadata, overall_metadata);
                            let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                            &&& abstract_op_log matches Some(abstract_op_log)
                            &&& abstract_op_log.physical_op_list == phys_log_view
                            &&& AbstractPhysicalOpLogEntry::log_inv(phys_log_view, version_metadata, overall_metadata)
                            &&& forall |i: int| 0 <= i < phys_log_view.len() ==> #[trigger] (phys_log_view[i]).inv(version_metadata, overall_metadata)
                        }
                    }
                    Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption(),
                    Err(_) => false,
                }
    {
        let log_start_addr = overall_metadata.log_area_addr;
        let log_size = overall_metadata.log_area_size;
        let region_size = overall_metadata.region_size;
        let overall_metadata_addr = version_metadata.overall_metadata_addr;

        let ghost base_log_state = UntrustedLogImpl::recover(pm_region@.durable_state, log_start_addr as nat, log_size as nat).unwrap();
        let ghost phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
        let ghost abstract_op_log = Self::parse_log_ops(phys_op_log_buffer, log_start_addr as nat, 
                log_size as nat, region_size as nat, version_metadata.overall_metadata_addr as nat).unwrap();

        let mut offset = 0;
        let mut ops = Vec::<PhysicalOpLogEntry>::new();

        proof {
            // Before the loop, we haven't parsed anything
            let phys_log_view = Seq::new(ops@.len(), |i: int| ops[i]@);
            assert(phys_log_view == Seq::<AbstractPhysicalOpLogEntry>::empty());
            assert(Some(phys_log_view) == Self::parse_log_ops_helper(0, 0, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat, overall_metadata_addr as nat));
        }

        while offset < log_bytes.len()
            invariant
                u64::spec_size_of() * 2 <= log_bytes.len() <= u64::MAX,
                0 < abstract_op_log.len() <= u64::MAX,
                Self::parse_log_ops(log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat, overall_metadata_addr as nat) is Some,
                ({
                    let phys_log_view = Seq::new(ops@.len(), |i: int| ops[i]@);
                    &&& Self::parse_log_ops_helper(0, offset as nat, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat, overall_metadata_addr as nat) matches Some(abstract_log_view)
                    &&& phys_log_view == abstract_log_view
                    &&& AbstractPhysicalOpLogEntry::log_inv(phys_log_view, version_metadata, overall_metadata)
                }),
                ({
                    let recovered_log = UntrustedOpLog::<K, L>::recover(pm_region@.durable_state, version_metadata, overall_metadata);
                    let parsed_ops = Self::parse_log_ops(log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat, overall_metadata_addr as nat);
                    &&& recovered_log matches Some(recovered_log)
                    &&& parsed_ops matches Some(parsed_ops)
                    &&& recovered_log.physical_op_list == parsed_ops
                }),
                ({
                    let base_log_state = UntrustedLogImpl::recover(pm_region@.durable_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat);
                    &&& base_log_state matches Some(base_log_state)
                    &&& log_bytes@ == extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat)
                }),
                log_start_addr + log_size <= u64::MAX,
                offset <= log_bytes.len(),
                log_start_addr == overall_metadata.log_area_addr,
                log_size == overall_metadata.log_area_size,
                region_size == overall_metadata.region_size,
                overall_metadata_addr == version_metadata.overall_metadata_addr,
                forall |i: int| 0 <= i < ops.len() ==> #[trigger] (ops[i]).inv(version_metadata, overall_metadata)
        {
            broadcast use pmcopy_axioms;

            proof {
                assert(Self::parse_log_ops_helper(0, offset as nat, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat, overall_metadata_addr as nat) is Some);
                assert(UntrustedOpLog::<K, L>::recover(pm_region@.durable_state, version_metadata, overall_metadata) is Some);
                let recovered_base_log = UntrustedLogImpl::recover(pm_region@.durable_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();

                let log_contents = Self::get_log_contents(recovered_base_log).unwrap();
                assert(log_contents == extract_bytes(recovered_base_log.log, 0, (recovered_base_log.log.len() - u64::spec_size_of()) as nat));
                assert(log_contents == log_bytes@);
                // the full op log, as well as the op log up to offset, both recover correctly.
                // this should imply that there is either a valid entry at offset, or that offset is 
                // is at the end 
                Self::lemma_parse_up_to_offset_succeeds(offset as nat, pm_region@, log_contents, version_metadata, overall_metadata);

                assert(offset <= log_contents.len());
                let current_op = Self::parse_log_op(offset as nat, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat, overall_metadata_addr as nat);
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
                ||| addr <= traits_t::size_of::<VersionMetadata>() as u64 + traits_t::size_of::<u64>() as u64
                ||| addr < version_metadata.overall_metadata_addr + traits_t::size_of::<OverallMetadata>() as u64 + traits_t::size_of::<u64>() as u64
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
                assert(Self::parse_log_op(old_offset as nat, log_bytes@, log_start_addr as nat, log_size as nat, 
                    region_size as nat, overall_metadata_addr as nat) is Some);
                Self::lemma_op_log_parse_equal(0, old_offset as nat, offset as nat, log_bytes@, log_start_addr as nat, 
                    log_size as nat, region_size as nat, overall_metadata_addr as nat);      
                
                let abstract_partial_log = Self::parse_log_ops_helper(0, offset as nat, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat, overall_metadata_addr as nat);
                assert(abstract_partial_log is Some);
                let abstract_partial_log = abstract_partial_log.unwrap();
                assert(abstract_partial_log == phys_log_view);

                Self::lemma_successful_log_ops_parse_implies_inv(0, offset as nat, log_bytes@, version_metadata, overall_metadata);
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
        pm_region: &PoWERPersistentMemoryRegion<Perm, PM>,
        version_metadata: VersionMetadata,
        overall_metadata: OverallMetadata
    ) -> (result: Result<(Self, Vec<PhysicalOpLogEntry>), KvError<K>>)
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires
            pm_region.inv(),
            pm_region@.flush_predicted(),
            overall_metadata.log_area_addr + overall_metadata.log_area_size <= pm_region@.len() <= u64::MAX,
            overall_metadata.log_area_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
            Self::recover(pm_region@.durable_state, version_metadata, overall_metadata) is Some,
            pm_region@.len() == overall_metadata.region_size,
            ({
                let base_log_state = UntrustedLogImpl::recover(pm_region@.durable_state,
                                                               overall_metadata.log_area_addr as nat,
                                                               overall_metadata.log_area_size as nat).unwrap();
                let phys_op_log_buffer = extract_bytes(base_log_state.log, 0,
                                                       (base_log_state.log.len() - u64::spec_size_of()) as nat);
                let abstract_op_log = Self::parse_log_ops(phys_op_log_buffer, overall_metadata.log_area_addr as nat, 
                        overall_metadata.log_area_size as nat, overall_metadata.region_size as nat,
                                                          version_metadata.overall_metadata_addr as nat);
                ||| base_log_state.log.len() == 0 
                ||| {
                        &&& abstract_op_log matches Some(abstract_log)
                        &&& 0 <= abstract_log.len() <= u64::MAX
                    }
            }),
            overall_metadata.log_area_addr + overall_metadata.log_area_size <= u64::MAX,
            overall_metadata.log_area_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
            overall_metadata.log_area_addr as int % const_persistence_chunk_size() == 0,
            overall_metadata.log_area_size as int % const_persistence_chunk_size() == 0,
        ensures
            match result {
                Ok((op_log_impl, phys_log)) => {
                    &&& op_log_impl.inv(pm_region@, version_metadata, overall_metadata)
                    &&& op_log_impl.base_log_view() == op_log_impl.base_log_view().drop_pending_appends()
                    &&& {
                        ||| {
                            let abstract_op_log = UntrustedOpLog::<K, L>::recover(pm_region@.durable_state,
                                                                                  version_metadata, overall_metadata);
                            &&& abstract_op_log matches Some(abstract_op_log)
                            &&& abstract_op_log == op_log_impl@
                            &&& phys_log.len() == 0
                            &&& abstract_op_log.physical_op_list.len() == 0
                            &&& !abstract_op_log.op_list_committed
                        }
                        ||| {
                            let abstract_op_log = UntrustedOpLog::<K, L>::recover(pm_region@.durable_state,
                                                                                  version_metadata, overall_metadata);
                            let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                            &&& abstract_op_log matches Some(abstract_op_log)
                            &&& abstract_op_log == op_log_impl@
                            &&& abstract_op_log.physical_op_list == phys_log_view
                            &&& AbstractPhysicalOpLogEntry::log_inv(phys_log_view, version_metadata, overall_metadata)
                            &&& abstract_op_log.op_list_committed
                            &&& abstract_op_log.physical_op_list.len() > 0
                        }
                    }
                }
                Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption(),
                Err(_) => false
            }
    {
        proof {
            pm_region.lemma_inv_implies_view_valid();
        }
        
        let log_start_addr = overall_metadata.log_area_addr;
        let log_size = overall_metadata.log_area_size;

        // Start the base log
        let ghost base_log_state =
            UntrustedLogImpl::recover(pm_region@.durable_state, log_start_addr as nat, log_size as nat).unwrap();
        let log = match UntrustedLogImpl::start(pm_region, log_start_addr, log_size, Ghost(base_log_state)) {
            Ok(log) => log,
            Err(LogErr::CRCMismatch) => return Err(KvError::CRCMismatch),
            Err(e) => { assert(false); return Err(KvError::LogErr{ log_err: e }) },
        };
        let ghost op_log_state = Self::recover(pm_region@.durable_state, version_metadata, overall_metadata);

        proof {
            // Prove that all current possible crash states recover to `op_log_state`
            assert(Self::recover(pm_region@.durable_state, version_metadata, overall_metadata) ==
                   Some(op_log_state.unwrap()));
        }

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

        let (mut combined_bytes, combined_addrs) = match log.read(pm_region, log_start_addr, log_size, head, (tail - head) as u64) {
            Ok(bytes) => bytes,
            Err(e) => {
                assert(head == log@.head);
                assert(tail < log@.head + log@.log.len());
                return Err(KvError::LogErr { log_err: e });
            }
        };

        let len = ((tail - head) as u64 - traits_t::size_of::<u64>() as u64) as usize;
        let crc_bytes = combined_bytes.split_off(len);
        let log_bytes = combined_bytes;
        let ghost log_addrs = combined_addrs@.subrange(0 as int, len as int);
        let ghost crc_addrs = combined_addrs@.subrange(len as int, combined_addrs@.len() as int);

        let computed_crc = calculate_crc_bytes(log_bytes.as_slice());
        let crcs_match = compare_crcs(crc_bytes.as_slice(), computed_crc);

        proof {
            let true_log_bytes = log@.read(head as int, len as int);
            let true_crc_bytes = spec_crc_bytes(true_log_bytes);
            if pm_region.constants().impervious_to_corruption() {
                pm_region.constants().maybe_corrupted_zero_addrs(log_bytes@, true_log_bytes, log_addrs);
                pm_region.constants().maybe_corrupted_zero_addrs(crc_bytes@, true_crc_bytes, crc_addrs);
                assert(log_bytes@ == true_log_bytes);
                assert(crc_bytes@ == true_crc_bytes);
            } else if crcs_match {
                pm_region.constants().maybe_corrupted_crc(log_bytes@, true_log_bytes, log_addrs,
                                                          crc_bytes@, true_crc_bytes, crc_addrs);
            }
        }

        if !crcs_match {
            return Err(KvError::CRCMismatch);
        }

        let phys_op_log = Self::parse_phys_op_log(pm_region, log_bytes, version_metadata, overall_metadata)?;

        let op_log_impl = Self {
            log,
            state: Ghost(op_log_state.unwrap()),
            current_transaction_crc: CrcDigest::new(),
            _phantom: None
        };

        Ok((
            op_log_impl,
            phys_op_log
        ))
    }

    // This lemma proves that if we append a log entry to the current op log,
    // and append the same log entry as a sequence of bytes to the current 
    // base log, then parsing the log in the base log will return the 
    // current op log.
    proof fn lemma_appending_log_entry_bytes_appends_op_to_list(
        self,
        pm_region: PersistentMemoryRegionView,
        log_entry: PhysicalOpLogEntry,
        version_metadata: VersionMetadata,
        overall_metadata: OverallMetadata,
    )
        requires
            ({
                let pending_bytes = self.log@.pending;
                let log_ops = Self::parse_log_ops(pending_bytes, overall_metadata.log_area_addr as nat, 
                    overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
                &&& log_ops is Some 
                &&& log_ops.unwrap() == self@.physical_op_list
                &&& pending_bytes.len() + u64::spec_size_of() * 2 <= u64::MAX
                &&& pending_bytes.len() + u64::spec_size_of() * 2 + log_entry.len <= u64::MAX
            }),
            // log entry is valid
            0 <= log_entry.absolute_addr,
            log_entry.absolute_addr + log_entry.len <= pm_region.len() <= u64::MAX,
            ({
                ||| log_entry.absolute_addr + log_entry.len <= overall_metadata.log_area_addr
                ||| overall_metadata.log_area_addr + overall_metadata.log_area_size <= log_entry.absolute_addr
            }),
            log_entry.bytes@.len() <= u64::MAX,
            log_entry.len != 0,
            log_entry.len == log_entry.bytes@.len(),
            log_entry.absolute_addr + log_entry.len <= overall_metadata.region_size,
            overall_metadata.region_size == pm_region.len(),
            log_entry.inv(version_metadata, overall_metadata),
        ensures 
            ({
                let pending_bytes = self.log@.pending;
                let bytes = log_entry.bytes@;
                let new_pending_bytes = pending_bytes + log_entry.absolute_addr.spec_to_bytes() + (log_entry.bytes.len() as u64).spec_to_bytes() + bytes;
                let new_log_ops = Self::parse_log_ops(new_pending_bytes, overall_metadata.log_area_addr as nat, 
                    overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
                &&& new_log_ops is Some 
                &&& new_log_ops.unwrap() == self@.physical_op_list.push(log_entry@)

            })
    {
        broadcast use pmcopy_axioms;

        let log_start_addr = overall_metadata.log_area_addr as nat;
        let log_size = overall_metadata.log_area_size as nat;
        let region_size = overall_metadata.region_size as nat;
        let overall_metadata_addr = version_metadata.overall_metadata_addr as nat;

        let pending_bytes = self.log@.pending;
        let bytes = log_entry.bytes@;
        let new_pending_bytes = pending_bytes + log_entry.absolute_addr.spec_to_bytes() + (log_entry.bytes.len() as u64).spec_to_bytes() + bytes;
        let old_log_ops = Self::parse_log_ops(pending_bytes, overall_metadata.log_area_addr as nat, 
            overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat).unwrap();

        // parsing just the new operation's bytes succeeds
        let new_op = Self::parse_log_op(pending_bytes.len(), new_pending_bytes, log_start_addr, log_size, region_size, overall_metadata_addr);
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
        Self::lemma_parsing_same_range_equal(pending_bytes, new_pending_bytes, log_start_addr, log_size, region_size, overall_metadata_addr);

        // Appending the new op to the pending_bytes op log is equivalent to parsing all of new_pending_bytes
        Self::lemma_op_log_parse_equal(0, pending_bytes.len(), new_pending_bytes.len(), new_pending_bytes, log_start_addr, log_size, region_size, overall_metadata_addr);
        let new_log_ops = Self::parse_log_ops(new_pending_bytes, overall_metadata.log_area_addr as nat, 
            overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
        
        assert(new_log_ops.unwrap() == old_log_ops.push(new_op.unwrap()));
    }

    pub exec fn abort_transaction<Perm, PM>(
        &mut self, 
        log_powerpm: &mut PoWERPersistentMemoryRegion<Perm, PM>,
        version_metadata: VersionMetadata,
        overall_metadata: OverallMetadata,
    )
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires 
            old(self).spec_base_log().inv(old(log_powerpm)@, overall_metadata.log_area_addr as nat, 
                overall_metadata.log_area_size as nat),
            old(log_powerpm).inv(),
            overall_metadata.log_area_addr as int % const_persistence_chunk_size() == 0,
            overall_metadata.log_area_size as int % const_persistence_chunk_size() == 0,
            no_outstanding_writes_to_metadata(old(log_powerpm)@, overall_metadata.log_area_addr as nat),
            Self::recover(old(log_powerpm)@.read_state, version_metadata, overall_metadata) ==
                Some(AbstractOpLogState::initialize()),
            Self::recover(old(log_powerpm)@.durable_state, version_metadata, overall_metadata) ==
                Some(AbstractOpLogState::initialize()),
            overall_metadata.region_size == old(log_powerpm)@.len(),
            !old(self)@.op_list_committed,
        ensures 
            log_powerpm.constants() == old(log_powerpm).constants(),
            log_powerpm@.len() == old(log_powerpm)@.len(), 
            self.base_log_view().pending.len() == 0,
            self.base_log_view().log == old(self).base_log_view().log,
            self.base_log_view().head == old(self).base_log_view().head,
            self.base_log_view().capacity == old(self).base_log_view().capacity,
            old(log_powerpm)@.flush_predicted(),
            log_powerpm@.flush_predicted(),
            log_powerpm.inv(),
            Self::recover(log_powerpm@.read_state, version_metadata, overall_metadata) ==
                Some(AbstractOpLogState::initialize()),
            Self::recover(log_powerpm@.durable_state, version_metadata, overall_metadata) ==
                Some(AbstractOpLogState::initialize()),
            self.inv(log_powerpm@, version_metadata, overall_metadata), 
            self@.physical_op_list.len() == 0,
            states_differ_only_in_log_region(old(log_powerpm)@.read_state, log_powerpm@.durable_state, 
                overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat),
            states_differ_only_in_log_region(old(log_powerpm)@.durable_state, log_powerpm@.durable_state, 
                overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat),
            !self@.op_list_committed,
    {
        /*
        assert(self.log@.log.len() == 0) by {
            self.log.lemma_inv_implies_can_only_crash_as_state(old(log_powerpm)@, overall_metadata.log_area_addr as nat,
                                                               overall_metadata.log_area_size as nat);
        }
        */
        self.log.abort_pending_appends(log_powerpm, overall_metadata.log_area_addr, overall_metadata.log_area_size);
        self.current_transaction_crc = CrcDigest::new();
        self.state = Ghost(AbstractOpLogState {
            physical_op_list: Seq::empty(),
            op_list_committed: false
        });
        assert(UntrustedLogImpl::recover(log_powerpm@.durable_state, overall_metadata.log_area_addr as nat,
                                         overall_metadata.log_area_size as nat) == Some(self.log@));
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
        log_powerpm: &mut PoWERPersistentMemoryRegion<Perm, PM>,
        log_entry: &PhysicalOpLogEntry,
        version_metadata: VersionMetadata,
        overall_metadata: OverallMetadata,
        Ghost(crash_pred): Ghost<spec_fn(Seq<u8>) -> bool>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), KvError<K>>)
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires 
            old(self).inv(old(log_powerpm)@, version_metadata, overall_metadata),
            old(log_powerpm).inv(),
            log_entry@.inv(version_metadata, overall_metadata),
            !old(self)@.op_list_committed,
            overall_metadata.region_size == old(log_powerpm)@.len(),
            Self::parse_log_ops(old(self).base_log_view().pending, overall_metadata.log_area_addr as nat, 
                                overall_metadata.log_area_size as nat, overall_metadata.region_size as nat,
                                version_metadata.overall_metadata_addr as nat) is Some,
            Self::recover(old(log_powerpm)@.durable_state, version_metadata, overall_metadata) ==
                Some(AbstractOpLogState::initialize()),
            Self::recover(old(log_powerpm)@.read_state, version_metadata, overall_metadata) ==
                Some(AbstractOpLogState::initialize()),
            crash_pred(old(log_powerpm)@.durable_state),
            forall |s1: Seq<u8>, s2: Seq<u8>| {
                &&& s1.len() == s2.len() 
                &&& #[trigger] crash_pred(s1)
                &&& states_differ_only_in_log_region(s1, s2, overall_metadata.log_area_addr as nat,
                                                   overall_metadata.log_area_size as nat)
                &&& Self::recover(s1, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize())
                &&& Self::recover(s2, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize())
            } ==> #[trigger] crash_pred(s2),
            forall |s| crash_pred(s) ==> perm.permits(s),
            log_entry.len == log_entry.bytes@.len(),
            log_entry.absolute_addr + log_entry.len <= overall_metadata.region_size,
            ({
                let pending_bytes = old(self).base_log_view().pending;
                let log_ops = Self::parse_log_ops(pending_bytes, overall_metadata.log_area_addr as nat, 
                                                  overall_metadata.log_area_size as nat,
                                                  overall_metadata.region_size as nat,
                                                  version_metadata.overall_metadata_addr as nat);
                &&& log_ops is Some 
                &&& log_ops.unwrap() == old(self)@.physical_op_list
            }),
        ensures 
            log_powerpm.constants() == old(log_powerpm).constants(),
            log_powerpm@.len() == old(log_powerpm)@.len(), 
            log_powerpm.inv(),
            Self::recover(log_powerpm@.durable_state, version_metadata, overall_metadata) ==
                Some(AbstractOpLogState::initialize()),
            Self::recover(log_powerpm@.read_state, version_metadata, overall_metadata) ==
                Some(AbstractOpLogState::initialize()),
            self.inv(log_powerpm@, version_metadata, overall_metadata), // can we maintain this here?
            views_differ_only_in_log_region(old(log_powerpm)@, log_powerpm@, 
                                            overall_metadata.log_area_addr as nat,
                                            overall_metadata.log_area_size as nat),
            match result {
                Ok(()) => {
                    &&& self@ == old(self)@.tentatively_append_log_entry(log_entry@)
                }
                Err(KvError::OutOfSpace) => {
                    &&& !self@.op_list_committed
                    &&& self.base_log_view().pending.len() == 0
                    &&& self.base_log_view().log == old(self).base_log_view().log
                    &&& self.base_log_view().head == old(self).base_log_view().head
                    &&& self.base_log_view().capacity == old(self).base_log_view().capacity
                    &&& log_powerpm@.flush_predicted()
                    &&& self@.physical_op_list.len() == 0
                }
                Err(_) => false 
            }
    {
        let ghost log_start_addr = overall_metadata.log_area_addr as nat;
        let ghost log_size = overall_metadata.log_area_size as nat;
        let ghost old_powerpm = log_powerpm@;

        assert(states_differ_only_in_log_region(old(log_powerpm)@.durable_state, log_powerpm@.durable_state, 
                                                overall_metadata.log_area_addr as nat,
                                                overall_metadata.log_area_size as nat));
        
        // this assert is sufficient to hit the triggers we need to prove that the log entries
        // are all valid after appending the new one
        assert(forall |i: int| 0 <= i < self@.physical_op_list.len() ==> {
            let op = #[trigger] self@.physical_op_list[i];
            op.inv(version_metadata, overall_metadata)
        });

        let pending_len = self.log.get_pending_len(log_powerpm, &overall_metadata);
        if {
            ||| pending_len > u64::MAX - traits_t::size_of::<u64>() as u64 * 2 
            ||| log_entry.len > u64::MAX - traits_t::size_of::<u64>() as u64 * 2
            ||| pending_len > u64::MAX - traits_t::size_of::<u64>() as u64 * 2 - log_entry.len
        } {
            self.abort_transaction(log_powerpm, version_metadata,overall_metadata);
            return Err(KvError::OutOfSpace);
        } 

        proof {
            assert(pending_len == self.log@.pending.len());
            assert(pending_len + u64::spec_size_of() * 2 <= u64::MAX);
            assert(pending_len + u64::spec_size_of() * 2 + log_entry.len <= u64::MAX);

            // before we append anything, prove that appending this entry will maintain the loop invariant
            self.lemma_appending_log_entry_bytes_appends_op_to_list(log_powerpm@, *log_entry,
                                                                    version_metadata, overall_metadata);
            self.log.lemma_all_crash_states_recover_to_drop_pending_appends(*log_powerpm, log_start_addr, log_size);
            log_powerpm.lemma_inv_implies_view_valid();
        }

        let absolute_addr = log_entry.absolute_addr;

        let ghost old_digest = self.current_transaction_crc.bytes_in_digest();
        let ghost old_pending = self.log@.pending;

        assert(states_differ_only_in_log_region(old(log_powerpm)@.durable_state, log_powerpm@.durable_state, 
                                                overall_metadata.log_area_addr as nat,
                                                overall_metadata.log_area_size as nat));

        let result = self.log.tentatively_append(
            log_powerpm,
            overall_metadata.log_area_addr, 
            overall_metadata.log_area_size, 
            absolute_addr.as_byte_slice(),
            Ghost(crash_pred),
            Tracked(perm)
        );
        
        match result {
            Ok(_) => {}
            Err(e) => {
                self.abort_transaction(log_powerpm, version_metadata,overall_metadata);
                match e {
                    LogErr::InsufficientSpaceForAppend{available_space} =>
                        return Err(KvError::OutOfSpace),
                    _ => {
                        assert(false);
                        return Err(KvError::InternalError);
                    }
                }
            }
        }
        self.current_transaction_crc.write_bytes(absolute_addr.as_byte_slice());

        assert(states_differ_only_in_log_region(old(log_powerpm)@.durable_state, log_powerpm@.durable_state, 
                                                overall_metadata.log_area_addr as nat,
                                                overall_metadata.log_area_size as nat)) by {
            log_powerpm.lemma_inv_implies_view_valid();
            lemma_if_views_differ_only_in_region_then_states_do(
                old(log_powerpm)@,
                log_powerpm@,
                overall_metadata.log_area_addr as nat,
                overall_metadata.log_area_size as nat
            );
        }

        proof {
            // This proves that the CRC digest bytes and log pending bytes are the same
            let current_digest = self.current_transaction_crc.bytes_in_digest();
            let bytes = absolute_addr.spec_to_bytes();
            assert(current_digest == old_digest.push(bytes));
            assert(self.log@.pending == old_pending + bytes);
            assert(old_digest.flatten() == old_pending);
            lemma_seqs_flatten_equal_suffix(current_digest);
            assert(current_digest[current_digest.len() - 1] == bytes);
            assert(current_digest.subrange(0, current_digest.len() - 1) == old_digest);
            assert(current_digest.flatten() == old_digest.flatten() + bytes);
        }

        let len = log_entry.bytes.len() as u64;

        let ghost old_digest = self.current_transaction_crc.bytes_in_digest();
        let ghost old_pending = self.log@.pending;

        assert(states_differ_only_in_log_region(old(log_powerpm)@.durable_state, log_powerpm@.durable_state, 
                                                overall_metadata.log_area_addr as nat,
                                                overall_metadata.log_area_size as nat));

        let result = self.log.tentatively_append(
            log_powerpm,
            overall_metadata.log_area_addr, 
            overall_metadata.log_area_size, 
            len.as_byte_slice(),
            Ghost(crash_pred),
            Tracked(perm)
        );
        match result {
            Ok(_) => {}
            Err(e) => {
                self.abort_transaction(log_powerpm, version_metadata,overall_metadata);
                match e {
                    LogErr::InsufficientSpaceForAppend{available_space} =>
                        return Err(KvError::OutOfSpace),
                    _ => {
                        assert(false);
                        return Err(KvError::InternalError);
                    }
                }
            }
        }
        self.current_transaction_crc.write_bytes(len.as_byte_slice());

        assert(states_differ_only_in_log_region(old(log_powerpm)@.durable_state, log_powerpm@.durable_state, 
                                                overall_metadata.log_area_addr as nat,
                                                overall_metadata.log_area_size as nat));

        proof {
            // This proves that the CRC digest bytes and log pending bytes are the same
            let current_digest = self.current_transaction_crc.bytes_in_digest();
            let bytes = len.spec_to_bytes();
            assert(current_digest == old_digest.push(bytes));
            assert(self.log@.pending == old_pending + bytes);
            assert(old_digest.flatten() == old_pending);
            lemma_seqs_flatten_equal_suffix(current_digest);
            assert(current_digest[current_digest.len() - 1] == bytes);
            assert(current_digest.subrange(0, current_digest.len() - 1) == old_digest);
            assert(current_digest.flatten() == old_digest.flatten() + bytes);
        }
        
        assert(self.current_transaction_crc.bytes_in_digest().flatten() == self.log@.pending);

        let ghost old_digest = self.current_transaction_crc.bytes_in_digest();
        let ghost old_pending = self.log@.pending;

        let bytes = log_entry.bytes.as_slice();
        let result = self.log.tentatively_append(
            log_powerpm, 
            overall_metadata.log_area_addr, 
            overall_metadata.log_area_size, 
            bytes,
            Ghost(crash_pred),
            Tracked(perm)
        );
        match result {
            Ok(_) => {}
            Err(e) => {
                self.abort_transaction(log_powerpm, version_metadata,overall_metadata);
                match e {
                    LogErr::InsufficientSpaceForAppend{available_space} => return Err(KvError::OutOfSpace),
                    _ => {
                        assert(false);
                        return Err(KvError::InternalError);
                    }
                }
            }
        }
        // update the op log's CRC digest
        self.current_transaction_crc.write_bytes(bytes);

        assert(states_differ_only_in_log_region(old(log_powerpm)@.durable_state, log_powerpm@.durable_state, 
                                                overall_metadata.log_area_addr as nat,
                                                overall_metadata.log_area_size as nat));

        proof {
            let current_digest = self.current_transaction_crc.bytes_in_digest();
            let bytes = bytes@;
            assert(current_digest == old_digest.push(bytes));
            assert(self.log@.pending == old_pending + bytes);
            assert(old_digest.flatten() == old_pending);
            lemma_seqs_flatten_equal_suffix(current_digest);
            assert(current_digest[current_digest.len() - 1] == bytes);
            assert(current_digest.subrange(0, current_digest.len() - 1) == old_digest);
            assert(current_digest.flatten() == old_digest.flatten() + bytes);
        }

        // update the ghost state to reflect the new entry
        let ghost new_state = self.state@.tentatively_append_log_entry(log_entry@);
        self.state = Ghost(new_state);

        assert(states_differ_only_in_log_region(old(log_powerpm)@.durable_state, log_powerpm@.durable_state, 
                                                overall_metadata.log_area_addr as nat,
                                                overall_metadata.log_area_size as nat));

        proof {
            // We need to prove that we maintain the invariant that parsing the pending log bytes
            // gives us the current abstract op log
            let old_pending_bytes = old(self).log@.pending;
            let new_pending_bytes = self.log@.pending;

            assert(new_pending_bytes == old_pending_bytes + absolute_addr.spec_to_bytes() + len.spec_to_bytes() + bytes@);

            let old_log_ops = Self::parse_log_ops(old_pending_bytes, overall_metadata.log_area_addr as nat, 
                overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
            let new_log_ops = Self::parse_log_ops(new_pending_bytes, overall_metadata.log_area_addr as nat, 
                overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
            assert(old_log_ops is Some);
            assert(new_log_ops is Some);
            assert(new_log_ops.unwrap() == self@.physical_op_list);
        }

        assert(states_differ_only_in_log_region(old(log_powerpm)@.durable_state, log_powerpm@.durable_state, 
                                                overall_metadata.log_area_addr as nat,
                                                overall_metadata.log_area_size as nat));
        
        Ok(())
    }

    // This function commits the operation log. It first appends the CRC of the current
    // digest, then commits the base log. If either the append or the base log commit 
    // operation fail, then the transaction is aborted.
    pub exec fn commit_log<Perm, PM>(
        &mut self, 
        log_powerpm: &mut PoWERPersistentMemoryRegion<Perm, PM>,
        version_metadata: VersionMetadata,
        overall_metadata: OverallMetadata,
        Ghost(crash_pred): Ghost<spec_fn(Seq<u8>) -> bool>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), KvError<K>>)
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires 
            old(self).inv(old(log_powerpm)@, version_metadata, overall_metadata),
            old(self)@.physical_op_list.len() > 0,
            !old(self)@.op_list_committed,
            old(log_powerpm).inv(),
            overall_metadata.log_area_addr + spec_log_area_pos() <= old(log_powerpm)@.len(),
            Self::recover(old(log_powerpm)@.durable_state, version_metadata, overall_metadata) ==
                Some(AbstractOpLogState::initialize()),
            crash_pred(old(log_powerpm)@.durable_state),
            forall |s2: Seq<u8>| {
                let flushed_state = old(log_powerpm)@.read_state;
                &&& flushed_state.len() == s2.len() 
                &&& states_differ_only_in_log_region(flushed_state, s2, overall_metadata.log_area_addr as nat,
                                                   overall_metadata.log_area_size as nat)
                &&& Self::recover(s2, version_metadata, overall_metadata) == Some(old(self)@.commit_op_log())
            } ==> perm.permits(s2),
            forall |s2: Seq<u8>| {
                let crash_state = old(log_powerpm)@.durable_state;
                &&& crash_state.len() == s2.len() 
                &&& states_differ_only_in_log_region(crash_state, s2, overall_metadata.log_area_addr as nat,
                                                   overall_metadata.log_area_size as nat)
                &&& Self::recover(s2, version_metadata, overall_metadata) ==
                       Some(AbstractOpLogState::initialize())
            } ==> perm.permits(s2),
            forall |s1: Seq<u8>, s2: Seq<u8>| {
                &&& s1.len() == s2.len() 
                &&& #[trigger] crash_pred(s1)
                &&& states_differ_only_in_log_region(s1, s2, overall_metadata.log_area_addr as nat,
                                                   overall_metadata.log_area_size as nat)
                &&& Self::recover(s1, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize())
                &&& Self::recover(s2, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize())
            } ==> #[trigger] crash_pred(s2),
            forall |s| crash_pred(s) ==> perm.permits(s),
            // TODO: log probably shouldn't know about version metadata
            no_outstanding_writes_to_version_metadata(old(log_powerpm)@),
            old(log_powerpm)@.len() >= VersionMetadata::spec_size_of(),
        ensures 
            self.inv(log_powerpm@, version_metadata, overall_metadata),
            log_powerpm.inv(),
            log_powerpm@.len() == old(log_powerpm)@.len(),
            log_powerpm.constants() == old(log_powerpm).constants(),
            log_powerpm@.flush_predicted(),
            states_differ_only_in_log_region(old(log_powerpm)@.read_state, log_powerpm@.durable_state, 
                                             overall_metadata.log_area_addr as nat,
                                             overall_metadata.log_area_size as nat),
            views_differ_only_in_log_region(old(log_powerpm)@, log_powerpm@,
                                            overall_metadata.log_area_addr as nat,
                                            overall_metadata.log_area_size as nat),
            self.base_log_view().pending.len() == 0,
            match result {
                Ok(()) => {
                    &&& self@ == old(self)@.commit_op_log()
                    &&& Self::recover(log_powerpm@.durable_state, version_metadata, overall_metadata) == Some(self@)
                    &&& Self::recover(log_powerpm@.read_state, version_metadata, overall_metadata) == Some(self@)
                }
                Err(KvError::LogErr{log_err}) => {
                    &&& !self@.op_list_committed
                    &&& self.base_log_view().log == old(self).base_log_view().log
                    &&& self.base_log_view().head == old(self).base_log_view().head
                    &&& self.base_log_view().capacity == old(self).base_log_view().capacity
                    &&& old(log_powerpm)@.flush_predicted()
                    &&& log_powerpm@.flush_predicted()
                    &&& self@.physical_op_list.len() == 0
                    &&& Self::recover(log_powerpm@.durable_state, version_metadata, overall_metadata) == 
                            Some(AbstractOpLogState::initialize())
                    &&& Self::recover(log_powerpm@.read_state, version_metadata, overall_metadata) == 
                            Some(AbstractOpLogState::initialize())
                }
                Err(_) => false 
            }
    {
        let ghost log_start_addr = overall_metadata.log_area_addr as nat;
        let ghost log_size = overall_metadata.log_area_size as nat;

        let transaction_crc = self.current_transaction_crc.sum64();
        let bytes = transaction_crc.as_byte_slice();

        proof {
            broadcast use pmcopy_axioms;
            // All base log crash states that result in self.base_log_view.drop_pending_appends() will result in 
            // an op log state that is allowed by `perm`. The base log's `tentatively_append` requires that perm
            // allow base log states that recover to self.base_log_view.drop_pending_appends(), so this 
            // assertion tells us that all crash states considered legal in the base log's `tentatively_append` 
            // also recover to a legal op log state
            assert forall |s| UntrustedLogImpl::recover(s, overall_metadata.log_area_addr as nat,
                                                   overall_metadata.log_area_size as nat) == 
                    Some(self.base_log_view().drop_pending_appends())
                implies #[trigger] Self::recover(s, version_metadata, overall_metadata) ==
                                   Some(AbstractOpLogState::initialize()) 
            by {
                let base_log_recovery_state = UntrustedLogImpl::recover(s, overall_metadata.log_area_addr as nat,
                                                                        overall_metadata.log_area_size as nat);
                assert(base_log_recovery_state is Some);
                assert(base_log_recovery_state.unwrap().log.len() == 0);
            }
            assert(bytes.len() > 0);
        }

        let ghost old_pending_bytes = self.log@.pending;

        proof {
            self.log.lemma_all_crash_states_recover_to_drop_pending_appends(*log_powerpm, log_start_addr, log_size);
        }

        match self.log.tentatively_append(log_powerpm, overall_metadata.log_area_addr,
                                          overall_metadata.log_area_size, bytes, Ghost(crash_pred), Tracked(perm)) {
            Ok(_) => {}
            Err(e) => {
                self.log.abort_pending_appends(log_powerpm, overall_metadata.log_area_addr,
                                               overall_metadata.log_area_size);
                self.current_transaction_crc = CrcDigest::new();
                self.state = Ghost(AbstractOpLogState {
                    physical_op_list: Seq::empty(),
                    op_list_committed: false
                });
                assert(log_powerpm@.flush_predicted());
                assert(Self::recover(log_powerpm@.durable_state, version_metadata, overall_metadata) ==
                       Some(AbstractOpLogState::initialize()));
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
            self.log.lemma_all_crash_states_recover_to_drop_pending_appends(*log_powerpm, log_start_addr, log_size);
//            assert(log_powerpm@.can_crash_as(log_powerpm@.durable_state));
        }
        
        match self.log.commit(log_powerpm, overall_metadata.log_area_addr, overall_metadata.log_area_size, Ghost(crash_pred), Tracked(perm)) {
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
        log_powerpm: &mut PoWERPersistentMemoryRegion<Perm, PM>,
        version_metadata: VersionMetadata,
        overall_metadata: OverallMetadata,
        Ghost(crash_pred): Ghost<spec_fn(Seq<u8>) -> bool>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), KvError<K>>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires 
            old(self).inv(old(log_powerpm)@, version_metadata, overall_metadata),
            old(log_powerpm).inv(),
            old(self)@.op_list_committed,
            overall_metadata.log_area_addr + spec_log_area_pos() <= old(log_powerpm)@.len(),
            old(self).base_log_view().pending.len() == 0,
            old(log_powerpm)@.flush_predicted(),
            Self::recover(old(log_powerpm)@.durable_state, version_metadata, overall_metadata) == Some(old(self)@),
            Self::recover(old(log_powerpm)@.read_state, version_metadata, overall_metadata) == Some(old(self)@),
            crash_pred(old(log_powerpm)@.durable_state),
            forall |s2: Seq<u8>| {
                let flushed_state = old(log_powerpm)@.read_state;
                &&& flushed_state.len() == s2.len() 
                &&& states_differ_only_in_log_region(s2, flushed_state, overall_metadata.log_area_addr as nat,
                                                   overall_metadata.log_area_size as nat)
                &&& Self::recover(s2, version_metadata, overall_metadata) == Some(old(self)@)
            } ==> #[trigger] crash_pred(s2),
            forall |s2: Seq<u8>| {
                let crash_state = old(log_powerpm)@.durable_state;
                &&& crash_state.len() == s2.len() 
                &&& states_differ_only_in_log_region(s2, crash_state,
                                                   overall_metadata.log_area_addr as nat,
                                                   overall_metadata.log_area_size as nat)
                &&& Self::recover(s2, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize())
            } ==> #[trigger] crash_pred(s2),
            forall |s1: Seq<u8>, s2: Seq<u8>| {
                &&& s1.len() == s2.len() 
                &&& #[trigger] crash_pred(s1)
                &&& states_differ_only_in_log_region(s1, s2, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
                &&& Self::recover(s1, version_metadata, overall_metadata) == Some(old(self)@)
                &&& Self::recover(s2, version_metadata, overall_metadata) == Some(old(self)@)
            } ==> #[trigger] crash_pred(s2),
            forall |s| crash_pred(s) ==> perm.permits(s),
        ensures 
            self.inv(log_powerpm@, version_metadata, overall_metadata),
            log_powerpm@.len() == old(log_powerpm)@.len(),
            log_powerpm.constants() == old(log_powerpm).constants(),
            log_powerpm.inv(),
            log_powerpm@.flush_predicted(),
            Self::recover(log_powerpm@.durable_state, version_metadata, overall_metadata) ==
                Some(AbstractOpLogState::initialize()),
            Self::recover(log_powerpm@.read_state, version_metadata, overall_metadata) ==
                Some(AbstractOpLogState::initialize()),
            views_differ_only_in_log_region(old(log_powerpm)@, log_powerpm@, 
                                            overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat),
            perm.permits(log_powerpm@.durable_state),
            match result {
                Ok(()) => {
                    Ok::<_, ()>(self@) == old(self)@.clear_log()
                }
                Err(_) => false 
            }
    {
        let log_start_addr = overall_metadata.log_area_addr;
        let log_size = overall_metadata.log_area_size;

        // To clear the log, we'll look up its head and tail, then advance the head to the tail
        let (head, tail, capacity) = match self.log.get_head_tail_and_capacity(log_powerpm, log_start_addr, log_size) {
            Ok((head, tail, capacity)) => (head, tail, capacity),
            Err(e) => {
                assert(false);
                return Err(KvError::LogErr{log_err: e});
            }
        };

        proof {
            self.log.lemma_all_crash_states_recover_to_drop_pending_appends(*log_powerpm, log_start_addr as nat,
                                                                            log_size as nat);
        }

        // Now, advance the head to the tail. Verus is able to prove the required crash preconditions on its own
        match self.log.advance_head(log_powerpm, tail, log_start_addr, log_size, Ghost(crash_pred), Tracked(perm)) {
            Ok(()) => {}
            Err(e) => {
                assert(false);
                return Err(KvError::LogErr{log_err: e});
            }
        }

        // update the op log's state -- it is now empty and is not committed
        self.state = Ghost(self.state@.clear_log().unwrap());

        // Prove that the only possible crash state is an empty op log
        assert(self.log@.drop_pending_appends().log.len() == 0);
        assert(UntrustedLogImpl::can_only_crash_as_state(log_powerpm@, log_start_addr as nat, log_size as nat,
                                                         self.log@.drop_pending_appends()));

        assert(Self::recover(log_powerpm@.durable_state, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize()));

        assert(self.log@.pending.len() == 0);
        assert(self.current_transaction_crc.bytes_in_digest().flatten() =~= self.log@.pending);

        Ok(())
    }
}
}
