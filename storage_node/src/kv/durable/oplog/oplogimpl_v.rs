use std::fmt::Write;

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::kv::durable::metadata::layout_v::ListEntryMetadata;
use crate::log2::logimpl_v::*;
use crate::log2::logspec_t::*;
use crate::log2::layout_v::*;
use crate::kv::durable::oplog::logentry_v::*;
use crate::kv::durable::oplog::oplogspec_t::*;
use crate::kv::kvimpl_t::*;
use crate::kv::layout_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t;
use crate::pmem::traits_t::PmSafe;
use crate::pmem::crc_t::*;
use vstd::bytes::*;

use super::inv_v::*;

verus! {
    pub struct UntrustedOpLog<K, L>
        where 
            L: PmCopy
    {
        log: UntrustedLogImpl,
        state: Ghost<AbstractOpLogState<L>>,
        current_transaction_crc: CrcDigest,
        _phantom: Option<K>
    }

    impl<K, L> UntrustedOpLog<K, L>
        where 
            L: PmCopy + Copy,
            K: std::fmt::Debug,
    {

        // TODO: should this take overall metadata and say that recovery is successful?
        pub closed spec fn inv<Perm, PM>(self, pm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>, log_start_addr: nat, log_size: nat) -> bool
            where 
                Perm: CheckPermission<Seq<u8>>,
                PM: PersistentMemoryRegion,
        {
            &&& self.log.inv(pm_region, log_start_addr, log_size)
            &&& ({
                    // either the log is empty or it has valid matching logical and physical op logs
                    ||| self.log@.log.len() == 0
                    ||| logical_and_physical_logs_correspond(self@.logical_op_list, self@.physical_op_list)
                })
            &&& forall |i: int| 0 <= i < self@.physical_op_list.len() ==> {
                    let op = #[trigger] self@.physical_op_list[i];
                    // all addrs are within the bounds of the device
                    &&& 0 <= op.absolute_addr < op.absolute_addr + op.len < pm_region@.len() <= u64::MAX
                    // no logged ops change bytes belonging to the log itself
                    &&& (op.absolute_addr + op.len < log_start_addr || log_start_addr + log_size <= op.absolute_addr)
            } 
        }

        pub closed spec fn view(self) -> AbstractOpLogState<L>
        {
            self.state@
        }

        pub open spec fn recover(mem: Seq<u8>, overall_metadata: OverallMetadata) -> Option<AbstractOpLogState<L>>
        {
            // use log's recover method to recover the log state, then parse it into operations
            match UntrustedLogImpl::recover(mem, overall_metadata.log_area_addr as nat,
                                            overall_metadata.log_area_size as nat) {
                Some(log) => {
                    if log.log.len() == 0 {
                        Some(AbstractOpLogState {
                            logical_op_list: Seq::empty(),
                            physical_op_list: Seq::empty(),
                            op_list_committed: true
                        })
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
                            // parsing the log only obtains physical entries, but we (should) know that there is a corresponding logical op log (even
                            // if we don't know exactly what it is)
                            if let Some(physical_log_entries) =  Self::parse_log_ops(
                                log_contents, 
                                overall_metadata.log_area_addr as nat, 
                                overall_metadata.log_area_size as nat,
                                overall_metadata.region_size as nat
                            ) {
                                if exists |logical_log: Seq<LogicalOpLogEntry<_>>| logical_and_physical_logs_correspond::<L>(logical_log, physical_log_entries) {
                                    let logical_log_entries = choose |logical_log| logical_and_physical_logs_correspond(logical_log, physical_log_entries);
                                    Some(AbstractOpLogState {
                                        logical_op_list: logical_log_entries,
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
                }
                None => None
            }
        }

        pub open spec fn parse_log_ops(log_contents: Seq<u8>, log_start_addr: nat, log_size: nat, region_size: nat) -> Option<Seq<AbstractPhysicalOpLogEntry>>
        {
            let ops = Seq::empty();
            Self::parse_log_ops_helper(0, log_contents, ops, log_start_addr, log_size, region_size)
        }

        // want to be able to talk about prefixes...all log entries up to 
        // some offset.
        // what exactly does the other one do. what exactly does offset mean.
        // it gives you entries AFTER offset and appends them to the existingt
        // sequence. but what would work better here is to get entries BEFORE
        // some offset.... but you can't really do that because you don't know 
        // how big they are. but you can look at lengths before doing anything else,
        // maybe that will help?
        pub open spec fn parse_log_ops_helper_number2(
            offset: nat,
            log_contents: Seq<u8>,
            // op_log_seq: Seq<AbstractPhysicalOpLogEntry>,
            log_start_addr: nat, 
            log_size: nat,
            region_size: nat,
        ) -> Option<Seq<AbstractPhysicalOpLogEntry>>
            decreases log_contents.len() - offset 
        {
            if log_contents.len() - offset == 0 {
                Some(Seq::empty())
            } else {
                if log_contents.len() < u64::spec_size_of() * 2 {
                    None
                } else {
                    let absolute_addr = u64::spec_from_bytes(extract_bytes(log_contents, offset, u64::spec_size_of())) as nat;
                    let len = u64::spec_from_bytes(extract_bytes(log_contents, offset + u64::spec_size_of(), u64::spec_size_of())) as nat;
                    let entry_size = u64::spec_size_of() * 2 + len;
                    if {
                        ||| len == 0
                        ||| offset + entry_size > log_contents.len()
                    } {
                        None
                    } else {
                        let seq = Self::parse_log_ops_helper_number2(offset + entry_size, log_contents, log_start_addr, log_size, region_size);
                        if let Some(seq) = seq {
                            let bytes = extract_bytes(log_contents, offset + u64::spec_size_of() * 2, len as nat);
                            let op = AbstractPhysicalOpLogEntry {
                                offset,
                                absolute_addr, 
                                len, 
                                bytes
                            };
                            Some(seq![op] + seq)
                        } else {
                            None
                        }
                    }
                }
            }
        }

        // structure differently? parse everything but the last one, then parse that one?
        // maybe would work better to get a prefix?
        pub open spec fn parse_log_ops_helper(
            offset: nat,
            log_contents: Seq<u8>,
            op_log_seq: Seq<AbstractPhysicalOpLogEntry>,
            log_start_addr: nat, 
            log_size: nat,
            region_size: nat,
        ) -> Option<Seq<AbstractPhysicalOpLogEntry>>
            decreases log_contents.len() - offset 
        {
            if log_contents.len() - offset == 0 {
                Some(op_log_seq)
            } else {
                // If the log is not empty but doesn't have enough space for a log entry,
                // recovery cannot succeed
                if log_contents.len() < u64::spec_size_of() * 2 {
                    None
                } else {
                    // 1. Read the absolute addr and log entry size
                    let absolute_addr = u64::spec_from_bytes(extract_bytes(log_contents, offset, u64::spec_size_of()));
                    let len = u64::spec_from_bytes(extract_bytes(log_contents, offset + u64::spec_size_of(), u64::spec_size_of()));
                    if {
                        ||| absolute_addr + len > region_size
                        ||| log_start_addr <= absolute_addr < log_start_addr + log_size 
                        ||| log_start_addr <= absolute_addr + len < log_start_addr + log_size
                        ||| len == 0
                        ||| log_contents.len() - u64::spec_size_of() * 2 < len
                    } {
                        // if the entry contains invalid values, recovery fails
                        None 
                    } else {
                        // 2. Read the log entry contents
                        let log_entry_contents = extract_bytes(log_contents, offset + u64::spec_size_of() * 2, len as nat);
                        
                        // 3. Construct the physical log entry and add it to the list
                        let op_log_seq = op_log_seq.push(
                            AbstractPhysicalOpLogEntry { offset, absolute_addr: absolute_addr as nat, len: len as nat, bytes: log_entry_contents }
                        );

                        // 4. Go to the next log entry
                        let total_entry_len = u64::spec_size_of() * 2 + len;
                        if total_entry_len <= 0 {
                            None
                        } else {
                            let new_offset = offset + total_entry_len;
                            if log_contents.len() - new_offset < 0 {
                                None
                            } else {
                                Self::parse_log_ops_helper(
                                    new_offset as nat,
                                    log_contents,
                                    op_log_seq,
                                    log_start_addr,
                                    log_size,
                                    region_size
                                )
                            }
                        }
                        
                    }
                }
            }
        }

        pub open spec fn parse_log_op(
            offset: nat,
            log_contents: Seq<u8>,
            log_start_addr: nat, 
            log_size: nat,
            region_size: nat,
        ) -> Option<AbstractPhysicalOpLogEntry>
        {
            // 1. Read the absolute addr and log entry size
            let absolute_addr = u64::spec_from_bytes(extract_bytes(log_contents, 0, u64::spec_size_of()));
            let len = u64::spec_from_bytes(extract_bytes(log_contents, u64::spec_size_of(), u64::spec_size_of()));
            if {
                ||| absolute_addr + len > region_size
                ||| log_start_addr <= absolute_addr < log_start_addr + log_size 
                ||| log_start_addr <= absolute_addr + len < log_start_addr + log_size
                ||| len == 0
                ||| log_contents.len() - u64::spec_size_of() * 2 < len
            } {
                // if the entry contains invalid values, recovery fails
                None 
            } else {
                // 2. Read the log entry contents
                let log_entry_contents = extract_bytes(log_contents, u64::spec_size_of() * 2, len as nat);

                // 3. Construct the physical log entry
                let new_op = AbstractPhysicalOpLogEntry { offset, absolute_addr: absolute_addr as nat, len: len as nat, bytes: log_entry_contents };
            
                Some(new_op)
            }
        }

        pub open spec fn parse_log_ops_helper2(
            offset: nat,
            log_contents: Seq<u8>, 
            op_log_seq: Seq<AbstractPhysicalOpLogEntry>,
            log_start_addr: nat, 
            log_size: nat,
            region_size: nat,
        ) -> Option<Seq<AbstractPhysicalOpLogEntry>>
            decreases log_contents.len() 
        {
            if log_contents.len() == 0 {
                Some(op_log_seq)
            } else {
                // If the log is not empty but doesn't have enough space for a log entry,
                // recovery cannot succeed
                if log_contents.len() < u64::spec_size_of() * 2 {
                    None
                } else {
                    let op = Self::parse_log_op(offset, log_contents, log_start_addr, log_size, region_size);
                    if let Some(op) = op {
                        let op_log_seq = op_log_seq.push(op);
                        let total_entry_len = u64::spec_size_of() * 2 + op.len;
                        let offset = offset + total_entry_len;
                        Self::parse_log_ops_helper(
                            offset as nat,
                            extract_bytes(log_contents, total_entry_len as nat, (log_contents.len() - total_entry_len) as nat),
                            op_log_seq,
                            log_start_addr,
                            log_size,
                            region_size
                        )
                    } else {
                        None
                    }
                    // // 1. Read the absolute addr and log entry size
                    // let absolute_addr = u64::spec_from_bytes(extract_bytes(log_contents, 0, u64::spec_size_of()));
                    // let len = u64::spec_from_bytes(extract_bytes(log_contents, u64::spec_size_of(), u64::spec_size_of()));
                    // if {
                    //     ||| absolute_addr + len > region_size
                    //     ||| log_start_addr <= absolute_addr < log_start_addr + log_size 
                    //     ||| log_start_addr <= absolute_addr + len < log_start_addr + log_size
                    //     ||| len == 0
                    // } {
                    //     // if the entry contains invalid values, recovery fails
                    //     None 
                    // } else if log_contents.len() - u64::spec_size_of() * 2 < len {
                    //     // If the log doesn't have enough space for the rest of the entry, recovery fails
                    //     None
                    // } else {
                    //     // 2. Read the log entry contents
                    //     let log_entry_contents = extract_bytes(log_contents, u64::spec_size_of() * 2, len as nat);
                        
                    //     // 3. Construct the physical log entry and add it to the list
                    //     let new_op = 
                    //         AbstractPhysicalOpLogEntry { offset, absolute_addr: absolute_addr as nat, len: len as nat, bytes: log_entry_contents };
                    //         // AbstractPhysicalOpLogEntry { absolute_addr: absolute_addr as nat, len: len as nat, bytes: log_entry_contents };

                    //     let op_log_seq = op_log_seq.push(new_op);

                    //     // 4. Go to the next log entry
                    //     let total_entry_len = u64::spec_size_of() * 2 + len;
                    //     let offset = offset + total_entry_len;
                    //     Self::parse_log_ops_helper(
                    //         offset as nat,
                    //         extract_bytes(log_contents, total_entry_len as nat, (log_contents.len() - total_entry_len) as nat),
                    //         op_log_seq,
                    //         log_start_addr,
                    //         log_size,
                    //         region_size
                    //     )
                    // }
                }
            }
        }


        // both offset and index into op_log_seq matter here....

        proof fn lemma_offsets_match_helper(
            offset: nat,
            log_contents: Seq<u8>,
            op_log_seq: Seq<AbstractPhysicalOpLogEntry>,
            log_start_addr: nat, 
            log_size: nat,
            region_size: nat,
        )
            requires
                Some(op_log_seq) == Self::parse_log_ops_helper_number2(offset, log_contents, log_start_addr, log_size, region_size)
            ensures 
                ({
                    forall |i: int| 0 <= i < op_log_seq.len() ==> {
                        // let op = #[trigger] op_log_seq[i];
                        // op.len > 0
                        let op = #[trigger] op_log_seq[i];
                        let absolute_addr = u64::spec_from_bytes(extract_bytes(log_contents, op.offset, u64::spec_size_of())) as nat;
                        let len = u64::spec_from_bytes(extract_bytes(log_contents, (op.offset + u64::spec_size_of()) as nat, u64::spec_size_of())) as nat;
                        let bytes = extract_bytes(log_contents, (op.offset + u64::spec_size_of() * 2) as nat, len as nat);
                        &&& op.absolute_addr == absolute_addr 
                        &&& op.len == len 
                        &&& op.bytes == bytes
                    }
                })
            decreases log_contents.len() - offset 
        {
            if log_contents.len() - offset == 0 {
                // trivial
            } else {
                if log_contents.len() < u64::spec_size_of() * 2 {
                    assert(false);
                } else {
                    let absolute_addr = u64::spec_from_bytes(extract_bytes(log_contents, offset, u64::spec_size_of())) as nat;
                    let len = u64::spec_from_bytes(extract_bytes(log_contents, offset + u64::spec_size_of(), u64::spec_size_of())) as nat;
                    let entry_size = u64::spec_size_of() * 2 + len;
                    if {
                        ||| len == 0
                        ||| offset + entry_size > log_contents.len()
                    } {
                        assert(false);
                    } else {
                        let seq = Self::parse_log_ops_helper_number2(offset + entry_size, log_contents, log_start_addr, log_size, region_size);
                        if let Some(seq) = seq {
                            assert(seq == op_log_seq.drop_first());
                            Self::lemma_offsets_match_helper(
                                offset + entry_size,
                                log_contents,
                                op_log_seq.drop_first(),
                                log_start_addr,
                                log_size,
                                region_size
                            );
                        } else {
                            assert(false);
                        }
                    }
                }
            }
        }

        proof fn lemma_offsets_match(
            log_bytes: Seq<u8>, 
            op_log_seq: Seq<AbstractPhysicalOpLogEntry>,
            log_start_addr: nat, 
            log_size: nat,
            region_size: nat,
        ) 
            requires
                Some(op_log_seq) == Self::parse_log_ops_helper_number2(0, log_bytes, log_start_addr, log_size, region_size)
            ensures
                ({
                    forall |i: int| 0 <= i < op_log_seq.len() ==> {
                        let op = #[trigger] op_log_seq[i];
                        let absolute_addr = u64::spec_from_bytes(extract_bytes(log_bytes, op.offset, u64::spec_size_of())) as nat;
                        let len = u64::spec_from_bytes(extract_bytes(log_bytes, (op.offset + u64::spec_size_of()) as nat, u64::spec_size_of())) as nat;
                        let bytes = extract_bytes(log_bytes, (op.offset + u64::spec_size_of() * 2) as nat, len as nat);
                        &&& op.absolute_addr == absolute_addr 
                        &&& op.len == len 
                        &&& op.bytes == bytes
                    }
                })
        {
            Self::lemma_offsets_match_helper(0, log_bytes, op_log_seq, log_start_addr, log_size, region_size);
        }

        fn parse_phys_op_log<Perm, PM>(
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
                    &&& abstract_log.len() > 0
                }),
                u64::spec_size_of() * 2 <= log_bytes.len() <= u64::MAX
            ensures 
                match result {
                    Ok(phys_log) => {
                        let base_log_state = UntrustedLogImpl::recover(pm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
                        let phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
                        // TODO: no corruption
                        let abstract_op_log = Self::parse_log_ops(phys_op_log_buffer, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat);
                        let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                        &&& abstract_op_log matches Some(abstract_op_log)
                        &&& abstract_op_log == phys_log_view
                    }
                    Err(_) => true // TODO
                }
        {
            
            let ghost base_log_state = UntrustedLogImpl::recover(pm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
            let ghost phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
            let ghost abstract_op_log = Self::parse_log_ops(phys_op_log_buffer, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat).unwrap();

            // // so basically we don't know anything about it...
            // assert(abstract_op_log.len() > 0);
            // assert(0 <= abstract_op_log[0].offset < phys_op_log_buffer.len());
            // assert(abstract_op_log[0].offset == 0);

            let mut offset = 0;
            let mut index = 0;
            let mut ops = Vec::<PhysicalOpLogEntry>::new();
            while offset < log_bytes.len() 
                invariant 
                    forall |i: int| 0 <= i < ops.len() ==> #[trigger] ops[i]@ == #[trigger] abstract_op_log[i],
                    u64::spec_size_of() * 2 <= log_bytes.len() <= u64::MAX,
                    ops.len() <= abstract_op_log.len(),
                    index <= abstract_op_log.len(),
            {
                assume(false);
                broadcast use pmcopy_axioms;
                let ghost op = abstract_op_log[index as int];

                if offset > log_bytes.len() - traits_t::size_of::<u64>() * 2
                {
                    return Err(KvError::InternalError);
                }
                let absolute_addr_bytes = slice_range(&log_bytes, offset, traits_t::size_of::<u64>());
                let len_bytes = slice_range(&log_bytes, offset + traits_t::size_of::<u64>(), traits_t::size_of::<u64>());
                let absolute_addr = u64_from_le_bytes(absolute_addr_bytes);
                assert(absolute_addr == op.absolute_addr);
                let len = u64_from_le_bytes(len_bytes);
                if len == 0 {
                    return Err(KvError::InternalError);
                }

                if {
                    ||| traits_t::size_of::<u64>() * 2 >= (u64::MAX - len) as usize
                    ||| log_bytes.len() < traits_t::size_of::<u64>() * 2 + len as usize
                    ||| offset > log_bytes.len() - (traits_t::size_of::<u64>() * 2 + len as usize)
                } {
                    return Err(KvError::InternalError);
                }

                let bytes = slice_range_to_vec(&log_bytes, offset + traits_t::size_of::<u64>() * 2, len as usize);

                let op = PhysicalOpLogEntry {
                    offset: offset as u64,
                    absolute_addr,
                    len,
                    bytes
                };
                ops.push(op);

                offset += traits_t::size_of::<u64>() + len as usize;
                index += 1;
            }

            Err(KvError::NotImplemented)
        }
            

        // Note that the op log is given the entire PM device but only deals with the log region
        pub exec fn start<Perm, PM>(
            pm_region: &WriteRestrictedPersistentMemoryRegion<Perm, PM>,
            overall_metadata: OverallMetadata
        ) -> (result: Result<(Self, Vec<u8>), KvError<K>>)
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
            ensures
                match result {
                    Ok((op_log_impl, phys_log)) => {
                        true
                        // let base_log_state = UntrustedLogImpl::recover(pm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
                        // &&& op_log_impl.inv(*pm_region, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
                        // &&& ({
                        //     ||| phys_op_log_buffer@.len() == 0
                        //     ||| {
                        //             &&& phys_op_log_buffer@ == extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat)
                        //             &&& Self::parse_log_ops(
                        //                     phys_op_log_buffer@, 
                        //                     overall_metadata.log_area_addr as nat, 
                        //                     overall_metadata.log_area_size as nat,
                        //                     overall_metadata.region_size as nat
                        //                 ) matches Some(physical_log)
                        //             &&& physical_log == op_log_impl@.physical_op_list
                        //         }
                        // })
                    }
                    Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                    Err(KvError::LogErr { log_err }) => true, // TODO: better handling for this and PmemErr
                    Err(KvError::PmemErr { pmem_err }) => true,
                    Err(KvError::InternalError) => true,
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
                Err(e) => return Err(KvError::LogErr { log_err: e })
            };
            let ghost op_log_state = Self::recover(pm_region@.committed(), overall_metadata);
            
            // proof {
            //     if op_log_state.unwrap().physical_op_list.len() > 0 {
            //         assert(op_log_state.unwrap().physical_op_list[0].offset == 0);
            //     }
            // }

            // Read the entire log and its CRC and check for corruption. we have to do this before we can parse the bytes.
            // Obtain the head and tail of the log so that we know the region to read to get the log contents and the CRC
            let (head, tail, capacity) = match log.get_head_tail_and_capacity(pm_region, log_start_addr, log_size) {
                Ok((head, tail, capacity)) => (head, tail, capacity),
                Err(e) => return Err(KvError::LogErr { log_err: e }),
            };

            if tail == head {
                // if the log is empty, we don't have to do anything else -- just return the started op log and
                // an empty buffer to indicate that there are no log entries to replay
                return Ok((
                    Self {
                        log,
                        state: Ghost(op_log_state.unwrap()),
                        current_transaction_crc: CrcDigest::new(),
                        _phantom: None
                    },
                    Vec::new(),
                ));
            } else if tail < traits_t::size_of::<u64>() as u128 || tail - head < traits_t::size_of::<u64>() as u128 {
                // TODO: more detailed error (although this should not ever happen) (then why does it need a more detailed error?)
                return Err(KvError::InternalError); 
            }

            let len = (tail - head) as u64 - traits_t::size_of::<u64>() as u64;

            proof { log.lemma_reveal_log_inv(*pm_region, log_start_addr as nat, log_size as nat); }
            
            let (log_bytes, log_addrs) = match log.read(pm_region, log_start_addr, log_size, head, len) {
                Ok(bytes) => bytes,
                Err(e) => return Err(KvError::LogErr { log_err: e }),
            };
            let (crc_bytes, crc_addrs) = match log.read(pm_region, log_start_addr, log_size, tail - traits_t::size_of::<u64>() as u128, traits_t::size_of::<u64>() as u64) {
                Ok(bytes) => bytes,
                Err(e) => return Err(KvError::LogErr { log_err: e }),
            };

            if !check_crc(log_bytes.as_slice(), crc_bytes.as_slice(), Ghost(pm_region@.committed()),
                Ghost(pm_region.constants().impervious_to_corruption), log_addrs, crc_addrs) 
            {
                return Err(KvError::CRCMismatch);
            }

            let op_log_impl = Self {
                log,
                state: Ghost(op_log_state.unwrap()),
                current_transaction_crc: CrcDigest::new(),
                _phantom: None
            };

            proof {
                assert(pm_region@.len() == overall_metadata.region_size);
                if op_log_impl@.physical_op_list.len() == 0 {
                    
                } else {
                    assume(false);
                    let log_contents = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
                    // assert(log_contents == extract_bytes(log_contents, 0, (log_contents.len() - 0) as nat));
                    // Self::lemma_phys_ops_properties(0, log_contents, log_contents, op_log_state.unwrap().physical_op_list, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat);
                    // assert forall |i: int| 0 <= i < op_log_impl@.physical_op_list.len() implies {
                    //     let op = #[trigger] op_log_impl@.physical_op_list[i];
                    //     // all addrs are within the bounds of the device
                    //     &&& 0 <= op.absolute_addr 
                    //     &&& op.absolute_addr < op.absolute_addr + op.len // fail
                    //     // &&& op.absolute_addr + op.len < pm_region@.len() // fail

                    //     // &&& 0 <= op.absolute_addr < op.absolute_addr + op.len < pm_region@.len() <= u64::MAX

                    //     // no logged ops change bytes belonging to the log itself
                    //     // &&& (op.absolute_addr + op.len < log_start_addr || log_start_addr + log_size <= op.absolute_addr)
                    // } by {
                    //     let op = #[trigger] op_log_impl@.physical_op_list[i];
                    //     // assert(op.len > 0);
                    //     assume(false);
                    // }
                }
                
                // assert(op_log_impl.inv(*pm_region, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat));
            }

            assume(false);
            

            Ok((
                op_log_impl,
                log_bytes
            ))
        }

        // // TODO: should we do checks on log entries/CRC here? Or do that as part of reading the log?
        // // If we know we didn't crash, we don't have to replay the log, so we should probably keep the
        // // replay step separate
        // pub exec fn start<PM>(
        //     pm_region: &PM,
        //     overall_metadata: OverallMetadata,
        // ) -> (result: Result<(Self, Vec<OpLogEntryType<L>>), KvError<K>>)
        //     where 
        //         PM: PersistentMemoryRegion,
        //     requires 
        //         pm_region.inv(),
        //         pm_region@.no_outstanding_writes(),
        //         overall_metadata.log_area_addr + overall_metadata.log_area_size <= pm_region@.len() <= u64::MAX,
        //         overall_metadata.log_area_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
        //         Self::recover(pm_region@.committed(), overall_metadata) is Some, 
        //     ensures 
        //         match result {
        //             Ok((op_log_impl, op_log)) => {
        //                 &&& op_log_impl.inv(pm_region, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
        //                 &&& Some(op_log_impl@) == Self::recover(pm_region@.committed(), overall_metadata)
        //             }
        //             Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
        //             Err(KvError::LogErr { log_err }) => true, // TODO: better handling for this and PmemErr
        //             Err(KvError::PmemErr { pmem_err }) => true,
        //             Err(_) => false
        //         }
        // {
        //     let ghost base_log_state = UntrustedLogImpl::recover(pm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
        //     let base_log = match UntrustedLogImpl::start(pm_region, overall_metadata.log_area_addr, overall_metadata.log_area_size, Ghost(base_log_state)) {
        //         Ok(log) => log,
        //         Err(LogErr::CRCMismatch) => return Err(KvError::CRCMismatch),
        //         Err(e) => return Err(KvError::LogErr { log_err: e })
        //     };

        //     let ghost op_log_state = Self::recover(pm_region@.committed(), overall_metadata);
            
        //     Ok((
        //             Self {
        //             log: base_log,
        //             state: Ghost(op_log_state.unwrap()),
        //             current_transaction_crc: CrcDigest::new(),
        //             _phantom: None
        //         },
        //         Vec::new(),
        //     ))
        // }

        // pub exec fn read_op_log<PM>(
        //     &self,
        //     pm_region: &PM,
        //     log_start_addr: u64,
        //     log_size: u64, 
        // ) -> (result: Result<Vec<OpLogEntryType<L>>, KvError<K>>)
        //     where 
        //         PM: PersistentMemoryRegion,
        //     requires
        //         self.inv(pm_region, log_start_addr as nat, log_size as nat),
        //     ensures
        //         true 
        // {
        //     let log = &self.log;

        //     // first, read the entire log and its CRC and check for corruption. we have to do this before we can parse the bytes
        //     // Obtain the head and tail of the log so that we know the region to read to get the log contents and the CRC
        //     let (head, tail, capacity) = match log.get_head_tail_and_capacity(pm_region, log_start_addr, log_size) {
        //         Ok((head, tail, capacity)) => (head, tail, capacity),
        //         Err(e) => return Err(KvError::LogErr { log_err: e }),
        //     };

        //     if tail == head {
        //         return Ok(Vec::new());
        //     } else if tail < traits_t::size_of::<u64>() as u128 {
        //         // TODO: more detailed error (although this should not ever happen)
        //         return Err(KvError::InternalError); 
        //     }

        //     let len = (tail - head) as u64;

        //     proof { log.lemma_reveal_log_inv(pm_region, log_start_addr as nat, log_size as nat); }
            
        //     let (log_bytes, log_addrs) = match log.read(pm_region, log_start_addr, log_size, head, len) {
        //         Ok(bytes) => bytes,
        //         Err(e) => return Err(KvError::LogErr { log_err: e }),
        //     };
        //     let (crc_bytes, crc_addrs) = match log.read(pm_region, log_start_addr, log_size, tail - traits_t::size_of::<u64>() as u128, traits_t::size_of::<u64>() as u64) {
        //         Ok(bytes) => bytes,
        //         Err(e) => return Err(KvError::LogErr { log_err: e }),
        //     };

        //     if !check_crc(log_bytes.as_slice(), crc_bytes.as_slice(), Ghost(pm_region@.committed()),
        //         Ghost(pm_region.constants().impervious_to_corruption), log_addrs, crc_addrs) 
        //     {
        //         return Err(KvError::CRCMismatch);
        //     }
        //     // precondition needs to say that we expect the CRC to be correct? once it does we should not 
        //     // need any proof here hopefully
        //     proof {
        //         let true_crc_bytes = Seq::new(crc_addrs@.len(), |i: int| pm_region@.committed()[crc_addrs@[i]]);
        //         let true_bytes = Seq::new(log_addrs@.len(), |i: int| pm_region@.committed()[log_addrs@[i]]);
                
        //         // TODO NEXT
        //         // this needs to be part of the invariant? or precondition
        //         assume(false);
        //         assert(true_crc_bytes == spec_crc_bytes(true_bytes));
        //     }

        //     // We now know that the bytes are not corrupted, but we still need to determine what 
        //     // log entry types make up the vector of bytes.

        //     self.parse_op_log(log_bytes, Ghost(pm_region@.committed()), log_addrs, Ghost(pm_region.constants().impervious_to_corruption))
        // }

        // pub exec fn parse_op_log(
        //     &self,
        //     log_contents: Vec<u8>,
        //     Ghost(mem): Ghost<Seq<u8>>,
        //     Ghost(log_contents_addrs): Ghost<Seq<int>>,
        //     Ghost(impervious_to_corruption): Ghost<bool>,
        // ) -> (result: Result<Vec<OpLogEntryType<L>>, KvError<K>>)
        //     requires 
        //         ({
        //             // We must have already proven that the bytes are not corrupted. This is already known
        //             // if we are impervious to corruption, but we must have done the CRC check in case we aren't.
        //             let true_bytes = Seq::new(log_contents_addrs.len(), |i: int| mem[log_contents_addrs[i]]);
        //             true_bytes == log_contents@
        //         })
        //     ensures
        //         // TODO
        //         // result vector is equal to the seq returned by spec parse log fn
        // {
        //     assume(false);
        //     Err(KvError::NotImplemented)
        // }
        //     assume(false);

        //     let mut op_list = Vec::new();

        //     let mut current_offset = 0;
        //     // we iterate over the length of the log minus the size of the CRC, since we have already 
        //     // read the CRC and don't want to accidentally interpret it as a log type field
        //     let log_contents_len = log_contents.len() - traits_t::size_of::<u64>();
        //     while current_offset < log_contents_len
        //         invariant
        //             // TODO 
        //     {   
        //         assume(false);

        //         // Obtain the entry type by reading the first 8 bytes at the current offset and extracting them to a u64.
        //         // We've already proven that the bytes are not corrupted, although we will still have to prove that this 
        //         // field was previously initialized with a u64.
        //         let mut entry_type_value = MaybeCorruptedBytes::<u64>::new();
        //         // obtain a slice of just the section of the log contents we want.
        //         let entry_type_slice = slice_range(&log_contents, current_offset, traits_t::size_of::<u64>());
                
        //         let ghost entry_type_addrs = log_contents_addrs.subrange(current_offset as int, current_offset + u64::spec_size_of());
        //         let ghost true_entry_type_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem[entry_type_addrs[i]]);
        //         let ghost true_entry_type = u64::spec_from_bytes(true_entry_type_bytes);

        //         entry_type_value.copy_from_slice(entry_type_slice, Ghost(true_entry_type), 
        //             Ghost(entry_type_addrs), Ghost(impervious_to_corruption));
        //         let entry_type = entry_type_value.extract_init_val(Ghost(true_entry_type), 
        //             Ghost(true_entry_type_bytes), Ghost(impervious_to_corruption));
    
        //         // Using the entry type we read, read the log entry and extract its value, then translate it 
        //         // into a OpLogEntryType enum variant.
        //         // TODO: This may need to take the existence of the log entry as a precondition?
        //         let (log_entry, bytes_read) = Self::parse_op_log_entry(current_offset, *entry_type, &log_contents, log_id, 
        //             Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption))?;
        //         op_list.push(log_entry);
        //         current_offset += bytes_read;
        //     }

        //     Ok(op_list)
        // }

        // // returns the log entry as well as the number of bytes the function read
        // // so that the caller can increment its offset
        // pub exec fn parse_op_log_entry(
        //     current_offset: usize,
        //     entry_type: u64,
        //     log_contents: &Vec<u8>,
        //     log_id: u128,
        //     Ghost(mem): Ghost<Seq<u8>>,
        //     Ghost(log_contents_addrs): Ghost<Seq<int>>,
        //     Ghost(impervious_to_corruption): Ghost<bool>,
        // ) -> (result: Result<(OpLogEntryType<L>, usize), KvError<K>>)
        //     requires 
        //         ({
        //             // We must have already proven that the bytes are not corrupted. This is already known
        //             // if we are impervious to corruption, but we must have done the CRC check in case we aren't.
        //             let true_bytes = Seq::new(log_contents_addrs.len(), |i: int| mem[log_contents_addrs[i]]);
        //             true_bytes == log_contents@
        //         })
        //     ensures 
        //         // TODO
        // {
        //     assume(false);
        //     let mut bytes_read = 0;

        //     // Read the struct at the current offset, casting it to the type indicated by the 
        //     // entry type argument.
        //     let log_entry: OpLogEntryType<L> = match entry_type {
        //         COMMIT_ITEM_TABLE_ENTRY => {
        //             let log_entry = Self::read_and_cast_type_from_vec::<CommitItemEntry>(current_offset, &log_contents,
        //                 log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
        //             bytes_read += traits_t::size_of::<CommitItemEntry>();
        //             OpLogEntryType::from_commit_entry(log_entry)
        //         }
        //         INVALIDATE_ITEM_TABLE_ENTRY => {
        //             let log_entry = Self::read_and_cast_type_from_vec::<InvalidateItemEntry>(current_offset, &log_contents,
        //                 log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
        //             bytes_read += traits_t::size_of::<InvalidateItemEntry>();
        //             OpLogEntryType::from_invalidate_entry(log_entry)
        //         }
        //         APPEND_LIST_NODE_ENTRY => {
        //             let log_entry = Self::read_and_cast_type_from_vec::<AppendListNodeEntry>(current_offset, &log_contents,
        //                 log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
        //             bytes_read += traits_t::size_of::<AppendListNodeEntry>();
        //             OpLogEntryType::from_append_list_node_entry(log_entry)
        //         }
        //         INSERT_LIST_ELEMENT_ENTRY => {
        //             let log_entry = Self::read_and_cast_type_from_vec::<InsertListElementEntry>(current_offset, &log_contents,
        //                 log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
        //             let list_element = Self::read_and_cast_type_from_vec::<L>(current_offset + traits_t::size_of::<InsertListElementEntry>(), 
        //                 &log_contents, log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
        //             bytes_read += traits_t::size_of::<InsertListElementEntry>() + traits_t::size_of::<L>();
        //             OpLogEntryType::from_insert_list_element_entry(log_entry, list_element)
        //         }
        //         COMMIT_METADATA_ENTRY => {
        //             let log_entry = Self::read_and_cast_type_from_vec::<MetadataLogEntry>(current_offset, &log_contents,
        //                 log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
        //             bytes_read += traits_t::size_of::<MetadataLogEntry>();
        //             OpLogEntryType::from_commit_metadata_entry(log_entry)
        //         }
        //         INVALIDATE_METADATA_ENTRY => {
        //             let log_entry = Self::read_and_cast_type_from_vec::<MetadataLogEntry>(current_offset, &log_contents,
        //                 log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
        //             bytes_read += traits_t::size_of::<MetadataLogEntry>();
        //             OpLogEntryType::from_invalidate_metadata_entry(log_entry)
        //         }
        //         UPDATE_METADATA_ENTRY => {
        //             let log_entry = Self::read_and_cast_type_from_vec::<UpdateMetadataEntry>(current_offset, &log_contents,
        //                 log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
        //             let new_metadata = Self::read_and_cast_type_from_vec::<ListEntryMetadata>(current_offset + traits_t::size_of::<UpdateMetadataEntry>(), 
        //                 &log_contents, log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
        //             bytes_read += traits_t::size_of::<UpdateMetadataEntry>() + traits_t::size_of::<ListEntryMetadata>();
        //             OpLogEntryType::from_update_metadata_entry(log_entry, new_metadata)
        //         }
        //         _ => {
        //             assert(false);
        //             return Err(KvError::InvalidLogEntryType);
        //         }
        //     };

        //     Ok((log_entry, bytes_read))
        // }

        // // Generic function to read bytes from a vector that has been proven to be uncorrupted and 
        // // interpret them as the given type. Caller must prove that there is a valid instance 
        // // of T at this location. This is useful when reading a large number of bytes from the log and 
        // // then splitting it into slices and interpreting each slice as a different type.
        // exec fn read_and_cast_type_from_vec<T: PmCopy>(
        //     current_offset: usize,
        //     log_contents: &Vec<u8>,
        //     log_id: u128,
        //     Ghost(mem): Ghost<Seq<u8>>,
        //     Ghost(log_contents_addrs): Ghost<Seq<int>>,
        //     Ghost(impervious_to_corruption): Ghost<bool>,
        // ) -> (out: Box<T>)
        //     requires 
        //         // TODO: caller needs to prove that we can actually "read" an instance of T
        //         // from this location. This will require a pretty strong precondition
        //         // The precondition should ensure that the read is valid and cannot fail
        //     ensures 
        //         // TODO 
        // {
        //     assume(false);
        //     let mut bytes = MaybeCorruptedBytes::<T>::new();
        //     let bytes_slice = slice_range(&log_contents, current_offset, traits_t::size_of::<T>());
        //     let ghost addrs = log_contents_addrs.subrange(current_offset as int, current_offset + T::spec_size_of());
        //     let ghost true_bytes = Seq::new(T::spec_size_of() as nat, |i: int| mem[addrs[i]]);
        //     let ghost true_entry = T::spec_from_bytes(true_bytes);

        //     bytes.copy_from_slice(bytes_slice, Ghost(true_entry), Ghost(addrs), Ghost(impervious_to_corruption));
        //     let init_val = bytes.extract_init_val(Ghost(true_entry), Ghost(true_bytes), Ghost(impervious_to_corruption));
        //     init_val
        // }

        // // This function tentatively appends a log entry and its CRC to the op log.
        // pub exec fn tentatively_append_log_entry<PM>(
        //     &mut self,
        //     log_wrpm: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PM>,
        //     log_id: u128,
        //     log_entry: &OpLogEntryType<L>,
        //     Tracked(perm): Tracked<&TrustedPermission>,
        // ) -> (result: Result<(), KvError<K>>)
        //     where 
        //         PM: PersistentMemoryRegion,
        //     requires 
        //         // TODO
        //     ensures 
        //         // TODO 
        //         // match statement on the log entry types
        // {
        //     assume(false);
        //     match log_entry {
        //         OpLogEntryType::ItemTableEntryCommit { item_index } => {
        //             let log_entry = log_entry.to_commit_entry().unwrap();
        //             self.append_to_oplog(log_wrpm, log_id, &log_entry, Tracked(perm))
        //         }
        //         OpLogEntryType::ItemTableEntryInvalidate { item_index } => {
        //             let log_entry = log_entry.to_invalidate_entry().unwrap();
        //             self.append_to_oplog(log_wrpm, log_id, &log_entry, Tracked(perm))
        //         }
        //         OpLogEntryType::AppendListNode { metadata_index, old_tail, new_tail } => {
        //             let log_entry = log_entry.to_append_list_node_entry().unwrap();
        //             self.append_to_oplog(log_wrpm, log_id, &log_entry, Tracked(perm))
        //         }
        //         OpLogEntryType::InsertListElement { node_offset, index_in_node, list_element } => {
        //             let log_entry = log_entry.to_insert_list_element_entry().unwrap();
        //             self.append_to_oplog(log_wrpm, log_id, &log_entry, Tracked(perm))?;
        //             self.append_to_oplog(log_wrpm, log_id, list_element, Tracked(perm))
        //         }
        //         OpLogEntryType::CommitMetadataEntry { metadata_index } => {
        //             let log_entry = log_entry.to_commit_metadata_entry().unwrap();
        //             self.append_to_oplog(log_wrpm, log_id, &log_entry, Tracked(perm))
        //         }
        //         OpLogEntryType::InvalidateMetadataEntry { metadata_index } => {
        //             let log_entry = log_entry.to_invalidate_metadata_entry().unwrap();
        //             self.append_to_oplog(log_wrpm, log_id, &log_entry, Tracked(perm))
        //         }
        //         OpLogEntryType::UpdateMetadataEntry { metadata_index, new_metadata, new_crc } => {
        //             let log_entry = log_entry.to_update_metadata_entry().unwrap();
        //             self.append_to_oplog(log_wrpm, log_id, &log_entry, Tracked(perm))?;
        //             self.append_to_oplog(log_wrpm, log_id, new_metadata, Tracked(perm))
        //         }
        //         OpLogEntryType::NodeDeallocInMemory { old_head, new_head } => return Err(KvError::InvalidLogEntryType)
        //     }
        // }

        // exec fn append_to_oplog<PM, S>(
        //     &mut self,
        //     log_wrpm: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PM>,
        //     log_id: u128,
        //     to_write: &S,
        //     Tracked(perm): Tracked<&TrustedPermission>,
        // ) -> (result: Result<(), KvError<K>>)
        //     where 
        //         PM: PersistentMemoryRegion,
        //         S: PmCopy + PmSafe
        // {
        //     assume(false);
        //     // Because the log may need to wrap around, it cannot easily serialize the object to write
        //     // for us the way serialize_and_write does. We need to convert it to a byte-level 
        //     // representation first, then append that to the log.
        //     let bytes = to_write.as_byte_slice();
        //     match self.log.tentatively_append(log_wrpm, bytes, Ghost(log_id), Tracked(perm)) {
        //         Ok(_) => {}
        //         Err(e) => return Err(KvError::LogErr { log_err: e })
        //     }
        //     self.current_transaction_crc.write(to_write);
        //     Ok(())
        // }


        // pub exec fn commit_log<PM>(
        //     &mut self, 
        //     log_wrpm: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PM>,
        //     log_id: u128,
        //     Tracked(perm): Tracked<&TrustedPermission>,
        // ) -> (result: Result<(), KvError<K>>)
        //     where 
        //         PM: PersistentMemoryRegion,
        //     requires 
        //         // TODO
        //     ensures 
        //         // TODO
        // {
        //     assume(false);
        //     let transaction_crc = self.current_transaction_crc.sum64();
        //     let bytes = transaction_crc.as_byte_slice();
        //     match self.log.tentatively_append(log_wrpm, bytes, Ghost(log_id), Tracked(perm)) {
        //         Ok(_) => {}
        //         Err(e) => return Err(KvError::LogErr { log_err: e })
        //     }
        //     match self.log.commit(log_wrpm, Ghost(log_id), Tracked(perm)) {
        //         Ok(_) => {}
        //         Err(e) => return Err(KvError::LogErr { log_err: e })
        //     }
        //     Ok(())
        // }

        // pub exec fn clear_log<PM>(
        //     &mut self, 
        //     log_wrpm: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PM>,
        //     log_id: u128,
        //     Tracked(perm): Tracked<&TrustedPermission>,
        // ) -> (result: Result<(), KvError<K>>)
        //     where 
        //         PM: PersistentMemoryRegion,
        //     requires 
        //         // TODO
        //     ensures 
        //         // TODO
        // {
        //     assume(false);
        //     // look up the tail of the log, then advance the head to that point
        //     let (head, tail, capacity) = match self.log.get_head_tail_and_capacity(log_wrpm, Ghost(log_id)) {
        //         Ok((head, tail, capacity)) => (head, tail, capacity),
        //         Err(e) => return Err(KvError::LogErr { log_err: e })
        //     };
        //     match self.log.advance_head(log_wrpm, tail, Ghost(log_id), Tracked(perm)) {
        //         Ok(()) => Ok(()),
        //         Err(e) => Err(KvError::LogErr { log_err: e })
        //     }
        // }


    }
}
