use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::log::logimpl_v::*;
use crate::log::logimpl_t::*;
use crate::log::logspec_t::*;
use crate::log::layout_v::*;
use crate::kv::durable::logentry_v::*;
use crate::kv::durable::logentry_t::*;
use crate::kv::durable::oplog::oplogspec_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t;
use crate::kv::kvimpl_t::*;
use vstd::bytes::*;

verus! {
    pub struct UntrustedOpLog<K, L, E>
        where 
            L: PmCopy
    {
        log: UntrustedLogImpl,
        state: Ghost<AbstractOpLogState<L>>,
        _phantom: Option<(K, E)>
    }

    impl<K, L, E> UntrustedOpLog<K, L, E>
        where 
            L: PmCopy + Copy,
            K: std::fmt::Debug,
            E: std::fmt::Debug
    {
        pub closed spec fn recover(mem: Seq<u8>, kvstore_id: u128) -> Option<AbstractOpLogState<L>>
        {
            // use log's recover method to recover the log state, then parse it into operations
            match UntrustedLogImpl::recover(mem, kvstore_id) {
                Some(log) => {
                    if log.log.len() == 0 {
                        Some(AbstractOpLogState {
                            op_list: Seq::empty(),
                            op_list_committed: true
                        })
                    } else {
                        let log_entries_bytes = log.log.subrange(0, log.log.len() - u64::spec_size_of() as int);
                        let crc = spec_u64_from_le_bytes(log.log.subrange(log.log.len() - u64::spec_size_of() as int, log.log.len() as int));
                        // if the crc written at the end of the transaction does not match the crc of the rest of the log contents, the log is invalid
                        if crc != spec_crc_u64(log_entries_bytes) {
                            None
                        } else {
                            Self::parse_log_ops(log_entries_bytes)
                        }
                    }
                    
                }
                None => None
            }
        }


        closed spec fn parse_log_ops(log_contents: Seq<u8>) -> Option<AbstractOpLogState<L>>
        {
            // parse the log contents into operations
            let op_log_seq = Seq::empty();

            match Self::parse_log_ops_helper(log_contents, op_log_seq) {
                Some(op_log_seq) => {
                    Some(AbstractOpLogState {
                        op_list: op_log_seq,
                        op_list_committed: true, 
                    })
                }
                None => None
            }
        }

        closed spec fn parse_log_ops_helper(
            log_contents: Seq<u8>, 
            op_log_seq: Seq<OpLogEntryType<L>>, 
        ) -> Option<Seq<OpLogEntryType<L>>>
            decreases log_contents.len()
        {
            if log_contents.len() <= 0 {
                Some(op_log_seq)
            } else {
                // 1. read the entry type to determine how to serialize it
                let entry_type = u64::spec_from_bytes(log_contents.subrange(0, 8));
                // 2. serialize the entry based on the read type and loop over the remaining log contents
                match entry_type {
                    COMMIT_ITEM_TABLE_ENTRY => {
                        if log_contents.len() < LENGTH_OF_COMMIT_ITEM_ENTRY {
                            None
                        } else {
                            let read_entry = CommitItemEntry::spec_from_bytes(log_contents.subrange(0 as int, LENGTH_OF_COMMIT_ITEM_ENTRY as int));
                            let entry = OpLogEntryType::ItemTableEntryCommit {
                                item_index: read_entry.item_index,
                                metadata_index: read_entry.metadata_index,
                                metadata_crc: read_entry.metadata_crc
                            };
                            let log_contents = log_contents.subrange(LENGTH_OF_COMMIT_ITEM_ENTRY as int, log_contents.len() as int);
                            Self::parse_log_ops_helper(log_contents, op_log_seq.push(entry))
                        }
                    }
                    INVALIDATE_ITEM_TABLE_ENTRY => {
                        if log_contents.len() < LENGTH_OF_INVALIDATE_ITEM_ENTRY {
                            None 
                        } else {
                            let read_entry = InvalidateItemEntry::spec_from_bytes(log_contents.subrange(0 as int, LENGTH_OF_INVALIDATE_ITEM_ENTRY as int));
                            let entry = OpLogEntryType::ItemTableEntryInvalidate {
                                item_index: read_entry.item_index
                            };
                            let log_contents = log_contents.subrange(LENGTH_OF_INVALIDATE_ITEM_ENTRY as int, log_contents.len() as int);
                            Self::parse_log_ops_helper(log_contents, op_log_seq.push(entry))
                        }
                    }
                    APPEND_LIST_NODE_ENTRY => {
                        if log_contents.len() < LENGTH_OF_APPEND_NODE_ENTRY {
                            None 
                        } else {
                            let read_entry = AppendListNodeEntry::spec_from_bytes(log_contents.subrange(0 as int, LENGTH_OF_APPEND_NODE_ENTRY as int));
                            let entry = OpLogEntryType::AppendListNode {
                                metadata_index: read_entry.metadata_index,
                                old_tail: read_entry.old_tail,
                                new_tail: read_entry.new_tail,
                                metadata_crc: read_entry.metadata_crc
                            };
                            let log_contents = log_contents.subrange(LENGTH_OF_APPEND_NODE_ENTRY as int, log_contents.len() as int);
                            Self::parse_log_ops_helper(log_contents, op_log_seq.push(entry))
                        }
                    }
                    INSERT_LIST_ELEMENT_ENTRY => {
                        if log_contents.len() < LENGTH_OF_INSERT_LIST_ELEMENT_ENTRY {
                            None 
                        } else {
                            let read_entry = InsertListElementEntry::spec_from_bytes(log_contents.subrange(0 as int, LENGTH_OF_INSERT_LIST_ELEMENT_ENTRY as int));
                            let list_element = L::spec_from_bytes(log_contents.subrange(LENGTH_OF_INSERT_LIST_ELEMENT_ENTRY as int, LENGTH_OF_INSERT_LIST_ELEMENT_ENTRY + L::spec_size_of()));
                            let entry = OpLogEntryType::InsertListElement {
                                node_offset: read_entry.node_offset,
                                index_in_node: read_entry.index_in_node,
                                list_element
                            };
                            let log_contents = log_contents.subrange(LENGTH_OF_INSERT_LIST_ELEMENT_ENTRY as int, log_contents.len() as int);
                            Self::parse_log_ops_helper(log_contents, op_log_seq.push(entry))
                        }
                    }
                    UPDATE_LIST_LEN_ENTRY => {
                        if log_contents.len() < LENGTH_OF_UPDATE_LIST_LEN_ENTRY {
                            None 
                        } else {
                            let read_entry = UpdateListLenEntry::spec_from_bytes(log_contents.subrange(0 as int, LENGTH_OF_UPDATE_LIST_LEN_ENTRY as int));
                            let entry = OpLogEntryType::UpdateListLen {
                                metadata_index: read_entry.metadata_index,
                                new_length: read_entry.new_length,
                                metadata_crc: read_entry.metadata_crc
                            };
                            let log_contents = log_contents.subrange(LENGTH_OF_UPDATE_LIST_LEN_ENTRY as int, log_contents.len() as int);
                            Self::parse_log_ops_helper(log_contents, op_log_seq.push(entry))
                        }
                    }
                    TRIM_LIST_METADATA_UPDATE_ENTRY => {
                        if log_contents.len() < LENGTH_OF_TRIM_LIST_ENTRY {
                            None 
                        } else {
                            let read_entry = TrimListEntry::spec_from_bytes(log_contents.subrange(0 as int, LENGTH_OF_TRIM_LIST_ENTRY as int));
                            let entry = OpLogEntryType::TrimList {
                                metadata_index: read_entry.metadata_index,
                                new_head_node: read_entry.new_head_node,
                                new_list_len: read_entry.new_list_len,
                                new_list_start_index: read_entry.new_list_start_index,
                                metadata_crc: read_entry.metadata_crc
                            };
                            let log_contents = log_contents.subrange(LENGTH_OF_TRIM_LIST_ENTRY as int, log_contents.len() as int);
                            Self::parse_log_ops_helper(log_contents, op_log_seq.push(entry))
                        }
                    }
                    COMMIT_METADATA_ENTRY => {
                        if log_contents.len() < LENGTH_OF_COMMIT_METADATA_ENTRY {
                            None 
                        } else {
                            let read_entry = CommitMetadataEntry::spec_from_bytes(log_contents.subrange(0 as int, LENGTH_OF_COMMIT_METADATA_ENTRY as int));
                            let entry = OpLogEntryType::CommitMetadataEntry {
                                metadata_index: read_entry.metadata_index,
                                item_index: read_entry.item_index
                            };
                            let log_contents = log_contents.subrange(LENGTH_OF_COMMIT_METADATA_ENTRY as int, log_contents.len() as int);
                            Self::parse_log_ops_helper(log_contents, op_log_seq.push(entry))
                        }
                    }
                    INVALIDATE_METADATA_ENTRY => {
                        if log_contents.len() < LENGTH_OF_INVALIDATE_METADATA_ENTRY {
                            None 
                        } else {
                            let read_entry = InvalidateMetadataEntry::spec_from_bytes(log_contents.subrange(0 as int, LENGTH_OF_INVALIDATE_METADATA_ENTRY as int));
                            let entry = OpLogEntryType::InvalidateMetadataEntry {
                                metadata_index: read_entry.metadata_index
                            };
                            let log_contents = log_contents.subrange(LENGTH_OF_INVALIDATE_METADATA_ENTRY as int, log_contents.len() as int);
                            Self::parse_log_ops_helper(log_contents, op_log_seq.push(entry))
                        }
                    }
                   _ => None
                }
            }
        }
        
        pub exec fn start<PM>(
            log_wrpm: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PM>,
            log_id: u128,
            Tracked(perm): Tracked<&TrustedPermission>,
        ) -> (result: Result<Self, KvError<K, E>>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                // TODO
                // log_wrpm should have already been set up with the regular log setup method
            ensures 
                // TODO
        {
            assume(false);
            let log = match UntrustedLogImpl::start(log_wrpm, log_id, Tracked(&perm), Ghost(UntrustedLogImpl::recover(log_wrpm@.flush().committed(), log_id).unwrap())) {
                Ok(log) => log,
                Err(e) => return Err(KvError::LogErr { log_err: e }),
            };
            let state = Ghost(Self::recover(log_wrpm@.flush().committed(), log_id).unwrap());
            Ok(Self {
                log,
                state,
                _phantom: None
            })
        }

        pub exec fn read_op_log<PM>(
            log: &UntrustedLogImpl,
            wrpm_region: &WriteRestrictedPersistentMemoryRegion<TrustedPermission, PM>,
            log_id: u128,
        ) -> (result: Result<Vec<OpLogEntryType<L>>, KvError<K, E>>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                log.inv(wrpm_region, log_id),
            ensures 
                // TODO
        {
            assume(false);

            // first, read the entire log and its CRC and check for corruption. we have to do this before we can parse the bytes
            // Obtain the head and tail of the log so that we know the region to read to get the log contents and the CRC
            let (head, tail, capacity) = match log.get_head_tail_and_capacity(wrpm_region, Ghost(log_id)) {
                Ok((head, tail, capacity)) => (head, tail, capacity),
                Err(e) => return Err(KvError::LogErr { log_err: e }),
            };

            // TODO: check for errors on the cast (or take a u128 as len?)
            // Read the log contents and the CRC. Note that the log only supports unaligned reads.
            let len = (tail - head) as u64;
            let (log_bytes, log_addrs) = match log.read(wrpm_region, head, len, Ghost(log_id)) {
                Ok(bytes) => bytes,
                Err(e) => return Err(KvError::LogErr { log_err: e }),
            };
            let (crc_bytes, crc_addrs) = match log.read(wrpm_region, tail - traits_t::size_of::<u64>() as u128, traits_t::size_of::<u64>() as u64, Ghost(log_id)) {
                Ok(bytes) => bytes,
                Err(e) => return Err(KvError::LogErr { log_err: e }),
            };

            if !check_crc(log_bytes.as_slice(), crc_bytes.as_slice(), Ghost(wrpm_region@.committed()),
                Ghost(wrpm_region.constants().impervious_to_corruption), log_addrs, crc_addrs) 
            {
                return Err(KvError::CRCMismatch);
            }

            // We now know that the bytes are not corrupted, but we still need to determine what 
            // log entry types make up the vector of bytes.



            Err(KvError::NotImplemented)
            
        }

        pub exec fn parse_op_log<PM>(
            log: &UntrustedLogImpl,
            log_contents: Vec<u8>,
            log_id: u128,
            Ghost(mem): Ghost<Seq<u8>>,
            Ghost(log_contents_addrs): Ghost<Seq<int>>,
            Ghost(impervious_to_corruption): Ghost<bool>,
        ) -> (result: Result<Vec<OpLogEntryType<L>>, KvError<K, E>>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                ({
                    // We must have already proven that the bytes are not corrupted. This is already known
                    // if we are impervious to corruption, but we must have done the CRC check in case we aren't.
                    let true_bytes = Seq::new(log_contents_addrs.len(), |i: int| mem[log_contents_addrs[i]]);
                    true_bytes == log_contents@
                })
            ensures
                // TODO
                // result vector is equal to the seq returned by spec parse log fn
        {
            assume(false);

            let mut op_list = Vec::new();

            let mut current_offset = 0;
            // we iterate over the length of the log minus the size of the CRC, since we have already 
            // read the CRC and don't want to accidentally interpret it as a log type field
            let log_contents_len = log_contents.len() - traits_t::size_of::<u64>();
            while current_offset < log_contents_len
                invariant
                    // TODO 
            {   
                assume(false);

                // Obtain the entry type by reading the first 8 bytes at the current offset and extracting them to a u64.
                // We've already proven that the bytes are not corrupted, although we will still have to prove that this 
                // field was previously initialized with a u64.
                let mut entry_type_value = MaybeCorruptedBytes::<u64>::new();
                // obtain a slice of just the section of the log contents we want.
                let entry_type_slice = slice_range(&log_contents, current_offset, traits_t::size_of::<u64>());
                
                let ghost entry_type_addrs = log_contents_addrs.subrange(current_offset as int, current_offset + u64::spec_size_of());
                let ghost true_entry_type_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem[entry_type_addrs[i]]);
                let ghost true_entry_type = choose |val: u64| true_entry_type_bytes == val.spec_to_bytes();

                entry_type_value.copy_from_slice(entry_type_slice, Ghost(true_entry_type), 
                    Ghost(entry_type_addrs), Ghost(impervious_to_corruption));
                let entry_type = entry_type_value.extract_init_val(Ghost(true_entry_type), 
                    Ghost(true_entry_type_bytes), Ghost(impervious_to_corruption));
    
                // Using the entry type we read, read the log entry and extract its value, then translate it 
                // into a OpLogEntryType enum variant.
                // TODO: This may need to take the existence of the log entry as a precondition?
                let (log_entry, bytes_read) = Self::parse_op_log_entry(current_offset, *entry_type, &log_contents, log_id, 
                    Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption))?;
                op_list.push(log_entry);
                current_offset += bytes_read;
            }

            Ok(op_list)
        }

        // returns the log entry as well as the number of bytes the function read
        // so that the caller can increment its offset
        pub exec fn parse_op_log_entry(
            current_offset: usize,
            entry_type: u64,
            log_contents: &Vec<u8>,
            log_id: u128,
            Ghost(mem): Ghost<Seq<u8>>,
            Ghost(log_contents_addrs): Ghost<Seq<int>>,
            Ghost(impervious_to_corruption): Ghost<bool>,
        ) -> (result: Result<(OpLogEntryType<L>, usize), KvError<K, E>>)
            requires 
                ({
                    // We must have already proven that the bytes are not corrupted. This is already known
                    // if we are impervious to corruption, but we must have done the CRC check in case we aren't.
                    let true_bytes = Seq::new(log_contents_addrs.len(), |i: int| mem[log_contents_addrs[i]]);
                    true_bytes == log_contents@
                })
            ensures 
                // TODO
        {
            assume(false);
            let mut bytes_read = 0;

            // Read the struct at the current offset, casting it to the type indicated by the 
            // entry type argument.
            let log_entry: OpLogEntryType<L> = match entry_type {
                COMMIT_ITEM_TABLE_ENTRY => {
                    let log_entry = Self::read_and_cast_type_from_vec::<CommitItemEntry>(current_offset, &log_contents,
                        log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
                    bytes_read += traits_t::size_of::<CommitItemEntry>();
                    OpLogEntryType::from_commit_entry(log_entry)
                }
                INVALIDATE_ITEM_TABLE_ENTRY => {
                    let log_entry = Self::read_and_cast_type_from_vec::<InvalidateItemEntry>(current_offset, &log_contents,
                        log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
                    bytes_read += traits_t::size_of::<InvalidateItemEntry>();
                    OpLogEntryType::from_invalidate_entry(log_entry)
                }
                APPEND_LIST_NODE_ENTRY => {
                    let log_entry = Self::read_and_cast_type_from_vec::<AppendListNodeEntry>(current_offset, &log_contents,
                        log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
                    bytes_read += traits_t::size_of::<AppendListNodeEntry>();
                    OpLogEntryType::from_append_list_node_entry(log_entry)
                }
                INSERT_LIST_ELEMENT_ENTRY => {
                    let log_entry = Self::read_and_cast_type_from_vec::<InsertListElementEntry>(current_offset, &log_contents,
                        log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
                    let list_element = Self::read_and_cast_type_from_vec::<L>(current_offset + traits_t::size_of::<InsertListElementEntry>(), 
                        &log_contents, log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
                    bytes_read += traits_t::size_of::<InsertListElementEntry>() + traits_t::size_of::<L>();
                    OpLogEntryType::from_insert_list_element_entry(log_entry, list_element)
                }
                UPDATE_LIST_LEN_ENTRY => {
                    let log_entry = Self::read_and_cast_type_from_vec::<UpdateListLenEntry>(current_offset, &log_contents,
                        log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
                    bytes_read += traits_t::size_of::<UpdateListLenEntry>();
                    OpLogEntryType::from_update_list_len_entry(log_entry)
                }
                TRIM_LIST_METADATA_UPDATE_ENTRY => {
                    let log_entry = Self::read_and_cast_type_from_vec::<TrimListEntry>(current_offset, &log_contents,
                        log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
                    bytes_read += traits_t::size_of::<TrimListEntry>();
                    OpLogEntryType::from_trim_list_entry(log_entry)
                }
                COMMIT_METADATA_ENTRY => {
                    let log_entry = Self::read_and_cast_type_from_vec::<CommitMetadataEntry>(current_offset, &log_contents,
                        log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
                    bytes_read += traits_t::size_of::<CommitMetadataEntry>();
                    OpLogEntryType::from_commit_metadata_entry(log_entry)
                }
                INVALIDATE_METADATA_ENTRY => {
                    let log_entry = Self::read_and_cast_type_from_vec::<InvalidateMetadataEntry>(current_offset, &log_contents,
                        log_id, Ghost(mem), Ghost(log_contents_addrs), Ghost(impervious_to_corruption));
                    bytes_read += traits_t::size_of::<InvalidateMetadataEntry>();
                    OpLogEntryType::from_invalidate_metadata_entry(log_entry)
                }
                _ => {
                    assert(false);
                    return Err(KvError::InvalidLogEntryType);
                }
            };

            Ok((log_entry, bytes_read))
        }

        // Generic function to read bytes from a vector that has been proven to be uncorrupted and 
        // interpret them as the given type. Caller must prove that there is a valid instance 
        // of T at this location. This is useful when reading a large number of bytes from the log and 
        // then splitting it into slices and interpreting each slice as a different type.
        exec fn read_and_cast_type_from_vec<T: PmCopy>(
            current_offset: usize,
            log_contents: &Vec<u8>,
            log_id: u128,
            Ghost(mem): Ghost<Seq<u8>>,
            Ghost(log_contents_addrs): Ghost<Seq<int>>,
            Ghost(impervious_to_corruption): Ghost<bool>,
        ) -> (out: Box<T>)
            requires 
                // TODO: caller needs to prove that we can actually "read" an instance of T
                // from this location. This will require a pretty strong precondition
                // The precondition should ensure that the read is valid and cannot fail
            ensures 
                // TODO 
        {
            assume(false);
            let mut bytes = MaybeCorruptedBytes::<T>::new();
            let bytes_slice = slice_range(&log_contents, current_offset, traits_t::size_of::<T>());
            let ghost addrs = log_contents_addrs.subrange(current_offset as int, current_offset + T::spec_size_of());
            let ghost true_bytes = Seq::new(T::spec_size_of() as nat, |i: int| mem[addrs[i]]);
            let ghost true_entry = choose |val: T| true_bytes == val.spec_to_bytes();

            bytes.copy_from_slice(bytes_slice, Ghost(true_entry), Ghost(addrs), Ghost(impervious_to_corruption));
            let init_val = bytes.extract_init_val(Ghost(true_entry), Ghost(true_bytes), Ghost(impervious_to_corruption));
            init_val
        }

        // This function tentatively appends a log entry and its CRC to the op log.
        pub exec fn tentatively_append_log_entry<PM, S>(
            &mut self,
            log_wrpm: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PM>,
            log_id: u128,
            log_entry: &S,
            Tracked(perm): Tracked<&TrustedPermission>,
        ) -> (result: Result<(), LogErr>)
            where 
                PM: PersistentMemoryRegion,
                S: PmCopy,
            requires 
                // TODO
            ensures 
                // TODO 
                // match statement on the log entry types
        {
            // Because the log may need to wrap around, it cannot easily serialize the log entry
            // for us the way serialize_and_write does. We need to convert it to a byte-level 
            // representation first, then append that to the log.
            assume(false);
            let log_entry_bytes = log_entry.as_byte_slice();
            let log_entry_crc = calculate_crc(log_entry);
            let log_entry_crc_bytes = log_entry_crc.as_byte_slice();
            self.log.tentatively_append(log_wrpm, log_entry_bytes, Ghost(log_id), Tracked(perm))?;
            self.log.tentatively_append(log_wrpm, log_entry_crc_bytes, Ghost(log_id), Tracked(perm))?;
            Ok(())
        }

        pub exec fn commit_log<PM>(
            &mut self, 
            log_wrpm: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PM>,
            log_id: u128,
            Tracked(perm): Tracked<&TrustedPermission>,
        ) -> (result: Result<(), LogErr>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                // TODO
            ensures 
                // TODO
        {
            assume(false);
            // TODO: need to write the crc of the current log
            self.log.commit(log_wrpm, Ghost(log_id), Tracked(perm))?;
            Ok(())
        }

        pub exec fn clear_log<PM>(
            &mut self, 
            log_wrpm: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PM>,
            log_id: u128,
            Tracked(perm): Tracked<&TrustedPermission>,
        ) -> (result: Result<(), LogErr>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                // TODO
            ensures 
                // TODO
        {
            assume(false);
            // look up the tail of the log, then advance the head to that point
            let (head, tail, capacity) = self.log.get_head_tail_and_capacity(log_wrpm, Ghost(log_id))?;
            self.log.advance_head(log_wrpm, tail, Ghost(log_id), Tracked(perm))
        }


    }
}