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
            let (head, tail, capacity) = match log.get_head_tail_and_capacity(wrpm_region, Ghost(log_id)) {
                Ok((head, tail, capacity)) => (head, tail, capacity),
                Err(e) => return Err(KvError::LogErr { log_err: e }),
            };

            // TODO: check for errors on the cast (or take a u128 as len?)
            let len = (tail - head) as u64;
            let log_bytes = match log.read(wrpm_region, head, len, Ghost(log_id)) {
                Ok(bytes) => bytes,
                Err(e) => return Err(KvError::LogErr { log_err: e }),
            };
            let crc_bytes = match log.read(wrpm_region, tail - traits_t::size_of::<u64>() as u128, traits_t::size_of::<u64>() as u64, Ghost(log_id)) {
                Ok(bytes) => bytes,
                Err(e) => return Err(KvError::LogErr { log_err: e }),
            };

            Err(KvError::NotImplemented)
            
        }
        

        // // reads the op log, checks the CRC of each entry, and returns a vector of entries for replay
        // // it would be faster to read them on demand, but this would be harder to prove correct.
        // // we pass in a log because this will be called as part of `start`, so the UntrustedOpLog doesn't exist yet.
        // // log `read` does not work well with serialization because an entry might be split due to wrapping and give us
        // // back a vector of bytes, but we can deserialize it in place to avoid any additional copying
        // pub exec fn read_op_log<PM>(
        //     log: &UntrustedLogImpl,
        //     wrpm_region: &WriteRestrictedPersistentMemoryRegion<TrustedPermission, PM>,
        //     log_id: u128,
        // ) -> (result: Result<Vec<OpLogEntryType<L>>, KvError<K, E>>)
        //     where 
        //         PM: PersistentMemoryRegion,
        //     requires 
        //         log.inv(wrpm_region, log_id)
        //     ensures 
        //         // TODO 
        // {
        //     assume(false);
        //     let mut op_vec = Vec::new();
        //     let (head, tail, capacity) = match log.get_head_tail_and_capacity(wrpm_region, Ghost(log_id)) {
        //         Ok((head, tail, capacity)) => (head, tail, capacity),
        //         Err(e) => return Err(KvError::LogErr { log_err: e }),
            
        //     };
        //     let mut current_read_pos = head;
        //     while current_read_pos < tail 
        //         invariant
        //             log.inv(wrpm_region, log_id),
        //             current_read_pos <= tail,
        //             current_read_pos + LENGTH_OF_COMMIT_ITEM_ENTRY + traits_t::size_of::<u64>() <= u128::MAX
        //     {
        //         assume(false);
        //         let entry_type_bytes = match log.read(wrpm_region, current_read_pos, 8, Ghost(log_id)) {
        //             Ok(bytes) => bytes,
        //             Err(e) => return Err(KvError::LogErr { log_err: e }),
        //         };
        //         let entry_type = u64_from_le_bytes(entry_type_bytes.as_slice());
        //         match entry_type {
        //             COMMIT_ITEM_TABLE_ENTRY => {
        //                 let entry_read_pos = current_read_pos;
        //                 let log_entry_bytes = match log.read(wrpm_region, current_read_pos, LENGTH_OF_COMMIT_ITEM_ENTRY, Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 let log_entry = CommitItemEntry::deserialize_bytes(log_entry_bytes.as_slice());
        //                 current_read_pos += LENGTH_OF_COMMIT_ITEM_ENTRY as u128;
        //                 let crc_bytes = match log.read(wrpm_region, current_read_pos, traits_t::size_of::<u64>(), Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 let crc = u64_from_le_bytes(crc_bytes.as_slice());
        //                 // TODO: this isn't going to work -- the log entry may have been read from non-consecutive bytes
        //                 // but the log doesn't expose that information. The check_crc_deserialized function assumes 
        //                 // that deserialized objects are read sequentially from consecutive bytes but that is not
        //                 // necessarily true here.
        //                 // The read positions are also logical log positions, not physical PM addresses; I'm not sure if 
        //                 // that is a problem or not...
        //                 if !check_crc_deserialized2(
        //                     log_entry, 
        //                     &crc, 
        //                     Ghost(wrpm_region@.flush().committed()), 
        //                     Ghost(wrpm_region.constants().impervious_to_corruption), 
        //                     Ghost(entry_read_pos as u64), // TODO: shouldn't cast u128 as u64
        //                     Ghost(LENGTH_OF_COMMIT_ITEM_ENTRY), 
        //                     Ghost(current_read_pos as u64) // TODO: shouldn't cast u128 as u64
        //                 ) {
        //                     return Err(KvError::CRCMismatch);
        //                 }
        //                 current_read_pos += traits_t::size_of::<u64>() as u128;

        //                 let entry = OpLogEntryType::ItemTableEntryCommit {
        //                     item_index: log_entry.item_index,
        //                     metadata_index: log_entry.metadata_index,
        //                     metadata_crc: log_entry.metadata_crc
        //                 };
        //                 op_vec.push(entry);
        //             }
        //             INVALIDATE_ITEM_TABLE_ENTRY => {
        //                 let entry_read_pos = current_read_pos;
        //                 let log_entry_bytes = match log.read(wrpm_region, current_read_pos, LENGTH_OF_INVALIDATE_ITEM_ENTRY, Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 let log_entry = InvalidateItemEntry::deserialize_bytes(log_entry_bytes.as_slice());
        //                 current_read_pos += LENGTH_OF_INVALIDATE_ITEM_ENTRY as u128;
        //                 let crc_bytes = match log.read(wrpm_region, current_read_pos, traits_t::size_of::<u64>(), Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 let crc = u64_from_le_bytes(crc_bytes.as_slice());
        //                 // TODO: CRC check
        //                 current_read_pos += traits_t::size_of::<u64>() as u128;

        //                 let entry = OpLogEntryType::ItemTableEntryInvalidate {
        //                     item_index: log_entry.item_index
        //                 };
        //                 op_vec.push(entry);
        //             }
        //             APPEND_LIST_NODE_ENTRY => {
        //                 let entry_read_pos = current_read_pos;
        //                 let log_entry_bytes = match log.read(wrpm_region, current_read_pos, LENGTH_OF_APPEND_NODE_ENTRY, Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 let log_entry = AppendListNodeEntry::deserialize_bytes(log_entry_bytes.as_slice());
        //                 current_read_pos += LENGTH_OF_APPEND_NODE_ENTRY as u128;
        //                 let crc_bytes = match log.read(wrpm_region, current_read_pos, traits_t::size_of::<u64>(), Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 let crc = u64_from_le_bytes(crc_bytes.as_slice());
        //                 // TODO: CRC check
        //                 current_read_pos += traits_t::size_of::<u64>() as u128;

        //                 let entry = OpLogEntryType::AppendListNode {
        //                     metadata_index: log_entry.metadata_index,
        //                     old_tail: log_entry.old_tail,
        //                     new_tail: log_entry.new_tail,
        //                     metadata_crc: log_entry.metadata_crc
        //                 };
        //                 op_vec.push(entry);
        //             }
        //             INSERT_LIST_ELEMENT_ENTRY => {
        //                 let entry_read_pos = current_read_pos;
        //                 let log_entry_bytes = match log.read(wrpm_region, current_read_pos, LENGTH_OF_INSERT_LIST_ELEMENT_ENTRY, Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 let log_entry = InsertListElementEntry::deserialize_bytes(log_entry_bytes.as_slice());
        //                 current_read_pos += LENGTH_OF_INSERT_LIST_ELEMENT_ENTRY as u128;
        //                 let list_element_bytes = match log.read(wrpm_region, current_read_pos, L::size_of(), Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 // TODO: the list element needs to be deserialized; it also may not have been read from contiguous bytes...
        //                 let list_element = L::deserialize_bytes(list_element_bytes.as_slice());
        //                 let crc_bytes = match log.read(wrpm_region, current_read_pos, traits_t::size_of::<u64>(), Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 let crc = u64_from_le_bytes(crc_bytes.as_slice());
        //                 // TODO: CRC check
        //                 current_read_pos += traits_t::size_of::<u64>() as u128;

        //                 let entry = OpLogEntryType::InsertListElement {
        //                     node_offset: log_entry.node_offset,
        //                     index_in_node: log_entry.index_in_node,
        //                     list_element: *list_element // TODO: can we do this without copying the list element in DRAM?
        //                 };
        //                 op_vec.push(entry);
        //             }
        //             UPDATE_LIST_LEN_ENTRY => {
        //                 let entry_read_pos = current_read_pos;
        //                 let log_entry_bytes = match log.read(wrpm_region, current_read_pos, LENGTH_OF_UPDATE_LIST_LEN_ENTRY, Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 let log_entry = UpdateListLenEntry::deserialize_bytes(log_entry_bytes.as_slice());
        //                 current_read_pos += LENGTH_OF_UPDATE_LIST_LEN_ENTRY as u128;
        //                 let crc_bytes = match log.read(wrpm_region, current_read_pos, traits_t::size_of::<u64>(), Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 let crc = u64_from_le_bytes(crc_bytes.as_slice());
        //                 // TODO: CRC check
        //                 current_read_pos += traits_t::size_of::<u64>() as u128;

        //                 let entry = OpLogEntryType::UpdateListLen {
        //                     metadata_index: log_entry.metadata_index,
        //                     new_length: log_entry.new_length,
        //                     metadata_crc: log_entry.metadata_crc
        //                 };
        //                 op_vec.push(entry);
        //             }
        //             TRIM_LIST_METADATA_UPDATE_ENTRY => {
        //                 let entry_read_pos = current_read_pos;
        //                 let log_entry_bytes = match log.read(wrpm_region, current_read_pos, LENGTH_OF_TRIM_LIST_ENTRY, Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 let log_entry = TrimListEntry::deserialize_bytes(log_entry_bytes.as_slice());
        //                 current_read_pos += LENGTH_OF_TRIM_LIST_ENTRY as u128;
        //                 let crc_bytes = match log.read(wrpm_region, current_read_pos, traits_t::size_of::<u64>(), Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 let crc = u64_from_le_bytes(crc_bytes.as_slice());
        //                 // TODO: CRC check
        //                 current_read_pos += traits_t::size_of::<u64>() as u128;

        //                 let entry = OpLogEntryType::TrimList {
        //                     metadata_index: log_entry.metadata_index,
        //                     new_head_node: log_entry.new_head_node,
        //                     new_list_len: log_entry.new_list_len,
        //                     new_list_start_index: log_entry.new_list_start_index,
        //                     metadata_crc: log_entry.metadata_crc
        //                 };
        //                 op_vec.push(entry);
                        
        //             }
        //             COMMIT_METADATA_ENTRY => {
        //                 let entry_read_pos = current_read_pos;
        //                 let log_entry_bytes = match log.read(wrpm_region, current_read_pos, LENGTH_OF_COMMIT_METADATA_ENTRY, Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 let log_entry = CommitMetadataEntry::deserialize_bytes(log_entry_bytes.as_slice());
        //                 current_read_pos += LENGTH_OF_COMMIT_METADATA_ENTRY as u128;
        //                 let crc_bytes = match log.read(wrpm_region, current_read_pos, traits_t::size_of::<u64>(), Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 let crc = u64_from_le_bytes(crc_bytes.as_slice());
        //                 // TODO: CRC check
        //                 current_read_pos += traits_t::size_of::<u64>() as u128;

        //                 let entry = OpLogEntryType::CommitMetadataEntry {
        //                     metadata_index: log_entry.metadata_index,
        //                     item_index: log_entry.item_index
        //                 };
        //                 op_vec.push(entry);
        //             }
        //             INVALIDATE_METADATA_ENTRY => {
        //                 let entry_read_pos = current_read_pos;
        //                 let log_entry_bytes = match log.read(wrpm_region, current_read_pos, LENGTH_OF_INVALIDATE_METADATA_ENTRY, Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 let log_entry = InvalidateMetadataEntry::deserialize_bytes(log_entry_bytes.as_slice());
        //                 current_read_pos += LENGTH_OF_INVALIDATE_METADATA_ENTRY as u128;
        //                 let crc_bytes = match log.read(wrpm_region, current_read_pos, traits_t::size_of::<u64>(), Ghost(log_id)) {
        //                     Ok(bytes) => bytes,
        //                     Err(e) => return Err(KvError::LogErr { log_err: e }),
        //                 };
        //                 let crc = u64_from_le_bytes(crc_bytes.as_slice());
        //                 // TODO: CRC check

        //                 let entry = OpLogEntryType::InvalidateMetadataEntry {
        //                     metadata_index: log_entry.metadata_index
        //                 };
        //                 op_vec.push(entry);                        
        //             }
        //             _ => { return Err(KvError::InvalidLogEntryType); }
        //         }
        //     }
        //     Ok(op_vec)
        // }

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