use builtin::*;
use builtin_macros::*;
use std::hash::Hash;
use vstd::prelude::*;
use vstd::bytes::*;
use crate::kv::durable::logentry_v::*;
use crate::kv::kvimpl_t::*;
use crate::kv::durable::metadata::metadataspec_t::*;
use crate::kv::durable::metadata::layout_v::*;
use crate::kv::durable::oplog::oplogspec_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use crate::pmem::pmemutil_v::*;

verus! {
    pub struct MetadataTable<K, E> {
        metadata_table_free_list: Vec<u64>,
        state: Ghost<MetadataTableView<K>>,
        _phantom: Option<E>
    }

    impl<K, E> MetadataTable<K, E>
        where 
            K: Serializable + std::fmt::Debug,
            E: std::fmt::Debug,
    {
        pub closed spec fn view(self) -> MetadataTableView<K> 
        {
            self.state@
        }

        pub closed spec fn recover<L>(
            mems: Seq<Seq<u8>>,
            node_size: u64,
            op_log: Seq<OpLogEntryType<K>>,
            list_entry_map: Map<OpLogEntryType<K>, L>,
            kvstore_id: u128,
        ) -> Option<MetadataTableView<K>>
        {
            if mems.len() != 1 {
                None
            } else {
                let metadata_table_mem = mems[0];
                // let list_node_region_mem = mems[1];
                if metadata_table_mem.len() < ABSOLUTE_POS_OF_METADATA_TABLE {
                    // Invalid if the metadata table sequence is not large enough
                    // to store the metadata header. It actually needs to be big
                    // enough to store an entry for every key, but we don't know
                    // the number of keys yet.
                    None
                } else {
                    // the metadata header is immutable, so we can check that is valid before doing 
                    // any log replay
                    let metadata_header_bytes = metadata_table_mem.subrange(
                        ABSOLUTE_POS_OF_METADATA_HEADER as int,
                        ABSOLUTE_POS_OF_METADATA_HEADER + LENGTH_OF_METADATA_HEADER
                    );
                    let crc_bytes = metadata_table_mem.subrange(
                        ABSOLUTE_POS_OF_HEADER_CRC as int,
                        ABSOLUTE_POS_OF_HEADER_CRC + CRC_SIZE
                    );
                    let metadata_header = GlobalListMetadata::spec_deserialize(metadata_header_bytes);
                    let crc = u64::spec_deserialize(crc_bytes);
                    if crc != metadata_header.spec_crc() {
                        // The list is invalid if the stored CRC does not match the contents
                        // of the metadata header
                        None
                    } else {
                        // replay the log on the metadata table and the list region, then parse them into a list view
                        let metadata_table_mem = Self::replay_log_metadata_table(metadata_table_mem, op_log);
                        // let list_nodes_mem = Self::replay_log_list_nodes(list_node_region_mem, node_size, op_log, list_entry_map);

                        // parse the item table into a mapping index->entry so that we can use it to 
                        // construct each list.
                        // TODO: IGNORE INVALID ENTRIES
                        let metadata_table = parse_metadata_table(metadata_header, metadata_table_mem);
                        match metadata_table {
                            Some(metadata_table) => Some(MetadataTableView::new(metadata_header, metadata_table)),
                            None => None
                        }
                    }
                }
            }
        }

        closed spec fn replay_log_metadata_table(mem: Seq<u8>, op_log: Seq<OpLogEntryType<K>>) -> Seq<u8>
            decreases op_log.len()
        {
            if op_log.len() == 0 {
                mem 
            } else {
                let current_op = op_log[0];
                let op_log = op_log.drop_first();
                let mem = Self::apply_log_op_to_metadata_table_mem(mem, current_op);
                Self::replay_log_metadata_table(mem, op_log)
            }
        }

        // metadata table-related log entries store the CRC that the entry *will* have when all updates are written to it.
        // this ensures that we end up with the correct CRC even if updates to this entry were interrupted by a crash or 
        // if corruption has occurred. So, we don't check CRCs here, we just overwrite the current CRC with the new one and 
        // update relevant fields.
        closed spec fn apply_log_op_to_metadata_table_mem(mem: Seq<u8>, op: OpLogEntryType<K>) -> Seq<u8>
        {
            let table_entry_slot_size = LENGTH_OF_ENTRY_METADATA_MINUS_KEY + CRC_SIZE + CDB_SIZE + K::spec_serialized_len();
            match op {
                OpLogEntryType::ItemTableEntryCommit { item_index, metadata_index, metadata_crc } => {
                    // on item table commit, the corresponding entry in the metadata table updates its item pointer
                    // to point to the newly-committed item. We don't handle item invalidate here because when an item is 
                    // invalidated, either its entire record will be deleted (so this metadata entry will also be deleted)
                    // or we are updating it with a newly-committed item.
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + metadata_index * table_entry_slot_size;
                    let item_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_ITEM_INDEX;
                    let item_index_bytes = item_index.spec_serialize();
                    let crc_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
                    let crc_bytes = metadata_crc.spec_serialize();
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if item_addr <= pos < item_addr + 8 {
                            item_index_bytes[pos - item_addr]
                        } else if crc_addr <= pos < crc_addr + 8 {
                            crc_bytes[pos - crc_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                OpLogEntryType::AppendListNode{list_metadata_index, old_tail, new_tail, metadata_crc} => {
                    // updates the tail field and the entry's CRC. We don't use the old tail value here -- that is only used
                    // when updating list nodes
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + list_metadata_index * table_entry_slot_size;
                    let crc_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
                    let tail_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_TAIL;
                    let crc_bytes = spec_u64_to_le_bytes(metadata_crc);
                    let new_tail_bytes = spec_u64_to_le_bytes(new_tail);
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if crc_addr <= pos < crc_addr + 8 {
                            crc_bytes[pos - crc_addr]
                        } else if tail_addr <= pos < tail_addr + 8 {
                            new_tail_bytes[pos - tail_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                OpLogEntryType::UpdateListLen{list_metadata_index, new_length, metadata_crc} => {
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + list_metadata_index * table_entry_slot_size;
                    let crc_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
                    let len_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_LENGTH;
                    let crc_bytes = spec_u64_to_le_bytes(metadata_crc);
                    let len_bytes = spec_u64_to_le_bytes(new_length);
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if crc_addr <= pos < crc_addr + 8 {
                            crc_bytes[pos - crc_addr]
                        } else if len_addr <= pos < len_addr + 8 {
                            len_bytes[pos - len_addr]
                        } else {
                            pre_byte 
                        }
                    });
                    mem
                } 
                OpLogEntryType::TrimList{list_metadata_index, new_head_node, new_list_len, new_list_start_index, metadata_crc} => {
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + list_metadata_index * table_entry_slot_size;
                    let crc_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
                    let head_addr = entry_offset +  RELATIVE_POS_OF_ENTRY_METADATA_HEAD;
                    let len_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_LENGTH;
                    let start_index_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_FIRST_OFFSET;
                    let crc_bytes = spec_u64_to_le_bytes(metadata_crc);
                    let head_bytes = spec_u64_to_le_bytes(new_head_node);
                    let len_bytes = spec_u64_to_le_bytes(new_list_len);
                    let start_bytes = spec_u64_to_le_bytes(new_list_start_index);
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if crc_addr <= pos < crc_addr + 8 {
                            crc_bytes[pos - crc_addr]
                        } else if head_addr <= pos < head_addr + 8 {
                            head_bytes[pos - head_addr]
                        } else if len_addr <= pos < len_addr + 8 {
                            len_bytes[pos - len_addr]
                        } else if start_index_addr <= pos < start_index_addr + 8 {
                            start_bytes[pos - start_index_addr]
                        } else {
                            pre_byte 
                        }
                    });
                    mem
                }
                OpLogEntryType::CreateListTableEntry{list_metadata_index, head, item_index, key} => {
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + list_metadata_index * table_entry_slot_size;
                    // construct a ghost entry with the values that the new entry will have so that we can obtain a CRC 
                    let entry = ListEntryMetadata::new(head, head, 0, 0, item_index);
                    let entry_crc = entry.spec_crc();
                    let crc_bytes = spec_u64_to_le_bytes(entry_crc);
                    let crc_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
                    let entry_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA;
                    let cdb_bytes = spec_u64_to_le_bytes(CDB_TRUE);
                    let cdb_addr = entry_offset + RELATIVE_POS_OF_VALID_CDB;
                    let key_bytes = key.spec_serialize();
                    let key_addr = entry_offset + RELATIVE_POS_OF_ENTRY_KEY;
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if crc_addr <= pos < crc_addr + 8 {
                            crc_bytes[pos - crc_addr]
                        } else if cdb_addr <= pos < cdb_addr + 8 {
                            cdb_bytes[pos - cdb_addr]
                        } else if entry_addr <= pos < entry_addr + LENGTH_OF_ENTRY_METADATA_MINUS_KEY {
                            entry.spec_serialize()[pos - entry_addr]
                        } else if key_addr <= pos < key_addr + K::spec_serialized_len(){
                            key_bytes[pos - key_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                OpLogEntryType::DeleteListTableEntry{list_metadata_index} => {
                    // In this case, we just have to flip the entry's CDB. We don't clear any other fields
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + list_metadata_index * table_entry_slot_size;
                    let cdb_addr = entry_offset + RELATIVE_POS_OF_VALID_CDB;
                    let cdb_bytes = spec_u64_to_le_bytes(CDB_FALSE);
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if cdb_addr <= pos < cdb_addr + 8 {
                            cdb_bytes[pos - cdb_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                _ => mem // all other ops do not modify the metadata table
            }
        }

        pub fn read_table_metadata<PM>(pm_regions: &PM, list_id: u128) -> (result: Result<&GlobalListMetadata, KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                pm_regions.inv(),
                // TODO
            ensures
                match result {
                    Ok(output_metadata) => {
                        let metadata_size = ListEntryMetadata::spec_serialized_len();
                        let key_size = K::spec_serialized_len();
                        let metadata_slot_size = metadata_size + CRC_SIZE + key_size + CDB_SIZE;
                        &&& output_metadata.num_keys * metadata_slot_size <= u64::MAX
                        &&& ABSOLUTE_POS_OF_METADATA_TABLE + metadata_slot_size * output_metadata.num_keys  <= u64::MAX
                    }
                    Err(_) => true // TODO
                }
                // TODO
        {
            assume(false);

            let ghost mem = pm_regions@[0].committed();

            // read in the header and its CRC, check for corruption
            let metadata: &GlobalListMetadata = pm_regions.read_and_deserialize(0, ABSOLUTE_POS_OF_METADATA_HEADER);
            let metadata_crc = pm_regions.read_and_deserialize(0, ABSOLUTE_POS_OF_HEADER_CRC);

            if !check_crc_deserialized(metadata, metadata_crc, Ghost(mem),
                    Ghost(pm_regions.constants().impervious_to_corruption),
                    Ghost(ABSOLUTE_POS_OF_METADATA_HEADER), Ghost(LENGTH_OF_METADATA_HEADER),
                    Ghost(ABSOLUTE_POS_OF_HEADER_CRC)) {
                return Err(KvError::CRCMismatch);
            }

            // Since we've already checked for corruption, this condition will only fail
            // if the caller tries to use an L with a different size than the one
            // the list was originally set up with
            if {
                ||| metadata.version_number != LIST_METADATA_VERSION_NUMBER
                ||| metadata.program_guid != METADATA_TABLE_PROGRAM_GUID
            } {
                return Err(KvError::InvalidListMetadata);
            }

            Ok(metadata)
        }
    }
}