use builtin::*;
use builtin_macros::*;
use std::fs::Metadata;
use std::hash::Hash;
use vstd::prelude::*;
use vstd::bytes::*;
use crate::kv::durable::oplog::logentry_v::*;
use crate::kv::kvimpl_t::*;
use crate::kv::durable::metadata::metadataspec_t::*;
use crate::kv::durable::metadata::layout_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::crc_t::*;
use crate::pmem::traits_t;

verus! {
    pub struct MetadataTable<K> {
        metadata_table_free_list: Vec<u64>,
        state: Ghost<MetadataTableView<K>>,
    }

    impl<K> MetadataTable<K>
        where 
            K: PmCopy + std::fmt::Debug,
    {
        pub closed spec fn view(self) -> MetadataTableView<K> 
        {
            self.state@
        }

        pub closed spec fn recover<L>(
            mem: Seq<u8>,
            node_size: u64,
            op_log: Seq<OpLogEntryType<L>>,
            kvstore_id: u128,
        ) -> Option<MetadataTableView<K>>
        where 
            L: PmCopy,
        {
            if mem.len() < ABSOLUTE_POS_OF_METADATA_TABLE {
                // Invalid if the metadata table sequence is not large enough
                // to store the metadata header. It actually needs to be big
                // enough to store an entry for every key, but we don't know
                // the number of keys yet.
                None
            } else {
                // the metadata header is immutable, so we can check that is valid before doing 
                // any log replay
                let metadata_header_bytes = mem.subrange(
                    ABSOLUTE_POS_OF_METADATA_HEADER as int,
                    ABSOLUTE_POS_OF_METADATA_HEADER + MetadataTableHeader::spec_size_of()
                );
                let crc_bytes = mem.subrange(
                    ABSOLUTE_POS_OF_HEADER_CRC as int,
                    ABSOLUTE_POS_OF_HEADER_CRC + u64::spec_size_of()
                );
                let metadata_header = MetadataTableHeader::spec_from_bytes(metadata_header_bytes);
                let crc = u64::spec_from_bytes(crc_bytes);
                if crc != metadata_header.spec_crc() {
                    // The list is invalid if the stored CRC does not match the contents
                    // of the metadata header
                    None
                } else {
                    // replay the log on the metadata table and the list region, then parse them into a list view
                    let mem = Self::spec_replay_log_metadata_table(mem, op_log);
                    // let list_nodes_mem = Self::replay_log_list_nodes(list_node_region_mem, node_size, op_log, list_entry_map);

                    // parse the item table into a mapping index->entry so that we can use it to 
                    // construct each list.
                    // TODO: IGNORE INVALID ENTRIES
                    let metadata_table = parse_metadata_table(metadata_header, mem);
                    match metadata_table {
                        Some(metadata_table) => Some(MetadataTableView::new(metadata_header, metadata_table)),
                        None => None
                    }
                }
            }
        }

        closed spec fn spec_replay_log_metadata_table<L>(mem: Seq<u8>, op_log: Seq<OpLogEntryType<L>>) -> Seq<u8>
            where 
                L: PmCopy,
            decreases op_log.len()
        {
            if op_log.len() == 0 {
                mem 
            } else {
                let current_op = op_log[0];
                let op_log = op_log.drop_first();
                let mem = Self::apply_log_op_to_metadata_table_mem(mem, current_op);
                Self::spec_replay_log_metadata_table(mem, op_log)
            }
        }

        // metadata table-related log entries store the CRC that the entry *will* have when all updates are written to it.
        // this ensures that we end up with the correct CRC even if updates to this entry were interrupted by a crash or 
        // if corruption has occurred. So, we don't check CRCs here, we just overwrite the current CRC with the new one and 
        // update relevant fields.
        closed spec fn apply_log_op_to_metadata_table_mem<L>(mem: Seq<u8>, op: OpLogEntryType<L>) -> Seq<u8>
            where 
                L: PmCopy,
        {
            let table_entry_slot_size = ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of();
            match op {
                OpLogEntryType::AppendListNode{metadata_index, old_tail, new_tail} => {
                    // updates the tail field and the entry's CRC. We don't use the old tail value here -- that is only used
                    // when updating list nodes
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + metadata_index * table_entry_slot_size;
                    let crc_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
                    let tail_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_TAIL;
                    let new_tail_bytes = spec_u64_to_le_bytes(new_tail);
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if tail_addr <= pos < tail_addr + 8 {
                            new_tail_bytes[pos - tail_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                OpLogEntryType::CommitMetadataEntry{metadata_index} => {
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + metadata_index * table_entry_slot_size;
                    let cdb_bytes = spec_u64_to_le_bytes(CDB_TRUE);
                    let cdb_addr = entry_offset + RELATIVE_POS_OF_VALID_CDB;
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if cdb_addr <= pos < cdb_addr + 8 {
                            cdb_bytes[pos - cdb_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                OpLogEntryType::InvalidateMetadataEntry{metadata_index} => {
                    // In this case, we just have to flip the entry's CDB. We don't clear any other fields
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + metadata_index * table_entry_slot_size;
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

        pub fn read_table_metadata<PM>(pm_regions: &PM, list_id: u128) -> (result: Result<Box<MetadataTableHeader>, KvError<K>>)
            where
                PM: PersistentMemoryRegions,
            requires
                pm_regions.inv(),
                // TODO
            ensures
                match result {
                    Ok(output_metadata) => {
                        let metadata_size = ListEntryMetadata::spec_size_of();
                        let key_size = K::spec_size_of();
                        let metadata_slot_size = metadata_size + u64::spec_size_of() + key_size + u64::spec_size_of();
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
            let ghost true_metadata = choose |metadata: MetadataTableHeader| metadata.spec_to_bytes() == mem.subrange(ABSOLUTE_POS_OF_METADATA_HEADER as int, ABSOLUTE_POS_OF_METADATA_HEADER + MetadataTableHeader::spec_size_of());
            let ghost true_crc = choose |val: u64| val.spec_to_bytes() == mem.subrange(ABSOLUTE_POS_OF_HEADER_CRC as int, ABSOLUTE_POS_OF_HEADER_CRC + u64::spec_size_of());

            let metadata = pm_regions.read_aligned::<MetadataTableHeader>(0, ABSOLUTE_POS_OF_METADATA_HEADER, Ghost(true_metadata)).map_err(|e| KvError::PmemErr { pmem_err: e })?;
            let metadata_crc = pm_regions.read_aligned::<u64>(0, ABSOLUTE_POS_OF_HEADER_CRC, Ghost(true_crc)).map_err(|e| KvError::PmemErr { pmem_err: e })?;

            let ghost metadata_addrs = Seq::new(MetadataTableHeader::spec_size_of() as nat, |i: int| ABSOLUTE_POS_OF_METADATA_HEADER + i);
            let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| ABSOLUTE_POS_OF_HEADER_CRC + i);

            let ghost true_metadata_bytes = Seq::new(MetadataTableHeader::spec_size_of() as nat, |i: int| mem[metadata_addrs[i]]);
            let ghost true_crc_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem[crc_addrs[i]]);

            if !check_crc(metadata.as_slice(), metadata_crc.as_slice(), Ghost(mem),
                    Ghost(pm_regions.constants().impervious_to_corruption),
                    Ghost(metadata_addrs),
                    Ghost(crc_addrs)) {
                return Err(KvError::CRCMismatch);
            }

            let metadata = metadata.extract_init_val(
                Ghost(true_metadata),
                Ghost(true_metadata_bytes),
                Ghost(pm_regions.constants().impervious_to_corruption),
            );

            // Since we've already checked for corruption, this condition will only fail
            // if the caller tries to use an L with a different size than the one
            // the list was originally set up with
            if {
                ||| metadata.version_number != METADATA_TABLE_VERSION_NUMBER
                ||| metadata.program_guid != METADATA_TABLE_PROGRAM_GUID
            } {
                return Err(KvError::InvalidListMetadata);
            }

            Ok(metadata)
        }

        // this uses the old PM approach but we will switch over to the new lens approach at some point
        pub exec fn setup<PM>(
            pm_region: &mut PM,
            table_id: u128,
            num_keys: u64,
            list_element_size: u32,
            node_size: u32,
        ) -> (result: Result<(), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires
                old(pm_region).inv(),
                ({
                    let entry_slot_size = ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of();
                    &&& entry_slot_size <= u64::MAX
                    &&& ABSOLUTE_POS_OF_METADATA_TABLE + num_keys * entry_slot_size <= usize::MAX
                }),
                list_element_size + u64::spec_size_of() <= u32::MAX,
                // TODO 
            ensures 
                pm_region.inv(),
                // TODO
        {
            // ensure that there are no outstanding writes
            pm_region.flush();

            // check that the regions the caller passed in are sufficiently large
            let region_size = pm_region.get_region_size();
            let entry_slot_size = (traits_t::size_of::<ListEntryMetadata>() + traits_t::size_of::<u64>() + traits_t::size_of::<u64>() + K::size_of()) as u64;
            let required_region_size = ABSOLUTE_POS_OF_METADATA_TABLE + num_keys * entry_slot_size;
            if required_region_size > region_size {
                return Err(KvError::RegionTooSmall{ required: required_region_size as usize, actual: region_size as usize });
            }

            let full_list_element_size = list_element_size + traits_t::size_of::<u64>() as u32; 

            Self::write_setup_metadata(pm_region, num_keys, full_list_element_size, node_size);

            // invalidate all of the entries
            for index in 0..num_keys 
                invariant
                    pm_region.inv(),
            {
                assume(false);
                let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + index * entry_slot_size;
                pm_region.serialize_and_write(entry_offset + RELATIVE_POS_OF_VALID_CDB, &CDB_FALSE);
            }

            pm_region.flush();

            Ok(())
        }

        pub exec fn start<PM, L>(
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedMetadataPermission, PM>,
            table_id: u128,
            log_entries: &Vec<OpLogEntryType<L>>,
            Tracked(perm): Tracked<&TrustedMetadataPermission>,
            Ghost(state): Ghost<MetadataTableView<K>>,
        ) -> (result: Result<Self, KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
                L: PmCopy,
            requires 
                old(wrpm_region).inv(),
                // TODO
            ensures 
                wrpm_region.inv(),
                // TODO
        {
            assume(false);

            // 1. ensure that there are no outstanding writes
            wrpm_region.flush();

            let pm_region = wrpm_region.get_pm_region_ref();
            let ghost mem = pm_region@.committed();

            // 2. check that the caller passed in a region that is large enough to store the metadata table header
            // we will check that it fits the number of entries we want below
            let region_size = pm_region.get_region_size();
            if region_size < ABSOLUTE_POS_OF_METADATA_TABLE {
                return Err(KvError::RegionTooSmall{ required: ABSOLUTE_POS_OF_METADATA_TABLE as usize, actual: region_size as usize });
            }

            // 3. read and check the header 
            let header = Self::read_header(pm_region, table_id)?;

            // finish validity checks -- check that the regions the caller passed in are sufficiently large
            // we can't do this until after reading the header since it depends on the number of keys we expect
            // to be able to store
            let entry_slot_size = (traits_t::size_of::<ListEntryMetadata>() + traits_t::size_of::<u64>() + traits_t::size_of::<u64>() + K::size_of()) as u64;
            let required_region_size = ABSOLUTE_POS_OF_METADATA_TABLE + header.num_keys * entry_slot_size;
            if required_region_size > region_size {
                return Err(KvError::RegionTooSmall{ required: required_region_size as usize, actual: region_size as usize });
            }

            // 4. run recovery using the list of log entries.
            Self::replay_log_metadata_table(wrpm_region, table_id, log_entries, Tracked(perm), Ghost(state))?;

            // reborrow to satisfy the borrow checker
            let pm_region = wrpm_region.get_pm_region_ref();
            let ghost mem = pm_region@.committed();

            // 5. read valid bytes and construct the allocator 
            let mut metadata_allocator: Vec<u64> = Vec::with_capacity(header.num_keys as usize);
            for index in 0..header.num_keys 
                // TODO: invariant
            {
                assume(false);
                let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + index * entry_slot_size;
                let cdb_addr = entry_offset + RELATIVE_POS_OF_VALID_CDB;
                let ghost true_cdb = choose |val: u64| val.spec_to_bytes() == mem.subrange(cdb_addr as int, cdb_addr + u64::spec_size_of());
                let cdb = pm_region.read_aligned::<u64>(cdb_addr, Ghost(true_cdb)).map_err(|e| KvError::PmemErr { pmem_err: e })?;
                let ghost cdb_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| cdb_addr + i);
                match check_cdb(cdb, Ghost(true_cdb), Ghost(mem), Ghost(pm_region.constants().impervious_to_corruption), Ghost(cdb_addrs)) {
                    Some(false) => metadata_allocator.push(index),
                    Some(true) => {},
                    None => return Err(KvError::CRCMismatch),
                }
            }

            Ok(Self {
                metadata_table_free_list: metadata_allocator,
                state: Ghost(MetadataTableView::new(*header, parse_metadata_table(*header, mem).unwrap())),
            })
        }

        exec fn replay_log_metadata_table<PM, L>(
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedMetadataPermission, PM>,
            table_id: u128,
            log_entries: &Vec<OpLogEntryType<L>>,
            Tracked(perm): Tracked<&TrustedMetadataPermission>,
            Ghost(state): Ghost<MetadataTableView<K>>,
        ) -> Result<(), KvError<K>>
            where 
                PM: PersistentMemoryRegion,
                L: PmCopy,
        {
            for i in 0..log_entries.len()
                invariant 
                    // TODO
            {
                assume(false);
                // CDB + CDC + metadata + key
                let entry_slot_size = (traits_t::size_of::<u64>() + traits_t::size_of::<u64>() + 
                    traits_t::size_of::<ListEntryMetadata>() + K::size_of()) as u64;

                let log_entry = &log_entries[i];
                match log_entry {
                    OpLogEntryType::CommitMetadataEntry { metadata_index } => {
                        // commit metadata just sets the CDB -- the metadata fields have already been filled in.
                        // We also have to commit the item, but we'll do that in item table recovery
                        let cdb_addr = ABSOLUTE_POS_OF_METADATA_TABLE + metadata_index * entry_slot_size;
                        
                        wrpm_region.serialize_and_write(cdb_addr, &CDB_TRUE, Tracked(perm));
                    }
                    OpLogEntryType::InvalidateMetadataEntry { metadata_index } => {
                        // invalidate metadata just writes CDB_FALSE to the entry's CDB
                        let cdb_addr = ABSOLUTE_POS_OF_METADATA_TABLE + metadata_index * entry_slot_size;
                        
                        wrpm_region.serialize_and_write(cdb_addr, &CDB_FALSE, Tracked(perm));
                    }
                    OpLogEntryType::UpdateMetadataEntry { metadata_index, new_metadata } => {
                        let cdb_addr = ABSOLUTE_POS_OF_METADATA_TABLE + metadata_index * entry_slot_size;
                        let crc_addr = cdb_addr + traits_t::size_of::<u64>() as u64;
                        let metadata_slot_addr = crc_addr + traits_t::size_of::<u64>() as u64;

                        let crc = calculate_crc(new_metadata);

                        wrpm_region.serialize_and_write(crc_addr, &crc, Tracked(perm));
                        wrpm_region.serialize_and_write(metadata_slot_addr, new_metadata, Tracked(perm));
                    }
                    _ => {} // the other operations do not modify the metadata table
                }
                
            }
            Ok(())
        }

        // Since metadata table entries have a valid CDB, we can tentatively write the whole entry and log a commit op for it,
        // then flip the CDB once the log has been committed
        pub exec fn tentative_create<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedMetadataPermission, PM>,
            Ghost(table_id): Ghost<u128>,
            list_node_index: u64,
            item_table_index: u64,
            key: &K,
            Tracked(perm): Tracked<&TrustedMetadataPermission>
        ) -> (result: Result<u64, KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                old(wrpm_region).inv(),
                // TODO
            ensures 
                wrpm_region.inv(),
                // TODO
        {
            assume(false);

            // 1. pop an index from the free list
            // since this index is on the free list, its CDB is already false
            let free_index = match self.metadata_table_free_list.pop(){
                Some(index) => index,
                None => return Err(KvError::OutOfSpace),
            };

            // 2. construct the entry with list metadata and item index
            let entry = ListEntryMetadata::new(list_node_index, list_node_index, 0, 0, item_table_index);

            // 3. calculate the CRC of the entry + key 
            let mut digest = CrcDigest::new();
            digest.write(&entry);
            digest.write(key);
            let crc = digest.sum64();

            // 4. write CRC and entry 
            let entry_slot_size = (traits_t::size_of::<ListEntryMetadata>() + traits_t::size_of::<u64>() + traits_t::size_of::<u64>() + K::size_of()) as u64;
            let slot_addr = ABSOLUTE_POS_OF_METADATA_TABLE + free_index * entry_slot_size;
            // CDB is at slot addr -- we aren't setting that one yet
            let entry_addr = slot_addr + traits_t::size_of::<u64>() as u64;
            let crc_addr = entry_addr + traits_t::size_of::<ListEntryMetadata>() as u64;
            let key_addr = crc_addr + traits_t::size_of::<u64>() as u64;

            wrpm_region.serialize_and_write(crc_addr, &crc, Tracked(perm));
            wrpm_region.serialize_and_write(entry_addr, &entry, Tracked(perm));
            wrpm_region.serialize_and_write(key_addr, key, Tracked(perm));

            Ok(free_index)
        }

        // Overwrite an existing metadata table entry with a new one. The function does NOT overwrite the key,
        // but we need to use the key to calculate the new CRC and reading it from PM here would require an extra
        // CRC check. This is a committing operation, so the overwrite must have already been logged. 
        pub exec fn overwrite_entry<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedMetadataPermission, PM>,
            metadata_index: u64,
            new_metadata: &ListEntryMetadata,
            key: &K,
            Ghost(table_id): Ghost<u128>,
            Tracked(perm): Tracked<&TrustedMetadataPermission>
        ) -> (result: Result<(), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                old(wrpm_region).inv(),
                // TODO
                // the key that is passed in is the same as the one already with the entry on PM
            ensures 
                wrpm_region.inv(),
                // TODO
        {
            assume(false);

            // 1. calculate the CRC of the entry + key 
            let mut digest = CrcDigest::new();
            digest.write(new_metadata);
            digest.write(key);
            let crc = digest.sum64();

            // 2. Write the CRC and entry (but not the key)
            let entry_slot_size = (traits_t::size_of::<ListEntryMetadata>() + traits_t::size_of::<u64>() + traits_t::size_of::<u64>() + K::size_of()) as u64;
            let slot_addr = ABSOLUTE_POS_OF_METADATA_TABLE + metadata_index * entry_slot_size;
            let entry_addr = slot_addr + traits_t::size_of::<u64>() as u64;
            let crc_addr = entry_addr + traits_t::size_of::<ListEntryMetadata>() as u64;

            wrpm_region.serialize_and_write(crc_addr, &crc, Tracked(perm));
            wrpm_region.serialize_and_write(entry_addr, new_metadata, Tracked(perm));

            Ok(())
        }

        // Makes a slot valid by setting its valid CDB.
        // Must log the commit operation before calling this function.
        pub exec fn commit_entry<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedMetadataPermission, PM>,
            table_id: u128,
            index: u64,
            Tracked(perm): Tracked<&TrustedMetadataPermission>
        ) -> (result: Result<(), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                old(wrpm_region).inv(),
                // TODO
            ensures 
                wrpm_region.inv(),
                // TODO
        {
            assume(false);

            let entry_slot_size = (traits_t::size_of::<ListEntryMetadata>() + traits_t::size_of::<u64>() + traits_t::size_of::<u64>() + K::size_of()) as u64;
            let slot_addr = ABSOLUTE_POS_OF_METADATA_TABLE + index * entry_slot_size;
            let cdb_addr = slot_addr;

            wrpm_region.serialize_and_write(cdb_addr, &CDB_TRUE, Tracked(perm));

            Ok(())
        }

        pub exec fn get_key_and_metadata_entry_at_index<PM>(
            &self,
            pm_region: &PM,
            table_id: u128,
            metadata_index: u64,
        ) -> (result: Result<(Box<K>, Box<ListEntryMetadata>), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                pm_region.inv(),
                // TODO
            ensures 
                // TODO
        {
            assume(false);

            // TODO: why is the CRC between the key and the entry? they should be consecutive to make things a little
            // bit easier.

            // TODO: store this so we don't have to recalculate it every time
            let entry_slot_size = (traits_t::size_of::<ListEntryMetadata>() + traits_t::size_of::<u64>() + traits_t::size_of::<u64>() + K::size_of()) as u64;
            let slot_addr = ABSOLUTE_POS_OF_METADATA_TABLE + metadata_index * entry_slot_size;
            let cdb_addr = slot_addr;
            let entry_addr = cdb_addr + traits_t::size_of::<u64>() as u64;
            let crc_addr = entry_addr + traits_t::size_of::<ListEntryMetadata>() as u64;
            let key_addr = crc_addr + traits_t::size_of::<u64>() as u64;

            // 1. Read the CDB, metadata entry, key, and CRC at the index
            let ghost mem = pm_region@.committed();

            let ghost true_cdb_bytes = extract_bytes(mem, cdb_addr as int, u64::spec_size_of());
            let ghost true_entry_bytes = extract_bytes(mem, entry_addr as int, ListEntryMetadata::spec_size_of());
            let ghost true_crc_bytes = extract_bytes(mem, crc_addr as int, u64::spec_size_of());
            let ghost true_key_bytes = extract_bytes(mem, key_addr as int, K::spec_size_of());

            let ghost true_cdb = u64::spec_from_bytes(true_cdb_bytes);
            let ghost true_entry = ListEntryMetadata::spec_from_bytes(true_entry_bytes);
            let ghost true_crc = u64::spec_from_bytes(true_crc_bytes);
            let ghost true_key = K::spec_from_bytes(true_key_bytes);

            let ghost cdb_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| cdb_addr + i);
            let ghost entry_addrs = Seq::new(ListEntryMetadata::spec_size_of() as nat, |i: int| entry_addr + i);
            let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| crc_addr + i);
            let ghost key_addrs = Seq::new(K::spec_size_of() as nat, |i: int| key_addr + i);

            // 2. Check the CDB to determine whether the entry is valid
            let cdb = match pm_region.read_aligned::<u64>(cdb_addr, Ghost(true_cdb)) {
                Ok(cdb) => cdb,
                Err(e) => return Err(KvError::PmemErr { pmem_err: e })
            };
            let cdb_result = check_cdb(cdb, Ghost(true_cdb), Ghost(mem), 
                Ghost(pm_region.constants().impervious_to_corruption), Ghost(cdb_addrs));
            match cdb_result {
                Some(true) => {} // continue 
                Some(false) => return Err(KvError::EntryIsNotValid),
                None => return Err(KvError::CRCMismatch)
            }

            // TODO: error handling
            let metadata_entry = match pm_region.read_aligned::<ListEntryMetadata>(entry_addr, Ghost(true_entry)) {
                Ok(metadata_entry) => metadata_entry,
                Err(e) => return Err(KvError::PmemErr { pmem_err: e })
            };
            let crc = match pm_region.read_aligned::<u64>(crc_addr, Ghost(true_crc)) {
                Ok(crc) => crc,
                Err(e) => return Err(KvError::PmemErr { pmem_err: e })
            };
            let key = match pm_region.read_aligned::<K>(key_addr, Ghost(true_key)) {
                Ok(key) => key,
                Err(e) => return Err(KvError::PmemErr {pmem_err: e })
            };

            // 3. Check for corruption
            if !check_crc_for_two_reads(metadata_entry.as_slice(), key.as_slice(), crc.as_slice(), Ghost(mem),
                Ghost(pm_region.constants().impervious_to_corruption), Ghost(entry_addrs), Ghost(key_addrs), Ghost(crc_addrs)) 
            {
                return Err(KvError::CRCMismatch);
            }

            // 4. Return the metadata entry and key
            let metadata_entry = metadata_entry.extract_init_val(Ghost(true_entry), Ghost(true_entry_bytes),
                Ghost(pm_region.constants().impervious_to_corruption));
            let key = key.extract_init_val(Ghost(true_key), Ghost(true_key_bytes), 
                Ghost(pm_region.constants().impervious_to_corruption));
            Ok((key, metadata_entry))
        }
        

        pub exec fn invalidate_entry<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedMetadataPermission, PM>,
            table_id: u128,
            index: u64,
            Tracked(perm): Tracked<&TrustedMetadataPermission>
        ) -> (result: Result<(), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                old(wrpm_region).inv(),
                // TODO
            ensures 
                wrpm_region.inv(),
                // TODO
        {
            assume(false);

            let entry_slot_size = (traits_t::size_of::<ListEntryMetadata>() + traits_t::size_of::<u64>() + traits_t::size_of::<u64>() + K::size_of()) as u64;
            let slot_addr = ABSOLUTE_POS_OF_METADATA_TABLE + index * entry_slot_size;
            let cdb_addr = slot_addr + RELATIVE_POS_OF_VALID_CDB;

            wrpm_region.serialize_and_write(cdb_addr, &CDB_FALSE, Tracked(perm));

            Ok(())
        }

        // Updates the list's length and the CRC of the entire entry. The caller must provide the CRC (either by calculating it
        // themselves or by reading it from a log entry).
        pub exec fn update_list_len<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedMetadataPermission, PM>,
            table_id: u128,
            index: u64,
            new_length: u64,
            metadata_crc: u64,
            Tracked(perm): Tracked<&TrustedMetadataPermission>
        ) -> (result: Result<(), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                old(wrpm_region).inv(),
                // TODO
            ensures 
                wrpm_region.inv(),
                // TODO
        {
            assume(false);

            let entry_slot_size = (traits_t::size_of::<ListEntryMetadata>() + traits_t::size_of::<u64>() + traits_t::size_of::<u64>() + K::size_of()) as u64;
            let slot_addr = ABSOLUTE_POS_OF_METADATA_TABLE + index * entry_slot_size;
            let crc_addr = slot_addr + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
            let len_addr = slot_addr + RELATIVE_POS_OF_ENTRY_METADATA_LENGTH;

            wrpm_region.serialize_and_write(crc_addr, &metadata_crc, Tracked(perm));
            wrpm_region.serialize_and_write(len_addr, &new_length, Tracked(perm));

            Ok(())
        }

        pub exec fn trim_list<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedMetadataPermission, PM>,
            table_id: u128,
            index: u64,
            new_head: u64,
            new_len: u64,
            new_list_start_index: u64,
            metadata_crc: u64,
            Tracked(perm): Tracked<&TrustedMetadataPermission>
        ) -> (result: Result<(), KvError<K>>) 
            where 
                PM: PersistentMemoryRegion,
            requires 
                old(wrpm_region).inv(),
                // TODO
            ensures 
                wrpm_region.inv(),
                // TODO
        {
            assume(false);

            let entry_slot_size = (traits_t::size_of::<ListEntryMetadata>() + traits_t::size_of::<u64>() + traits_t::size_of::<u64>() + K::size_of()) as u64;
            let slot_addr = ABSOLUTE_POS_OF_METADATA_TABLE + index * entry_slot_size;
            let crc_addr = slot_addr + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
            let head_addr = slot_addr + RELATIVE_POS_OF_ENTRY_METADATA_HEAD;
            let len_addr = slot_addr + RELATIVE_POS_OF_ENTRY_METADATA_LENGTH;
            let start_index_addr = slot_addr + RELATIVE_POS_OF_ENTRY_METADATA_FIRST_OFFSET;

            wrpm_region.serialize_and_write(crc_addr, &metadata_crc, Tracked(perm));
            wrpm_region.serialize_and_write(head_addr, &new_head, Tracked(perm));
            wrpm_region.serialize_and_write(len_addr, &new_len, Tracked(perm));
            wrpm_region.serialize_and_write(start_index_addr, &new_list_start_index, Tracked(perm));

            Ok(())
        }

        exec fn write_setup_metadata<PM>(
            pm_region: &mut PM, 
            num_keys: u64, 
            list_element_size: u32, 
            list_node_size: u32,
        )
            where 
                PM: PersistentMemoryRegion,
            requires 
                old(pm_region).inv(),
                // TODO
                // region is large enough
            ensures 
                pm_region.inv(),
                // TODO
        {
            assume(false);

            // initialize header and compute crc
            let header = MetadataTableHeader {
                element_size: list_element_size,
                node_size: list_node_size, 
                num_keys: num_keys,
                version_number: METADATA_TABLE_VERSION_NUMBER,
                _padding: 0,
                program_guid: METADATA_TABLE_PROGRAM_GUID,
            };
            let header_crc = calculate_crc(&header);

            pm_region.serialize_and_write( ABSOLUTE_POS_OF_METADATA_HEADER, &header);
            pm_region.serialize_and_write(ABSOLUTE_POS_OF_HEADER_CRC, &header_crc);
        }

        exec fn read_header<PM>(
            pm_region: &PM,
            table_id: u128
        ) -> (result: Result<Box<MetadataTableHeader>, KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                pm_region.inv(),
                // TODO
            ensures 
                // TODO
        {
            assume(false);

            let ghost mem = pm_region@.committed();

            let ghost true_header = choose |header: MetadataTableHeader| header.spec_to_bytes() == mem.subrange(ABSOLUTE_POS_OF_METADATA_HEADER as int, ABSOLUTE_POS_OF_METADATA_HEADER + MetadataTableHeader::spec_size_of());  
            let ghost true_crc = choose |val: u64| val.spec_to_bytes() == mem.subrange(ABSOLUTE_POS_OF_HEADER_CRC as int, ABSOLUTE_POS_OF_HEADER_CRC + u64::spec_size_of());
            
            let header = pm_region.read_aligned::<MetadataTableHeader>(ABSOLUTE_POS_OF_METADATA_HEADER, Ghost(true_header)).map_err(|e| KvError::PmemErr { pmem_err: e })?;
            let header_crc = pm_region.read_aligned::<u64>(ABSOLUTE_POS_OF_HEADER_CRC, Ghost(true_crc)).map_err(|e| KvError::PmemErr { pmem_err: e })?;

            let ghost header_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| ABSOLUTE_POS_OF_METADATA_HEADER + i);
            let ghost header_crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| ABSOLUTE_POS_OF_HEADER_CRC + i);

            let ghost true_header_bytes = Seq::new(MetadataTableHeader::spec_size_of() as nat, |i: int| mem[header_addrs[i]]);

            // check the CRC
            if !check_crc(header.as_slice(), header_crc.as_slice(), Ghost(mem),
                    Ghost(pm_region.constants().impervious_to_corruption),
                    Ghost(header_addrs),
                    Ghost(header_crc_addrs)) {
                return Err(KvError::CRCMismatch);
            }   

            let header = header.extract_init_val(
                Ghost(true_header),
                Ghost(true_header_bytes),
                Ghost(pm_region.constants().impervious_to_corruption),
            );

            // check that the contents of the header make sense; since we've already checked for corruption,
            // these checks should never fail
            if {
                ||| header.program_guid != METADATA_TABLE_PROGRAM_GUID 
                ||| header.version_number != METADATA_TABLE_VERSION_NUMBER
            } {
                Err(KvError::InvalidListMetadata)
            } else {
                Ok(header)
            }
        }
    }
}