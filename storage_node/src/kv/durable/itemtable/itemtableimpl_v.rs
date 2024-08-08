use crate::kv::durable::itemtable::itemtablespec_t::*;
use crate::kv::durable::itemtable::layout_v::*;
use crate::kv::durable::oplog::logentry_v::*;
use crate::kv::durable::inv_v::*;
use crate::kv::durable::oplog::oplogspec_t::AbstractOpLogState;
use crate::kv::kvimpl_t::*;
use crate::kv::layout_v::*;
use crate::kv::setup_v::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::traits_t;
use crate::pmem::subregion_v::*;
use builtin::*;
use builtin_macros::*;
use std::hash::Hash;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {
    pub struct DurableItemTable<K, I>
        where
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
    {
        item_size: u64,
        item_slot_size: u64,
        num_keys: u64,
        free_list: Vec<u64>,
        state: Ghost<DurableItemTableView<I>>,
        _phantom: Ghost<Option<K>>,
    }

    impl<K, I> DurableItemTable<K, I>
        where
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
    {
        pub closed spec fn view(self) -> DurableItemTableView<I>
        {
            self.state@
        }

        pub closed spec fn spec_item_size(self) -> u64
        {
            self.item_size
        }

        pub closed spec fn spec_num_keys(self) -> u64
        {
            self.num_keys
        }

        pub closed spec fn spec_free_list(self) -> Seq<u64>
        {
            self.free_list@
        }

        // pub open spec fn recover<L>(
        //     mem: Seq<u8>,
        //     // op_log: Seq<OpLogEntryType<L>>,
        //     valid_indices: Set<int>,
        //     num_keys: u64,
        // ) -> Option<DurableItemTableView<I>>
        //     where 
        //         L: PmCopy,
        // {
        //     if mem.len() < ABSOLUTE_POS_OF_TABLE_AREA {
        //         // If the memory is not large enough to store the metadata header,
        //         // it is not valid
        //         None
        //     }
        //     else {
        //         // replay the log on `mem`, then parse it into (hopefully) a valid item table view
        //         // TODO: may not need to do any replay here?
        //         // let mem = Self::spec_replay_log_item_table(mem, op_log);
        //         parse_item_table::<I, K>(mem, num_keys as nat, valid_indices)
        //     }

        // }

        // // Recursively apply log operations to the item table bytes. Skips all log entries that 
        // // do not modify the item table.
        // // TODO: check length of `mem`?
        // pub open spec fn spec_replay_log_item_table<L>(mem: Seq<u8>, op_log: Seq<LogicalOpLogEntry<L>>) -> Seq<u8>
        //     where 
        //         L: PmCopy,
        //     decreases op_log.len(),
        // {
        //     if op_log.len() == 0 {
        //         mem
        //     } else {
        //         let current_op = op_log[0];
        //         let op_log = op_log.drop_first();
        //         let mem = Self::apply_log_op_to_item_table_mem(mem, current_op);
        //         Self::spec_replay_log_item_table(mem, op_log)
        //     }
        // }

        // // TODO: refactor -- logic in both cases is the same
        // pub open spec fn apply_log_op_to_item_table_mem<L>(mem: Seq<u8>, op: OpLogEntryType<L>) -> Seq<u8>
        //     where 
        //         L: PmCopy,
        // {
        //     mem
        //     // let item_entry_size = I::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of();
        //     // match op {
        //     //     OpLogEntryType::ItemTableEntryCommit { item_index } => {
        //     //         let entry_offset = ABSOLUTE_POS_OF_TABLE_AREA + item_index * item_entry_size;
        //     //         let addr = entry_offset + RELATIVE_POS_OF_VALID_CDB;
        //     //         let valid_cdb = spec_u64_to_le_bytes(CDB_TRUE);
        //     //         let mem = mem.map(|pos: int, pre_byte: u8| 
        //     //                                             if addr <= pos < addr + valid_cdb.len() { valid_cdb[pos - addr]}
        //     //                                             else { pre_byte }
        //     //                                         );
        //     //         mem
        //     //     }
        //     //     OpLogEntryType::ItemTableEntryInvalidate { item_index } => {
        //     //         let entry_offset = ABSOLUTE_POS_OF_TABLE_AREA + item_index * item_entry_size;
        //     //         let addr = entry_offset + RELATIVE_POS_OF_VALID_CDB;
        //     //         let invalid_cdb = spec_u64_to_le_bytes(CDB_FALSE);
        //     //         let mem = mem.map(|pos: int, pre_byte: u8| 
        //     //                                             if addr <= pos < addr + invalid_cdb.len() { invalid_cdb[pos - addr]}
        //     //                                             else { pre_byte }
        //     //                                         );
        //     //         mem
        //     //     }
        //     //     _ => mem
        //     // }
        // }

        // TODO: write invariants
        closed spec fn inv(self) -> bool;

        pub exec fn item_slot_size(&self) -> u64 {
            self.item_slot_size
        }

        pub proof fn lemma_table_is_empty_at_setup<PM, L>(
            subregion: &WritablePersistentMemorySubregion,
            pm_region: &PM,
            valid_indices: Set<int>,
            num_keys: u64,
        )
            where 
                PM: PersistentMemoryRegion,
                L: PmCopy,
            requires 
                valid_indices == Set::<int>::empty(),
                ({ 
                    let mem = subregion.view(pm_region).committed();
                    let item_entry_size = I::spec_size_of() + u64::spec_size_of();
                    &&& num_keys * item_entry_size <= mem.len()
                    &&& mem.len() >= ABSOLUTE_POS_OF_TABLE_AREA
                }),
            ensures
                ({
                    let mem = subregion.view(pm_region).committed();
                    &&& parse_item_table::<I, K>(mem, num_keys as nat, valid_indices) matches Some(item_table_view)
                    &&& item_table_view == DurableItemTableView::<I>::init(num_keys as int)
                })
        {
            let mem = subregion.view(pm_region).committed();
            let item_entry_size = I::spec_size_of() + u64::spec_size_of();
            let item_table_view = parse_item_table::<I, K>(mem, num_keys as nat, valid_indices);
            assert(item_table_view is Some);

            let item_table_view = item_table_view.unwrap();
            assert(item_table_view.durable_item_table == item_table_view.tentative_item_table);
            
            assert(item_table_view == DurableItemTableView::<I>::init(num_keys as int));
        }

        pub exec fn start<PM, L>(
            subregion: &PersistentMemorySubregion,
            pm_region: &PM,
            valid_indices: Vec<u64>,
            overall_metadata: OverallMetadata,
            version_metadata: VersionMetadata,
        ) -> (result: Result<Self, KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
                L: PmCopy + std::fmt::Debug,
            requires
                subregion.inv(pm_region),
                pm_region@.no_outstanding_writes(),
                overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr, overall_metadata.kvstore_id),
                subregion.len() == overall_metadata.item_table_size,
                subregion.view(pm_region).no_outstanding_writes(),
                ({
                    let valid_indices_view = Seq::new(valid_indices@.len(), |i: int| valid_indices[i] as int);
                    let table = parse_item_table::<I, K>(subregion.view(pm_region).committed(), overall_metadata.num_keys as nat, valid_indices_view.to_set());
                    table is Some
                })
            ensures 
                match result {
                    Ok(item_table) => {
                        let valid_indices_view = Seq::new(valid_indices@.len(), |i: int| valid_indices[i] as int);
                        let table = parse_item_table::<I, K>(subregion.view(pm_region).committed(), overall_metadata.num_keys as nat, valid_indices_view.to_set()).unwrap();
                        table == item_table@
                        // TODO finish
                    }
                    Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                    Err(KvError::PmemErr{ pmem_err }) => true,
                    Err(_) => false
                }
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        /* temporarily commented out for subregion development 
        // TODO: this function doesn't do anything with state right now
        pub exec fn start<PM, L>(
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedItemTablePermission, PM>,
            item_table_id: u128,
            log_entries: &Vec<OpLogEntryType<L>>,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
            Ghost(state): Ghost<DurableItemTableView<I>>
        ) -> (result: Result<Self, KvError<K>>)
            where
                PM: PersistentMemoryRegion,
                L: PmCopy,
            requires
                old(wrpm_region).inv(),
                0 <= ItemTableMetadata::spec_size_of() + u64::spec_size_of() < usize::MAX,
                ({
                    let item_slot_size = I::spec_size_of() + u64::spec_size_of() + u64::spec_size_of();
                    let metadata_header_size = ItemTableMetadata::spec_size_of() + u64::spec_size_of();
                    &&& 0 <= item_slot_size < u64::MAX
                })
                // TODO: recovery and permissions checks
            ensures
                wrpm_region.inv(),
                // TODO: write the rest of the postconditions
        {
            let item_size = I::size_of() as u64;

            // ensure that there are no outstanding writes
            wrpm_region.flush();

            // check that the caller passed in one valid region. We assume that the caller has
            // set up the region with `setup`, which does these same checks, but we check here
            // again anyway in case they didn't.
            let pm_region = wrpm_region.get_pm_region_ref();
            let ghost mem = pm_region@.committed();
            let table_region_size = pm_region.get_region_size();
            if table_region_size < ABSOLUTE_POS_OF_TABLE_AREA {
                return Err(KvError::RegionTooSmall {required: ABSOLUTE_POS_OF_TABLE_AREA as usize, actual: table_region_size as usize});
            }

            // read and check the header metadata
            let table_metadata = Self::read_table_metadata(pm_region, item_table_id)?;

            // determine if the provided region is large enough for the
            // specified number of items
            let num_keys = table_metadata.num_keys;
            let item_slot_size = (item_size as usize + traits_t::size_of::<u64>() + traits_t::size_of::<u64>()) as u64;

            // Sanity check on the number of keys that helps prove the absence of overflow for the next check
            if (item_slot_size * num_keys) as usize > usize::MAX - ABSOLUTE_POS_OF_TABLE_AREA as usize {
                // TODO: more detailed error message that indicates the number of requested keys is 
                // too high to store
                return Err(KvError::InvalidParameter);
            }
            
            if ABSOLUTE_POS_OF_TABLE_AREA + (item_slot_size * num_keys) > table_region_size {
                let required: usize = (ABSOLUTE_POS_OF_TABLE_AREA + (item_slot_size * num_keys)) as usize;
                return Err(KvError::RegionTooSmall {required, actual: table_region_size as usize});
            }

            assume(false);
            // replay log entries onto the item table
            Self::replay_log_item_table(wrpm_region, item_table_id, log_entries, item_slot_size, Tracked(perm), Ghost(state))?;

            // reborrow to satisfy the borrow checker
            let pm_region = wrpm_region.get_pm_region_ref();
            let ghost mem = pm_region@.committed();

            // read the valid bits of each slot and set up the allocator
            let mut item_table_allocator: Vec<u64> = Vec::with_capacity(num_keys as usize);

            for index in 0..num_keys {
                assume(false);
                let item_slot_offset = ABSOLUTE_POS_OF_TABLE_AREA + index * item_slot_size;
                let cdb_addr = item_slot_offset + RELATIVE_POS_OF_VALID_CDB;
                let ghost cdb_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| cdb_addr + i);
                let ghost true_cdb = u64::spec_from_bytes(mem.subrange(cdb_addr as int, cdb_addr + u64::spec_size_of()));
                let cdb = pm_region.read_aligned::<u64>(cdb_addr).map_err(|e| KvError::PmemErr { pmem_err: e })?;
                match check_cdb(cdb, Ghost(mem),
                            Ghost(pm_region.constants().impervious_to_corruption),
                            Ghost(cdb_addrs)) {
                    Some(false) => item_table_allocator.push(index),
                    Some(true) => {}
                    None => return Err(KvError::CRCMismatch)
                }
            }

            Ok(Self {
                item_size,
                item_slot_size,
                num_keys,
                free_list: item_table_allocator,
                state: Ghost(state)
            })
        }

        pub exec fn play_item_log<PM, L>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedItemTablePermission, PM>,
            table_id: u128,
            log_entries: &Vec<OpLogEntryType<L>>,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
            Ghost(state): Ghost<DurableItemTableView<I>>
        ) -> (result: Result<(), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
                L: PmCopy,
            requires 
                // TODO
            ensures 
                // TODO 
        {
            Self::replay_log_item_table(wrpm_region, table_id, log_entries, self.item_slot_size, Tracked(perm), Ghost(state))?;
            // replay_log_item_table cannot add newly-invalidated metadata entries back into the allocator,
            // because it doesn't (and can't) take &mut self, so as a quick fix we'll just iterate over the log again.
            // TODO: refactor so this happens in the same pass as is used in replay_log_item_table

            for i in 0..log_entries.len() 
            {
                assume(false);
                let log_entry = &log_entries[i];

                if let OpLogEntryType::ItemTableEntryInvalidate { item_index } = log_entry {
                    self.free_list.push(*item_index);
                }
            }

            Ok(())
        }

        exec fn replay_log_item_table<PM, L>(
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedItemTablePermission, PM>,
            table_id: u128,
            log_entries: &Vec<OpLogEntryType<L>>,
            item_slot_size: u64,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
            Ghost(state): Ghost<DurableItemTableView<I>>
        ) -> (result: Result<(), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
                L: PmCopy,
            requires 
                // TODO
            ensures 
                // TODO 
        {
            // There are only two types of operation that need to be replayed onto the item table:
            // item commit and item invalidation. So we just need to determine the item index updated
            // by each log entry and what we need to set the CDB to.
            for i in 0..log_entries.len() 
                invariant 
                    // TODO
            {
                assume(false);
                let log_entry = &log_entries[i];

                let result = match log_entry {
                    OpLogEntryType::ItemTableEntryCommit { item_index } => Some((CDB_TRUE, item_index)),
                    OpLogEntryType::ItemTableEntryInvalidate { item_index } => Some((CDB_FALSE, item_index)),
                    _ => None  // the other operations do not modify the item table
                };

                if let Some((cdb_val, item_index)) = result {
                    // the slot offset is also the address of the CDB
                    let item_slot_offset = ABSOLUTE_POS_OF_TABLE_AREA + item_index * item_slot_size;
                    wrpm_region.serialize_and_write(item_slot_offset, &cdb_val, Tracked(perm));
                }
            }
            Ok(())
        }

        // this function can be used to both create new items and do COW updates to existing items.
        // must always write to an invalid slot
        // this operation is NOT directly logged
        // returns the index of the slot that the item was written to
        pub exec fn tentatively_write_item<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedItemTablePermission, PM>,
            Ghost(item_table_id): Ghost<u128>,
            item: &I,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
        ) -> (result: Result<u64, KvError<K>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(wrpm_region).inv(),
                forall |i: int|  0 <= i < old(self).spec_free_list().len() ==>
                    0 <= #[trigger] old(self).spec_free_list()[i] < old(self).spec_num_keys(),
                ({
                    let item_slot_size = old(self).spec_item_size() + u64::spec_size_of() + u64::spec_size_of();
                    let metadata_header_size = ItemTableMetadata::spec_size_of() + u64::spec_size_of();
                    &&& 0 <= item_slot_size < usize::MAX
                    &&& 0 <= item_slot_size * old(self).spec_num_keys() < usize::MAX
                    &&& 0 <= metadata_header_size + (item_slot_size * old(self).spec_num_keys()) < usize::MAX
                })
                // TODO
            ensures
                wrpm_region.inv()
                // TODO
        {
            // pop a free index from the free list
            assume(false);
            let free_index = match self.free_list.pop() {
                Some(index) => index,
                None => return Err(KvError::OutOfSpace)
            };
            assert(free_index < self.num_keys);
            let item_slot_size = (self.item_size as usize + traits_t::size_of::<u64>() + traits_t::size_of::<u64>()) as u64;
            let item_slot_offset = ABSOLUTE_POS_OF_TABLE_AREA + free_index * item_slot_size;
            let crc_addr = item_slot_offset + traits_t::size_of::<u64>() as u64;
            let item_addr = crc_addr + traits_t::size_of::<u64>() as u64;

            // calculate and write the CRC of the provided item
            let crc = calculate_crc(item);
            wrpm_region.serialize_and_write(crc_addr, &crc, Tracked(perm));
            // write the item itself
            wrpm_region.serialize_and_write(item_addr, item, Tracked(perm));

            Ok(free_index)
        }

        // makes a slot valid by setting its valid bit.
        // must log the operation before calling this function
        pub exec fn commit_item<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedItemTablePermission, PM>,
            item_table_id: u128,
            item_table_index: u64,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
        ) -> (result: Result<(), KvError<K>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(wrpm_region).inv(),
                ({
                    let item_slot_size = old(self).spec_item_size() + u64::spec_size_of() + u64::spec_size_of();
                    let metadata_header_size = ItemTableMetadata::spec_size_of() + u64::spec_size_of();
                    &&& 0 <= item_slot_size < usize::MAX
                    &&& 0 <= item_slot_size * old(self).spec_num_keys() < usize::MAX
                    &&& 0 <= metadata_header_size + (item_slot_size * old(self).spec_num_keys()) < usize::MAX
                })
                // TODO: item update must have been logged
            ensures
                wrpm_region.inv(),
                // TODO
        {
            assume(false);
            let item_slot_size = (self.item_size as usize + traits_t::size_of::<u64>() + traits_t::size_of::<u64>()) as u64;
            let item_slot_offset = ABSOLUTE_POS_OF_TABLE_AREA + item_table_index * item_slot_size;
            wrpm_region.serialize_and_write(item_slot_offset + RELATIVE_POS_OF_VALID_CDB, &CDB_TRUE, Tracked(perm));
            Ok(())
        }

        // Read an item from the item table given an index. Returns `None` if the index is 
        // does not contain a valid, uncorrupted item. 
        // TODO: should probably return result, not option
        pub exec fn read_item<PM>(
            &self,
            pm_region: &PM,
            item_table_id: u128,
            item_table_index: u64,
        ) -> (result: Result<Box<I>, KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                // TODO 
            ensures 
                // TODO 
        {
            assume(false);
            let ghost impervious_to_corruption = pm_region.constants().impervious_to_corruption;
            // TODO: store slot size so we don't have to calculate it each time
            let item_slot_size = (self.item_size as usize + traits_t::size_of::<u64>() + traits_t::size_of::<u64>()) as u64;
            let item_slot_offset = ABSOLUTE_POS_OF_TABLE_AREA + item_table_index * item_slot_size;

            let cdb_addr = item_slot_offset;
            let crc_addr = cdb_addr + traits_t::size_of::<u64>() as u64;
            let item_addr = crc_addr + traits_t::size_of::<u64>() as u64; 
            // Read the item and CRC at this slot
            let ghost mem = pm_region@.committed();

            let ghost true_cdb_bytes = extract_bytes(mem, cdb_addr as nat, u64::spec_size_of());
            let ghost true_crc_bytes = extract_bytes(mem, crc_addr as nat, u64::spec_size_of());
            let ghost true_item_bytes = extract_bytes(mem, item_addr as nat, I::spec_size_of());

            let ghost true_cdb = u64::spec_from_bytes(true_cdb_bytes);
            let ghost true_crc = u64::spec_from_bytes(true_crc_bytes);
            let ghost true_item = I::spec_from_bytes(true_item_bytes);

            let ghost cdb_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| cdb_addr + i);
            let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| crc_addr + i);
            let ghost item_addrs = Seq::new(I::spec_size_of() as nat, |i: int| item_addr + i);

            let cdb = match pm_region.read_aligned::<u64>(cdb_addr) {
                Ok(val) => val,
                Err(e) => return Err(KvError::PmemErr { pmem_err: e })
            };
            let crc = match pm_region.read_aligned::<u64>(crc_addr) {
                Ok(val) => val,
                Err(e) => return Err(KvError::PmemErr { pmem_err: e })
            };
            let item = match pm_region.read_aligned::<I>(item_addr) {
                Ok(val) => val,
                Err(e) => return Err(KvError::PmemErr { pmem_err: e })
            };
            // Check that the CDB is uncorrupted and indicates that the item is valid
            match check_cdb(cdb, Ghost(mem), Ghost(impervious_to_corruption), Ghost(cdb_addrs)) {
                Some(true) => {
                    // The CDB is valid. Check the item's CRC 
                    if !check_crc(item.as_slice(), crc.as_slice(), Ghost(mem), 
                        Ghost(impervious_to_corruption), Ghost(item_addrs), Ghost(crc_addrs)) 
                    {
                        Err(KvError::CRCMismatch)
                    } else {
                        let item = item.extract_init_val(Ghost(true_item), Ghost(true_item_bytes), Ghost(impervious_to_corruption));
                        Ok(item)
                    }
                }
                Some(false) => Err(KvError::EntryIsNotValid),
                _ => {
                    Err(KvError::CRCMismatch) // the CDB has been corrupted
                }

            }
        }

        // clears the valid bit for an entry. this should also
        // deallocate it
        pub exec fn invalidate_item<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedItemTablePermission, PM>,
            item_table_id: u128,
            item_table_index: u64,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
        ) -> (result: Result<(), KvError<K>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(wrpm_region).inv(),
                // TODO: item invalidation must have been logged
            ensures
                wrpm_region.inv(),
                // TODO
        {
            assume(false);
            let item_slot_size = (self.item_size as usize + traits_t::size_of::<u64>() + traits_t::size_of::<u64>()) as u64;
            let item_slot_offset = ABSOLUTE_POS_OF_TABLE_AREA + item_table_index * item_slot_size;
            wrpm_region.serialize_and_write(item_slot_offset + RELATIVE_POS_OF_VALID_CDB, &CDB_FALSE, Tracked(perm));
            Ok(())
        }

        pub fn write_setup_metadata<PM>(pm_region: &mut PM, num_keys: u64)
        where
            PM: PersistentMemoryRegion,
        requires
            old(pm_region).inv(),
            old(pm_region)@.len() == 1,
            old(pm_region)@.no_outstanding_writes(),
            ({
                let item_size = I::spec_size_of() + u64::spec_size_of() + u64::spec_size_of();
                let metadata_header_size = ItemTableMetadata::spec_size_of() + u64::spec_size_of();
                old(pm_region)@.len() >= metadata_header_size + (item_size * num_keys)
            })
            // TODO: precondition that the region is large enough
        ensures
            pm_region.inv(),
            // TODO: postcondition that the table is set up correctly
    {
        // Initialize metadata header and compute its CRC
        let metadata_header = ItemTableMetadata {
            version_number: ITEM_TABLE_VERSION_NUMBER,
            item_size: I::size_of() as u64,
            num_keys,
            _padding: 0,
            program_guid: ITEM_TABLE_PROGRAM_GUID,
        };
        let metadata_crc = calculate_crc(&metadata_header);

        let metadata_header_addr = ABSOLUTE_POS_OF_METADATA_HEADER;
        let crc_addr = metadata_header_addr + traits_t::size_of::<ItemTableMetadata>() as u64;

        pm_region.serialize_and_write(metadata_header_addr, &metadata_header);
        pm_region.serialize_and_write(crc_addr, &metadata_crc);
    }

    pub fn read_table_metadata<PM>(pm_region: &PM, table_id: u128) -> (result: Result<Box<ItemTableMetadata>, KvError<K>>)
        where
            PM: PersistentMemoryRegion,
        requires
            pm_region.inv()
            // TODO: finish writing preconditions
        ensures
            match result {
                Ok(output_table) => {
                    let item_slot_size = I::spec_size_of() + u64::spec_size_of() + u64::spec_size_of();
                    let metadata_header_size = ItemTableMetadata::spec_size_of() + u64::spec_size_of();
                    let num_keys = output_table.num_keys;
                    &&& 0 <= item_slot_size < usize::MAX
                    &&& 0 <= item_slot_size * num_keys < usize::MAX
                    &&& 0 <= metadata_header_size + (item_slot_size * num_keys) < usize::MAX
                    &&& output_table.item_size == I::spec_size_of()

                }
                Err(_) => true
            }
            // TODO: finish writing postconditions
        {
            assume(false);

            let ghost mem = pm_region@.committed();

            // read in the metadata structure and its CRC, make sure it has not been corrupted

            let ghost true_metadata_table = ItemTableMetadata::spec_from_bytes(mem.subrange(ABSOLUTE_POS_OF_METADATA_HEADER as int, ABSOLUTE_POS_OF_METADATA_HEADER + ItemTableMetadata::spec_size_of()));
            let ghost true_crc = u64::spec_from_bytes(mem.subrange(ABSOLUTE_POS_OF_HEADER_CRC as int, ABSOLUTE_POS_OF_HEADER_CRC + u64::spec_size_of()));

            let metadata_header_addr = ABSOLUTE_POS_OF_METADATA_HEADER;
            let crc_addr = metadata_header_addr + traits_t::size_of::<ItemTableMetadata>() as u64;

            let table_metadata = pm_region.read_aligned::<ItemTableMetadata>(metadata_header_addr).map_err(|e| KvError::PmemErr { pmem_err: e })?;
            let table_crc = pm_region.read_aligned::<u64>(crc_addr).map_err(|e| KvError::PmemErr { pmem_err: e })?;

            let ghost header_addrs = Seq::new(ItemTableMetadata::spec_size_of() as nat, |i: int| ABSOLUTE_POS_OF_METADATA_HEADER + i);
            let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| ABSOLUTE_POS_OF_HEADER_CRC + i);

            let ghost true_header_bytes = Seq::new(ItemTableMetadata::spec_size_of() as nat, |i: int| mem[header_addrs[i]]);
            let ghost true_crc_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem[crc_addrs[i]]);

            if !check_crc(table_metadata.as_slice(), table_crc.as_slice(), Ghost(mem),
                    Ghost(pm_region.constants().impervious_to_corruption),
                    Ghost(header_addrs), 
                    Ghost(crc_addrs)) {
                return Err(KvError::CRCMismatch);
            }

            let table_metadata = table_metadata.extract_init_val(
                Ghost(true_metadata_table),
                Ghost(true_header_bytes),
                Ghost(pm_region.constants().impervious_to_corruption),
            );

            // Since we've already checked for corruption, this condition should never fail
            if {
                ||| table_metadata.program_guid != ITEM_TABLE_PROGRAM_GUID
                ||| table_metadata.version_number != ITEM_TABLE_VERSION_NUMBER
                ||| table_metadata.item_size != I::size_of() as u64
            } {
                return Err(KvError::InvalidItemTableHeader);
            }

            return Ok(table_metadata);
        }
        */
    }
}
