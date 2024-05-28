use crate::kv::durable::itemtable::itemtablespec_t::*;
use crate::kv::durable::itemtable::layout_v::*;
use crate::kv::durable::logentry_t::*;
use crate::kv::kvimpl_t::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::serialization_t::*;
use crate::pmem::wrpm_t::*;
use builtin::*;
use builtin_macros::*;
use std::hash::Hash;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {
    pub struct DurableItemTable<K, I, E>
        where
            K: Hash + Eq + Clone + Serializable + Sized + std::fmt::Debug,
            I: Serializable + Item<K> + Sized + std::fmt::Debug,
            E: std::fmt::Debug,
    {
        _phantom: Ghost<core::marker::PhantomData<E>>,
        item_size: u64,
        num_keys: u64,
        free_list: Vec<u64>,
        state: Ghost<DurableItemTableView<I, K, E>>,
    }

    // // TODO: make a PR to Verus
    // #[verifier::opaque]
    // pub open spec fn filter_map<A, B>(seq: Seq<A>, pred: spec_fn(A) -> Option<B>) -> Seq<B>
    //     decreases seq.len()
    // {
    //     if seq.len() == 0 {
    //         Seq::<B>::empty()
    //     } else {
    //         let subseq = filter_map(seq.drop_last(), pred);
    //         let last = pred(seq.last());
    //         if let Some(last) = last {
    //             subseq.push(last)
    //         } else {
    //             subseq
    //         }
    //     }
    // }

    impl<K, I, E> DurableItemTable<K, I, E>
        where
            K: Hash + Eq + Clone + Serializable + Sized + std::fmt::Debug,
            I: Serializable + Item<K> + Sized + std::fmt::Debug,
            E: std::fmt::Debug,
    {
        pub closed spec fn view(self) -> DurableItemTableView<I, K, E>
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

        pub closed spec fn recover<L>(
            mem: Seq<u8>,
            op_log: Seq<OpLogEntryType<L>>,
            kvstore_id: u128
        ) -> Option<DurableItemTableView<I, K, E>>
            where 
                L: Serializable,
        {
            if mem.len() < ABSOLUTE_POS_OF_TABLE_AREA {
                // If the memory is not large enough to store the metadata header,
                // it is not valid
                None
            }
            else {
                // the metadata header is immutable, so we can check that it is valid before 
                // doing any log replay
                let metadata_header_bytes = mem.subrange(
                    ABSOLUTE_POS_OF_METADATA_HEADER as int,
                    ABSOLUTE_POS_OF_METADATA_HEADER + LENGTH_OF_METADATA_HEADER
                );
                let crc_bytes = mem.subrange(
                    ABSOLUTE_POS_OF_HEADER_CRC as int,
                    ABSOLUTE_POS_OF_HEADER_CRC + 8
                );
                let metadata_header = ItemTableMetadata::spec_deserialize(metadata_header_bytes);
                let crc = u64::spec_deserialize(crc_bytes);
                if crc != metadata_header.spec_crc() {
                    // The header is invalid if the stored CRC does not match the contents
                    // of the metadata header
                    None
                } else {
                    // replay the log on `mem`, then parse it into (hopefully) a valid item table view
                    let mem = Self::replay_log_item_table(mem, op_log);
                    parse_item_table(metadata_header, mem)
                }
            }

        }

        // Recursively apply log operations to the item table bytes. Skips all log entries that 
        // do not modify the item table.
        // TODO: check length of `mem`?
        closed spec fn replay_log_item_table<L>(mem: Seq<u8>, op_log: Seq<OpLogEntryType<L>>) -> Seq<u8>
            where 
                L: Serializable,
            decreases op_log.len(),
        {
            if op_log.len() == 0 {
                mem
            } else {
                let current_op = op_log[0];
                let op_log = op_log.drop_first();
                let mem = Self::apply_log_op_to_item_table_mem(mem, current_op);
                Self::replay_log_item_table(mem, op_log)
            }
        }

        // TODO: refactor -- logic in both cases is the same
        closed spec fn apply_log_op_to_item_table_mem<L>(mem: Seq<u8>, op: OpLogEntryType<L>) -> Seq<u8>
            where 
                L: Serializable,
        {
            let item_entry_size = I::spec_serialized_len() + CRC_SIZE + CDB_SIZE + K::spec_serialized_len();
            match op {
                OpLogEntryType::ItemTableEntryCommit { item_index, metadata_index, metadata_crc } => {
                    let entry_offset = ABSOLUTE_POS_OF_TABLE_AREA + item_index * item_entry_size;
                    let addr = entry_offset + RELATIVE_POS_OF_VALID_CDB;
                    let valid_cdb = spec_u64_to_le_bytes(CDB_TRUE);
                    let mem = mem.map(|pos: int, pre_byte: u8| 
                                                        if addr <= pos < addr + valid_cdb.len() { valid_cdb[pos - addr]}
                                                        else { pre_byte }
                                                    );
                    mem
                }
                OpLogEntryType::ItemTableEntryInvalidate { item_index } => {
                    let entry_offset = ABSOLUTE_POS_OF_TABLE_AREA + item_index * item_entry_size;
                    let addr = entry_offset + RELATIVE_POS_OF_VALID_CDB;
                    let invalid_cdb = spec_u64_to_le_bytes(CDB_FALSE);
                    let mem = mem.map(|pos: int, pre_byte: u8| 
                                                        if addr <= pos < addr + invalid_cdb.len() { invalid_cdb[pos - addr]}
                                                        else { pre_byte }
                                                    );
                    mem
                }
                OpLogEntryType::CommitMetadataEntry{metadata_index, item_index} => {
                    // committing a metadata entry implies that the corresponding item needs to be committed as well
                    let entry_offset = ABSOLUTE_POS_OF_TABLE_AREA + item_index * item_entry_size;
                    let addr = entry_offset + RELATIVE_POS_OF_VALID_CDB;
                    let valid_cdb = spec_u64_to_le_bytes(CDB_TRUE);
                    let mem = mem.map(|pos: int, pre_byte: u8| 
                                                        if addr <= pos < addr + valid_cdb.len() { valid_cdb[pos - addr]}
                                                        else { pre_byte }
                                                    );
                    mem
                }
                _ => mem
            }
        }

        // TODO: write invariants
        closed spec fn inv(self) -> bool;

        pub exec fn setup<PM>(
            pm_region: &mut PM,
            item_table_id: u128,
            num_keys: u64,
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(pm_region).inv(),
                0 <= ItemTableMetadata::spec_serialized_len() + CRC_SIZE < usize::MAX,
                ({
                    let item_slot_size = I::spec_serialized_len() + CDB_SIZE + CRC_SIZE;
                    &&& 0 <= item_slot_size < usize::MAX
                    &&& 0 <= item_slot_size * num_keys < usize::MAX
                    &&& 0 <= ABSOLUTE_POS_OF_TABLE_AREA + (item_slot_size * num_keys) < usize::MAX
                })
            ensures
                pm_region.inv(),
                pm_region@.no_outstanding_writes(),
                // TODO: write the rest of the postconditions
        {
            let item_size = I::serialized_len();

            // ensure that there are no outstanding writes
            pm_region.flush();

            let table_region_size = pm_region.get_region_size();
            // determine if the provided region is large enough for the
            // specified number of items
            let item_slot_size = item_size + CDB_SIZE + CRC_SIZE;
            if ABSOLUTE_POS_OF_TABLE_AREA + (item_slot_size * num_keys) > table_region_size {
                let required: usize = (ABSOLUTE_POS_OF_TABLE_AREA + (item_slot_size * num_keys)) as usize;
                return Err(KvError::RegionTooSmall {required, actual: table_region_size as usize});
            }

            assume(false);
            Self::write_setup_metadata(pm_region, num_keys);

            // we also have to set all of the valid bits of the item table slots
            // to 0 so they are not accidentally interpreted as being in use
            // TODO: move this into setup...
            // TODO: these invariants are tricky, probably because they involve nonlinear arithmetic?
            for index in 0..num_keys
                // invariant
                //     index <= num_keys,
                //     0 <= index * item_slot_size < ABSOLUTE_POS_OF_TABLE_AREA + index * item_slot_size <= table_region_size,
            {
                assume(false);
                let item_slot_offset = ABSOLUTE_POS_OF_TABLE_AREA + index * item_slot_size;
                pm_region.serialize_and_write(item_slot_offset + RELATIVE_POS_OF_VALID_CDB, &CDB_FALSE);
            }
            pm_region.flush();

            Ok(())
        }

        // TODO: this function doesn't do anything with state right now
        pub exec fn start<PM>(
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedItemTablePermission, PM>,
            item_table_id: u128,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
            Ghost(state): Ghost<DurableItemTableView<I, K, E>>
        ) -> (result: Result<Self, KvError<K, E>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(wrpm_region).inv(),
                0 <= ItemTableMetadata::spec_serialized_len() + CRC_SIZE < usize::MAX,
                ({
                    let item_slot_size = I::spec_serialized_len() + CDB_SIZE + CRC_SIZE;
                    let metadata_header_size = ItemTableMetadata::spec_serialized_len() + CRC_SIZE;
                    &&& 0 <= item_slot_size < usize::MAX
                })
                // TODO: recovery and permissions checks
            ensures
                wrpm_region.inv(),
                // TODO: write the rest of the postconditions
        {
            let item_size = I::serialized_len();

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


            let num_keys = table_metadata.num_keys;
            // determine if the provided region is large enough for the
            // specified number of items
            let item_slot_size = item_size + CDB_SIZE + CRC_SIZE;
            if ABSOLUTE_POS_OF_TABLE_AREA + (item_slot_size * num_keys) > table_region_size {
                let required: usize = (ABSOLUTE_POS_OF_TABLE_AREA + (item_slot_size * num_keys)) as usize;
                return Err(KvError::RegionTooSmall {required, actual: table_region_size as usize});
            }

            assume(false);

            // read the valid bits of each slot and set up the allocator
            let mut item_table_allocator: Vec<u64> = Vec::with_capacity(num_keys as usize);

            for index in 0..num_keys {
                assume(false);
                let item_slot_offset = ABSOLUTE_POS_OF_TABLE_AREA + index * item_slot_size;
                let cdb_addr = item_slot_offset + RELATIVE_POS_OF_VALID_CDB;
                let val: &u64 = pm_region.read_and_deserialize(cdb_addr);
                match check_cdb(&val, Ghost(mem),
                            Ghost(pm_region.constants().impervious_to_corruption),
                            Ghost(cdb_addr)) {
                    Some(false) => item_table_allocator.push(index),
                    Some(true) => {}
                    None => return Err(KvError::CRCMismatch)
                }
            }

            Ok(Self {
                _phantom: Ghost(spec_phantom_data()),
                item_size,
                num_keys,
                free_list: item_table_allocator,
                state: Ghost(state)
            })
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
        ) -> (result: Result<u64, KvError<K, E>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(wrpm_region).inv(),
                forall |i: int|  0 <= i < old(self).spec_free_list().len() ==>
                    0 <= #[trigger] old(self).spec_free_list()[i] < old(self).spec_num_keys(),
                ({
                    let item_slot_size = old(self).spec_item_size() + CDB_SIZE + CRC_SIZE;
                    let metadata_header_size = ItemTableMetadata::spec_serialized_len() + CRC_SIZE;
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
            let item_slot_size = self.item_size + CDB_SIZE + CRC_SIZE;
            let item_slot_offset = ABSOLUTE_POS_OF_TABLE_AREA + free_index * item_slot_size;

            // calculate and write the CRC of the provided item
            let crc = calculate_crc(item);
            wrpm_region.serialize_and_write(item_slot_offset + RELATIVE_POS_OF_ITEM_CRC, &crc, Tracked(perm));
            // write the item itself
            wrpm_region.serialize_and_write(item_slot_offset + RELATIVE_POS_OF_ITEM, item, Tracked(perm));

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
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(wrpm_region).inv(),
                ({
                    let item_slot_size = old(self).spec_item_size() + CDB_SIZE + CRC_SIZE;
                    let metadata_header_size = ItemTableMetadata::spec_serialized_len() + CRC_SIZE;
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
            let item_slot_size = self.item_size + CDB_SIZE + CRC_SIZE;
            let item_slot_offset = ABSOLUTE_POS_OF_TABLE_AREA + item_table_index * item_slot_size;
            wrpm_region.serialize_and_write(item_slot_offset + RELATIVE_POS_OF_VALID_CDB, &CDB_TRUE, Tracked(perm));
            Ok(())
        }

        // clears the valid bit for an entry. this should also
        // deallocate it
        pub exec fn invalidate_item<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedItemTablePermission, PM>,
            item_table_id: u128,
            item_table_index: u64,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
        ) -> (result: Result<(), KvError<K, E>>)
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
            let item_slot_size = self.item_size + CDB_SIZE + CRC_SIZE;
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
                let item_size = I::spec_serialized_len() + CDB_SIZE + CRC_SIZE;
                let metadata_header_size = ItemTableMetadata::spec_serialized_len() + CRC_SIZE;
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
            item_size: I::serialized_len(),
            num_keys,
            _padding: 0,
            program_guid: ITEM_TABLE_PROGRAM_GUID,
        };
        let metadata_crc = calculate_crc(&metadata_header);

        pm_region.serialize_and_write(ABSOLUTE_POS_OF_METADATA_HEADER, &metadata_header);
        pm_region.serialize_and_write(ABSOLUTE_POS_OF_HEADER_CRC, &metadata_crc);
    }

    pub fn read_table_metadata<PM>(pm_region: &PM, table_id: u128) -> (result: Result<&ItemTableMetadata, KvError<K, E>>)
        where
            PM: PersistentMemoryRegion,
        requires
            pm_region.inv()
            // TODO: finish writing preconditions
        ensures
            match result {
                Ok(output_table) => {
                    let item_slot_size = I::spec_serialized_len() + CDB_SIZE + CRC_SIZE;
                    let metadata_header_size = ItemTableMetadata::spec_serialized_len() + CRC_SIZE;
                    let num_keys = output_table.num_keys;
                    &&& 0 <= item_slot_size < usize::MAX
                    &&& 0 <= item_slot_size * num_keys < usize::MAX
                    &&& 0 <= metadata_header_size + (item_slot_size * num_keys) < usize::MAX
                    &&& output_table.item_size == I::spec_serialized_len()

                }
                Err(_) => true
            }
            // TODO: finish writing postconditions
        {
            assume(false);

            let ghost mem = pm_region@.committed();

            // read in the metadata structure and its CRC, make sure it has not been corrupted
            let table_metadata: &ItemTableMetadata = pm_region.read_and_deserialize(ABSOLUTE_POS_OF_METADATA_HEADER);
            let table_crc = pm_region.read_and_deserialize(ABSOLUTE_POS_OF_HEADER_CRC);

            let ghost header_addrs = Seq::new(ItemTableMetadata::spec_serialized_len(), |i: int| ABSOLUTE_POS_OF_METADATA_HEADER + i);
            let ghost crc_addrs = Seq::new(CRC_SIZE as nat, |i: int| ABSOLUTE_POS_OF_HEADER_CRC + i);

            if !check_crc_deserialized2(table_metadata, table_crc, Ghost(mem),
                    Ghost(pm_region.constants().impervious_to_corruption),
                    Ghost(header_addrs), 
                    Ghost(crc_addrs)) {
                return Err(KvError::CRCMismatch);
            }

            // Since we've already checked for corruption, this condition should never fail
            if {
                ||| table_metadata.program_guid != ITEM_TABLE_PROGRAM_GUID
                ||| table_metadata.version_number != ITEM_TABLE_VERSION_NUMBER
                ||| table_metadata.item_size != I::serialized_len()
            } {
                return Err(KvError::InvalidItemTableHeader);
            }

            return Ok(table_metadata);
        }

    }
}
