use crate::kv::durable::itemtable::itemtablespec_t::*;
use crate::kv::durable::itemtable::layout_v::*;
use crate::kv::durable::oplog::oplogspec_t::*;
use crate::kv::kvimpl_t::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::serialization_t::*;
use crate::pmem::wrpm_v::*;
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
        _phantom: Ghost<core::marker::PhantomData<(K, I, E)>>,
        item_size: u64,
        num_keys: u64,
        free_list: Vec<u64>,
        state: Ghost<DurableItemTableView<I>>,
    }

    // TODO: make a PR to Verus
    #[verifier::opaque]
    pub open spec fn filter_map<A, B>(seq: Seq<A>, pred: spec_fn(A) -> Option<B>) -> Seq<B>
        decreases seq.len()
    {
        if seq.len() == 0 {
            Seq::<B>::empty()
        } else {
            let subseq = filter_map(seq.drop_last(), pred);
            let last = pred(seq.last());
            if let Some(last) = last {
                subseq.push(last)
            } else {
                subseq
            }
        }
    }

    impl<K, I, E> DurableItemTable<K, I, E>
        where
            K: Hash + Eq + Clone + Serializable + Sized + std::fmt::Debug,
            I: Serializable + Item<K> + Sized + std::fmt::Debug,
            E: std::fmt::Debug,
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

        // TODO: this really only needs to take a Seq<u8> but this is still backed
        // by pm region*s*
        // TODO: Refactor -- this is huge
        // TODO: this may not be correct if it's possible to insert/commit and remove the same index in the same
        // transaction. I don't expect that to ever be necessary so we should explicitly prevent it to ensure this
        // spec is correct.
        pub closed spec fn recover(mems: Seq<Seq<u8>>, op_log: Seq<OpLogEntryType>, kvstore_id: u128) -> Option<DurableItemTableView<I>>
        {
            // The item table only uses one region
            if mems.len() != 1 {
                None
            } else {
                let mem = mems[0];
                if mem.len() < ABSOLUTE_POS_OF_TABLE_AREA {
                    // If the memory is not large enough to store the metadata header,
                    // it is not valid
                    None
                }
                else {
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
                        if metadata_header.program_guid != ITEM_TABLE_PROGRAM_GUID {
                            // The header must contain the correct GUID; if it doesn't, then
                            // this structure wasn't created by this program.
                            None
                        } else if metadata_header.version_number == 1 {
                            // If the metadata was written by version #1 of this code, then this
                            // is how to interpret it:

                            // The header is invalid if it isn't large enough to contain an entry
                            // for each key, or if the specified item size doesn't match the serialized
                            // len of `I`.
                            if {
                                ||| metadata_header.item_size != I::spec_serialized_len()
                                ||| mem.len() < ABSOLUTE_POS_OF_TABLE_AREA + (metadata_header.item_size + CRC_SIZE + CDB_SIZE) * metadata_header.num_keys
                            } {
                                None
                            } else {
                                // TODO: Can we simplify this logic? It's pretty complicated for a spec function
                                let table_area = mem.subrange(ABSOLUTE_POS_OF_TABLE_AREA as int, mem.len() as int);
                                let item_entry_size = metadata_header.item_size + CRC_SIZE + CDB_SIZE;
                                // split `mem` into a map where table indices map to the bytes in that slot
                                let item_slot_bytes = Map::new(|i: int| 0 <= i < metadata_header.num_keys, |i: int| {
                                    mem.subrange(i * item_entry_size, i * item_entry_size + item_entry_size)
                                });
                                let indexes_to_insert = filter_map(op_log, |entry: OpLogEntryType| {
                                    match entry {
                                        OpLogEntryType::ItemTableEntryCommit {table_index} => Some(table_index),
                                        _ => None
                                    }
                                });
                                let indexes_to_remove = filter_map(op_log, |entry: OpLogEntryType| {
                                    match entry {
                                        OpLogEntryType::ItemTableEntryInvalidate {table_index} => Some(table_index),
                                        _ => None
                                    }
                                });
                                // determine the list of indices that are *not* live (i.e., are invalid
                                // and are not updated by a log entry, or are invalidated by a log entry)
                                let filter_indices = item_slot_bytes.dom().filter(|i: int| {
                                    let item_bytes = item_slot_bytes[i];
                                    let valid = spec_u64_from_le_bytes(item_bytes.subrange(
                                        RELATIVE_POS_OF_VALID_CDB as int,
                                        RELATIVE_POS_OF_VALID_CDB + CDB_SIZE
                                    ));

                                    indexes_to_remove.contains(i as u64) || (valid == CDB_FALSE && !indexes_to_insert.contains(i as u64))
                                });
                                // remove non-live indices
                                let item_slot_bytes = item_slot_bytes.remove_keys(filter_indices);
                                // convert byte sequence values to view elements
                                let items = item_slot_bytes.map_entries(|i: int, bytes: Seq<u8> | {
                                    let crc = u64::spec_deserialize(bytes.subrange(RELATIVE_POS_OF_ITEM_CRC as int, RELATIVE_POS_OF_ITEM_CRC + 8));
                                    let item = I::spec_deserialize(bytes.subrange(RELATIVE_POS_OF_ITEM as int, RELATIVE_POS_OF_ITEM + metadata_header.item_size));
                                    DurableItemTableViewEntry::new(crc, item)
                                });
                                Some(DurableItemTableView::new(items))
                            }
                        } else {
                            // Version #1 is currently the only valid version; return None if we see any other versions
                            None
                        }
                    }
                }
            }
        }

        // TODO: write invariants
        closed spec fn inv(self) -> bool;

        pub exec fn setup<PM>(
            pm_regions: &mut PM,
            item_table_id: u128,
            num_keys: u64,
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegions,
            requires
                old(pm_regions).inv(),
                old(pm_regions)@.len() == 1,
                0 <= ItemTableMetadata::spec_serialized_len() + CRC_SIZE < usize::MAX,
                ({
                    let item_slot_size = I::spec_serialized_len() + CDB_SIZE + CRC_SIZE;
                    &&& 0 <= item_slot_size < usize::MAX
                    &&& 0 <= item_slot_size * num_keys < usize::MAX
                    &&& 0 <= ABSOLUTE_POS_OF_TABLE_AREA + (item_slot_size * num_keys) < usize::MAX
                })
            ensures
                pm_regions.inv(),
                pm_regions@.no_outstanding_writes(),
                // TODO: write the rest of the postconditions
        {
            let item_size = I::serialized_len();

            // ensure that there are no outstanding writes
            pm_regions.flush();

            // check that the caller only passsed in one region
            let region_sizes = get_region_sizes(pm_regions);
            let num_regions = region_sizes.len();
            if num_regions < 1 {
                return Err(KvError::TooFewRegions {required: 1, actual: num_regions});
            } else if num_regions > 1 {
                return Err(KvError::TooManyRegions {required: 1, actual: num_regions});
            }

            let table_region_size = region_sizes[0];
            // determine if the provided region is large enough for the
            // specified number of items
            let item_slot_size = item_size + CDB_SIZE + CRC_SIZE;
            if ABSOLUTE_POS_OF_TABLE_AREA + (item_slot_size * num_keys) > table_region_size {
                let required: usize = (ABSOLUTE_POS_OF_TABLE_AREA + (item_slot_size * num_keys)) as usize;
                let actual: usize = region_sizes[0] as usize;
                return Err(KvError::RegionTooSmall {required, actual});
            }

            assume(false);
            Self::write_setup_metadata(pm_regions, num_keys);

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
                pm_regions.serialize_and_write(0, item_slot_offset, &CDB_FALSE);
            }
            pm_regions.flush();

            Ok(())
        }

        // TODO: this function doesn't do anything with state right now
        pub exec fn start<PM>(
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedItemTablePermission, PM>,
            item_table_id: u128,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
            Ghost(state): Ghost<DurableItemTableView<I>>
        ) -> (result: Result<Self, KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(wrpm_regions).inv(),
                0 <= ItemTableMetadata::spec_serialized_len() + CRC_SIZE < usize::MAX,
                ({
                    let item_slot_size = I::spec_serialized_len() + CDB_SIZE + CRC_SIZE;
                    let metadata_header_size = ItemTableMetadata::spec_serialized_len() + CRC_SIZE;
                    &&& 0 <= item_slot_size < usize::MAX
                })
                // TODO: recovery and permissions checks
            ensures
                wrpm_regions.inv(),
                // TODO: write the rest of the postconditions
        {
            let item_size = I::serialized_len();

            // ensure that there are no outstanding writes
            wrpm_regions.flush();

            // check that the caller passed in one valid region. We assume that the caller has
            // set up the region with `setup`, which does these same checks, but we check here
            // again anyway in case they didn't.
            let pm_regions = wrpm_regions.get_pm_regions_ref();
            let ghost mem = pm_regions@[0].committed();
            let region_sizes = get_region_sizes(pm_regions);
            let num_regions = region_sizes.len();
            if num_regions < 1 {
                return Err(KvError::TooFewRegions {required: 1, actual: num_regions});
            } else if num_regions > 1 {
                return Err(KvError::TooManyRegions {required: 1, actual: num_regions});
            }
            // TODO: check that the region is large enough to store the table metadata before
            // we attempt to read it

            // read and check the header metadata
            let table_metadata = Self::read_table_metadata(pm_regions, item_table_id)?;


            let num_keys = table_metadata.num_keys;
            let table_region_size = region_sizes[0];
            // determine if the provided region is large enough for the
            // specified number of items
            let item_slot_size = item_size + CDB_SIZE + CRC_SIZE;
            if ABSOLUTE_POS_OF_TABLE_AREA + (item_slot_size * num_keys) > table_region_size {
                let required: usize = (ABSOLUTE_POS_OF_TABLE_AREA + (item_slot_size * num_keys)) as usize;
                let actual: usize = region_sizes[0] as usize;
                return Err(KvError::RegionTooSmall {required, actual});
            }

            assume(false);

            // read the valid bits of each slot and set up the allocator
            let mut item_table_allocator: Vec<u64> = Vec::with_capacity(num_keys as usize);

            for index in 0..num_keys {
                assume(false);
                let item_slot_offset = ABSOLUTE_POS_OF_TABLE_AREA + index * item_slot_size;
                let cdb_addr = item_slot_offset + RELATIVE_POS_OF_VALID_CDB;
                let val: &u64 = pm_regions.read_and_deserialize(0, cdb_addr);
                match check_cdb(&val, Ghost(mem),
                            Ghost(pm_regions.constants().impervious_to_corruption),
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
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedItemTablePermission, PM>,
            item_table_id: u128,
            item: &I,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
        ) -> (result: Result<u64, KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(wrpm_regions).inv(),
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
                wrpm_regions.inv()
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
            wrpm_regions.serialize_and_write(0, item_slot_offset + RELATIVE_POS_OF_ITEM_CRC, &crc, Tracked(perm));
            // write the item itself
            wrpm_regions.serialize_and_write(0, item_slot_offset + RELATIVE_POS_OF_ITEM, item, Tracked(perm));

            Ok(free_index)
        }

        // makes a slot valid by setting its valid bit.
        // must log the operation before calling this function
        pub exec fn commit_item<PM>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedItemTablePermission, PM>,
            item_table_id: u128,
            item_table_index: u64,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(wrpm_regions).inv(),
                ({
                    let item_slot_size = old(self).spec_item_size() + CDB_SIZE + CRC_SIZE;
                    let metadata_header_size = ItemTableMetadata::spec_serialized_len() + CRC_SIZE;
                    &&& 0 <= item_slot_size < usize::MAX
                    &&& 0 <= item_slot_size * old(self).spec_num_keys() < usize::MAX
                    &&& 0 <= metadata_header_size + (item_slot_size * old(self).spec_num_keys()) < usize::MAX
                })
                // TODO: item update must have been logged
            ensures
                wrpm_regions.inv(),
                // TODO
        {
            assume(false);
            let item_slot_size = self.item_size + CDB_SIZE + CRC_SIZE;
            let item_slot_offset = ABSOLUTE_POS_OF_TABLE_AREA + item_table_index * item_slot_size;
            wrpm_regions.serialize_and_write(0, item_slot_offset + RELATIVE_POS_OF_VALID_CDB, &CDB_TRUE, Tracked(perm));
            Ok(())
        }

        // clears the valid bit for an entry. this should also
        // deallocate it
        pub exec fn invalidate_item<PM>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedItemTablePermission, PM>,
            item_table_id: u128,
            item_table_index: u64,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(wrpm_regions).inv(),
                // TODO: item invalidation must have been logged
            ensures
                wrpm_regions.inv(),
                // TODO
        {
            assume(false);
            let item_slot_size = self.item_size + CDB_SIZE + CRC_SIZE;
            let item_slot_offset = ABSOLUTE_POS_OF_TABLE_AREA + item_table_index * item_slot_size;
            wrpm_regions.serialize_and_write(0, item_slot_offset + RELATIVE_POS_OF_VALID_CDB, &CDB_FALSE, Tracked(perm));
            Ok(())
        }

        pub fn write_setup_metadata<PM>(pm_regions: &mut PM, num_keys: u64)
        where
            PM: PersistentMemoryRegions
        requires
            old(pm_regions).inv(),
            old(pm_regions)@.len() == 1,
            old(pm_regions)@.no_outstanding_writes(),
            ({
                let item_size = I::spec_serialized_len() + CDB_SIZE + CRC_SIZE;
                let metadata_header_size = ItemTableMetadata::spec_serialized_len() + CRC_SIZE;
                old(pm_regions)@[0].len() >= metadata_header_size + (item_size * num_keys)
            })
            // TODO: precondition that the region is large enough
        ensures
            pm_regions.inv(),
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

        proof {
            ItemTableMetadata::lemma_auto_serialized_len();
        }

        pm_regions.serialize_and_write(0, ABSOLUTE_POS_OF_METADATA_HEADER, &metadata_header);
        pm_regions.serialize_and_write(0, ABSOLUTE_POS_OF_HEADER_CRC, &metadata_crc);
    }

    pub fn read_table_metadata<PM>(pm_regions: &PM, table_id: u128) -> (result: Result<&ItemTableMetadata, KvError<K, E>>)
        where
            PM: PersistentMemoryRegions
        requires
            pm_regions.inv()
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

            let ghost mem = pm_regions@[0].committed();

            // read in the metadata structure and its CRC, make sure it has not been corrupted
            let table_metadata: &ItemTableMetadata = pm_regions.read_and_deserialize(0, ABSOLUTE_POS_OF_METADATA_HEADER);
            let table_crc = pm_regions.read_and_deserialize(0, ABSOLUTE_POS_OF_HEADER_CRC);

            if !check_crc_deserialized(table_metadata, table_crc, Ghost(mem),
                    Ghost(pm_regions.constants().impervious_to_corruption),
                    Ghost(ABSOLUTE_POS_OF_METADATA_HEADER), Ghost(LENGTH_OF_METADATA_HEADER),
                    Ghost(ABSOLUTE_POS_OF_HEADER_CRC)) {
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
