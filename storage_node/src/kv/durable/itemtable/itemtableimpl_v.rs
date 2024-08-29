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
use vstd::assert_seqs_equal;
use vstd::hash_map::*;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {
    pub open spec fn key_index_info_contains_index<K>(key_index_info: Seq<(Box<K>, u64, u64)>, idx: u64) -> bool
    {
        exists|j: int| 0 <= j < key_index_info.len() && (#[trigger] key_index_info[j]).2 == idx
    }

    pub open spec fn subregion_grants_access_to_item_table_entry<I>(
        subregion: WriteRestrictedPersistentMemorySubregion,
        idx: u64
    ) -> bool
        where
            I: PmCopy + Sized,
    {
        let entry_size = I::spec_size_of() + u64::spec_size_of();
        forall|addr: u64| idx * entry_size <= addr < idx * entry_size + entry_size ==>
            subregion.is_writable_relative_addr(addr as int)
    }

    pub struct DurableItemTable<K, I>
        where
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
    {
        item_size: u64,
        entry_size: u64,
        num_keys: u64,
        free_list: Vec<u64>,
        pending_allocations: Vec<u64>,
        valid_indices: Ghost<Set<u64>>,
        outstanding_item_table: Ghost<Seq<Option<I>>>,
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

        pub closed spec fn allocator_view(self) -> Set<u64>
        {
            self.free_list@.to_set()
        }

        pub closed spec fn pending_allocations_view(self) -> Set<u64>
        {
            self.pending_allocations@.to_set()
        }
        
        pub closed spec fn spec_outstanding_item_table(self) -> Seq<Option<I>>
        {
            self.outstanding_item_table@
        }

        pub closed spec fn opaque_inv(self, overall_metadata: OverallMetadata) -> bool
        {
            let entry_size = I::spec_size_of() + u64::spec_size_of();
            &&& self.item_size == overall_metadata.item_size
            &&& self.entry_size == entry_size
            &&& self.free_list@.no_duplicates()
            &&& self.pending_allocations@.no_duplicates()
            &&& forall |i: int| 0 <= i < self.pending_allocations.len() ==> 
                !self.free_list@.contains(#[trigger] self.pending_allocations[i])
            &&& forall |i: int| 0 <= i < self.free_list.len() ==> 
                !self.pending_allocations@.contains(#[trigger] self.free_list[i])
            &&& forall|i: int| 0 <= i < self.free_list@.len() ==> 
                    self.free_list@[i] < overall_metadata.num_keys
            &&& forall|i: int| 0 <= i < self.pending_allocations@.len() ==> 
                    self.pending_allocations@[i] < overall_metadata.num_keys
        }

        // TODO: this needs to say something about pending allocations
        pub open spec fn inv(self, pm_view: PersistentMemoryRegionView, overall_metadata: OverallMetadata) -> bool
        {
            let entry_size = I::spec_size_of() + u64::spec_size_of();
            &&& self.opaque_inv(overall_metadata)
            &&& self@.len() == self.spec_outstanding_item_table().len() == self.spec_num_keys() == overall_metadata.num_keys
            &&& pm_view.len() >= overall_metadata.item_table_size >= overall_metadata.num_keys * entry_size
            &&& forall|idx: u64| #[trigger] self.spec_valid_indices().contains(idx) ==> 
                    !self.spec_free_list().contains(idx) && !self.pending_allocations_view().contains(idx)
            &&& forall |s| #[trigger] pm_view.can_crash_as(s) ==>
                   parse_item_table::<I, K>(s, overall_metadata.num_keys as nat, self.spec_valid_indices()) ==
                       Some(self@)
            &&& forall|i: int, j: int| 0 <= i < self.spec_free_list().len() && 0 <= j < self.spec_free_list().len() && i != j ==>
                self.spec_free_list()[i] != self.spec_free_list()[j]
            &&& forall|i: int| 0 <= i < self.spec_free_list().len() ==> self.spec_free_list()[i] < overall_metadata.num_keys
            &&& self.spec_outstanding_item_table().len() == self@.durable_item_table.len()
            &&& forall|i: int| 0 <= i < self.spec_free_list().len() ==>
                self.spec_outstanding_item_table()[#[trigger] self.spec_free_list()[i] as int] is None
            &&& forall|idx: u64| idx < overall_metadata.num_keys &&
                #[trigger] self.spec_outstanding_item_table()[idx as int] is None ==>
                pm_view.no_outstanding_writes_in_range(idx * entry_size, idx * entry_size + entry_size)
            &&& forall|idx: u64| self.spec_valid_indices().contains(idx) ==> {
                let entry_bytes = extract_bytes(pm_view.committed(), (idx * entry_size) as nat, entry_size as nat);
                &&& idx < overall_metadata.num_keys
                &&& validate_item_table_entry::<I, K>(entry_bytes)
                &&& self@.durable_item_table[idx as int] is Some
                &&& self@.durable_item_table[idx as int] == parse_item_entry::<I, K>(entry_bytes)
            }
        }

        pub open spec fn valid(self, pm_view: PersistentMemoryRegionView, overall_metadata: OverallMetadata) -> bool
        {
            &&& self.inv(pm_view, overall_metadata)
            &&& forall|idx: u64| idx < overall_metadata.num_keys ==>
                #[trigger] self.spec_outstanding_item_table()[idx as int] is None
        }

        pub open spec fn subregion_grants_access_to_free_slots(
            self,
            subregion: WriteRestrictedPersistentMemorySubregion
        ) -> bool
        {
            forall|idx: u64| {
                &&& idx < self@.len()
                &&& !self.spec_valid_indices().contains(idx)
            } ==> #[trigger] subregion_grants_access_to_item_table_entry::<I>(subregion, idx)
        }

        pub closed spec fn spec_num_keys(self) -> u64
        {
            self.num_keys
        }

        pub closed spec fn spec_free_list(self) -> Seq<u64>
        {
            self.free_list@
        }

        pub closed spec fn spec_pending_allocations(self) -> Seq<u64>
        {
            self.pending_allocations@
        }

        pub closed spec fn spec_valid_indices(self) -> Set<u64>
        {
            self.valid_indices@
        }

        proof fn lemma_establish_bytes_parseable_for_valid_item(
            self,
            pm: PersistentMemoryRegionView,
            overall_metadata: OverallMetadata,
            index: u64,
        )
            requires
                self.valid(pm, overall_metadata),
                0 <= index < overall_metadata.num_keys,
                self.spec_valid_indices().contains(index),
                self@.durable_item_table[index as int] is Some,
            ensures
                ({
                    let entry_size = I::spec_size_of() + u64::spec_size_of();
                    let crc_bytes = extract_bytes(
                        pm.committed(),
                        (index * entry_size as u64) as nat,
                        u64::spec_size_of() as nat,
                    );
                    let item_bytes = extract_bytes(
                        pm.committed(),
                        (index * entry_size as u64) as nat + u64::spec_size_of(),
                        I::spec_size_of() as nat,
                    );
                    &&& u64::bytes_parseable(crc_bytes)
                    &&& I::bytes_parseable(item_bytes)
                    &&& crc_bytes == spec_crc_bytes(item_bytes)
                }),
        {
            let entry_size = I::spec_size_of() + u64::spec_size_of();
            lemma_valid_entry_index(index as nat, overall_metadata.num_keys as nat, entry_size as nat);
            let entry_bytes = extract_bytes(pm.committed(), (index * entry_size) as nat, entry_size as nat);
            assert(extract_bytes(entry_bytes, 0, u64::spec_size_of()) =~=
                   extract_bytes(pm.committed(), (index * entry_size as u64) as nat, u64::spec_size_of()));
            assert(extract_bytes(entry_bytes, u64::spec_size_of(), I::spec_size_of()) =~=
                   extract_bytes(pm.committed(),
                                 (index * entry_size as u64) as nat + u64::spec_size_of(),
                                 I::spec_size_of()));
            assert(validate_item_table_entry::<I, K>(entry_bytes));
        }

        // Read an item from the item table given an index. Returns `None` if the index is 
        // does not contain a valid, uncorrupted item. 
        // TODO: should probably return result, not option
        pub exec fn read_item<PM>(
            &self,
            subregion: &PersistentMemorySubregion,
            pm_region: &PM,
            item_table_index: u64,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        ) -> (result: Result<Box<I>, KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires
                subregion.inv(pm_region),
                self.valid(subregion.view(pm_region), overall_metadata),
                item_table_index < self.spec_num_keys(),
                self.spec_valid_indices().contains(item_table_index),
                self.spec_outstanding_item_table()[item_table_index as int] is None,
            ensures
                match result {
                    Ok(item) => item == self@.durable_item_table[item_table_index as int].unwrap(),
                    Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                    _ => false,
                },
        {
            let ghost pm_view = subregion.view(pm_region);
            let entry_size = self.entry_size;
            proof {
                lemma_valid_entry_index(item_table_index as nat, overall_metadata.num_keys as nat, entry_size as nat);
            }
            let crc_addr = item_table_index * (entry_size as u64);
            let item_addr = crc_addr + traits_t::size_of::<u64>() as u64;

            // Read the item and CRC at this slot
            let ghost mem = pm_view.committed();
            let ghost entry_bytes = extract_bytes(mem, (item_table_index * entry_size) as nat, entry_size as nat);
            let ghost true_crc_bytes = extract_bytes(mem, crc_addr as nat, u64::spec_size_of());
            let ghost true_item_bytes = extract_bytes(mem, item_addr as nat, I::spec_size_of());

            let ghost true_crc = u64::spec_from_bytes(true_crc_bytes);
            let ghost true_item = I::spec_from_bytes(true_item_bytes);

            let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| crc_addr + subregion.start() + i);
            let ghost item_addrs = Seq::new(I::spec_size_of() as nat, |i: int| item_addr + subregion.start() + i);

            proof {
                self.lemma_establish_bytes_parseable_for_valid_item(pm_view, overall_metadata, item_table_index);
                assert(extract_bytes(pm_view.committed(), crc_addr as nat, u64::spec_size_of()) =~=
                       Seq::new(u64::spec_size_of() as nat, |i: int| pm_region@.committed()[crc_addrs[i]]));
                assert(extract_bytes(pm_view.committed(), item_addr as nat, I::spec_size_of()) =~=
                       Seq::new(I::spec_size_of() as nat, |i: int| pm_region@.committed()[item_addrs[i]]));
                assert(true_crc_bytes =~= extract_bytes(entry_bytes, 0, u64::spec_size_of()));
                assert(true_item_bytes =~= extract_bytes(entry_bytes, u64::spec_size_of(), I::spec_size_of()));
                assert(self@.durable_item_table[item_table_index as int] == parse_item_entry::<I, K>(entry_bytes));
            }

            let crc = match subregion.read_relative_aligned::<u64, PM>(pm_region, crc_addr) {
                Ok(val) => val,
                Err(e) => { assert(false); return Err(KvError::PmemErr { pmem_err: e }); }
            };
            let item = match subregion.read_relative_aligned::<I, PM>(pm_region, item_addr) {
                Ok(val) => val,
                Err(e) => { assert(false); return Err(KvError::PmemErr { pmem_err: e }); },
            };
            
            if !check_crc(item.as_slice(), crc.as_slice(), Ghost(pm_region@.committed()),
                          Ghost(pm_region.constants().impervious_to_corruption), Ghost(item_addrs), Ghost(crc_addrs)) {
                return Err(KvError::CRCMismatch);
            }

            let item = item.extract_init_val(Ghost(true_item));
            Ok(item)
        }

        proof fn lemma_changing_unused_entry_doesnt_affect_parse_item_table(
            self: Self,
            v1: PersistentMemoryRegionView,
            v2: PersistentMemoryRegionView,
            crash_state2: Seq<u8>,
            overall_metadata: OverallMetadata,
            which_entry: u64,
        )
            requires
                self.inv(v1, overall_metadata),
                !self.spec_valid_indices().contains(which_entry),
                v1.len() == v2.len(),
                v2.can_crash_as(crash_state2),
                which_entry < overall_metadata.num_keys,
                forall|addr: int| {
                    let entry_size = I::spec_size_of() + u64::spec_size_of();
                    let start_addr = which_entry * entry_size;
                    let end_addr = start_addr + entry_size;
                    &&& 0 <= addr < v1.len()
                    &&& !(start_addr <= addr < end_addr)
                } ==> v2.state[addr] == v1.state[addr],
            ensures
                parse_item_table::<I, K>(crash_state2, overall_metadata.num_keys as nat,
                                         self.spec_valid_indices()) == Some(self@),
        {
            let entry_size = I::spec_size_of() + u64::spec_size_of();
            let num_keys = overall_metadata.num_keys;
            let start_addr = which_entry * entry_size;
            let end_addr = start_addr + entry_size;
            let can_views_differ_at_addr = |addr: int| start_addr <= addr < end_addr;
            let crash_state1 = lemma_get_crash_state_given_one_for_other_view_differing_only_at_certain_addresses(
                v2, v1, crash_state2, can_views_differ_at_addr
            );
            assert(parse_item_table::<I, K>(crash_state1, num_keys as nat, self.spec_valid_indices()) == Some(self@));
            lemma_valid_entry_index(which_entry as nat, num_keys as nat, entry_size as nat);
            let entry_bytes = extract_bytes(crash_state1, (which_entry * entry_size) as nat, entry_size as nat);
            lemma_subrange_of_subrange_forall(crash_state1);
            assert forall|addr: int| {
                let addrs_entry = addr / entry_size as int;
                &&& 0 <= addr < crash_state1.len()
                &&& addrs_entry < overall_metadata.num_keys
                &&& self.spec_valid_indices().contains(addrs_entry as u64)
            } implies crash_state1[addr] == crash_state2[addr] by {
                let addrs_entry = addr / entry_size as int;
                lemma_valid_entry_index(addrs_entry as nat, overall_metadata.num_keys as nat, entry_size as nat);
                lemma_entries_dont_overlap_unless_same_index(addrs_entry as nat, which_entry as nat, entry_size as nat);
                assert(!can_views_differ_at_addr(addr));
            }
            lemma_parse_item_table_doesnt_depend_on_fields_of_invalid_entries::<I, K>(
                crash_state1, crash_state2, num_keys, self.spec_valid_indices()
            );
        }

        // this function can be used to both create new items and do COW updates to existing items.
        // must always write to an invalid slot
        // this operation is NOT directly logged
        // returns the index of the slot that the item was written to
        pub exec fn tentatively_write_item<PM, Perm>(
            &mut self,
            subregion: &WriteRestrictedPersistentMemorySubregion,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
            item: &I,
            Tracked(perm): Tracked<&Perm>,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        ) -> (result: Result<u64, KvError<K>>)
            where
                PM: PersistentMemoryRegion,
                Perm: CheckPermission<Seq<u8>>,
            requires
                subregion.inv(old::<&mut _>(wrpm_region), perm),
                old(self).valid(subregion.view(old::<&mut _>(wrpm_region)), overall_metadata),
                subregion.len() >= overall_metadata.item_table_size,
                old(self).subregion_grants_access_to_free_slots(*subregion),
            ensures
                subregion.inv(wrpm_region, perm),
                self.inv(subregion.view(wrpm_region), overall_metadata),
                self.spec_valid_indices() == old(self).spec_valid_indices(),
                match result {
                    Ok(index) => {
                        &&& old(self).spec_free_list().contains(index)
                        &&& self@.durable_item_table == old(self)@.durable_item_table
                        &&& forall |i: int| 0 <= i < overall_metadata.num_keys && i != index ==>
                            #[trigger] self.spec_outstanding_item_table()[i] ==
                            old(self).spec_outstanding_item_table()[i]
                        &&& self.spec_outstanding_item_table()[index as int] == Some(*item)
                        &&& forall |other_index: u64| self.spec_free_list().contains(other_index) <==>
                            old(self).spec_free_list().contains(other_index) && other_index != index
                    },
                    Err(KvError::OutOfSpace) => {
                        &&& self@ == old(self)@
                        &&& self.spec_outstanding_item_table() == old(self).spec_outstanding_item_table()
                        &&& self.spec_free_list() == old(self).spec_free_list()
                        &&& self.spec_free_list().len() == 0
                        &&& wrpm_region == old(wrpm_region)
                    },
                    _ => false,
                }
        {
            let ghost old_pm_view = subregion.view(wrpm_region);
            assert(parse_item_table::<I, K>(old_pm_view.committed(), overall_metadata.num_keys as nat,
                                            self.spec_valid_indices()) == Some(self@)) by {
                lemma_persistent_memory_view_can_crash_as_committed(old_pm_view);
            }
            
            let entry_size = self.entry_size;
            assert(self.valid(subregion.view(wrpm_region), overall_metadata));
            assert(self.inv(subregion.view(wrpm_region), overall_metadata));
            assert(entry_size == u64::spec_size_of() + I::spec_size_of());
            
            // pop a free index from the free list
            let free_index = match self.free_list.pop() {
                Some(index) => index,
                None => {
                    assert(self.spec_valid_indices() == old(self).spec_valid_indices());
                    return Err(KvError::OutOfSpace);
                }
            };
            self.pending_allocations.push(free_index);

            assert(!self.free_list@.contains(free_index));
            assert(subregion_grants_access_to_item_table_entry::<I>(*subregion, free_index));
            assert(self.spec_valid_indices() == old(self).spec_valid_indices());

            broadcast use pmcopy_axioms;
            
            proof {
                lemma_valid_entry_index(free_index as nat, overall_metadata.num_keys as nat, entry_size as nat);
                assert(self.spec_outstanding_item_table()[free_index as int] is None);
            }

            let crc_addr = free_index * (entry_size as u64);
            let item_addr = crc_addr + traits_t::size_of::<u64>() as u64;

            // calculate and write the CRC of the provided item
            let crc: u64 = calculate_crc(item);
            subregion.serialize_and_write_relative::<u64, Perm, PM>(wrpm_region, crc_addr, &crc, Tracked(perm));
            // write the item itself
            subregion.serialize_and_write_relative::<I, Perm, PM>(wrpm_region, item_addr, item, Tracked(perm));

            self.outstanding_item_table = Ghost(self.outstanding_item_table@.update(free_index as int, Some(*item)));

            let ghost pm_view = subregion.view(wrpm_region);
            assert forall|idx: u64| idx < overall_metadata.num_keys &&
                   #[trigger] self.spec_outstanding_item_table()[idx as int] is None implies
                pm_view.no_outstanding_writes_in_range(idx * entry_size, idx * entry_size + entry_size) by {
                lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, entry_size as nat);
                lemma_entries_dont_overlap_unless_same_index(idx as nat, free_index as nat, entry_size as nat);
            }
            assert forall|idx: u64| self.spec_valid_indices().contains(idx) implies {
                let entry_bytes = extract_bytes(pm_view.committed(), (idx * entry_size) as nat, entry_size as nat);
                &&& idx < overall_metadata.num_keys
                &&& validate_item_table_entry::<I, K>(entry_bytes)
                &&& self@.durable_item_table[idx as int] is Some
                &&& self@.durable_item_table[idx as int] == parse_item_entry::<I, K>(entry_bytes)
            } by {
                let entry_bytes = extract_bytes(pm_view.committed(), (idx * entry_size) as nat, entry_size as nat);
                lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, entry_size as nat);
                lemma_entries_dont_overlap_unless_same_index(idx as nat, free_index as nat, entry_size as nat);
                assert(entry_bytes =~= extract_bytes(subregion.view(old::<&mut _>(wrpm_region)).committed(),
                                                     (idx * entry_size) as nat, entry_size as nat));
            }

            assert forall |other_index: u64| self.spec_free_list().contains(other_index) <==>
                     old(self).spec_free_list().contains(other_index) && other_index != free_index by {
                if other_index != free_index {
                    if old(self).spec_free_list().contains(other_index) {
                        let j = choose|j: int| 0 <= j < old(self).free_list@.len() && old(self).free_list@[j] == other_index;
                        assert(self.free_list@[j] == other_index);
                        assert(self.spec_free_list().contains(other_index));
                    }
                }
            }

            assert forall |s| #[trigger] pm_view.can_crash_as(s) implies {
                parse_item_table::<I, K>(s, overall_metadata.num_keys as nat, self.spec_valid_indices()) == Some(self@)
            } by {
                old(self).lemma_changing_unused_entry_doesnt_affect_parse_item_table(
                    old_pm_view, pm_view, s, overall_metadata, free_index
                );
            }

            Ok(free_index)
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

        pub proof fn lemma_table_is_empty_at_setup<PM, L>(
            subregion: &WritablePersistentMemorySubregion,
            pm_region: &PM,
            valid_indices: Set<u64>,
            num_keys: u64,
        )
            where 
                PM: PersistentMemoryRegion,
                L: PmCopy,
            requires 
                valid_indices == Set::<u64>::empty(),
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
            
            assert(item_table_view == DurableItemTableView::<I>::init(num_keys as int));
        }

        pub exec fn start<PM, L>(
            subregion: &PersistentMemorySubregion,
            pm_region: &PM,
            key_index_info: &Vec<(Box<K>, u64, u64)>,
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
                    let valid_indices_view = Seq::new(key_index_info@.len(), |i: int| key_index_info[i].2);
                    let table = parse_item_table::<I, K>(subregion.view(pm_region).committed(), overall_metadata.num_keys as nat, valid_indices_view.to_set());
                    table is Some
                }),
                overall_metadata.item_size == I::spec_size_of(),
                forall |j: int| 0 <= j < key_index_info.len() ==> 
                    0 <= (#[trigger] key_index_info[j]).2 < overall_metadata.num_keys,
                overall_metadata.item_size + u64::spec_size_of() <= u64::MAX,
            ensures 
                match result {
                    Ok(item_table) => {
                        let valid_indices_view = Seq::new(key_index_info@.len(), |i: int| key_index_info[i].2);
                        let table = parse_item_table::<I, K>(subregion.view(pm_region).committed(), overall_metadata.num_keys as nat, valid_indices_view.to_set()).unwrap();
                        &&& item_table.valid(subregion.view(pm_region), overall_metadata)
                        // table view is correct
                        &&& table == item_table@
                        &&& forall |i: int| 0 <= i < key_index_info.len() ==> {
                                let index = #[trigger] key_index_info[i].2;
                                // all indexes that are in use are not in the free list
                                !item_table.spec_free_list().contains(index)
                            }
                        &&& {
                            let in_use_indices = Set::new(|i: u64| 0 <= i < overall_metadata.num_keys && key_index_info_contains_index(key_index_info@, i));
                            let all_possible_indices = Set::new(|i: u64| 0 <= i < overall_metadata.num_keys);
                            let free_indices = all_possible_indices - in_use_indices;
                            // all free indexes are in the free list
                            &&& forall |i: u64| free_indices.contains(i) ==> #[trigger] item_table.spec_free_list().contains(i)
                            &&& item_table.spec_valid_indices() == in_use_indices
                        }
                    }
                    Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                    Err(KvError::PmemErr{ pmem_err }) => true,
                    Err(_) => false
                }
        {
            // The main thing we need to do here is to use the key_index_info vector to construct the item table's
            // allocator. We don't need to read anything from the item table, but we should have its subregion so we can 
            // prove that the allocator is correct

            let num_keys = overall_metadata.num_keys;
            let ghost pm_view = subregion.view(pm_region);

            let ghost valid_indices_view = Seq::new(key_index_info@.len(), |i: int| key_index_info[i].2);
            let ghost table = parse_item_table::<I, K>(pm_view.committed(), overall_metadata.num_keys as nat, valid_indices_view.to_set());

            // TODO: we could make this a bit more efficient by making the boolean vector a bitmap
            let mut free_vec: Vec<bool> = Vec::with_capacity(num_keys as usize);
            let mut i: usize = 0;
            // initialize the vec to all true; we'll set indexes that are in-use to false. 
            // verus doesn't support array literals right now, so we have to do this with a loop
            while i < num_keys as usize
                invariant 
                    0 <= i <= num_keys,
                    free_vec.len() == i,
                    forall |j: int| 0 <= j < i ==> free_vec[j],
            {
                free_vec.push(true);
                i += 1;    
            }

            i = 0;
            // now set all indexes that are in use to false
            let ghost old_free_vec_len = free_vec.len();
            while i < key_index_info.len()
                invariant 
                    0 <= i <= key_index_info.len(),
                    free_vec.len() == old_free_vec_len,
                    free_vec.len() == num_keys,
                    forall |j: int| 0 <= j < key_index_info.len() ==> 0 <= #[trigger] key_index_info[j].2 < num_keys,
                    forall |j: int| 0 <= j < i ==> {
                        let index = #[trigger] key_index_info[j].2;
                        !free_vec[index as int]
                    },
                    forall |j: int| 0 <= j < free_vec.len() ==> {
                        // either free_vec is true at j and there are no entries between 0 and i with this index
                        #[trigger] free_vec[j] <==> (forall |k: int| 0 <= k < i ==> #[trigger] key_index_info[k].2 != j)
                    },
            {
                let index = key_index_info[i].2;
                free_vec.set(index as usize, false);
                i += 1;
            }

            // next, build the allocator based on the values in the boolean array. indexes containing true 
            // are free, indexes containing false are not
            let mut item_table_allocator: Vec<u64> = Vec::with_capacity(num_keys as usize);
            i = 0;
            while i < num_keys as usize
                invariant
                    0 <= i <= num_keys,
                    item_table_allocator.len() <= i <= num_keys,
                    free_vec.len() == num_keys,
                    forall |j: u64| 0 <= j < i ==> free_vec[j as int] ==> item_table_allocator@.contains(j),
                    forall |j: int| 0 <= j < key_index_info.len() ==> !item_table_allocator@.contains(#[trigger] key_index_info[j].2),
                    forall |j: int| 0 <= j < free_vec.len() ==> 
                        (#[trigger] free_vec[j] <==>
                         forall |k: int| 0 <= k < key_index_info.len() ==> #[trigger] key_index_info[k].2 != j),
                    forall |j: int| 0 <= j < item_table_allocator.len() ==> item_table_allocator@[j] < i,
                    forall |j: int, k: int| 0 <= j < item_table_allocator.len() && 0 <= k < item_table_allocator.len() && j != k ==>
                        item_table_allocator@[j] != item_table_allocator@[k],
            {
                let ghost old_item_table_allocator = item_table_allocator;
                assert(forall |j: int| 0 <= j < key_index_info.len() ==> !item_table_allocator@.contains(#[trigger] key_index_info[j].2));
                if free_vec[i] {
                    item_table_allocator.push(i as u64);
                    assert(item_table_allocator@.subrange(0, item_table_allocator.len() - 1) == old_item_table_allocator@);
                    assert(item_table_allocator@[item_table_allocator.len() - 1] == i);
                    assert(forall |j: int| 0 <= j < key_index_info.len() ==> #[trigger] key_index_info[j].2 != i);
                }
                
                i += 1;
            }

            let ghost in_use_indices = Set::new(|i: u64| 0 <= i < overall_metadata.num_keys &&
                                                key_index_info_contains_index(key_index_info@, i));
            let ghost outstanding_item_table = Seq::new(overall_metadata.num_keys as nat, |i: int| None);
            let item_table = Self {
                item_size: overall_metadata.item_size,
                entry_size: overall_metadata.item_size + traits_t::size_of::<u64>() as u64, // item + CRC
                num_keys: overall_metadata.num_keys,
                free_list: item_table_allocator,
                pending_allocations: Vec::new(),
                valid_indices: Ghost(in_use_indices),
                outstanding_item_table: Ghost(outstanding_item_table),
                state: Ghost(table.unwrap()),
                _phantom: Ghost(None)
            };

            proof {
                assert(forall |i: int| 0 <= i < key_index_info.len() ==> {
                    let index = #[trigger] key_index_info[i].2;
                    !item_table.spec_free_list().contains(index)
                });

                let all_possible_indices = Set::new(|i: u64| 0 <= i < overall_metadata.num_keys);
                let free_indices = all_possible_indices - in_use_indices;
                let entry_size = I::spec_size_of() + u64::spec_size_of();

                assert forall|idx: u64| #[trigger] item_table.valid_indices@.contains(idx) implies
                    !item_table.free_list@.contains(idx) && item_table.state@.durable_item_table[idx as int] is Some by {
                    let j: int = choose|j: int| 0 <= j < key_index_info.len() && (#[trigger] key_index_info[j]).2 == idx;
                    assert(valid_indices_view[j] == idx);
                    assert(valid_indices_view.to_set().contains(idx));
                    assert(idx * entry_size + entry_size <= overall_metadata.num_keys * entry_size) by {
                        lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, entry_size as nat);
                    }
                    assert(validate_item_table_entry::<I, K>(extract_bytes(pm_view.committed(),
                                                                           (idx * entry_size) as nat, entry_size as nat)));
                }

                assert forall|idx: u64| idx < num_keys &&
                           #[trigger] item_table.spec_outstanding_item_table()[idx as int] is None implies
                    pm_view.no_outstanding_writes_in_range(idx * entry_size, idx * entry_size + entry_size) by {
                        lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, entry_size as nat);
                }
            }

            proof {
                // Prove that the item table region only has one crash state, which recovers to the initial table's state
                let pm_view = subregion.view(pm_region);
                lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(pm_view);
                assert(forall |s| pm_view.can_crash_as(s) ==> s == pm_view.committed());
                assert(forall |s| #[trigger] pm_view.can_crash_as(s) ==> 
                    parse_item_table::<I, K>(s, overall_metadata.num_keys as nat, item_table.spec_valid_indices()) == Some(item_table@));
            }

            Ok(item_table)
        }

        pub exec fn deallocate_item<Perm, PM>(
            &mut self,
            wrpm_region: &WriteRestrictedPersistentMemoryRegion<Perm, PM>,
            item_table_id: u128,
            item_table_index: u64,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        ) -> (result: Result<(), KvError<K>>)
            where 
                Perm: CheckPermission<Seq<u8>>,
                PM: PersistentMemoryRegion,
            requires 
                old(self).inv(wrpm_region@, overall_metadata),
                wrpm_region@.no_outstanding_writes(),
                // the given index is free (i.e. not valid) but not in the free list
                0 <= item_table_index < old(self)@.len(),
                !old(self).spec_valid_indices().contains(item_table_index),
                !old(self).allocator_view().contains(item_table_index),
                !old(self).spec_pending_allocations().contains(item_table_index),
                old(self).spec_outstanding_item_table()[item_table_index as int] is None,
                old(self)@.durable_item_table[item_table_index as int] is None,
                // the allocator contains all invalid indices except for item_table_index
                forall |i: u64| {
                    &&& 0 <= i < old(self)@.len()
                    &&& i != item_table_index
                } ==> (!old(self).spec_valid_indices().contains(i) <==> old(self).allocator_view().contains(i))
            ensures 
                self.inv(wrpm_region@, overall_metadata),
        {
            assert(forall |i: u64| 0 <= i < self@.len() && i != item_table_index ==> 
                    (!self.spec_valid_indices().contains(i) <==> self.allocator_view().contains(i)));

            self.free_list.push(item_table_index);

            proof {
                // Prove that the index has been added to the free list
                assert(self.free_list@.subrange(0, self.free_list@.len() - 1) == old(self).free_list@);
                assert(self.free_list@[self.free_list@.len() - 1] == item_table_index);
                assert(self.free_list@.contains(item_table_index));
            }

            Ok(())
        }

        pub exec fn abort_transaction(
            &mut self,
            Ghost(pm): Ghost<PersistentMemoryRegionView>,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        )
            requires 
                pm.no_outstanding_writes(),
                old(self).opaque_inv(overall_metadata),
                forall|idx: u64| #[trigger] old(self).spec_valid_indices().contains(idx) ==> 
                    !old(self).spec_free_list().contains(idx) && !old(self).pending_allocations_view().contains(idx),
                old(self)@.len() == old(self).spec_outstanding_item_table().len() == old(self).spec_num_keys() == overall_metadata.num_keys,
                ({
                    let entry_size = I::spec_size_of() + u64::spec_size_of();
                    &&& pm.len() >= overall_metadata.item_table_size >= overall_metadata.num_keys * entry_size
                }),
                forall|idx: u64| #[trigger] old(self).spec_valid_indices().contains(idx) ==> 
                    !old(self).spec_free_list().contains(idx),
                forall |s| #[trigger] pm.can_crash_as(s) ==> {
                    &&& parse_item_table::<I, K>(s, overall_metadata.num_keys as nat, old(self).spec_valid_indices())
                            matches Some(table_view)
                    &&& table_view.durable_item_table == old(self)@.durable_item_table
                },
                forall|idx: u64| old(self).spec_valid_indices().contains(idx) ==> {
                    let entry_size = I::spec_size_of() + u64::spec_size_of();
                    let entry_bytes = extract_bytes(pm.committed(), (idx * entry_size) as nat, entry_size as nat);
                    &&& idx < overall_metadata.num_keys
                    &&& validate_item_table_entry::<I, K>(entry_bytes)
                    &&& old(self)@.durable_item_table[idx as int] is Some
                    &&& old(self)@.durable_item_table[idx as int] == parse_item_entry::<I, K>(entry_bytes)
                },
            ensures
                self.valid(pm, overall_metadata),
                self.spec_valid_indices() == old(self).spec_valid_indices(),
        {
            // Move all pending allocations back into the free list
            self.free_list.append(&mut self.pending_allocations);

            // Drop all outstanding updates from the view
            self.outstanding_item_table = Ghost(Seq::new(self.outstanding_item_table@.len(), |i: int| None));

            proof {
                let entry_size = I::spec_size_of() + u64::spec_size_of();
                assert forall|idx: u64| {
                    &&& idx < overall_metadata.num_keys
                    &&& #[trigger] self.spec_outstanding_item_table()[idx as int] is None 
                } implies pm.no_outstanding_writes_in_range(idx * entry_size, idx * entry_size + entry_size) by {
                    lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, entry_size as nat);
                    assert(overall_metadata.num_keys * entry_size <= pm.len());
                }
                assert(forall |idx: u64| self.free_list@.contains(idx) ==> {
                    ||| old(self).free_list@.contains(idx)
                    ||| old(self).pending_allocations@.contains(idx)
                });
                assert(self.spec_valid_indices() == old(self).spec_valid_indices());
            }
        }

        /* temporarily commented out for subregion development 

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

    pub proof fn lemma_parse_item_table_doesnt_depend_on_fields_of_invalid_entries<I, K>(
        mem1: Seq<u8>,
        mem2: Seq<u8>,
        num_keys: u64,
        valid_indices: Set<u64>
    )
        where 
            I: PmCopy,
            K: PmCopy + std::fmt::Debug,
        requires
            mem1.len() == mem2.len(),
            mem1.len() >= num_keys * (I::spec_size_of() + u64::spec_size_of()),
            forall|addr: int| {
                let entry_size = (I::spec_size_of() + u64::spec_size_of()) as int;
                let which_entry = addr / entry_size;
                &&& 0 <= addr < mem1.len()
                &&& which_entry < num_keys
                &&& valid_indices.contains(which_entry as u64)
            } ==> mem1[addr] == mem2[addr],
        ensures
            parse_item_table::<I, K>(mem1, num_keys as nat, valid_indices) ==
            parse_item_table::<I, K>(mem2, num_keys as nat, valid_indices)
    {
        if mem1.len() < num_keys * (I::spec_size_of() + u64::spec_size_of()) {
            return;
        }

        let entry_size = I::spec_size_of() + u64::spec_size_of();
        assert forall |i: u64| i < num_keys && valid_indices.contains(i) implies
            extract_bytes(mem1, (i * entry_size) as nat, entry_size) ==
            extract_bytes(mem2, (i * entry_size) as nat, entry_size) by {
            lemma_valid_entry_index(i as nat, num_keys as nat, entry_size as nat);
            assert forall|addr: int| i * entry_size <= addr < i * entry_size + entry_size implies mem1[addr] == mem2[addr] by {
                assert(addr / entry_size as int == i) by {
                    lemma_addr_in_entry_divided_by_entry_size(i as nat, entry_size as nat, addr as int);
                }
            }
            assert(extract_bytes(mem1, (i * entry_size) as nat, entry_size) =~=
                   extract_bytes(mem2, (i * entry_size) as nat, entry_size));

        }
        assert(validate_item_table_entries::<I, K>(mem1, num_keys as nat, valid_indices) =~=
               validate_item_table_entries::<I, K>(mem2, num_keys as nat, valid_indices));
        let item_table_view1 = Seq::new(
            num_keys as nat,
            |i: int| {
                // TODO: probably can't have if {} in here
                if i <= u64::MAX && valid_indices.contains(i as u64) {
                    let bytes = extract_bytes(mem1, (i * entry_size) as nat, entry_size as nat);
                    parse_item_entry::<I, K>(bytes)
                } else {
                    None
                }
            }
        );
        let item_table_view2 = Seq::new(
            num_keys as nat,
            |i: int| {
                // TODO: probably can't have if {} in here
                if i <= u64::MAX && valid_indices.contains(i as u64) {
                    let bytes = extract_bytes(mem2, (i * entry_size) as nat, entry_size as nat);
                    parse_item_entry::<I, K>(bytes)
                } else {
                    None
                }
            }
        );
        assert(item_table_view1 =~= item_table_view2);
    }
}
