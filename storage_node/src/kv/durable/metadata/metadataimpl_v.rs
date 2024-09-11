use builtin::*;
use builtin_macros::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse};
use vstd::arithmetic::mul::*;
use vstd::set_lib::*;
use vstd::slice::*;
use vstd::seq_lib::*;
use std::fs::Metadata;
use std::hash::Hash;
use vstd::prelude::*;
use vstd::bytes::*;
use crate::kv::durable::oplog::logentry_v::*;
use crate::kv::kvimpl_t::*;
use crate::kv::durable::metadata::layout_v::*;
use crate::kv::durable::inv_v::*;
use crate::kv::durable::util_v::*;
use crate::kv::layout_v::*;
use crate::kv::setup_v::*;
use crate::pmem::crc_t::*;
use crate::pmem::subregion_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::subregion_v::*;
use crate::pmem::traits_t;
use crate::pmem::wrpm_t::*;
use crate::util_v::*;

verus! {
    pub struct MetadataTableViewEntry<K> {
        pub crc: u64,
        pub entry: ListEntryMetadata,
        pub key: K,
    }

    impl<K> MetadataTableViewEntry<K> {
        pub open spec fn new(crc: u64, entry: ListEntryMetadata, key: K) -> Self {
            Self {
                crc,
                entry,
                key,
            }
        }

        pub closed spec fn crc(self) -> u64 {
            self.crc
        }

        pub closed spec fn list_head_index(self) -> u64 {
            self.entry.head
        }

        pub open spec fn item_index(self) -> u64 {
            self.entry.item_index
        }

        pub closed spec fn len(self) -> u64 
        {
            self.entry.length
        }

        pub open spec fn key(self) -> K {
            self.key
        }
    }

    #[verifier::ext_equal]
    pub struct MetadataTableView<K> {
        pub durable_metadata_table: Seq<DurableEntry<MetadataTableViewEntry<K>>>,
    }

    impl<K> MetadataTableView<K>
        where
            K: PmCopy,
    {
        pub open spec fn init(num_keys: u64) -> Self {
            Self {
                durable_metadata_table: Seq::new(num_keys as nat, |i: int| DurableEntry::Invalid),
            }
        }

        pub open spec fn inv(self, overall_metadata: OverallMetadata) -> bool
        {
            &&& forall |i| #![trigger self.durable_metadata_table[i]] {
                  let entries = self.durable_metadata_table;
                  0 <= i < entries.len() ==> !(entries[i] is Tentative)
            }
            &&& forall |i: nat, j: nat| i < overall_metadata.num_keys && j < overall_metadata.num_keys && i != j ==> {
                    &&& #[trigger] self.durable_metadata_table[i as int] is Valid
                    &&& #[trigger] self.durable_metadata_table[j as int] is Valid
                } ==> self.durable_metadata_table[i as int]->Valid_0.item_index() != 
                        self.durable_metadata_table[j as int]->Valid_0.item_index()
        }

        pub open spec fn len(self) -> nat
        {
            self.durable_metadata_table.len()
        }

        pub open spec fn new(
            metadata_table: Seq<DurableEntry<MetadataTableViewEntry<K>>>
        ) -> Self {
            Self {
                durable_metadata_table: metadata_table,
            }
        }

        pub open spec fn get_durable_metadata_table(self) -> Seq<DurableEntry<MetadataTableViewEntry<K>>>
        {
            self.durable_metadata_table
        }

        pub open spec fn delete(self, index: int) -> Option<Self>
        {
            if index < 0 || index >= self.durable_metadata_table.len() {
                None 
            } else {
                Some(Self {
                    durable_metadata_table: self.durable_metadata_table.update(index, DurableEntry::Invalid)
                })
                // match self.durable_metadata_table[index] {
                //     DurableEntry::Valid(_) => {
                //         Some(Self {
                //             durable_metadata_table: self.durable_metadata_table.update(index, DurableEntry::Invalid)
                //         })
                //     }
                //     _ => None
                // }
                // if self.durable_metadata_table@[i] matches DurableEntry::Invalid {
                //     None
                // } else {
                //     Some(Self {
                //         durable_metadata_table: self.durable_metadata_table.set(i, DurableEntry::Invalid)
                //     })
                // }
            }
        }

        // pub closed spec fn spec_index(self, index: int) -> Option<MetadataTableViewEntry<K>> {
        //     if 0 <= index < self.metadata_table.len() {
        //         self.metadata_table[index]
        //     } else {
        //         None
        //     }
        // }

        pub open spec fn valid_item_indices(self) -> Set<u64> {
            Set::new(|i: u64| exists |j: int| {
                    &&& 0 <= j < self.durable_metadata_table.len() 
                    &&& #[trigger] self.durable_metadata_table[j] matches DurableEntry::Valid(entry)
                    &&& entry.item_index() == i
                }
            )
        }

        pub open spec fn has_same_valid_items(self, other: Self) -> bool
        {
            &&& self.durable_metadata_table.len() == other.durable_metadata_table.len()
            &&& forall|i: int| 0 <= i < self.durable_metadata_table.len() ==>
                   match #[trigger] self.durable_metadata_table[i] {
                       DurableEntry::Valid(e) => other.durable_metadata_table[i] == DurableEntry::Valid(e),
                       _ => !(other.durable_metadata_table[i] is Valid)
                   }
        }
    }

    pub struct MetadataTable<K> {
        metadata_node_size: u32,
        metadata_table_free_list: Vec<u64>,
        pending_allocations: Vec<u64>,
        pending_deallocations: Vec<u64>,
        state: Ghost<MetadataTableView<K>>,
        outstanding_cdb_writes: Ghost<Seq<Option<bool>>>,
        outstanding_entry_writes: Ghost<Seq<Option<MetadataTableViewEntry<K>>>>,
    }

    pub closed spec fn outstanding_bytes_match(pm: PersistentMemoryRegionView, start: int, bytes: Seq<u8>) -> bool
    {
        forall|addr: int| start <= addr < start + bytes.len() ==>
            #[trigger] pm.state[addr].outstanding_write == Some(bytes[addr - start])
    }

    pub open spec fn subregion_grants_access_to_main_table_entry<K>(
        subregion: WriteRestrictedPersistentMemorySubregion,
        idx: u64
    ) -> bool
        where 
            K: PmCopy + Sized,
    {
        let entry_size = ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of();
        forall|addr: u64| idx * entry_size + u64::spec_size_of() <= addr < idx * entry_size + entry_size ==>
            subregion.is_writable_relative_addr(addr as int)
    }

    impl<K> MetadataTable<K>
        where 
            K: PmCopy + std::fmt::Debug,
    {
        pub closed spec fn view(self) -> MetadataTableView<K> 
        {
            self.state@
        }

        pub closed spec fn allocator_view(self) -> Set<u64>
        {
            self.metadata_table_free_list@.to_set()
        }

        pub closed spec fn pending_allocations_view(self) -> Set<u64>
        {
            self.pending_allocations@.to_set()
        }

        pub closed spec fn pending_deallocations_view(self) -> Set<u64>
        {
            self.pending_deallocations@.to_set()
        }

        pub closed spec fn spec_outstanding_cdb_writes(self) -> Seq<Option<bool>>
        {
            self.outstanding_cdb_writes@
        }

        pub closed spec fn spec_outstanding_entry_writes(self) -> Seq<Option<MetadataTableViewEntry<K>>>
        {
            self.outstanding_entry_writes@
        }

        pub closed spec fn spec_metadata_node_size(self) -> u32 
        {
            self.metadata_node_size
        }

        pub open spec fn no_outstanding_writes_to_index(self, idx: int) -> bool
        {
            &&& self.spec_outstanding_cdb_writes()[idx] is None
            &&& self.spec_outstanding_entry_writes()[idx] is None
        }

        pub open spec fn no_outstanding_writes_except_to_index(self, idx: int) -> bool
        {
            forall|i| 0 <= i < self@.durable_metadata_table.len() && i != idx ==> self.no_outstanding_writes_to_index(i)
        }

        pub open spec fn no_outstanding_writes(self) -> bool
        {
            forall|i| 0 <= i < self@.durable_metadata_table.len() ==> self.no_outstanding_writes_to_index(i)
        }

        // We return the free indices as a set, not a seq, because the order they are listed in
        // doesn't actually matter, and then we don't have to worry about matching the order
        // they are kept in in executable code.
        // An index is only considered free if it is free in the durable view of the table and
        // if it has no outstanding writes.
        pub open spec fn free_indices(self) -> Set<u64> {
            Set::new(|i: u64| {
                &&& 0 <= i < self@.durable_metadata_table.len() 
                &&& self.spec_outstanding_cdb_writes()[i as int] is None
                &&& self.spec_outstanding_entry_writes()[i as int] is None
                &&& self@.durable_metadata_table[i as int] matches DurableEntry::Invalid
            })
        }

        pub closed spec fn outstanding_cdb_write_matches_pm_view(self, pm: PersistentMemoryRegionView, i: int,
                                                                 metadata_node_size: u32) -> bool
        {
            let start = index_to_offset(i as nat, metadata_node_size as nat) as int;
            match self.outstanding_cdb_writes@[i] {
                None => pm.no_outstanding_writes_in_range(start as int, start + u64::spec_size_of()),
                Some(b) => {
                    let cdb = if b { CDB_TRUE } else { CDB_FALSE };
                    let cdb_bytes = u64::spec_to_bytes(cdb);
                    outstanding_bytes_match(pm, start, cdb_bytes)
                },
            }
        }

        pub closed spec fn outstanding_entry_write_matches_pm_view(self, pm: PersistentMemoryRegionView, i: int,
                                                                   metadata_node_size: u32) -> bool
        {
            let start = index_to_offset(i as nat, metadata_node_size as nat) as int;
            match self.outstanding_entry_writes@[i] {
                None => pm.no_outstanding_writes_in_range(start + u64::spec_size_of(), start + metadata_node_size),
                Some(e) => {
                    &&& outstanding_bytes_match(pm, start + u64::spec_size_of(), u64::spec_to_bytes(e.crc))
                    &&& outstanding_bytes_match(pm, start + u64::spec_size_of() * 2,
                                              ListEntryMetadata::spec_to_bytes(e.entry))
                    &&& outstanding_bytes_match(pm, start + u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of(),
                                              K::spec_to_bytes(e.key))
                },
            }
        }

        pub closed spec fn opaque_inv(self, overall_metadata: OverallMetadata) -> bool
        {
            &&& self.metadata_table_free_list@.no_duplicates()
            &&& self.pending_allocations@.no_duplicates()
            &&& self.pending_deallocations@.no_duplicates()
            &&& forall |i: int| 0 <= i < self.pending_allocations.len() ==> 
                !self.metadata_table_free_list@.contains(#[trigger] self.pending_allocations[i])
            &&& forall |i: int| 0 <= i < self.pending_deallocations.len() ==> 
                !self.metadata_table_free_list@.contains(#[trigger] self.pending_deallocations[i])
            &&& forall |idx: u64| self.metadata_table_free_list@.contains(idx) ==> idx < overall_metadata.num_keys
            &&& forall |idx: u64| self.pending_allocations@.contains(idx) ==> idx < overall_metadata.num_keys
            &&& forall |idx: u64| self.pending_deallocations@.contains(idx) ==> idx < overall_metadata.num_keys
            // &&& forall |idx: u64| self.pending_allocations@.contains(idx) ==> {
            //         ||| self@.durable_metadata_table[idx as int] matches DurableEntry::Invalid 
            //         ||| self@.durable_metadata_table[idx as int] matches DurableEntry::Tentative(_)
            //     }
            // &&& forall |idx: u64| self.metadata_table_free_list@.contains(idx) ==> 
            //         { self@.durable_metadata_table[idx as int] matches DurableEntry::Invalid }
            // &&& forall |idx: u64| self.pending_deallocations@.contains(idx) ==> 
            //         { self@.durable_metadata_table[idx as int] matches DurableEntry::Valid(_) }
            &&& forall |idx: u64| {
                    &&& 0 <= idx < self@.durable_metadata_table.len()
                    &&& self.spec_outstanding_cdb_writes()[idx as int] is Some
                } ==> #[trigger] self.pending_allocations@.contains(idx)
            &&& forall |idx: u64| {
                    &&& 0 <= idx < self@.durable_metadata_table.len()
                    &&& self.spec_outstanding_entry_writes()[idx as int] is Some
                } ==> #[trigger] self.pending_allocations@.contains(idx)
        }

        pub open spec fn inv(self, pm: PersistentMemoryRegionView, overall_metadata: OverallMetadata) -> bool
        {
            &&& self.opaque_inv(overall_metadata)
            &&& overall_metadata.main_table_size >= overall_metadata.num_keys * overall_metadata.metadata_node_size
            &&& pm.len() >= overall_metadata.main_table_size
            &&& self.spec_metadata_node_size() == overall_metadata.metadata_node_size
            &&& overall_metadata.metadata_node_size ==
                    ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of()
            &&& forall |s| #[trigger] pm.can_crash_as(s) ==> 
                    parse_metadata_table::<K>(s, overall_metadata.num_keys, overall_metadata.metadata_node_size) == Some(self@)
            &&& self@.durable_metadata_table.len() == self.spec_outstanding_cdb_writes().len() ==
                    self.spec_outstanding_entry_writes().len() == overall_metadata.num_keys
            &&& forall |i| 0 <= i < self@.durable_metadata_table.len() ==>
                    self.outstanding_cdb_write_matches_pm_view(pm, i, overall_metadata.metadata_node_size)
            &&& forall |i| 0 <= i < self@.durable_metadata_table.len() ==>
                    self.outstanding_entry_write_matches_pm_view(pm, i, overall_metadata.metadata_node_size)
            &&& self@.inv(overall_metadata)
            &&& forall |idx: u64| self.allocator_view().contains(idx) ==> idx < overall_metadata.num_keys
            &&& forall |idx: u64| self.allocator_view().contains(idx) ==> self.free_indices().contains(idx)
            &&& forall |idx: u64| self.pending_allocations_view().contains(idx) ==> idx < overall_metadata.num_keys
            &&& forall |idx: u64| self.pending_allocations_view().contains(idx) ==> !self.free_indices().contains(idx)
            &&& forall |idx: u64| self.free_indices().contains(idx) ==> idx < overall_metadata.num_keys
            &&& forall |i| 0 <= i < self@.durable_metadata_table.len() ==> 
                    match #[trigger] self@.durable_metadata_table[i] {
                        DurableEntry::Valid(entry) => entry.entry.item_index < overall_metadata.num_keys,
                        _ => true
                    }
        }

        pub open spec fn allocator_inv(self) -> bool
        {
            &&& self.allocator_view() == self.free_indices()
        }

        pub open spec fn pending_alloc_inv(self, current_durable_state: Seq<u8>, tentative_state: Seq<u8>, overall_metadata: OverallMetadata) -> bool 
        {
            let current_view = parse_metadata_table::<K>(current_durable_state, overall_metadata.num_keys, overall_metadata.metadata_node_size);
            let tentative_view = parse_metadata_table::<K>(tentative_state, overall_metadata.num_keys, overall_metadata.metadata_node_size);
            &&& current_view matches Some(current_view)
            &&& tentative_view matches Some(tentative_view)
            &&& forall |idx: u64| 0 <= idx < current_view.durable_metadata_table.len() ==> 
                    self.pending_alloc_check(idx, current_view, tentative_view)
        }

        pub open spec fn pending_alloc_check(self, idx: u64, current_view: MetadataTableView<K>, tentative_view: MetadataTableView<K>) -> bool 
        {
            // if an index is valid in the current state but invalid in the tentative state,
            // it is pending deallocation
            &&& {
                &&& current_view.durable_metadata_table[idx as int] is Valid
                &&& tentative_view.durable_metadata_table[idx as int] is Invalid
            } <==> self.pending_deallocations_view().contains(idx)
            // if an index is invalid in the current state but valid in the tentative state, 
            // it is pending allocation
            &&& {
                &&& current_view.durable_metadata_table[idx as int] is Invalid
                &&& tentative_view.durable_metadata_table[idx as int] is Valid
            } <==> self.pending_allocations_view().contains(idx)
            // if an index is invalid in both the current and tentative state,
            // it is in the free list
            &&& {
                &&& current_view.durable_metadata_table[idx as int] is Invalid
                &&& tentative_view.durable_metadata_table[idx as int] is Invalid
            } <==> self.allocator_view().contains(idx)
            // if an index is valid in both the current and tentative state, they match
            &&& {
                &&& current_view.durable_metadata_table[idx as int] is Valid
                &&& tentative_view.durable_metadata_table[idx as int] is Valid
            } ==> current_view.durable_metadata_table[idx as int] ==
                  tentative_view.durable_metadata_table[idx as int]
        }

        pub open spec fn valid(self, pm: PersistentMemoryRegionView, overall_metadata: OverallMetadata) -> bool
        {
            &&& self.inv(pm, overall_metadata)
            &&& forall |i| 0 <= i < self.spec_outstanding_cdb_writes().len() ==> self.spec_outstanding_cdb_writes()[i] is None
            &&& forall |i| 0 <= i < self.spec_outstanding_entry_writes().len() ==> self.spec_outstanding_entry_writes()[i] is None
        }

        pub open spec fn subregion_grants_access_to_free_slots(
            self,
            subregion: WriteRestrictedPersistentMemorySubregion
        ) -> bool
        {
            forall|idx: u64| {
                &&& idx < self@.len()
                &&& self.allocator_view().contains(idx)
            } ==> #[trigger] subregion_grants_access_to_main_table_entry::<K>(subregion, idx)
        }

        pub proof fn lemma_establish_bytes_parseable_for_valid_entry(
            self,
            pm: PersistentMemoryRegionView,
            overall_metadata: OverallMetadata,
            index: u64,
        )
            requires
                self.inv(pm, overall_metadata),
                0 <= index < overall_metadata.num_keys,
                self@.durable_metadata_table[index as int] is Valid,
            ensures
                ({
                    let cdb_bytes = extract_bytes(
                        pm.committed(),
                        index_to_offset(index as nat, overall_metadata.metadata_node_size as nat),
                        u64::spec_size_of() as nat,
                    );
                    let cdb = u64::spec_from_bytes(cdb_bytes);
                    let crc_bytes = extract_bytes(
                        pm.committed(),
                        index_to_offset(index as nat, overall_metadata.metadata_node_size as nat) + u64::spec_size_of(),
                        u64::spec_size_of() as nat,
                    );
                    let crc = u64::spec_from_bytes(crc_bytes);
                    let entry_bytes = extract_bytes(
                        pm.committed(),
                        index_to_offset(index as nat, overall_metadata.metadata_node_size as nat) + u64::spec_size_of() * 2,
                        ListEntryMetadata::spec_size_of() as nat,
                    );
                    let entry = ListEntryMetadata::spec_from_bytes(entry_bytes);
                    let key_bytes = extract_bytes(
                        pm.committed(),
                        index_to_offset(index as nat, overall_metadata.metadata_node_size as nat) + u64::spec_size_of() * 2 +
                            ListEntryMetadata::spec_size_of(),
                        K::spec_size_of() as nat,
                    );
                    let key = K::spec_from_bytes(key_bytes);
                    let meta = self@.durable_metadata_table[index as int]->Valid_0;
                    &&& u64::bytes_parseable(cdb_bytes)
                    &&& u64::bytes_parseable(crc_bytes)
                    &&& ListEntryMetadata::bytes_parseable(entry_bytes)
                    &&& K::bytes_parseable(key_bytes)
                    &&& cdb == CDB_TRUE
                    &&& crc_bytes == spec_crc_bytes(entry_bytes + key_bytes)
                    &&& crc == meta.crc
                    &&& entry == meta.entry
                    &&& key == meta.key
                }),
        {
            assert(pm.can_crash_as(pm.committed()));
            let metadata_node_size = overall_metadata.metadata_node_size;
            lemma_valid_entry_index(index as nat, overall_metadata.num_keys as nat, metadata_node_size as nat);
            let entry_bytes = extract_bytes(pm.committed(), (index * metadata_node_size) as nat, metadata_node_size as nat);
            assert(extract_bytes(entry_bytes, 0, u64::spec_size_of()) =~=
                   extract_bytes(pm.committed(), index_to_offset(index as nat, overall_metadata.metadata_node_size as nat),
                                 u64::spec_size_of()));
            assert(extract_bytes(entry_bytes, u64::spec_size_of(), u64::spec_size_of()) =~=
                   extract_bytes(pm.committed(),
                        index_to_offset(index as nat, overall_metadata.metadata_node_size as nat) + u64::spec_size_of(),
                                 u64::spec_size_of()));
            assert(extract_bytes(entry_bytes, u64::spec_size_of() * 2, ListEntryMetadata::spec_size_of()) =~=
                   extract_bytes(pm.committed(),
                                index_to_offset(index as nat, overall_metadata.metadata_node_size as nat) + u64::spec_size_of() * 2,
                                 ListEntryMetadata::spec_size_of()));
            assert(extract_bytes(entry_bytes, u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of(),
                                 K::spec_size_of()) =~=
                   extract_bytes(pm.committed(),
                                index_to_offset(index as nat, overall_metadata.metadata_node_size as nat)+ u64::spec_size_of() * 2
                                 + ListEntryMetadata::spec_size_of(),
                                 K::spec_size_of()));
        }

        pub open spec fn spec_replay_log_metadata_table<L>(mem: Seq<u8>, op_log: Seq<LogicalOpLogEntry<L>>) -> Seq<u8>
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
        pub open spec fn apply_log_op_to_metadata_table_mem<L>(mem: Seq<u8>, op: LogicalOpLogEntry<L>) -> Seq<u8>
            where 
                L: PmCopy,
        {
            let table_entry_slot_size = ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of();
            match op {
                LogicalOpLogEntry::CommitMainTableEntry { index } => {
                    let entry_offset = index * table_entry_slot_size;
                    let cdb_bytes = CDB_TRUE.spec_to_bytes();
                    // Note: the cdb is written at offset 0 in the entry
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if entry_offset <= pos < entry_offset + u64::spec_size_of() {
                            cdb_bytes[pos - entry_offset]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                LogicalOpLogEntry::InvalidateMainTableEntry { index } => {
                    let entry_offset = index * table_entry_slot_size;
                    let cdb_bytes = CDB_FALSE.spec_to_bytes();
                    // Note: the cdb is written at offset 0 in the entry
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if entry_offset <= pos < entry_offset + u64::spec_size_of() {
                            cdb_bytes[pos - entry_offset]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                LogicalOpLogEntry::UpdateMainTableEntry { index, new_crc, new_metadata } => {
                    let entry_offset = index * table_entry_slot_size;
                    let crc_addr = entry_offset + u64::spec_size_of();
                    let metadata_addr = crc_addr + u64::spec_size_of();
                    let new_crc_bytes = new_crc.spec_to_bytes();
                    let new_metadata_bytes = new_metadata.spec_to_bytes();
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if crc_addr <= pos < crc_addr + u64::spec_size_of() {
                            new_crc_bytes[pos - crc_addr]
                        } else if metadata_addr <= pos < metadata_addr + ListEntryMetadata::spec_size_of() {
                            new_metadata_bytes[pos - metadata_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                _ => mem // all other log ops do not modify the main table
            }
        }

        spec fn extract_cdb_for_entry(mem: Seq<u8>, k: nat, metadata_node_size: u32) -> u64
        {
            u64::spec_from_bytes(extract_bytes(mem, index_to_offset(k, metadata_node_size as nat), u64::spec_size_of()))
        }

        pub exec fn setup<PM, L>(
            subregion: &WritablePersistentMemorySubregion,
            pm_region: &mut PM,
            num_keys: u64,
            metadata_node_size: u32,
        ) -> (result: Result<(), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
                L: PmCopy
            requires
                subregion.inv(&*old(pm_region)),
                forall |addr: int| #[trigger] subregion.is_writable_absolute_addr_fn()(addr),
                subregion.view(&*(old(pm_region))).no_outstanding_writes(),
                num_keys * metadata_node_size <= subregion.view(&*(old(pm_region))).len() <= u64::MAX,
                metadata_node_size == ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() +
                                      K::spec_size_of(),
            ensures
                subregion.inv(pm_region),
                pm_region.inv(),
                pm_region@.len() == old(pm_region)@.len(),
                match result {
                    Ok(()) => {
                        let replayed_bytes = Self::spec_replay_log_metadata_table(subregion.view(pm_region).flush().committed(), Seq::<LogicalOpLogEntry<L>>::empty());
                        &&& parse_metadata_table::<K>(subregion.view(pm_region).flush().committed(), num_keys, metadata_node_size) matches Some(recovered_view)
                        &&& recovered_view == MetadataTableView::<K>::init(num_keys)
                    }
                    Err(_) => true // TODO
                }
        {
            assert(metadata_node_size >= u64::spec_size_of());
            let ghost original_pm_len = pm_region@.len();

            // invalidate all of the entries
            let mut entry_offset: u64 = 0;
            assert(entry_offset == 0 * metadata_node_size) by {
                vstd::arithmetic::mul::lemma_mul_basics(metadata_node_size as int);
            }
            for index in 0..num_keys 
                invariant
                    subregion.inv(pm_region),
                    subregion.view(pm_region).no_outstanding_writes_in_range(entry_offset as int,
                                                                             subregion.view(pm_region).len() as int),
                    num_keys * metadata_node_size <= subregion.view(pm_region).len() <= u64::MAX,
                    // entry_offset == index * metadata_node_size,
                    entry_offset == index_to_offset(index as nat, metadata_node_size as nat),
                    metadata_node_size >= u64::spec_size_of(),
                    forall |addr: int| #[trigger] subregion.is_writable_absolute_addr_fn()(addr),
                    forall |k: nat| k < index ==> #[trigger] Self::extract_cdb_for_entry(
                        subregion.view(pm_region).flush().committed(), k, metadata_node_size
                    ) == CDB_FALSE,
                    ({
                        let mem = subregion.view(pm_region).flush().committed();
                        forall |k: nat| k < index ==> u64::bytes_parseable(#[trigger] extract_bytes(
                            mem,
                            index_to_offset(k, metadata_node_size as nat),
                            u64::spec_size_of())
                        )
                    }),
                    pm_region@.len() == original_pm_len,
            {
                proof {lemma_valid_entry_index(index as nat, num_keys as nat, metadata_node_size as nat);}
                let ghost v1 = subregion.view(pm_region);
                subregion.serialize_and_write_relative(pm_region, entry_offset, &CDB_FALSE);
                assert(CDB_FALSE.spec_to_bytes().len() == u64::spec_size_of()) by {
                    broadcast use pmcopy_axioms;
                }
                assert forall |k: nat| k < index + 1 implies #[trigger] Self::extract_cdb_for_entry(
                        subregion.view(pm_region).flush().committed(), k, metadata_node_size
                    ) == CDB_FALSE 
                by {
                    let mem = subregion.view(pm_region).flush().committed();
                    if k < index {
                        assert(Self::extract_cdb_for_entry(v1.flush().committed(), k, metadata_node_size) == CDB_FALSE);
                        assert(index_to_offset(k, metadata_node_size as nat) + u64::spec_size_of() <= entry_offset) by {
                            lemma_metadata_fits::<K>(k as int, index as int, metadata_node_size as int);
                        }
                        assert(extract_bytes(mem, index_to_offset(k, metadata_node_size as nat), u64::spec_size_of()) =~= 
                               extract_bytes(v1.flush().committed(), index_to_offset(k, metadata_node_size as nat), u64::spec_size_of()));
                    }
                    else {
                        assert(extract_bytes(mem, index_to_offset(k, metadata_node_size as nat), u64::spec_size_of()) ==
                               CDB_FALSE.spec_to_bytes());
                        broadcast use axiom_to_from_bytes;
                    }
                }

                // TODO: refactor this if you can -- the proof is the same as the above assertion, but we can't have
                // triggers on k in both arithmetic and non arithmetic contexts, so the two conjuncts have to be asserted
                // separately.
                assert forall |k: nat| k < index + 1 implies 
                    #[trigger] u64::bytes_parseable(extract_bytes(subregion.view(pm_region).flush().committed(), k * metadata_node_size as nat, u64::spec_size_of())) 
                by {
                    let mem = subregion.view(pm_region).flush().committed();
                    if k < index {
                        assert(Self::extract_cdb_for_entry(v1.flush().committed(), k, metadata_node_size) == CDB_FALSE);
                        assert(index_to_offset(k, metadata_node_size as nat) + u64::spec_size_of() <= entry_offset) by {
                            lemma_metadata_fits::<K>(k as int, index as int, metadata_node_size as int);
                        }
                        assert(extract_bytes(mem, index_to_offset(k, metadata_node_size as nat), u64::spec_size_of()) =~= 
                            extract_bytes(v1.flush().committed(), k * metadata_node_size as nat, u64::spec_size_of()));
                    }
                    else {
                        assert(extract_bytes(mem, index_to_offset(k, metadata_node_size as nat), u64::spec_size_of()) ==
                            CDB_FALSE.spec_to_bytes());
                        broadcast use axiom_to_from_bytes;
                    }
                }
                
                entry_offset += metadata_node_size as u64;
            }

            let ghost mem = subregion.view(pm_region).flush().committed();
            let ghost op_log = Seq::<LogicalOpLogEntry<L>>::empty();
            let ghost replayed_mem = Self::spec_replay_log_metadata_table(mem, op_log);
            let ghost recovered_view = parse_metadata_table::<K>(mem, num_keys, metadata_node_size);
            let ghost table_entry_slot_size = ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of();

            // Prove that all of the metadata entries are valid. We need to establish this to prove that the recovery view
            // of the table is Some so that we can then reason about its contents.
            assert forall |k: nat| k < num_keys implies {
                validate_metadata_entry::<K>(#[trigger] extract_bytes(mem, (k * metadata_node_size) as nat,
                        metadata_node_size as nat), num_keys as nat)
            } by {
                assert(u64::bytes_parseable(extract_bytes(mem, index_to_offset(k, metadata_node_size as nat), u64::spec_size_of())));
                assert(Self::extract_cdb_for_entry(mem, k, metadata_node_size) == CDB_FALSE);
                // Prove that k is a valid index in the table
                lemma_valid_entry_index(k, num_keys as nat, metadata_node_size as nat);
                // Prove that the subranges used by validate_metadata_entry and extract_cdb_for_entry to check CDB are the same
                lemma_subrange_of_extract_bytes_equal(mem, index_to_offset(k, metadata_node_size as nat), 
                        index_to_offset(k, metadata_node_size as nat), metadata_node_size as nat, u64::spec_size_of());
            }

            proof {
                let entries = parse_metadata_entries::<K>(mem, num_keys as nat, metadata_node_size as nat);
                assert forall |i: nat| 0 <= i < entries.len() implies #[trigger] entries[i as int] matches DurableEntry::Invalid by {
                    lemma_valid_entry_index(i, num_keys as nat, metadata_node_size as nat);
                    lemma_subrange_of_extract_bytes_equal(mem, index_to_offset(i, metadata_node_size as nat), 
                        index_to_offset(i, metadata_node_size as nat), metadata_node_size as nat, u64::spec_size_of());
                    assert(Self::extract_cdb_for_entry(mem, i, metadata_node_size) == CDB_FALSE);
                    assert(Self::extract_cdb_for_entry(mem, i, metadata_node_size) == CDB_FALSE ==> 
                        entries[i as int] matches DurableEntry::Invalid);
                }
                assert(no_duplicate_item_indexes(entries));
            }

            // Prove that entries with CDB of false are None in the recovery view of the table. We already know that all of the entries
            // have CDB_FALSE, so this proves the postcondition that the recovery view is equivalent to fresh initialized table view
            // since all entries in both are None
            let ghost metadata_table = recovered_view.unwrap().get_durable_metadata_table();
            assert forall |k: nat| k < num_keys implies #[trigger] metadata_table[k as int] matches DurableEntry::Invalid by {
                // Prove that k is a valid index in the table
                lemma_valid_entry_index(k, num_keys as nat, metadata_node_size as nat);
                // Prove that the subranges used by validate_metadata_entry and extract_cdb_for_entry to check CDB are the same
                lemma_subrange_of_extract_bytes_equal(mem, (k * metadata_node_size) as nat, (k * metadata_node_size) as nat, metadata_node_size as nat, u64::spec_size_of());
            
                assert(Self::extract_cdb_for_entry(mem, k, metadata_node_size) == CDB_FALSE);
            }
            // We need to reveal the opaque lemma at some point to be able to prove that the general PM invariant holds;
            // it's cleaner to do that here than in the caller
            proof { subregion.lemma_reveal_opaque_inv(pm_region); }
            assert({
                &&& recovered_view matches Some(recovered_view)
                &&& recovered_view =~= MetadataTableView::<K>::init(num_keys)
            });
            
            Ok(())
        }

        pub exec fn start<PM, I, L>(
            subregion: &PersistentMemorySubregion,
            pm_region: &PM,
            overall_metadata: OverallMetadata,
            version_metadata: VersionMetadata,
        ) -> (result: Result<(Self, Vec<(Box<K>, u64, u64)>), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
                I: PmCopy + Sized + std::fmt::Debug,
                L: PmCopy + std::fmt::Debug,
            requires
                subregion.inv(pm_region),
                pm_region@.no_outstanding_writes(),
                overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr, overall_metadata.kvstore_id),
                parse_metadata_table::<K>(
                    subregion.view(pm_region).committed(),
                    overall_metadata.num_keys, 
                    overall_metadata.metadata_node_size 
                ) is Some,
                ListEntryMetadata::spec_size_of() + u64::spec_size_of() * 2 + K::spec_size_of() <= u64::MAX,
                subregion.len() == overall_metadata.main_table_size,
                subregion.view(pm_region).no_outstanding_writes(),
                K::spec_size_of() > 0,
            ensures 
                match result {
                    Ok((main_table, entry_list)) => {
                        let table = parse_metadata_table::<K>(
                            subregion.view(pm_region).committed(),
                            overall_metadata.num_keys, 
                            overall_metadata.metadata_node_size
                        ).unwrap();
                        let key_entry_list_view = Set::new(
                            |val: (K, u64, u64)| {
                                exists |j: u64| {
                                    &&& 0 <= j < table.durable_metadata_table.len()
                                    &&& #[trigger] table.durable_metadata_table[j as int] matches DurableEntry::Valid(entry)
                                    &&& val == (entry.key(), j, entry.item_index())
                        }});
                        let entry_list_view = Seq::new(entry_list@.len(), |i: int| (*entry_list[i].0, entry_list[i].1, entry_list[i].2));
                        let item_index_view = Seq::new(entry_list@.len(), |i: int| entry_list[i].2);

                        &&& main_table.inv(subregion.view(pm_region), overall_metadata)
                        &&& main_table.allocator_inv()
                        &&& main_table.no_outstanding_writes()
                        &&& main_table.pending_allocations_view().is_empty()
                        &&& main_table.pending_deallocations_view().is_empty()
                        // main table states match
                        &&& table == main_table@
                        // the entry list corresponds to the table
                        &&& entry_list_view.to_set() == key_entry_list_view
                        // all indices in the entry list are valid
                        &&& forall |i: int| 0 <= i < entry_list.len() ==> {
                            &&& 0 <= (#[trigger] entry_list[i]).1 < overall_metadata.num_keys 
                            &&& 0 <= entry_list[i].2 < overall_metadata.num_keys
                        }
                        &&& item_index_view.to_set() == main_table@.valid_item_indices()
                        &&& forall|idx: u64| 0 <= idx < main_table.spec_outstanding_cdb_writes().len() ==>
                            main_table.spec_outstanding_cdb_writes()[idx as int] is None
                        &&& forall|idx: u64| 0 <= idx < main_table.spec_outstanding_entry_writes().len() ==>
                            main_table.spec_outstanding_entry_writes()[idx as int] is None
                        &&& main_table.pending_alloc_inv(subregion.view(pm_region).committed(), subregion.view(pm_region).committed(), overall_metadata)
                    }
                    Err(KvError::IndexOutOfRange) => {
                        let entry_slot_size = (ListEntryMetadata::spec_size_of() + u64::spec_size_of() * 2 + K::spec_size_of()) as u64;
                        overall_metadata.num_keys > overall_metadata.main_table_size / entry_slot_size
                    }
                    Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                    Err(KvError::PmemErr{ pmem_err }) => true,
                    Err(_) => false
                }
        {
            let num_keys = overall_metadata.num_keys;
            let metadata_node_size = overall_metadata.metadata_node_size;

            // Since we've already replayed the log, we just need to construct 
            // the allocator and determine which item indices are valid. 

            let mut metadata_allocator: Vec<u64> = Vec::with_capacity(num_keys as usize);
            let mut key_index_pairs: Vec<(Box<K>, u64, u64)> = Vec::new();
            let max_index = overall_metadata.main_table_size / (metadata_node_size as u64);
            let ghost mem = subregion.view(pm_region).committed();
            let mut index = 0;
            let ghost table = parse_metadata_table::<K>(
                mem,
                overall_metadata.num_keys, 
                overall_metadata.metadata_node_size 
            ).unwrap();
            let ghost old_pm_constants = pm_region.constants();

            proof {
                // proves that max_index * metadata_node_size <= overall_metadata.main_table_size
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(overall_metadata.main_table_size as int, metadata_node_size as int);
                // This helps Verus prove that we don't go out of bounds when reading the entry at index * metadata_node_size
                assert(metadata_node_size * max_index == max_index * metadata_node_size) by {
                    vstd::arithmetic::mul::lemma_mul_is_commutative(metadata_node_size as int, max_index as int);
                }

                // Proves that there is currently only one crash state, and it recovers to the current ghost table state.
                lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(subregion.view(pm_region));
                assert(forall |s| subregion.view(pm_region).can_crash_as(s) ==> s == mem);
                assert(parse_metadata_table::<K>(
                    mem,
                    overall_metadata.num_keys, 
                    overall_metadata.metadata_node_size 
                ) == Some(table));
            }

            while index < num_keys
                invariant
                    subregion.inv(pm_region),
                    index <= num_keys,
                    index * metadata_node_size <= overall_metadata.main_table_size <= u64::MAX,
                    max_index == overall_metadata.main_table_size / (metadata_node_size as u64),
                    max_index * metadata_node_size <= overall_metadata.main_table_size,
                    metadata_node_size * max_index == max_index * metadata_node_size, 
                    index <= max_index,
                    ListEntryMetadata::spec_size_of() + u64::spec_size_of() * 2 + K::spec_size_of() == metadata_node_size,
                    num_keys == overall_metadata.num_keys,
                    subregion.len() == overall_metadata.main_table_size,
                    subregion.view(pm_region).no_outstanding_writes(),
                    mem == subregion.view(pm_region).committed(),
                    old_pm_constants == pm_region.constants(),
                    subregion.view(pm_region).can_crash_as(subregion.view(pm_region).committed()),
                    forall |s| #[trigger] subregion.view(pm_region).can_crash_as(s) ==>  
                        parse_metadata_table::<K>(
                            s,
                            overall_metadata.num_keys, 
                            overall_metadata.metadata_node_size 
                        ) == Some(table),
                    metadata_node_size == overall_metadata.metadata_node_size,
                    forall |i: u64| 0 <= i < index ==> {
                        let entry = #[trigger] table.durable_metadata_table[i as int];
                        entry matches DurableEntry::Invalid <==> 
                            metadata_allocator@.contains(i)
                    },
                    forall |i: int| 0 <= i < metadata_allocator.len() ==> #[trigger] metadata_allocator[i] < index,
                    forall |i: int, j: int| 0 <= i < metadata_allocator.len() && 0 <= j < metadata_allocator.len() && i != j ==>
                        metadata_allocator[i] != metadata_allocator[j],
                    ({
                        let entry_list_view = Seq::new(key_index_pairs@.len(), |i: int| (*key_index_pairs[i].0, key_index_pairs[i].1, key_index_pairs[i].2));
                        let item_index_view = Seq::new(key_index_pairs@.len(), |i: int| key_index_pairs[i].2);
                        &&& forall |i: u64| 0 <= i < index ==> {
                                let entry = #[trigger] table.durable_metadata_table[i as int];
                                entry matches DurableEntry::Valid(valid_entry) ==> entry_list_view.contains((valid_entry.key(), i, valid_entry.item_index()))
                            }
                        &&& forall |i: int| 0 <= i < entry_list_view.len() ==> {
                                let table_index = entry_list_view[i].1;
                                let item_index = entry_list_view[i].2;
                                &&& table.durable_metadata_table[table_index as int] matches DurableEntry::Valid(valid_entry)
                                &&& valid_entry.key() == #[trigger] entry_list_view[i].0
                                &&& valid_entry.item_index() == item_index
                                &&& 0 <= table_index < table.durable_metadata_table.len()
                                &&& table.valid_item_indices().contains(item_index)
                                &&& item_index_view.contains(item_index)
                            }
                        &&& item_index_view.to_set().subset_of(table.valid_item_indices())
                    }),
                    forall |i: int| 0 <= i < key_index_pairs.len() ==> {
                        &&& 0 <= (#[trigger] key_index_pairs[i]).1 < overall_metadata.num_keys 
                        &&& 0 <= key_index_pairs[i].2 < overall_metadata.num_keys
                    },
                    K::spec_size_of() > 0,
                    metadata_allocator@.len() <= index,
                    metadata_allocator@.no_duplicates(),
                    // no duplicate item indexes in the main table
                    // TODO: could/should this go in `parse_metadata_table` instead?
                    forall |i: nat, j: nat| i < j < index ==> {
                        &&& #[trigger] table.durable_metadata_table[i as int] matches DurableEntry::Valid(entry1)
                        &&& #[trigger] table.durable_metadata_table[j as int] matches DurableEntry::Valid(entry2)
                    } ==> table.durable_metadata_table[i as int]->Valid_0.item_index() != 
                            table.durable_metadata_table[j as int]->Valid_0.item_index()
            {
                let ghost old_entry_list_view = Seq::new(key_index_pairs@.len(), |i: int| (*key_index_pairs[i].0, key_index_pairs[i].1, key_index_pairs[i].2));

                if index < max_index {
                    // This case proves that index * metadata_node_size will not overflow or go out of bounds (here or at the end
                    // of the loop) if index < max_index
                    proof {
                        lemma_mul_strict_inequality(index as int, max_index as int, metadata_node_size as int);
                        if index + 1 < max_index {
                            lemma_mul_strict_inequality(index + 1, max_index as int, metadata_node_size as int);
                        }
                        // also prove that we can read the next entry at this index without going out of bounds
                        vstd::arithmetic::mul::lemma_mul_is_distributive_add(metadata_node_size as int, index as int, 1int);
                        // asserting these here seems to help stabilize some arithmetic assertions later
                        assert(metadata_node_size * (index + 1) == metadata_node_size * index + metadata_node_size);
                        assert(metadata_node_size * (index + 1) <= metadata_node_size * max_index);
                    }
                } else {
                    proof { lemma_fundamental_div_mod(overall_metadata.main_table_size as int, metadata_node_size as int); }
                    return Err(KvError::IndexOutOfRange);
                }

                let entry_offset = index * (metadata_node_size as u64);

                // Read the CDB at this slot. If it's valid, we need to read the rest of the 
                // entry to get the key and check its CRC
                let relative_cdb_addr = entry_offset;
                proof {
                    lemma_if_table_parseable_then_all_entries_parseable::<K>(
                        subregion.view(pm_region).committed(),
                        overall_metadata.num_keys, 
                        overall_metadata.metadata_node_size
                    );
                    // trigger for CDB bytes parseable
                    assert(u64::bytes_parseable(extract_bytes(
                        subregion.view(pm_region).committed(),
                        index_to_offset(index as nat, metadata_node_size as nat),
                        u64::spec_size_of()
                    )));
                }
                let cdb = match subregion.read_relative_aligned::<u64, _>(pm_region, relative_cdb_addr) {
                    Ok(cdb) => cdb,
                    Err(e) => return Err(KvError::PmemErr { pmem_err: e })
                };
                let ghost relative_cdb_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| relative_cdb_addr + i);
                let ghost true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem[relative_cdb_addrs[i]]);
                let ghost true_cdb = u64::spec_from_bytes(true_cdb_bytes);
                // Proving that true_cdb_bytes matches various ways of obtaining the CDB subrange from mem is useful later to prove whether 
                // an entry is valid or invalid based on the value of its CDB
                assert(true_cdb_bytes == extract_bytes(subregion.view(pm_region).committed(), relative_cdb_addr as nat, u64::spec_size_of()));
                assert(true_cdb_bytes == extract_bytes(
                    extract_bytes(mem, (index * overall_metadata.metadata_node_size) as nat, overall_metadata.metadata_node_size as nat),
                    0,
                    u64::spec_size_of()
                ));

                match check_cdb_in_subregion(cdb, subregion, pm_region, Ghost(pm_region.constants().impervious_to_corruption), Ghost(relative_cdb_addrs)) {
                    Some(false) => {
                        // Slot is free -- we just need to put it in the allocator
                        let ghost old_metadata_allocator = metadata_allocator@;
                        metadata_allocator.push(index);
                        proof {
                            // these assertions hit triggers needed by the loop invariants
                            assert(metadata_allocator@.subrange(0, metadata_allocator@.len() - 1) == old_metadata_allocator);
                            assert(metadata_allocator@[metadata_allocator@.len() - 1] == index);
                            // Invoking this lemma here proves that the CDB we just read is the same one checked by parse_metadata_entry
                            lemma_subrange_of_extract_bytes_equal(mem, relative_cdb_addr as nat, relative_cdb_addr as nat, metadata_node_size as nat, u64::spec_size_of());
                        }
                    }, 
                    Some(true) => {
                        // TODO: refactor this into its own function
                        // We have to read the entry to get its key and item index
                        // We don't need the metadata here, but we have to read it so we can check the CRC
                        
                        let relative_crc_addr = relative_cdb_addr + traits_t::size_of::<u64>() as u64;
                        let relative_entry_addr = relative_crc_addr + traits_t::size_of::<u64>() as u64;
                        let relative_key_addr = relative_entry_addr + traits_t::size_of::<ListEntryMetadata>()  as u64;

                        let ghost relative_crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| relative_crc_addr + i);
                        let ghost relative_entry_addrs = Seq::new(ListEntryMetadata::spec_size_of() as nat, |i: int| relative_entry_addr + i);
                        let ghost relative_key_addrs = Seq::new(K::spec_size_of() as nat, |i: int| relative_key_addr + i);

                        let ghost true_crc_bytes = Seq::new(relative_crc_addrs.len(), |i: int| subregion.view(pm_region).committed()[relative_crc_addrs[i]]);
                        let ghost true_entry_bytes = Seq::new(relative_entry_addrs.len(), |i: int| subregion.view(pm_region).committed()[relative_entry_addrs[i]]);
                        let ghost true_key_bytes = Seq::new(relative_key_addrs.len(), |i: int| subregion.view(pm_region).committed()[relative_key_addrs[i]]);

                        let ghost true_crc = u64::spec_from_bytes(true_crc_bytes);
                        let ghost true_entry = ListEntryMetadata::spec_from_bytes(true_entry_bytes);
                        let ghost true_key = K::spec_from_bytes(true_key_bytes);

                        proof {
                            assert(index * metadata_node_size + u64::spec_size_of() * 2 < subregion.len());

                            assert(true_crc_bytes == extract_bytes(subregion.view(pm_region).committed(), relative_crc_addr as nat, u64::spec_size_of()));
                            assert(true_entry_bytes == extract_bytes(subregion.view(pm_region).committed(), relative_entry_addr as nat, ListEntryMetadata::spec_size_of()));
                            assert(true_entry_bytes == extract_bytes(
                                extract_bytes(mem, (index * metadata_node_size) as nat, metadata_node_size as nat),
                                u64::spec_size_of() * 2,
                                ListEntryMetadata::spec_size_of()
                            ));
                            assert(true_key_bytes == extract_bytes(subregion.view(pm_region).committed(), relative_key_addr as nat, K::spec_size_of()));
                            assert(true_key_bytes == extract_bytes(
                                extract_bytes(mem, (index * metadata_node_size) as nat, metadata_node_size as nat),
                                u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of(),
                                K::spec_size_of()
                            ));

                            lemma_if_table_parseable_then_all_entries_parseable::<K>(
                                subregion.view(pm_region).committed(),
                                overall_metadata.num_keys, 
                                overall_metadata.metadata_node_size
                            );
                        }
                        
                        let crc = match subregion.read_relative_aligned::<u64, PM>(pm_region, relative_crc_addr) {
                            Ok(crc) => crc,
                            Err(e) => return Err(KvError::PmemErr { pmem_err: e })
                        };
                        let entry = match subregion.read_relative_aligned::<ListEntryMetadata, PM>(pm_region,
                                                                                                   relative_entry_addr) {
                            Ok(entry) => entry,
                            Err(e) => return Err(KvError::PmemErr { pmem_err: e })
                        };
                        let key = match subregion.read_relative_aligned::<K, PM>(pm_region, relative_key_addr) {
                            Ok(key) => key,
                            Err(e) => return Err(KvError::PmemErr { pmem_err: e })
                        };
                        
                        if !check_crc_for_two_reads_in_subregion(
                            entry.as_slice(), key.as_slice(), crc.as_slice(), subregion, pm_region, 
                            Ghost(pm_region.constants().impervious_to_corruption), Ghost(relative_entry_addrs),
                            Ghost(relative_key_addrs), Ghost(relative_crc_addrs)) {
                            assert(!pm_region.constants().impervious_to_corruption);
                            return Err(KvError::CRCMismatch);
                        }

                        let ghost pre_entry_list = Seq::new(key_index_pairs@.len(), |i: int| (*key_index_pairs[i].0, key_index_pairs[i].1, key_index_pairs[i].2));

                        let crc = crc.extract_init_val(Ghost(true_crc));
                        let key = key.extract_init_val(Ghost(true_key));
                        let metadata = entry.extract_init_val(Ghost(true_entry));
                        
                        let ghost old_item_index_view = Seq::new(key_index_pairs@.len(), |i: int| key_index_pairs[i].2);
                        assert(old_item_index_view.to_set().subset_of(table.valid_item_indices()));
                        let ghost old_key_index_pairs = key_index_pairs;

                        let ghost old_entry_list_view = Seq::new(key_index_pairs@.len(), |i: int| (*key_index_pairs[i].0, key_index_pairs[i].1, key_index_pairs[i].2));
                        assert(forall |i: int| 0 <= i < old_entry_list_view.len() ==> {
                            let entry = #[trigger] old_entry_list_view[i];
                            let table_index = entry.1;
                            let item_index = entry.2;
                            &&& table.durable_metadata_table[table_index as int] matches DurableEntry::Valid(valid_entry)
                            &&& valid_entry.item_index() == item_index
                        });

                        key_index_pairs.push((key, index, metadata.item_index));

                        assert(key_index_pairs@.subrange(0, key_index_pairs.len() - 1) == old_key_index_pairs@);
                        assert(key_index_pairs@[key_index_pairs.len() - 1] == (key, index, metadata.item_index));
                        
                        proof {
                            let new_item_index_view = Seq::new(key_index_pairs@.len(), |i: int| key_index_pairs[i].2);
                            let entry_list_view = Seq::new(key_index_pairs@.len(), |i: int| (*key_index_pairs[i].0, key_index_pairs[i].1, key_index_pairs[i].2));
                            
                            assert(entry_list_view.subrange(0, entry_list_view.len() - 1) == old_entry_list_view);

                            assert forall |i: int| 0 <= i < entry_list_view.len() implies {
                                let entry = #[trigger] entry_list_view[i];
                                let table_index = entry.1;
                                let item_index = entry.2;
                                &&& table.durable_metadata_table[table_index as int] matches DurableEntry::Valid(valid_entry)
                                &&& valid_entry.key() == entry.0
                                &&& valid_entry.item_index() == item_index
                                &&& 0 <= table_index < table.durable_metadata_table.len()
                                &&& table.valid_item_indices().contains(item_index)
                                &&& new_item_index_view.contains(item_index)
                            } by {
                                let entry = entry_list_view[i];
                                let table_index = entry.1;
                                let item_index = entry.2;

                                assert(item_index == new_item_index_view[i]);
                                if i < entry_list_view.len() - 1 {
                                    assert(entry == old_entry_list_view[i]);
                                    assert(table.durable_metadata_table[table_index as int] matches DurableEntry::Valid(valid_entry));
                                }

                                assert(table.durable_metadata_table[table_index as int] matches DurableEntry::Valid(valid_entry));
                            }

                            // This witness and the following few assertions help us maintain the loop invariant that 
                            // the set of valid item indices we are constructing is a subset of table.valid_item_indices()
                            let witness = table.durable_metadata_table[index as int];
                            assert(witness matches DurableEntry::Valid(valid_entry));
                            if let DurableEntry::Valid(valid_entry) = witness {
                                assert(valid_entry.item_index() == metadata.item_index);
                            }
                            assert(exists |j: int| {
                                &&& 0 <= j < table.durable_metadata_table.len() 
                                &&& #[trigger] table.durable_metadata_table[j] matches DurableEntry::Valid(valid_entry) 
                                &&& valid_entry.item_index() == metadata.item_index
                            }); 
                            assert(table.valid_item_indices().contains(metadata.item_index));
                            assert(new_item_index_view == old_item_index_view.push(metadata.item_index));
                            assert(new_item_index_view.to_set().subset_of(table.valid_item_indices()));
                        }
                    }
                    None => return Err(KvError::CRCMismatch)
                }

                proof {
                    let entry_list_view = Seq::new(key_index_pairs@.len(), |i: int| (*key_index_pairs[i].0, key_index_pairs[i].1, key_index_pairs[i].2));
                
                    assert forall |i: u64| 0 <= i <= index implies {
                        let entry = #[trigger] table.durable_metadata_table[i as int];
                        entry matches DurableEntry::Valid(valid_entry) ==> entry_list_view.contains((valid_entry.key(), i, valid_entry.item_index()))
                    } by {
                        // We already know this is true for values less than index from the loop invariant.
                        // To help Verus prove this, we need to establish that the part of the entry list we are making an assertion about has not
                        // changed on this iteration.
                        assert(entry_list_view == old_entry_list_view || entry_list_view.subrange(0, entry_list_view.len() - 1) == old_entry_list_view);
                        // Prove that the assertion holds when i == index
                        if i == index {
                            let entry = table.durable_metadata_table[i as int];
                            if let DurableEntry::Valid(valid_entry) = entry {
                                assert(entry_list_view[entry_list_view.len() - 1] == (valid_entry.key(), index, valid_entry.item_index()));
                            }
                        }
                    }
                }
                index += 1;
            }

            let main_table = MetadataTable {
                metadata_node_size,
                metadata_table_free_list: metadata_allocator,
                pending_allocations: Vec::new(),
                pending_deallocations: Vec::new(),
                state: Ghost(parse_metadata_table::<K>(
                    subregion.view(pm_region).committed(),
                    overall_metadata.num_keys, 
                    overall_metadata.metadata_node_size 
                ).unwrap()),
                outstanding_cdb_writes: Ghost(Seq::<Option<bool>>::new(num_keys as nat, |i: int| None)),
                outstanding_entry_writes: Ghost(Seq::<Option<MetadataTableViewEntry<K>>>::new(num_keys as nat,                                                                            |i: int| None)),
            };
            assert(main_table.pending_deallocations_view().is_empty()) by {
                assert(main_table.pending_deallocations_view() =~= Set::<u64>::empty());
            }

            proof {
                let key_entry_list_view = Set::new(
                    |val: (K, u64, u64)| {
                        exists |j: u64| {
                            &&& 0 <= j < table.durable_metadata_table.len()
                            &&& #[trigger] table.durable_metadata_table[j as int] matches DurableEntry::Valid(entry)
                            &&& val == (entry.key(), j, entry.item_index())
                }});
                let entry_list_view = Seq::new(key_index_pairs@.len(), |i: int| (*key_index_pairs[i].0, key_index_pairs[i].1, key_index_pairs[i].2));
                let item_index_view = Seq::new(key_index_pairs@.len(), |i: int| key_index_pairs[i].2);

                assert(main_table.allocator_view() =~= main_table.free_indices());
                assert(entry_list_view.to_set() == key_entry_list_view);
                assert(item_index_view.to_set() == main_table@.valid_item_indices());

                metadata_allocator@.unique_seq_to_set();

                let pm_view = subregion.view(pm_region);

                assert forall |i| 0 <= i < main_table.state@.durable_metadata_table.len() implies {
                    &&& main_table.outstanding_cdb_write_matches_pm_view(pm_view, i, overall_metadata.metadata_node_size)
                    &&& main_table.outstanding_entry_write_matches_pm_view(pm_view, i, overall_metadata.metadata_node_size)
                } by {
                    
                    let metadata_node_size = overall_metadata.metadata_node_size;
                    lemma_metadata_fits::<K>(i as int, num_keys as int, metadata_node_size as int);
                    assert(pm_view.no_outstanding_writes_in_range(i * metadata_node_size,
                                                                  i * metadata_node_size + u64::spec_size_of()));
                }

                assert(forall |s| #[trigger] pm_view.can_crash_as(s) ==>
                    parse_metadata_table::<K>(s, overall_metadata.num_keys, overall_metadata.metadata_node_size) == Some(main_table@));
            }

            Ok((main_table, key_index_pairs))
        }

        pub exec fn get_key_and_metadata_entry_at_index<PM>(
            &self,
            subregion: &PersistentMemorySubregion,
            pm_region: &PM,
            metadata_index: u64,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        ) -> (result: Result<(Box<K>, Box<ListEntryMetadata>), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires
                subregion.inv(pm_region),
                self.inv(subregion.view(pm_region), overall_metadata),
                0 <= metadata_index < overall_metadata.num_keys,
                self@.durable_metadata_table[metadata_index as int] is Valid,
                self.spec_outstanding_cdb_writes()[metadata_index as int] is None,
                self.spec_outstanding_entry_writes()[metadata_index as int] is None,
            ensures
                ({
                    match result {
                        Ok((key, entry)) => {
                            let meta = self@.durable_metadata_table[metadata_index as int]->Valid_0;
                            &&& meta.key == key
                            &&& meta.entry == entry
                        },
                        Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                        _ => false,
                    }
                }),
        {
            let ghost pm_view = subregion.view(pm_region);
            let metadata_node_size = self.metadata_node_size;
            proof {
                lemma_valid_entry_index(metadata_index as nat, overall_metadata.num_keys as nat, metadata_node_size as nat);
            }

            let slot_addr = metadata_index * (metadata_node_size as u64);
            let cdb_addr = slot_addr;
            let crc_addr = cdb_addr + traits_t::size_of::<u64>() as u64;
            let entry_addr = crc_addr + traits_t::size_of::<u64>() as u64;
            let key_addr = entry_addr + traits_t::size_of::<ListEntryMetadata>() as u64;

            // 1. Read the CDB, metadata entry, key, and CRC at the index
            let ghost mem = pm_view.committed();

            let ghost true_cdb_bytes = extract_bytes(mem, cdb_addr as nat, u64::spec_size_of());
            let ghost true_crc_bytes = extract_bytes(mem, crc_addr as nat, u64::spec_size_of());
            let ghost true_entry_bytes = extract_bytes(mem, entry_addr as nat, ListEntryMetadata::spec_size_of());
            let ghost true_key_bytes = extract_bytes(mem, key_addr as nat, K::spec_size_of());

            let ghost true_cdb = u64::spec_from_bytes(true_cdb_bytes);
            let ghost true_crc = u64::spec_from_bytes(true_crc_bytes);
            let ghost true_entry = ListEntryMetadata::spec_from_bytes(true_entry_bytes);
            let ghost true_key = K::spec_from_bytes(true_key_bytes);

            let ghost cdb_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| cdb_addr + subregion.start() + i);
            let ghost entry_addrs = Seq::new(ListEntryMetadata::spec_size_of() as nat,
                                             |i: int| entry_addr + subregion.start() + i);
            let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| crc_addr + subregion.start() + i);
            let ghost key_addrs = Seq::new(K::spec_size_of() as nat, |i: int| key_addr + subregion.start() + i);

            // 2. Check the CDB to determine whether the entry is valid
            proof {
                assert(self.outstanding_cdb_write_matches_pm_view(pm_view, metadata_index as int, metadata_node_size));
                self.lemma_establish_bytes_parseable_for_valid_entry(pm_view, overall_metadata, metadata_index);
                assert(extract_bytes(pm_view.committed(), cdb_addr as nat, u64::spec_size_of()) =~=
                       Seq::new(u64::spec_size_of() as nat, |i: int| pm_region@.committed()[cdb_addrs[i]]));
            }
            let cdb = match subregion.read_relative_aligned::<u64, PM>(pm_region, cdb_addr) {
                Ok(cdb) => cdb,
                Err(_) => {
                    assert(false);
                    return Err(KvError::EntryIsNotValid);
                }
            };
            let cdb_result = check_cdb(cdb, Ghost(pm_region@.committed()),
                                       Ghost(pm_region.constants().impervious_to_corruption), Ghost(cdb_addrs));
            match cdb_result {
                Some(true) => {}, // continue 
                Some(false) => { assert(false); return Err(KvError::EntryIsNotValid); },
                None => { return Err(KvError::CRCMismatch); },
            }

            proof {
                assert(self.outstanding_entry_write_matches_pm_view(pm_view, metadata_index as int, metadata_node_size));
                assert(extract_bytes(pm_view.committed(), crc_addr as nat, u64::spec_size_of()) =~=
                       Seq::new(u64::spec_size_of() as nat, |i: int| pm_region@.committed()[crc_addrs[i]]));
                assert(extract_bytes(pm_view.committed(), entry_addr as nat, ListEntryMetadata::spec_size_of()) =~=
                       Seq::new(ListEntryMetadata::spec_size_of() as nat, |i: int| pm_region@.committed()[entry_addrs[i]]));
                assert(extract_bytes(pm_view.committed(), key_addr as nat, K::spec_size_of()) =~=
                       Seq::new(K::spec_size_of() as nat, |i: int| pm_region@.committed()[key_addrs[i]]));
            }
            let crc = match subregion.read_relative_aligned::<u64, PM>(pm_region, crc_addr) {
                Ok(crc) => crc,
                Err(e) => { assert(false); return Err(KvError::PmemErr { pmem_err: e }); },
            };
            let metadata_entry = match subregion.read_relative_aligned::<ListEntryMetadata, PM>(pm_region, entry_addr) {
                Ok(metadata_entry) => metadata_entry,
                Err(e) => { assert(false); return Err(KvError::PmemErr { pmem_err: e }); },
            };
            let key = match subregion.read_relative_aligned::<K, PM>(pm_region, key_addr) {
                Ok(key) => key,
                Err(e) => { assert(false); return Err(KvError::PmemErr {pmem_err: e }); },
            };

            // 3. Check for corruption
            if !check_crc_for_two_reads(
                metadata_entry.as_slice(), key.as_slice(), crc.as_slice(), Ghost(pm_region@.committed()),
                Ghost(pm_region.constants().impervious_to_corruption), Ghost(entry_addrs), Ghost(key_addrs),
                Ghost(crc_addrs)) 
            {
                return Err(KvError::CRCMismatch);
            }

            // 4. Return the metadata entry and key
            let metadata_entry = metadata_entry.extract_init_val(Ghost(true_entry));
            let key = key.extract_init_val(Ghost(true_key));
            Ok((key, metadata_entry))
        }

        proof fn lemma_changing_invalid_entry_doesnt_affect_parse_metadata_table(
            self: Self,
            v1: PersistentMemoryRegionView,
            v2: PersistentMemoryRegionView,
            crash_state2: Seq<u8>,
            overall_metadata: OverallMetadata,
            which_entry: u64,
        )
            requires
                self.inv(v1, overall_metadata),
                self.allocator_view().contains(which_entry),
                v1.len() == v2.len(),
                v2.can_crash_as(crash_state2),
                forall|addr: int| {
                    let start_addr = which_entry * overall_metadata.metadata_node_size;
                    let end_addr = start_addr + overall_metadata.metadata_node_size;
                    &&& 0 <= addr < v1.len()
                    &&& !(start_addr + u64::spec_size_of() <= addr < end_addr)
                } ==> v2.state[addr] == v1.state[addr],
            ensures
                parse_metadata_table::<K>(crash_state2, overall_metadata.num_keys, overall_metadata.metadata_node_size)
                    == Some(self@),
        {
            let num_keys = overall_metadata.num_keys;
            let metadata_node_size = overall_metadata.metadata_node_size;
            let start_addr = which_entry * metadata_node_size;
            let end_addr = start_addr + metadata_node_size;
            let crc_addr = start_addr + u64::spec_size_of();
            let can_views_differ_at_addr = |addr: int| crc_addr <= addr < end_addr;
            assert(which_entry < num_keys);
            let crash_state1 = lemma_get_crash_state_given_one_for_other_view_differing_only_at_certain_addresses(
                v2, v1, crash_state2, can_views_differ_at_addr
            );
            assert(parse_metadata_table::<K>(crash_state1, num_keys, metadata_node_size) == Some(self@));
            lemma_valid_entry_index(which_entry as nat, num_keys as nat, metadata_node_size as nat);
            let entry_bytes = extract_bytes(crash_state1,
                                            index_to_offset(which_entry as nat, metadata_node_size as nat),
                                            metadata_node_size as nat);
            assert(validate_metadata_entry::<K>(entry_bytes, num_keys as nat));
            lemma_subrange_of_subrange_forall(crash_state1);
            assert forall|addr: int| crc_addr <= addr < end_addr implies
                       address_belongs_to_invalid_main_table_entry(addr, crash_state1, num_keys, metadata_node_size)
            by {
                assert(addr / metadata_node_size as int == which_entry) by {
                    lemma_fundamental_div_mod_converse(
                        addr, metadata_node_size as int, which_entry as int, addr - which_entry * metadata_node_size
                    );
                }
            }
            assert forall|addr: int| 0 <= addr < crash_state1.len() && crash_state1[addr] != crash_state2[addr] implies
                   #[trigger] address_belongs_to_invalid_main_table_entry(addr, crash_state1, num_keys,
                                                                          metadata_node_size) by {
                assert(can_views_differ_at_addr(addr));
            }
            lemma_parse_metadata_table_doesnt_depend_on_fields_of_invalid_entries::<K>(
                crash_state1, crash_state2, num_keys, metadata_node_size
            );
        }

        // Since metadata table entries have a valid CDB, we can tentatively write the whole entry and log a commit op for it,
        // then flip the CDB once the log has been committed
        pub exec fn tentative_create<Perm, PM>(
            &mut self,
            subregion: &WriteRestrictedPersistentMemorySubregion,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
            list_node_index: u64,
            item_table_index: u64,
            key: &K,
            Tracked(perm): Tracked<&Perm>,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        ) -> (result: Result<u64, KvError<K>>)
            where 
                Perm: CheckPermission<Seq<u8>>,
                PM: PersistentMemoryRegion,
            requires 
                subregion.inv(old::<&mut _>(wrpm_region), perm),
                old(self).inv(subregion.view(old::<&mut _>(wrpm_region)), overall_metadata),
                subregion.len() >= overall_metadata.main_table_size,
                old(self).subregion_grants_access_to_free_slots(*subregion),
                old(self).allocator_inv(),
            ensures
                subregion.inv(wrpm_region, perm),
                self.inv(subregion.view(wrpm_region), overall_metadata),
                self.allocator_inv(),
                subregion.view(wrpm_region).committed() == subregion.view(old::<&mut _>(wrpm_region)).committed(),
                match result {
                    Ok(index) => {
                        &&& old(self).allocator_view().contains(index)
                        &&& forall|other_index: u64| self.allocator_view().contains(other_index) <==>
                            old(self).allocator_view().contains(other_index) && other_index != index
                        &&& self@.durable_metadata_table == old(self)@.durable_metadata_table
                        &&& self.spec_outstanding_cdb_writes().len() == self.spec_outstanding_entry_writes().len() ==
                            overall_metadata.num_keys
                        &&& forall |i: int| 0 <= i < overall_metadata.num_keys ==>
                            #[trigger] self.spec_outstanding_cdb_writes()[i] ==
                            old(self).spec_outstanding_cdb_writes()[i]
                        &&& forall |i: int| 0 <= i < overall_metadata.num_keys && i != index ==>
                            #[trigger] self.spec_outstanding_entry_writes()[i] ==
                            old(self).spec_outstanding_entry_writes()[i]
                        &&& self.spec_outstanding_entry_writes()[index as int] matches Some(e)
                        &&& e.key == *key
                        &&& e.entry.head == list_node_index
                        &&& e.entry.tail == list_node_index
                        &&& e.entry.length == 0
                        &&& e.entry.first_entry_offset == 0
                        &&& e.entry.item_index == item_table_index
                    },
                    Err(KvError::OutOfSpace) => {
                        &&& self@ == old(self)@
                        &&& self.allocator_view() == old(self).allocator_view()
                        &&& self.pending_allocations_view() == old(self).pending_allocations_view()
                        &&& self.pending_deallocations_view() == old(self).pending_deallocations_view()
                        &&& self.allocator_view().len() == 0
                        &&& wrpm_region == old(wrpm_region)
                    },
                    _ => false,
                }
        {
            let ghost old_pm_view = subregion.view(wrpm_region);
            assert(self.inv(old_pm_view, overall_metadata));

            // 1. pop an index from the free list
            // since this index is on the free list, its CDB is already false
            let free_index = match self.metadata_table_free_list.pop(){
                Some(index) => index,
                None => {
                    assert(self.metadata_table_free_list@.to_set().len() == 0) by {
                        self.metadata_table_free_list@.lemma_cardinality_of_set();
                    }

                    assert forall |i| 0 <= i < self@.durable_metadata_table.len() implies
                        self.outstanding_cdb_write_matches_pm_view(old_pm_view, i,
                                                                   overall_metadata.metadata_node_size) by {
                        assert(old(self).outstanding_cdb_write_matches_pm_view(old_pm_view, i,
                                                                             overall_metadata.metadata_node_size));
                    }

                    assert forall |i| 0 <= i < self@.durable_metadata_table.len() implies
                           self.outstanding_entry_write_matches_pm_view(old_pm_view, i,
                                                                        overall_metadata.metadata_node_size) by {
                        assert(old(self).outstanding_entry_write_matches_pm_view(old_pm_view, i,
                                                                               overall_metadata.metadata_node_size));
                    }

                    return Err(KvError::OutOfSpace);
                },
            };
            self.pending_allocations.push(free_index);
            assert(self.pending_allocations@.subrange(0, old(self).pending_allocations@.len() as int) == old(self).pending_allocations@);
            assert(forall |idx: u64| old(self).pending_allocations@.contains(idx) ==> self.pending_allocations@.contains(idx));
            
            assert(old(self).allocator_view().contains(free_index)) by {
                assert(old(self).metadata_table_free_list@.last() == free_index);
            }
            
            assert(self.allocator_view().len() < old(self).allocator_view().len()) by {
                assert(self.metadata_table_free_list@.len() < old(self).metadata_table_free_list@.len());
                self.metadata_table_free_list@.unique_seq_to_set();
                old(self).metadata_table_free_list@.unique_seq_to_set();
            }

            // assert forall |idx: u64| self.pending_allocations@.contains(idx) implies {
            //     ||| self@.durable_metadata_table[idx as int] matches DurableEntry::Invalid 
            //     ||| self@.durable_metadata_table[idx as int] matches DurableEntry::Tentative(_)
            // } by {
            //     if !old(self).pending_allocations@.contains(idx) {
            //         assert(old(self).metadata_table_free_list@.contains(idx));
            //     }
            // }

            // assert forall |idx: u64| self.metadata_table_free_list@.contains(idx) implies 
            //     self@.durable_metadata_table[idx as int] matches DurableEntry::Invalid 
            // by { assert(old(self).metadata_table_free_list@.contains(idx)); }

            proof {
                // Prove that the allocator and pending allocations lists maintain their invariants
                assert(self.pending_allocations@ == old(self).pending_allocations@.push(free_index));
                assert forall |idx| self.pending_allocations@.contains(idx) implies idx < overall_metadata.num_keys by {
                    if idx == free_index {
                        assert(free_index < overall_metadata.num_keys);
                    } else {
                        assert(old(self).pending_allocations@.contains(idx));
                    }
                }
                assert forall |idx| self.metadata_table_free_list@.contains(idx) implies idx < overall_metadata.num_keys by {
                    assert(old(self).metadata_table_free_list@.contains(idx));
                }
            }

            // 2. construct the entry with list metadata and item index
            let entry = ListEntryMetadata::new(list_node_index, list_node_index, 0, 0, item_table_index);

            // 3. calculate the CRC of the entry + key 
            let mut digest = CrcDigest::new();
            digest.write(&entry);
            digest.write(key);
            let crc = digest.sum64();

            broadcast use pmcopy_axioms;
            
            // 4. write CRC and entry 
            let metadata_node_size = self.metadata_node_size;
            proof {
                lemma_valid_entry_index(free_index as nat, overall_metadata.num_keys as nat, metadata_node_size as nat);
                assert(old(self).spec_outstanding_entry_writes()[free_index as int] is None);
                assert(old(self).outstanding_entry_write_matches_pm_view(old_pm_view, free_index as int,
                                                                       metadata_node_size));
            }
            let slot_addr = free_index * metadata_node_size as u64;
            // CDB is at slot addr -- we aren't setting that one yet
            let crc_addr = slot_addr + traits_t::size_of::<u64>() as u64;
            let entry_addr = crc_addr + traits_t::size_of::<u64>() as u64;
            let key_addr = entry_addr + traits_t::size_of::<ListEntryMetadata>() as u64;

            assert(subregion_grants_access_to_main_table_entry::<K>(*subregion, free_index));
            subregion.serialize_and_write_relative::<u64, Perm, PM>(wrpm_region, crc_addr, &crc, Tracked(perm));
            subregion.serialize_and_write_relative::<ListEntryMetadata, Perm, PM>(wrpm_region, entry_addr,
                                                                                  &entry, Tracked(perm));
            subregion.serialize_and_write_relative::<K, Perm, PM>(wrpm_region, key_addr, &key, Tracked(perm));

            let ghost metadata_table_entry = MetadataTableViewEntry{crc, entry, key: *key };
            self.outstanding_entry_writes =
                Ghost(self.outstanding_entry_writes@.update(free_index as int, Some(metadata_table_entry)));

            let ghost pm_view = subregion.view(wrpm_region);
            assert forall |idx: int| 0 <= idx < self@.durable_metadata_table.len() implies {
                &&& self.outstanding_cdb_write_matches_pm_view(pm_view, idx, metadata_node_size)
                &&& self.outstanding_entry_write_matches_pm_view(pm_view, idx, metadata_node_size)
            } by {
                lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, metadata_node_size as nat);
                lemma_entries_dont_overlap_unless_same_index(idx as nat, free_index as nat, metadata_node_size as nat);
                assert(old(self).outstanding_cdb_write_matches_pm_view(old_pm_view, idx, metadata_node_size));
                assert(old(self).outstanding_entry_write_matches_pm_view(old_pm_view, idx, metadata_node_size));
            }

            assert forall|idx: u64| self.allocator_view().contains(idx) implies self.free_indices().contains(idx) by {
                if idx != free_index {
                    assert(old(self).free_indices().contains(idx));
                }
                else {
                    let j = choose|j: int| {
                        &&& 0 <= j < self.metadata_table_free_list@.len()
                        &&& self.metadata_table_free_list@[j] == idx
                    };
                    assert(j == old(self).metadata_table_free_list@.len() - 1);
                    assert(false);
                }
            }

            assert forall|idx: u64| self.free_indices().contains(idx) implies self.allocator_view().contains(idx) by {
                assert(old(self).free_indices().contains(idx));
                assert(old(self).allocator_view().contains(idx));
                assert(idx != free_index);
                let j = choose|j: int| {
                    &&& 0 <= j < old(self).metadata_table_free_list@.len()
                    &&& old(self).metadata_table_free_list@[j] == idx
                };
                assert(j < old(self).metadata_table_free_list@.len() - 1);
                assert(self.metadata_table_free_list@[j] == idx);
            }

            assert(self.allocator_view() =~= self.free_indices());
            assert(pm_view.committed() == old_pm_view.committed());

            assert forall |s| #[trigger] pm_view.can_crash_as(s) implies
                parse_metadata_table::<K>(s, overall_metadata.num_keys,
                                          overall_metadata.metadata_node_size) == Some(self@) by {
                old(self).lemma_changing_invalid_entry_doesnt_affect_parse_metadata_table(
                    old_pm_view, pm_view, s, overall_metadata, free_index
                );
            }

            assert(subregion.view(wrpm_region).committed() =~= subregion.view(old::<&mut _>(wrpm_region)).committed());

            assert forall |idx: u64| {
                &&& 0 <= idx < self@.durable_metadata_table.len()
                &&& self.spec_outstanding_entry_writes()[idx as int] is Some
            } implies #[trigger] self.pending_allocations@.contains(idx) by {
                if idx == free_index {
                    assert(self.pending_allocations@[self.pending_allocations@.len()-1] == free_index);
                }
            }

            Ok(free_index)
        }

        pub exec fn tentatively_deallocate_entry(
            &mut self,
            Ghost(pm_subregion): Ghost<PersistentMemoryRegionView>,
            index: u64,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
            Ghost(current_tentative_state): Ghost<Seq<u8>>, 
        )
            requires 
                0 <= index < overall_metadata.num_keys,
                // the provided index is not currently free or pending (de)allocation
                !old(self).free_indices().contains(index),
                !old(self).pending_deallocations_view().contains(index),
                !old(self).pending_allocations_view().contains(index),
                // and it's currently valid in the durable metadata table state
                old(self)@.durable_metadata_table[index as int] matches DurableEntry::Valid(_),
                old(self).inv(pm_subregion, overall_metadata),
                // the pending alloc invariant holds for all indexes except the one we are deallocating
                ({
                    let tentative_subregion_state = extract_bytes(current_tentative_state, 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    let durable_main_table_view = parse_metadata_table::<K>(pm_subregion.committed(),
                        overall_metadata.num_keys, overall_metadata.metadata_node_size);
                    let tentative_main_table_view = parse_metadata_table::<K>(tentative_subregion_state,
                        overall_metadata.num_keys, overall_metadata.metadata_node_size);
                    &&& durable_main_table_view matches Some(durable_main_table_view)
                    &&& tentative_main_table_view matches Some(tentative_main_table_view)
                    &&& old(self)@ == durable_main_table_view
                    // we should have already logged the deletion of this record, 
                    // so it should be INVALID in the tentative view
                    &&& tentative_main_table_view.durable_metadata_table[index as int] matches DurableEntry::Invalid
                    &&& forall |idx: u64| 0 <= idx < durable_main_table_view.durable_metadata_table.len() && idx != index ==> {
                            old(self).pending_alloc_check(idx, durable_main_table_view, tentative_main_table_view)
                        }
                }),
                old(self).allocator_inv(),
            ensures 
                // we maintain all invariants and move the index into 
                // the pending deallocations set
                self.pending_deallocations_view().contains(index),
                self.inv(pm_subregion, overall_metadata),
                ({
                    let tentative_subregion_state = extract_bytes(current_tentative_state, 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    self.pending_alloc_inv(pm_subregion.committed(), tentative_subregion_state, overall_metadata)
                }),
                old(self).free_indices() == self.free_indices(),
                old(self).allocator_view() == self.allocator_view(),
                old(self).pending_allocations_view() == self.pending_allocations_view(),
                self.pending_deallocations_view() == old(self).pending_deallocations_view().insert(index),
                old(self).spec_outstanding_cdb_writes() == self.spec_outstanding_cdb_writes(),
                old(self).spec_outstanding_entry_writes() == self.spec_outstanding_entry_writes(),
                self.allocator_inv(),
                ({
                    let tentative_subregion_state = extract_bytes(current_tentative_state, 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    self.pending_alloc_inv(pm_subregion.committed(), tentative_subregion_state, overall_metadata)
                })
        {
            self.pending_deallocations.push(index);
            assert(self.pending_deallocations_view() =~= old(self).pending_deallocations_view().insert(index)) by {
                assert(self.pending_deallocations@.drop_last() == old(self).pending_deallocations@);
                assert(self.pending_deallocations@.last() == index);
            }

            proof {
                let durable_subregion_state = pm_subregion.committed();
                let durable_main_table_view = parse_metadata_table::<K>(durable_subregion_state,
                    overall_metadata.num_keys, overall_metadata.metadata_node_size).unwrap();
                let tentative_subregion_state = extract_bytes(current_tentative_state, 
                    overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let tentative_main_table_view = parse_metadata_table::<K>(tentative_subregion_state,
                    overall_metadata.num_keys, overall_metadata.metadata_node_size).unwrap();

                assert(self.pending_deallocations@.subrange(0, self.pending_deallocations@.len() - 1) == old(self).pending_deallocations@);
                assert(self.pending_deallocations@[self.pending_deallocations@.len() - 1] == index);
                assert forall |idx: u64| self.pending_deallocations@.contains(idx) implies idx < overall_metadata.num_keys by {
                    if idx != index {
                        assert(old(self).pending_deallocations@.contains(idx));
                    } else {
                        assert(index < overall_metadata.num_keys);
                    }
                }
                assert(forall |idx: u64| 0 <= idx < overall_metadata.num_keys && self.pending_deallocations@.contains(idx) ==> {
                    ||| old(self).pending_deallocations@.contains(idx)
                    ||| idx == index
                });

                assert(forall |i| 0 <= i < self@.durable_metadata_table.len() ==>
                    old(self).outstanding_cdb_write_matches_pm_view(pm_subregion, i, overall_metadata.metadata_node_size) ==>
                        self.outstanding_cdb_write_matches_pm_view(pm_subregion, i, overall_metadata.metadata_node_size));
                assert(forall |i| 0 <= i < self@.durable_metadata_table.len() ==>
                    old(self).outstanding_entry_write_matches_pm_view(pm_subregion, i, overall_metadata.metadata_node_size) ==> 
                        self.outstanding_entry_write_matches_pm_view(pm_subregion, i, overall_metadata.metadata_node_size));
                
                assert forall |idx: u64| 0 <= idx < durable_main_table_view.durable_metadata_table.len() implies 
                    self.pending_alloc_check(idx, durable_main_table_view, tentative_main_table_view) 
                by {
                    if idx != index {
                        assert(old(self).pending_alloc_check(idx, durable_main_table_view, tentative_main_table_view));
                    }
                }
            }  
        }

        pub exec fn finalize_pending_alloc_and_dealloc(
            &mut self,
            Ghost(pm): Ghost<PersistentMemoryRegionView>,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        )
            requires
                old(self).inv(pm, overall_metadata),
                pm.no_outstanding_writes(),
                // entries in the pending allocations list have become
                // valid in durable storage
                forall |idx: u64| {
                    &&& 0 <= idx < old(self)@.durable_metadata_table.len()
                    &&& old(self).pending_allocations_view().contains(idx) 
                } ==> old(self)@.durable_metadata_table[idx as int] matches DurableEntry::Valid(_),
                // entries in the pending deallocations list have become
                // invalid in durable storage
                forall |idx: u64| {
                    &&& 0 <= idx < old(self)@.durable_metadata_table.len()
                    &&& old(self).pending_deallocations_view().contains(idx) 
                } ==> old(self)@.durable_metadata_table[idx as int] matches DurableEntry::Invalid,
                ({
                    let durable_main_table_region = extract_bytes(pm.committed(), 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    parse_metadata_table::<K>(durable_main_table_region, 
                        overall_metadata.num_keys, overall_metadata.metadata_node_size) == Some(old(self)@)
                }),
                // the pending alloc invariant doesn't hold right now because we have 
                // not finalized the pending (de)allocs, but we need to use some
                // information from it that is still true in order to reestablish
                // the invariant for the postcondition.
                forall |idx: u64| 0 <= idx < old(self)@.durable_metadata_table.len() ==> {
                    let entry = #[trigger] old(self)@.durable_metadata_table[idx as int];
                    match entry {
                        DurableEntry::Invalid => {
                            ||| old(self).allocator_view().contains(idx)
                            ||| old(self).pending_deallocations_view().contains(idx)
                        }
                        DurableEntry::Valid(entry) => {
                            // if the entry is valid, either it was pending allocation
                            // or it's just valid and not in any of the three lists
                            ||| old(self).pending_allocations_view().contains(idx)
                            ||| ({
                                &&& !old(self).allocator_view().contains(idx)
                                &&& !old(self).pending_deallocations_view().contains(idx)
                                &&& !old(self).pending_allocations_view().contains(idx)
                            })
                        }
                        _ => false
                    }
                },
                forall |idx: u64| 0 <= idx < old(self)@.durable_metadata_table.len() ==> 
                    old(self).spec_outstanding_cdb_writes()[idx as int] is None,
                forall |idx: u64| 0 <= idx < old(self)@.durable_metadata_table.len() ==> 
                    old(self).spec_outstanding_entry_writes()[idx as int] is None,
                forall |i: int| 0 <= i < old(self)@.durable_metadata_table.len() ==> 
                    old(self).outstanding_cdb_write_matches_pm_view(pm, i, overall_metadata.metadata_node_size),
                forall |i: int| 0 <= i < old(self)@.durable_metadata_table.len() ==> 
                    old(self).outstanding_entry_write_matches_pm_view(pm, i, overall_metadata.metadata_node_size),
            ensures 
                self.inv(pm, overall_metadata),
                ({
                    let durable_main_table_region = extract_bytes(pm.committed(), 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    self.pending_alloc_inv(durable_main_table_region, durable_main_table_region, overall_metadata)
                }),
                self.pending_allocations_view().is_empty(),
                self.pending_deallocations_view().is_empty(),
        {
            // add the pending deallocations to the free list 
            // this also clears self.pending_deallocations
            self.metadata_table_free_list.append(&mut self.pending_deallocations);

            // clear the pending allocations list
            self.pending_allocations = Vec::new();

            proof {
                assert(self.pending_allocations@.len() == 0);
                assert(self.pending_deallocations@.len() == 0);
                self.pending_allocations@.unique_seq_to_set();
                self.pending_deallocations@.unique_seq_to_set();
                self.metadata_table_free_list@.unique_seq_to_set();

                assert(self.metadata_table_free_list@ == 
                    old(self).metadata_table_free_list@ + old(self).pending_deallocations@);
                assert(self.metadata_table_free_list@.subrange(0, old(self).metadata_table_free_list@.len() as int) == 
                    old(self).metadata_table_free_list@);
                assert(self.metadata_table_free_list@.subrange(old(self).metadata_table_free_list@.len() as int,
                    self.metadata_table_free_list@.len() as int) == old(self).pending_deallocations@);

                let durable_main_table_region = extract_bytes(pm.committed(), 
                    overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let current_view = parse_metadata_table::<K>(durable_main_table_region, 
                    overall_metadata.num_keys, overall_metadata.metadata_node_size).unwrap();
                assert(current_view == self@);
                assert forall |idx: u64| 0 <= idx < current_view.durable_metadata_table.len() implies
                    self.pending_alloc_check(idx, current_view, current_view) 
                by {
                    let entry = current_view.durable_metadata_table[idx as int];
                    match entry {
                        DurableEntry::Invalid => {
                            // this index was either pending deallocation or it was already free
                            assert({
                                ||| old(self).metadata_table_free_list@.contains(idx)
                                ||| old(self).pending_deallocations@.contains(idx)
                            });
                            
                            assert(self.metadata_table_free_list@.contains(idx));
                            assert(self.allocator_view().contains(idx));
                        }
                        DurableEntry::Valid(entry) => {
                            // This index was either pending allocation or already allocated
                            assert({
                                ||| old(self).pending_allocations_view().contains(idx)
                                ||| ({
                                    &&& !old(self).allocator_view().contains(idx)
                                    &&& !old(self).pending_deallocations_view().contains(idx)
                                    &&& !old(self).pending_allocations_view().contains(idx)
                                })
                            });
                            if old(self).pending_allocations_view().contains(idx) {
                                assert(!old(self).allocator_view().contains(idx));
                                assert(!old(self).pending_deallocations_view().contains(idx));
                                assert(!self.allocator_view().contains(idx));
                            } // else, trivial -- it wasn't in any of the sets before so it isn't now
                        }
                        _ => assert(false)
                    }
                }
                assert(self.pending_alloc_inv(durable_main_table_region, durable_main_table_region, overall_metadata));

                assert forall |i: int| 0 <= i < self@.durable_metadata_table.len() implies {
                    &&& self.outstanding_cdb_write_matches_pm_view(pm, i, overall_metadata.metadata_node_size)
                    &&& self.outstanding_entry_write_matches_pm_view(pm, i, overall_metadata.metadata_node_size)
                } by {
                    assert(old(self).outstanding_cdb_write_matches_pm_view(pm, i, overall_metadata.metadata_node_size));
                    assert(old(self).outstanding_entry_write_matches_pm_view(pm, i, overall_metadata.metadata_node_size));
                }

                assert(self.metadata_table_free_list@.subrange(old(self).metadata_table_free_list@.len() as int, 
                    self.metadata_table_free_list@.len() as int) == old(self).pending_deallocations@);
                assert forall |idx: u64| self.metadata_table_free_list@.contains(idx) implies idx < overall_metadata.num_keys by {
                    if !old(self).metadata_table_free_list@.contains(idx) {
                        assert(old(self).pending_deallocations@.contains(idx));
                    } 
                }

                assert(forall |idx: u64| old(self).metadata_table_free_list@.contains(idx) ==> 
                    old(self)@.durable_metadata_table[idx as int] matches DurableEntry::Invalid);


                assert(forall |idx: u64| {
                    &&& 0 <= idx < old(self)@.durable_metadata_table.len()
                    &&& old(self).pending_deallocations_view().contains(idx) 
                } ==> old(self)@.durable_metadata_table[idx as int] matches DurableEntry::Invalid);

                assert forall |idx: u64| self.metadata_table_free_list@.contains(idx) implies 
                    self.free_indices().contains(idx) 
                by {
                    if !old(self).metadata_table_free_list@.contains(idx) {
                        assert(old(self).pending_deallocations_view().contains(idx));
                        assert(forall |idx: u64| {
                            &&& 0 <= idx < old(self)@.durable_metadata_table.len()
                            &&& old(self).pending_deallocations_view().contains(idx) 
                        } ==> old(self)@.durable_metadata_table[idx as int] matches DurableEntry::Invalid);
                        assert(old(self)@.durable_metadata_table[idx as int] matches DurableEntry::Invalid);
                    }
                    assert(self@.durable_metadata_table[idx as int] matches DurableEntry::Invalid);
                }
            }
        }

        pub exec fn get_delete_log_entry(
            &self,
            Ghost(subregion_view): Ghost<PersistentMemoryRegionView>,
            Ghost(region_view): Ghost<PersistentMemoryRegionView>,
            index: u64,
            Ghost(version_metadata): Ghost<VersionMetadata>,
            overall_metadata: &OverallMetadata,
            Ghost(current_tentative_state): Ghost<Seq<u8>>, 
        ) -> (log_entry: PhysicalOpLogEntry)
            requires 
                self.inv(subregion_view, *overall_metadata),
                overall_metadata.main_table_size >= overall_metadata.num_keys * overall_metadata.metadata_node_size,
                0 <= index < self@.len(),
                // the index must refer to a currently-valid entry in the current durable table
                self@.durable_metadata_table[index as int] is Valid,
                !self.pending_deallocations_view().contains(index),
                parse_metadata_table::<K>(subregion_view.committed(), overall_metadata.num_keys,
                                          overall_metadata.metadata_node_size) == Some(self@),
                overall_metadata.metadata_node_size ==
                    ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
                region_view.len() == overall_metadata.region_size,
                overall_metadata.main_table_addr + overall_metadata.main_table_size <= overall_metadata.log_area_addr
                    <= overall_metadata.region_size <= region_view.len() <= u64::MAX,
                ({
                    let main_table_region = extract_bytes(current_tentative_state, 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    let main_table_view = parse_metadata_table::<K>(main_table_region,
                        overall_metadata.num_keys, overall_metadata.metadata_node_size);
                    &&& self.pending_alloc_inv(subregion_view.committed(), main_table_region, *overall_metadata)
                    &&& main_table_view matches Some(main_table_view)
                    &&& main_table_view.inv(*overall_metadata)
                }),
                current_tentative_state.len() == overall_metadata.region_size,
                VersionMetadata::spec_size_of() <= version_metadata.overall_metadata_addr,
                version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of()
                    <= overall_metadata.main_table_addr,
            ensures 
                log_entry@.inv(version_metadata, *overall_metadata),
                overall_metadata.main_table_addr <= log_entry.absolute_addr,
                log_entry.absolute_addr + log_entry.len <=
                    overall_metadata.main_table_addr + overall_metadata.main_table_size,
                ({
                    let new_mem = current_tentative_state.map(|pos: int, pre_byte: u8|
                        if log_entry.absolute_addr <= pos < log_entry.absolute_addr + log_entry.len {
                            log_entry.bytes[pos - log_entry.absolute_addr]
                        } else {
                            pre_byte
                        }
                    );
                    let current_main_table_region = extract_bytes(current_tentative_state, 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    let current_main_table_view = parse_metadata_table::<K>(current_main_table_region,
                        overall_metadata.num_keys, overall_metadata.metadata_node_size).unwrap();
                    let new_main_table_region = extract_bytes(new_mem, 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    let new_main_table_view = parse_metadata_table::<K>(new_main_table_region,
                        overall_metadata.num_keys, overall_metadata.metadata_node_size);
                    let item_index = self@.durable_metadata_table[index as int]->Valid_0.item_index();
                    &&& new_main_table_view is Some
                    &&& new_main_table_view == current_main_table_view.delete(index as int)
                    &&& new_main_table_view.unwrap().valid_item_indices() == current_main_table_view.valid_item_indices().remove(item_index)
                }),
        {
            let entry_slot_size = overall_metadata.metadata_node_size;
            let ghost item_index = self@.durable_metadata_table[index as int].unwrap_valid().item_index();
            // Proves that index * entry_slot_size will not overflow
            proof {
                lemma_valid_entry_index(index as nat, overall_metadata.num_keys as nat, entry_slot_size as nat);
            }
            
            let index_offset = index * entry_slot_size as u64;
            assert(index_offset == index_to_offset(index as nat, entry_slot_size as nat));

            let log_entry = PhysicalOpLogEntry {
                absolute_addr: overall_metadata.main_table_addr + index_offset,
                len: traits_t::size_of::<u64>() as u64,
                bytes: slice_to_vec(CDB_FALSE.as_byte_slice()),
            };

            proof {
                broadcast use pmcopy_axioms;

                let new_mem = current_tentative_state.map(|pos: int, pre_byte: u8|
                    if log_entry.absolute_addr <= pos < log_entry.absolute_addr + log_entry.len {
                        log_entry.bytes[pos - log_entry.absolute_addr]
                    } else {
                        pre_byte
                    }
                );
                
                let old_main_table_region = extract_bytes(current_tentative_state, 
                    overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let new_main_table_region = extract_bytes(new_mem, 
                    overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                lemma_establish_extract_bytes_equivalence(old_main_table_region, new_main_table_region);

                let committed_main_table_view = parse_metadata_table::<K>(subregion_view.committed(),
                    overall_metadata.num_keys, overall_metadata.metadata_node_size).unwrap();
                let old_main_table_view = parse_metadata_table::<K>(old_main_table_region,
                    overall_metadata.num_keys, overall_metadata.metadata_node_size).unwrap();
                let new_main_table_view = parse_metadata_table::<K>(new_main_table_region,
                    overall_metadata.num_keys, overall_metadata.metadata_node_size);
                assert(self.pending_alloc_check(index, committed_main_table_view, old_main_table_view));
                
                assert forall |i: nat| #![trigger extract_bytes(new_main_table_region,
                                                         index_to_offset(i, entry_slot_size as nat),
                                                         entry_slot_size as nat)]
                           i < overall_metadata.num_keys implies {
                    let offset = index_to_offset(i, entry_slot_size as nat);
                    let old_entry_bytes = extract_bytes(old_main_table_region, offset,
                                                        entry_slot_size as nat);
                    let entry_bytes = extract_bytes(new_main_table_region, offset, entry_slot_size as nat);
                    &&& validate_metadata_entry::<K>(entry_bytes, overall_metadata.num_keys as nat)
                    &&& i == index ==>
                           parse_metadata_entry::<K>(entry_bytes, overall_metadata.num_keys as nat) ==
                           DurableEntry::<MetadataTableViewEntry<K>>::Invalid
                    &&& i != index ==> parse_metadata_entry::<K>(entry_bytes, overall_metadata.num_keys as nat) == 
                           parse_metadata_entry::<K>(old_entry_bytes, overall_metadata.num_keys as nat)
                } by {
                    let offset = index_to_offset(i, entry_slot_size as nat);
                    lemma_valid_entry_index(i, overall_metadata.num_keys as nat, entry_slot_size as nat);
                    lemma_entries_dont_overlap_unless_same_index(i, index as nat, entry_slot_size as nat);
                    assert(new_main_table_region.len() >= offset + entry_slot_size);
                    // Handle the case where i != index separately from i == index.
                    if i != index {
                        assert(extract_bytes(new_main_table_region, offset, entry_slot_size as nat) =~=
                               extract_bytes(old_main_table_region, offset, entry_slot_size as nat));
                        } else {
                        // When `i == index`, the entry is valid because we just set its CDB to false,
                        // which makes its CDB a valid, parseable value. This also proves that this
                        // entry parses to an Invalid entry, since we know that
                        // `log_entry.bytes@ == CDB_FALSE.spec_to_bytes()`
                        let entry_bytes = extract_bytes(new_main_table_region, offset, entry_slot_size as nat);
                        let cdb_bytes = extract_bytes(entry_bytes, 0, u64::spec_size_of());
                        assert(cdb_bytes =~= log_entry.bytes@);
                    }
                }

                // NOTE: in progress
                assert(validate_metadata_entries::<K>(new_main_table_region, overall_metadata.num_keys as nat,
                    overall_metadata.metadata_node_size as nat));
                let entries = parse_metadata_entries::<K>(new_main_table_region, overall_metadata.num_keys as nat,
                    overall_metadata.metadata_node_size as nat);
                assert(new_main_table_region.len() >= overall_metadata.num_keys * overall_metadata.metadata_node_size);
                
                let old_entries =
                    parse_metadata_entries::<K>(old_main_table_region, overall_metadata.num_keys as nat,
                                                overall_metadata.metadata_node_size as nat);
                assert(!self.pending_deallocations_view().contains(index));
                assert(old_entries[index as int] is Valid);
                assert(old_entries[index as int]->Valid_0.item_index() == item_index);

                assert(no_duplicate_item_indexes(entries)) by {

                    assert forall|i, j| {
                        &&& 0 <= i < entries.len()
                        &&& 0 <= j < entries.len()
                        &&& i != j
                        &&& #[trigger] entries[i] is Valid
                        &&& #[trigger] entries[j] is Valid
                    } implies entries[i]->Valid_0.item_index() != entries[j]->Valid_0.item_index()
 by {
                        assert(i == index ==> old_entries[j]->Valid_0.item_index() != item_index);
                        assert(j == index ==> old_entries[i]->Valid_0.item_index() != item_index);
                    }
                }

                let updated_table = old_main_table_view.durable_metadata_table.update(
                    index as int,
                    DurableEntry::<MetadataTableViewEntry<K>>::Invalid
                );
                assert(updated_table.len() == old_main_table_view.durable_metadata_table.len());
                assert(updated_table.len() == overall_metadata.num_keys);
                assert forall |i: nat| i < overall_metadata.num_keys && i != index implies 
                    #[trigger] updated_table[i as int] == new_main_table_view.unwrap().durable_metadata_table[i as int]
                by {
                    lemma_valid_entry_index(i, overall_metadata.num_keys as nat, entry_slot_size as nat);
                    let offset = index_to_offset(i, entry_slot_size as nat);
                    let entry_bytes = extract_bytes(new_main_table_region, offset, entry_slot_size as nat);
                    let new_entry = parse_metadata_entry::<K>(entry_bytes, overall_metadata.num_keys as nat);
                    assert(new_main_table_view.unwrap().durable_metadata_table[i as int] =~= new_entry);
                }
                let new_main_table_view = new_main_table_view.unwrap();

                assert(new_main_table_view =~= old_main_table_view.delete(index as int).unwrap());

                // In addition to proving that this log entry makes the entry at this index in valid, we also have to 
                // prove that it makes the corresponding item table index invalid.
                
                assert(new_main_table_view.valid_item_indices() =~=
                       old_main_table_view.valid_item_indices().remove(item_index)) by {
                    assert forall|i: u64| old_main_table_view.valid_item_indices().remove(item_index).contains(i)
                        implies #[trigger] new_main_table_view.valid_item_indices().contains(i) by {
                        let j = choose|j: int| {
                            &&& 0 <= j < old_main_table_view.durable_metadata_table.len() 
                            &&& #[trigger] old_main_table_view.durable_metadata_table[j] matches
                                DurableEntry::Valid(entry)
                            &&& entry.item_index() == i
                        };
                        assert(new_main_table_view.durable_metadata_table[j] ==
                               old_main_table_view.durable_metadata_table[j]);
                    }
                }
            }
            log_entry
        }

        pub exec fn abort_transaction(
            &mut self,
            Ghost(pm): Ghost<PersistentMemoryRegionView>,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        ) 
            requires
                old(self).opaque_inv(overall_metadata),
                old(self).allocator_inv(),
                overall_metadata.main_table_size >= overall_metadata.num_keys * overall_metadata.metadata_node_size,
                pm.len() >= overall_metadata.main_table_size,
                old(self).spec_metadata_node_size() == overall_metadata.metadata_node_size,
                overall_metadata.metadata_node_size ==
                    ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
                forall |s| #[trigger] pm.can_crash_as(s) ==> 
                    parse_metadata_table::<K>(s, overall_metadata.num_keys, overall_metadata.metadata_node_size) == Some(old(self)@),
                old(self)@.durable_metadata_table.len() == old(self).spec_outstanding_cdb_writes().len() ==
                    old(self).spec_outstanding_entry_writes().len() == overall_metadata.num_keys,
                old(self)@.inv(overall_metadata),
                forall |idx: u64| old(self).allocator_view().contains(idx) ==> idx < overall_metadata.num_keys,
                forall |idx: u64| old(self).free_indices().contains(idx) ==> idx < overall_metadata.num_keys,
                forall |i| 0 <= i < old(self)@.durable_metadata_table.len() ==> 
                    match #[trigger] old(self)@.durable_metadata_table[i] {
                        DurableEntry::Valid(entry) => entry.entry.item_index < overall_metadata.num_keys,
                        _ => true
                    },
                pm.no_outstanding_writes(),
                forall |idx: u64| old(self).allocator_view().contains(idx) ==> old(self).free_indices().contains(idx),
                forall |idx: u64| old(self).pending_allocations_view().contains(idx) ==> {
                    &&& !old(self).free_indices().contains(idx)
                    &&& old(self)@.durable_metadata_table[idx as int] matches DurableEntry::Invalid
                    &&& idx < overall_metadata.num_keys
                },
                forall |idx: u64| old(self).pending_allocations_view().contains(idx) ==> {
                    old(self)@.durable_metadata_table[idx as int] matches DurableEntry::Invalid
                },
                forall |idx: u64| old(self).allocator_view().contains(idx) ==> {
                    old(self)@.durable_metadata_table[idx as int] matches DurableEntry::Invalid
                },
                parse_metadata_table::<K>(pm.committed(), overall_metadata.num_keys, 
                    overall_metadata.metadata_node_size) is Some,
            ensures
                self.valid(pm, overall_metadata),
                self.allocator_inv(),
                self.spec_outstanding_cdb_writes() == Seq::new(
                    old(self).spec_outstanding_cdb_writes().len(),
                    |i: int| None::<bool>
                ),
                self.spec_outstanding_entry_writes() == Seq::new(
                    old(self).spec_outstanding_entry_writes().len(),
                    |i: int| None::<MetadataTableViewEntry<K>>
                ),
                self@.valid_item_indices() == old(self)@.valid_item_indices(),
                self@.has_same_valid_items(old(self)@),
                self.pending_alloc_inv(pm.committed(), pm.committed(), overall_metadata),
                self.pending_allocations_view().is_empty(),
                self.pending_deallocations_view().is_empty(),
    {
            // Move all pending allocations from the pending list back into the free list
            self.metadata_table_free_list.append(&mut self.pending_allocations);
            
            self.pending_deallocations = Vec::new();

            proof { 
                self.metadata_table_free_list@.unique_seq_to_set(); 
                self.pending_allocations@.unique_seq_to_set(); 
                self.pending_deallocations@.unique_seq_to_set(); 

                assert forall |idx: u64| self.metadata_table_free_list@.contains(idx) implies
                    idx < overall_metadata.num_keys 
                by {
                    if !old(self).metadata_table_free_list@.contains(idx) {
                        assert(old(self).pending_allocations@.contains(idx));
                    } else {
                        assert(old(self).metadata_table_free_list@.contains(idx));
                    }
                }
            }

            // Mark all tentative entries as Invalid in ghost state. The fact that they have a new entry 
            // that has not been made valid yet no longer matters.
            self.state = Ghost(MetadataTableView {
                durable_metadata_table: self.state@.durable_metadata_table.map_values(
                    |e| match e {
                        DurableEntry::Tentative(e) => DurableEntry::Invalid,
                        _ => e
                    }
                )
            });

            // Drop all outstanding updates from the view
            self.outstanding_cdb_writes = Ghost(Seq::new(
                old(self)@.durable_metadata_table.len(),
                |i: int| None::<bool>
            ));
            self.outstanding_entry_writes = Ghost(Seq::new(
                old(self)@.durable_metadata_table.len(),
                |i: int| None::<MetadataTableViewEntry<K>>
            ));

            proof {
                // We now prove that aborting the transaction reestablishes invariants that 
                // were broken.

                assert forall |i| 0 <= i < self@.durable_metadata_table.len() implies {
                    &&& self.outstanding_cdb_write_matches_pm_view(pm, i, overall_metadata.metadata_node_size)
                    &&& self.outstanding_entry_write_matches_pm_view(pm, i, overall_metadata.metadata_node_size)
                } by {
                    let start = index_to_offset(i as nat, overall_metadata.metadata_node_size as nat) as int;
                    assert(i < overall_metadata.num_keys);
                    assert(i * overall_metadata.metadata_node_size <= overall_metadata.num_keys * overall_metadata.metadata_node_size) by {
                        lemma_mul_inequality(i as int, overall_metadata.num_keys as int, overall_metadata.metadata_node_size as int);
                    }
                    assert(i * overall_metadata.metadata_node_size + overall_metadata.metadata_node_size <= overall_metadata.num_keys * overall_metadata.metadata_node_size) by {
                        lemma_mul_inequality((i + 1) as int, overall_metadata.num_keys as int, overall_metadata.metadata_node_size as int);
                        lemma_mul_is_distributive_add_other_way(overall_metadata.metadata_node_size as int, 1int, i as int);
                    }
                }

                assert(forall |i: int| 0 <= i < self@.durable_metadata_table.len() ==> {
                    ||| #[trigger] self.state@.durable_metadata_table[i] matches DurableEntry::Invalid 
                    ||| self.state@.durable_metadata_table[i] matches DurableEntry::Valid(_)
                });

                // need this assertion for triggers
                assert(forall |s| #[trigger] pm.can_crash_as(s) ==> 
                    parse_metadata_table::<K>(s, overall_metadata.num_keys, overall_metadata.metadata_node_size) == Some(self@));

                assert forall |idx: u64| self.free_indices().contains(idx) implies 
                    self.allocator_view().contains(idx) 
                by {
                    assert(self@.durable_metadata_table[idx as int] matches DurableEntry::Invalid);
                    if old(self).free_indices().contains(idx) {
                        // index was free before the abort, so it's still free and in the allocator list now.
                        assert(old(self).allocator_view().contains(idx));
                        assert(forall |i: int| 0 <= i < old(self).metadata_table_free_list@.len() ==> 
                            old(self).metadata_table_free_list@[i] == self.metadata_table_free_list@[i]);
                        assert(self.metadata_table_free_list@.contains(idx));
                        assert(self.allocator_view().contains(idx));
                    } else {
                        // We need to hit the necessary triggers to prove that the index is pending 
                        // if it has outstanding writes.
                        if old(self).spec_outstanding_cdb_writes()[idx as int] is Some {
                            assert(old(self).pending_allocations@.contains(idx));
                        } else if old(self).spec_outstanding_entry_writes()[idx as int] is Some {
                            assert(old(self).pending_allocations@.contains(idx));
                        }
                        // Prove that this index would have been added to the allocator.
                        assert(self.metadata_table_free_list@.len() == old(self).metadata_table_free_list@.len() + old(self).pending_allocations@.len());
                        assert(forall |i: int| 0 <= i < old(self).pending_allocations@.len() ==> 
                            old(self).pending_allocations@[i] == self.metadata_table_free_list@[i + old(self).metadata_table_free_list@.len()]);
                    }
                }

                assert forall |idx: u64| self.allocator_view().contains(idx) implies 
                    self.free_indices().contains(idx) 
                by {
                    if old(self).allocator_view().contains(idx) {
                        assert(old(self).allocator_view().contains(idx) ==> old(self).free_indices().contains(idx));
                    } else {
                        assert(old(self).pending_allocations@.contains(idx));
                        assert(old(self)@.durable_metadata_table[idx as int] matches DurableEntry::Invalid);
                    }
                }
                assert(self.allocator_view() == self.free_indices());

                assert_sets_equal!(self@.valid_item_indices() == old(self)@.valid_item_indices(), elem => {
                    assert(forall |i: int| {
                        &&& 0 <= i < self@.durable_metadata_table.len() 
                        &&& self@.durable_metadata_table[i] matches DurableEntry::Valid(_)
                    } ==> self@.durable_metadata_table[i] == old(self)@.durable_metadata_table[i]);
                });

                let current_table_view = parse_metadata_table::<K>(pm.committed(), overall_metadata.num_keys, overall_metadata.metadata_node_size);
                assert(current_table_view is Some);
                let current_table_view = current_table_view.unwrap();
                assert(pm.can_crash_as(pm.committed()));
                assert(current_table_view == self@);
            }
        }

        pub exec fn update_ghost_state_to_current_bytes(
            &mut self,
            Ghost(pm): Ghost<PersistentMemoryRegionView>,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        )
            requires
                pm.no_outstanding_writes(),
                ({
                    let subregion_view = get_subregion_view(pm, overall_metadata.main_table_addr as nat,
                        overall_metadata.main_table_size as nat);
                    parse_metadata_table::<K>(subregion_view.committed(), overall_metadata.num_keys, overall_metadata.metadata_node_size) is Some
                })
            ensures 
                ({
                    let subregion_view = get_subregion_view(pm, overall_metadata.main_table_addr as nat,
                        overall_metadata.main_table_size as nat);
                    self@ == parse_metadata_table::<K>(subregion_view.committed(), overall_metadata.num_keys, overall_metadata.metadata_node_size).unwrap()
                }),
                self.allocator_view() == old(self).allocator_view(),
                self.pending_allocations_view() == old(self).pending_allocations_view(),
                self.pending_deallocations_view() == old(self).pending_deallocations_view(),
                self.spec_outstanding_cdb_writes() == Seq::new(old(self).spec_outstanding_cdb_writes().len(),
                    |i: int| None::<bool>),
                self.spec_outstanding_entry_writes() == Seq::new(old(self).spec_outstanding_entry_writes().len(),
                    |i: int| None::<MetadataTableViewEntry<K>>),

        {
            let ghost subregion_view = get_subregion_view(pm, overall_metadata.main_table_addr as nat,
                overall_metadata.main_table_size as nat);
            self.state = Ghost(parse_metadata_table::<K>(subregion_view.committed(), overall_metadata.num_keys, overall_metadata.metadata_node_size).unwrap());
            self.outstanding_cdb_writes = Ghost(Seq::new(old(self).spec_outstanding_cdb_writes().len(),
                |i: int| None::<bool>));
            self.outstanding_entry_writes = Ghost(Seq::new(old(self).spec_outstanding_entry_writes().len(),
                |i: int| None));
        }

/* Temporarily commented out for subregion work

        pub exec fn play_metadata_log<PM, L>(
            &mut self,
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
            Self::replay_log_metadata_table(wrpm_region, table_id, log_entries, Tracked(perm), Ghost(state))?;
            // replay_log_metadata_table cannot add newly-invalidated metadata entries back into the allocator,
            // because it doesn't (and can't) take &mut self, so as a quick fix we'll just iterate over the log again.
            // TODO: refactor so this happens in the same pass as is used in replay_log_metadata_table
            for i in 0..log_entries.len() 
            {
                assume(false);
                let log_entry = &log_entries[i];
                if let OpLogEntryType::InvalidateMetadataEntry { metadata_index } = log_entry {
                    self.metadata_table_free_list.push(*metadata_index);
                }
            }
            Ok(())
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
                let metadata_node_size = (traits_t::size_of::<u64>() + traits_t::size_of::<u64>() + 
                    traits_t::size_of::<ListEntryMetadata>() + K::size_of()) as u64;

                let log_entry = &log_entries[i];
                match log_entry {
                    OpLogEntryType::CommitMetadataEntry { metadata_index } => {
                        // commit metadata just sets the CDB -- the metadata fields have already been filled in.
                        // We also have to commit the item, but we'll do that in item table recovery
                        let cdb_addr = metadata_index * metadata_node_size;
                        
                        wrpm_region.serialize_and_write(cdb_addr, &CDB_TRUE, Tracked(perm));
                    }
                    OpLogEntryType::InvalidateMetadataEntry { metadata_index } => {
                        // invalidate metadata just writes CDB_FALSE to the entry's CDB
                        let cdb_addr = metadata_index * metadata_node_size;
                        
                        wrpm_region.serialize_and_write(cdb_addr, &CDB_FALSE, Tracked(perm));
                    }
                    OpLogEntryType::UpdateMetadataEntry { metadata_index, new_metadata, new_crc } => {
                        let cdb_addr = metadata_index * metadata_node_size;
                        let entry_addr = cdb_addr + traits_t::size_of::<u64>() as u64;
                        let crc_addr = entry_addr + traits_t::size_of::<ListEntryMetadata>() as u64;

                        wrpm_region.serialize_and_write(crc_addr, new_crc, Tracked(perm));
                        wrpm_region.serialize_and_write(entry_addr, new_metadata, Tracked(perm));
                    }
                    _ => {} // the other operations do not modify the metadata table
                }
                
            }
            Ok(())
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
            let metadata_node_size = (traits_t::size_of::<ListEntryMetadata>() + traits_t::size_of::<u64>() + traits_t::size_of::<u64>() + K::size_of()) as u64;
            let slot_addr = metadata_index * metadata_node_size;
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

            let metadata_node_size = (traits_t::size_of::<ListEntryMetadata>() + traits_t::size_of::<u64>() + traits_t::size_of::<u64>() + K::size_of()) as u64;
            let slot_addr = index * metadata_node_size;
            let cdb_addr = slot_addr;

            wrpm_region.serialize_and_write(cdb_addr, &CDB_TRUE, Tracked(perm));

            Ok(())
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

            let metadata_node_size = (traits_t::size_of::<ListEntryMetadata>() + traits_t::size_of::<u64>() + traits_t::size_of::<u64>() + K::size_of()) as u64;
            let slot_addr = index * metadata_node_size;
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

            let metadata_node_size = (traits_t::size_of::<ListEntryMetadata>() + traits_t::size_of::<u64>() + traits_t::size_of::<u64>() + K::size_of()) as u64;
            let slot_addr = index * metadata_node_size;
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

            let metadata_node_size = (traits_t::size_of::<ListEntryMetadata>() + traits_t::size_of::<u64>() + traits_t::size_of::<u64>() + K::size_of()) as u64;
            let slot_addr = index * metadata_node_size;
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

            let ghost true_header = MetadataTableHeader::spec_from_bytes(mem.subrange(ABSOLUTE_POS_OF_METADATA_HEADER as int, ABSOLUTE_POS_OF_METADATA_HEADER + MetadataTableHeader::spec_size_of()));
            let ghost true_crc = u64::spec_from_bytes(mem.subrange(ABSOLUTE_POS_OF_HEADER_CRC as int, ABSOLUTE_POS_OF_HEADER_CRC + u64::spec_size_of()));
            
            let header = pm_region.read_aligned::<MetadataTableHeader>(ABSOLUTE_POS_OF_METADATA_HEADER).map_err(|e| KvError::PmemErr { pmem_err: e })?;
            let header_crc = pm_region.read_aligned::<u64>(ABSOLUTE_POS_OF_HEADER_CRC).map_err(|e| KvError::PmemErr { pmem_err: e })?;

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

        */
    }
        
}
