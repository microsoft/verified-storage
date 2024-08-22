use builtin::*;
use builtin_macros::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use vstd::arithmetic::mul::lemma_mul_strict_inequality;
use vstd::set_lib::lemma_set_empty_equivalency_len;
use std::fs::Metadata;
use std::hash::Hash;
use vstd::prelude::*;
use vstd::bytes::*;
use crate::kv::durable::oplog::logentry_v::*;
use crate::kv::kvimpl_t::*;
use crate::kv::durable::metadata::metadataspec_t::*;
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

verus! {
    pub struct MetadataTable<K> {
        metadata_node_size: u32,
        metadata_table_free_list: Vec<u64>,
        state: Ghost<MetadataTableView<K>>,
        outstanding_cdb_writes: Ghost<Seq<Option<bool>>>,
        outstanding_entry_writes: Ghost<Seq<Option<MetadataTableViewEntry<K>>>>,
    }

    pub closed spec fn outstanding_bytes_match(pm: PersistentMemoryRegionView, start: int, bytes: Seq<u8>) -> bool
    {
        forall|addr: int| start <= addr < start + bytes.len() ==>
            #[trigger] pm.state[addr].outstanding_write == Some(bytes[addr - start])
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

        pub closed spec fn spec_outstanding_cdb_writes(self) -> Seq<Option<bool>>
        {
            self.outstanding_cdb_writes@
        }

        pub closed spec fn spec_outstanding_entry_writes(self) -> Seq<Option<MetadataTableViewEntry<K>>>
        {
            self.outstanding_entry_writes@
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
            let start = i * metadata_node_size;
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
            let start = i * metadata_node_size;
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

        pub closed spec fn opaque_inv(self, pm: PersistentMemoryRegionView, overall_metadata: OverallMetadata) -> bool
        {
            &&& self.metadata_node_size == overall_metadata.metadata_node_size
            &&& forall|i: int, j: int| {
                 &&& 0 <= i < self.metadata_table_free_list@.len()
                 &&& 0 <= j < self.metadata_table_free_list@.len()
                 &&& i != j
               } ==>
               self.metadata_table_free_list@[i] != self.metadata_table_free_list@[j]
        }

        pub open spec fn inv(self, pm: PersistentMemoryRegionView, overall_metadata: OverallMetadata) -> bool
        {
            &&& self.opaque_inv(pm, overall_metadata)
            &&& overall_metadata.main_table_size >= overall_metadata.num_keys * overall_metadata.metadata_node_size
            &&& pm.len() >= overall_metadata.main_table_size
            &&& overall_metadata.metadata_node_size ==
                ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of()
            &&& Some(self@) ==
                parse_metadata_table::<K>(pm.committed(), overall_metadata.num_keys, overall_metadata.metadata_node_size)
            &&& self@.durable_metadata_table.len() == self.spec_outstanding_cdb_writes().len() ==
                self.spec_outstanding_entry_writes().len() == overall_metadata.num_keys
            &&& forall |i| 0 <= i < self@.durable_metadata_table.len() ==>
                self.outstanding_cdb_write_matches_pm_view(pm, i, overall_metadata.metadata_node_size)
            &&& forall |i| 0 <= i < self@.durable_metadata_table.len() ==>
                self.outstanding_entry_write_matches_pm_view(pm, i, overall_metadata.metadata_node_size)
            &&& self@.inv()
            &&& self.allocator_view() == self.free_indices()
            &&& forall |idx: u64| self.allocator_view().contains(idx) ==> idx < overall_metadata.num_keys
        }

        pub open spec fn valid(self, pm: PersistentMemoryRegionView, overall_metadata: OverallMetadata) -> bool
        {
            &&& self.inv(pm, overall_metadata)
            &&& forall |i| 0 <= i < self.spec_outstanding_cdb_writes().len() ==> self.spec_outstanding_cdb_writes()[i] is None
            &&& forall |i| 0 <= i < self.spec_outstanding_entry_writes().len() ==> self.spec_outstanding_entry_writes()[i] is None
        }

        pub open spec fn subregion_grants_access_to_entry_slot(
            self,
            subregion: WriteRestrictedPersistentMemorySubregion,
            idx: u64
        ) -> bool
        {
            let entry_size = ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of();
            forall|addr: u64| idx * entry_size <= addr < idx * entry_size + entry_size ==>
                subregion.is_writable_relative_addr(addr as int)
        }

        pub open spec fn subregion_grants_access_to_free_slots(
            self,
            subregion: WriteRestrictedPersistentMemorySubregion
        ) -> bool
        {
            forall|idx: u64| {
                &&& idx < self@.len()
                &&& self.allocator_view().contains(idx)
            } ==> self.subregion_grants_access_to_entry_slot(subregion, idx)
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
                        (index * overall_metadata.metadata_node_size as u64) as nat,
                        u64::spec_size_of() as nat,
                    );
                    let cdb = u64::spec_from_bytes(cdb_bytes);
                    let crc_bytes = extract_bytes(
                        pm.committed(),
                        (index * overall_metadata.metadata_node_size as u64) as nat + u64::spec_size_of(),
                        u64::spec_size_of() as nat,
                    );
                    let crc = u64::spec_from_bytes(crc_bytes);
                    let entry_bytes = extract_bytes(
                        pm.committed(),
                        (index * overall_metadata.metadata_node_size as u64) as nat + u64::spec_size_of() * 2,
                        ListEntryMetadata::spec_size_of() as nat,
                    );
                    let entry = ListEntryMetadata::spec_from_bytes(entry_bytes);
                    let key_bytes = extract_bytes(
                        pm.committed(),
                        (index * overall_metadata.metadata_node_size as u64) as nat + u64::spec_size_of() * 2 +
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
            let metadata_node_size = overall_metadata.metadata_node_size;
            lemma_valid_entry_index(index as nat, overall_metadata.num_keys as nat, metadata_node_size as nat);
            let entry_bytes = extract_bytes(pm.committed(), (index * metadata_node_size) as nat, metadata_node_size as nat);
            assert(extract_bytes(entry_bytes, 0, u64::spec_size_of()) =~=
                   extract_bytes(pm.committed(), (index * overall_metadata.metadata_node_size as u64) as nat,
                                 u64::spec_size_of()));
            assert(extract_bytes(entry_bytes, u64::spec_size_of(), u64::spec_size_of()) =~=
                   extract_bytes(pm.committed(),
                                 (index * overall_metadata.metadata_node_size as u64) as nat + u64::spec_size_of(),
                                 u64::spec_size_of()));
            assert(extract_bytes(entry_bytes, u64::spec_size_of() * 2, ListEntryMetadata::spec_size_of()) =~=
                   extract_bytes(pm.committed(),
                                 (index * overall_metadata.metadata_node_size as u64) as nat + u64::spec_size_of() * 2,
                                 ListEntryMetadata::spec_size_of()));
            assert(extract_bytes(entry_bytes, u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of(),
                                 K::spec_size_of()) =~=
                   extract_bytes(pm.committed(),
                                 (index * overall_metadata.metadata_node_size as u64) as nat + u64::spec_size_of() * 2
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
            u64::spec_from_bytes(extract_bytes(mem, k * metadata_node_size as nat, u64::spec_size_of()))
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
                    entry_offset == index * metadata_node_size,
                    metadata_node_size >= u64::spec_size_of(),
                    forall |addr: int| #[trigger] subregion.is_writable_absolute_addr_fn()(addr),
                    forall |k: nat| k < index ==> #[trigger] Self::extract_cdb_for_entry(
                        subregion.view(pm_region).flush().committed(), k, metadata_node_size
                    ) == CDB_FALSE,
                    ({
                        let mem = subregion.view(pm_region).flush().committed();
                        forall |k: nat| k < index ==> u64::bytes_parseable(#[trigger] extract_bytes(
                            mem,
                            k * metadata_node_size as nat,
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
                        assert(k * metadata_node_size + u64::spec_size_of() <= entry_offset) by {
                            lemma_metadata_fits::<K>(k as int, index as int, metadata_node_size as int);
                        }
                        assert(extract_bytes(mem, k * metadata_node_size as nat, u64::spec_size_of()) =~= 
                               extract_bytes(v1.flush().committed(), k * metadata_node_size as nat, u64::spec_size_of()));
                    }
                    else {
                        assert(extract_bytes(mem, k * metadata_node_size as nat, u64::spec_size_of()) ==
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
                        assert(k * metadata_node_size + u64::spec_size_of() <= entry_offset) by {
                            lemma_metadata_fits::<K>(k as int, index as int, metadata_node_size as int);
                        }
                        assert(extract_bytes(mem, k * metadata_node_size as nat, u64::spec_size_of()) =~= 
                            extract_bytes(v1.flush().committed(), k * metadata_node_size as nat, u64::spec_size_of()));
                    }
                    else {
                        assert(extract_bytes(mem, k * metadata_node_size as nat, u64::spec_size_of()) ==
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
                assert(u64::bytes_parseable(extract_bytes(mem, k * metadata_node_size as nat, u64::spec_size_of())));
                assert(Self::extract_cdb_for_entry(mem, k, metadata_node_size) == CDB_FALSE);
                // Prove that k is a valid index in the table
                lemma_valid_entry_index(k, num_keys as nat, metadata_node_size as nat);
                // Prove that the subranges used by validate_metadata_entry and extract_cdb_for_entry to check CDB are the same
                lemma_subrange_of_extract_bytes_equal(mem, (k * metadata_node_size) as nat, (k * metadata_node_size) as nat, metadata_node_size as nat, u64::spec_size_of());
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
                        &&& main_table.no_outstanding_writes()
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
                subregion.view(pm_region).committed(),
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
                    parse_metadata_table::<K>(
                        subregion.view(pm_region).committed(),
                        overall_metadata.num_keys, 
                        overall_metadata.metadata_node_size 
                    ) is Some,
                    table == parse_metadata_table::<K>(
                        subregion.view(pm_region).committed(),
                        overall_metadata.num_keys, 
                        overall_metadata.metadata_node_size 
                    ).unwrap(),
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

                        assume(false);

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
                state: Ghost(parse_metadata_table::<K>(
                    subregion.view(pm_region).committed(),
                    overall_metadata.num_keys, 
                    overall_metadata.metadata_node_size 
                ).unwrap()),
                outstanding_cdb_writes: Ghost(Seq::<Option<bool>>::new(num_keys as nat, |i: int| None)),
                outstanding_entry_writes: Ghost(Seq::<Option<MetadataTableViewEntry<K>>>::new(num_keys as nat,
                                                                                              |i: int| None)),
            };

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
            }

            assert forall |i| 0 <= i < main_table.state@.durable_metadata_table.len() implies {
                &&& main_table.outstanding_cdb_write_matches_pm_view(subregion.view(pm_region), i,
                                                                    overall_metadata.metadata_node_size)
                &&& main_table.outstanding_entry_write_matches_pm_view(subregion.view(pm_region), i,
                                                                    overall_metadata.metadata_node_size)
            } by {
                let pm_view = subregion.view(pm_region);
                let metadata_node_size = overall_metadata.metadata_node_size;
                lemma_metadata_fits::<K>(i as int, num_keys as int, metadata_node_size as int);
                assert(pm_view.no_outstanding_writes_in_range(i * metadata_node_size,
                                                              i * metadata_node_size + u64::spec_size_of()));
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
                old(self).valid(subregion.view(old::<&mut _>(wrpm_region)), overall_metadata),
                subregion.len() >= overall_metadata.main_table_size,
                old(self).subregion_grants_access_to_free_slots(*subregion),
            ensures
                subregion.inv(wrpm_region, perm),
                self.inv(subregion.view(wrpm_region), overall_metadata),
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
                        &&& self.allocator_view().len() == 0
                    },
                    _ => false,
                }
        {
            let ghost pm_view = subregion.view(wrpm_region);
            assert(self.valid(pm_view, overall_metadata));
            assert(self.inv(pm_view, overall_metadata));

            // 1. pop an index from the free list
            // since this index is on the free list, its CDB is already false
            let free_index = match self.metadata_table_free_list.pop(){
                Some(index) => index,
                None => {
                    assert(self.metadata_table_free_list@.to_set().len() == 0) by {
                        self.metadata_table_free_list@.lemma_cardinality_of_set();
                    }

                    assert forall |i| 0 <= i < self@.durable_metadata_table.len() implies
                        self.outstanding_cdb_write_matches_pm_view(pm_view, i, overall_metadata.metadata_node_size) by {
                        assert(old(self).outstanding_cdb_write_matches_pm_view(pm_view, i,
                                                                             overall_metadata.metadata_node_size));
                    }

                    assert forall |i| 0 <= i < self@.durable_metadata_table.len() implies
                           self.outstanding_entry_write_matches_pm_view(pm_view, i,
                                                                        overall_metadata.metadata_node_size) by {
                        assert(old(self).outstanding_entry_write_matches_pm_view(pm_view, i,
                                                                               overall_metadata.metadata_node_size));
                    }

                    return Err(KvError::OutOfSpace);
                },
            };
            
            assert(old(self).allocator_view().contains(free_index)) by {
                assert(old(self).metadata_table_free_list@.last() == free_index);
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
                assert(old(self).outstanding_entry_write_matches_pm_view(pm_view, free_index as int, metadata_node_size));
            }
            let slot_addr = free_index * metadata_node_size as u64;
            // CDB is at slot addr -- we aren't setting that one yet
            let crc_addr = slot_addr + traits_t::size_of::<u64>() as u64;
            let entry_addr = crc_addr + traits_t::size_of::<u64>() as u64;
            let key_addr = entry_addr + traits_t::size_of::<ListEntryMetadata>() as u64;

            subregion.serialize_and_write_relative::<u64, Perm, PM>(wrpm_region, crc_addr, &crc, Tracked(perm));
            subregion.serialize_and_write_relative::<ListEntryMetadata, Perm, PM>(wrpm_region, entry_addr,
                                                                                  &entry, Tracked(perm));
            subregion.serialize_and_write_relative::<K, Perm, PM>(wrpm_region, key_addr, &key, Tracked(perm));

            let ghost metadata_table_entry = MetadataTableViewEntry{ crc, entry, key: *key };
            self.outstanding_entry_writes =
                Ghost(self.outstanding_entry_writes@.update(free_index as int, Some(metadata_table_entry)));

            let ghost old_pm_view = subregion.view(old::<&mut _>(wrpm_region));
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

            Ok(free_index)
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
