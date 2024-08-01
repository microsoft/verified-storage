//! This file contains a trait that defines the interface for the high-level
//! durable component of the KV store.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::assert_seqs_equal;
use vstd::bytes::u64_from_le_bytes;
use vstd::bytes::u64_to_le_bytes;
use vstd::prelude::*;

use crate::kv::durable::durablelist::durablelistimpl_v::*;
use crate::kv::durable::durablelist::durablelistspec_t::*;
use crate::kv::durable::durablelist::layout_v::*;
use crate::kv::durable::durablespec_t::*;
use crate::kv::durable::oplog::oplogimpl_v::*;
use crate::kv::durable::itemtable::itemtableimpl_v::*;
use crate::kv::durable::itemtable::itemtablespec_t::*;
use crate::kv::durable::itemtable::layout_v::*;
use crate::kv::durable::metadata::metadataimpl_v::*;
use crate::kv::durable::metadata::metadataspec_t::*;
use crate::kv::durable::metadata::layout_v::*;
use crate::kv::durable::oplog::logentry_v::*;
use crate::kv::durable::util_v::*;
use crate::kv::durable::inv_v::*;
use crate::kv::kvimpl_t::*;
use crate::kv::kvspec_t::*;
use crate::kv::layout_v::*;
use crate::kv::setup_v::*;
use crate::kv::volatile::volatilespec_t::*;
use crate::log2::layout_v::*;
use crate::log2::logimpl_v::*;
// use crate::log::logimpl_t::*;
use crate::log2::logspec_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::lemma_establish_extract_bytes_equivalence;
use crate::pmem::wrpm_t::*;
use crate::pmem::subregion_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t;
use crate::pmem::crc_t::*;
use std::borrow::Borrow;
use std::hash::Hash;

use super::inv_v::lemma_safe_recovery_writes;
use super::oplog::oplogspec_t::AbstractOpLogState;
use super::oplog::oplogspec_t::AbstractPhysicalOpLogEntry;

verus! {
    #[verifier::reject_recursive_types(K)]
    pub struct DurableKvStore<PM, K, I, L>
    where
        PM: PersistentMemoryRegion,
        K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + std::fmt::Debug,
    {
        item_table: DurableItemTable<K, I>,
        durable_list: DurableList<K, L>,
        log: UntrustedOpLog<K, L>,
        metadata_table: MetadataTable<K>,
        wrpm: WriteRestrictedPersistentMemoryRegion<TrustedKvPermission<PM>, PM>,
        pending_updates: Vec<LogicalOpLogEntry<L>>,
    }

    impl<PM, K, I, L> DurableKvStore<PM, K, I, L>
        where
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
    {
        // TODO: write this based on specs of the other structures
        pub closed spec fn view(&self) -> DurableKvStoreView<K, I, L>;

        pub closed spec fn inv(self, mem: Seq<u8>) -> bool 
        {
            let version_metadata = deserialize_version_metadata(mem);
            let overall_metadata = deserialize_overall_metadata(mem, version_metadata.overall_metadata_addr);

            let physical_recovery_state = Self::physical_recover(mem, overall_metadata);
            let logical_recovery_state = Self::logical_recover(mem, overall_metadata);

            &&& physical_recovery_state matches Some(physical_recovery_state)
            &&& logical_recovery_state matches Some(logical_recovery_state)
            &&& physical_recovery_state == logical_recovery_state
            // TODO: metadata invariants?
        }

        // In physical recovery, we blindly replay the physical log obtained by recovering the op log onto the rest of the
        // persistent memory region.
        pub open spec fn physical_recover(mem: Seq<u8>, overall_metadata: OverallMetadata) -> Option<DurableKvStoreView<K, I, L>> {
            let recovered_log = UntrustedOpLog::<K, L>::recover(mem, overall_metadata);
            if let Some(recovered_log) = recovered_log {
                // First, replay the physical log
                let physical_log_entries = recovered_log.physical_op_list;
                let mem_with_log_installed = Self::apply_physical_log_entries(mem, physical_log_entries);
                if let Some(mem_with_log_installed) = mem_with_log_installed {
                    // Then, parse the individual components from the updated mem
                    let main_table_region = extract_bytes(mem_with_log_installed, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    let item_table_region = extract_bytes(mem_with_log_installed, overall_metadata.item_table_addr as nat, overall_metadata.item_table_size as nat);
                    let list_area_region = extract_bytes(mem_with_log_installed, overall_metadata.list_area_addr as nat, overall_metadata.list_area_size as nat);

                    let main_table_view = parse_metadata_table::<K>(
                        main_table_region, 
                        overall_metadata.num_keys,
                        overall_metadata.metadata_node_size
                    );
                    if let Some(main_table_view) = main_table_view {
                        let item_table_view = parse_item_table::<I, K>(
                            item_table_region,
                            overall_metadata.num_keys as nat,
                            main_table_view.valid_item_indices()
                        );
                        if let Some(item_table_view) = item_table_view {
                            let list_view = DurableList::<K, L>::parse_all_lists(
                                main_table_view,
                                list_area_region,
                                overall_metadata.list_node_size,
                                overall_metadata.num_list_entries_per_node
                            );
                            if let Some(list_view) = list_view {
                                Some(Self::recover_from_component_views(recovered_log, main_table_view, item_table_view, list_view))
                            } else {
                                None
                            }
                        } else { 
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            }
        }

        pub open spec fn apply_physical_log_entries(mem: Seq<u8>, physical_log_entries: Seq<AbstractPhysicalOpLogEntry>) -> Option<Seq<u8>>
            decreases physical_log_entries.len()
        {
            if physical_log_entries.len() == 0 {
                Some(mem)
            } else {
                let entry = physical_log_entries[0];
                // Update the bytes indicated in the log entry
                let op = physical_log_entries[0];
                let mem = Self::apply_physical_log_entry(mem, op);
                if let Some(mem) = mem {
                    let physical_log_entries = physical_log_entries.drop_first();
                    Self::apply_physical_log_entries(mem, physical_log_entries)
                } else {
                    None
                }
            }
        }

        pub open spec fn apply_physical_log_entry(mem: Seq<u8>, log_op: AbstractPhysicalOpLogEntry) -> Option<Seq<u8>>
        {
            if {
                ||| log_op.absolute_addr > mem.len() 
                ||| log_op.absolute_addr + log_op.len > mem.len() 
                ||| log_op.bytes.len() != log_op.len
            } {
                // Return None if the log_op is ill-formed
                None
            } else {
                Some(mem.map(|pos: int, pre_byte: u8| 
                    if log_op.absolute_addr <= pos < log_op.absolute_addr + log_op.len {
                        log_op.bytes[pos - log_op.absolute_addr]
                    } else {
                        pre_byte
                    }
                ))
            }
        }

        // pub proof fn lemma_write_log_entry_equivalent_to_spec_apply(
        //     mem: PersistentMemoryRegionView,
        //     op: AbstractPhysicalOpLogEntry,
        // )
        //     requires
        //         Self::apply_physical_log_entry(mem.committed(), op) is Some 
        //     ensures 
        //         ({
        //             let mem_applied = Self::apply_physical_log_entry(mem.committed(), op).unwrap();
        //             let mem_written = mem.write(op.absolute_addr as int, op.bytes).flush();
        //             mem_applied =~= mem_written.committed()
        //         })
        // {
        //     assume(false);
        // }

        // pub proof fn lemma_apply_remaining_log_ops_obtains_final_state(
        //     original_mem: Seq<u8>,
        //     current_mem: Seq<u8>,
        //     final_mem: Seq<u8>,
        //     replayed_log_ops: Seq<AbstractPhysicalOpLogEntry>,
        //     remaining_log_ops: Seq<AbstractPhysicalOpLogEntry>
        // )
        //     requires
        //         Self::apply_physical_log_entries(original_mem, replayed_log_ops + remaining_log_ops) is Some,
        //         Self::apply_physical_log_entries(original_mem, replayed_log_ops) is Some,
        //         final_mem == Self::apply_physical_log_entries(original_mem, replayed_log_ops + remaining_log_ops).unwrap(),
        //         current_mem == Self::apply_physical_log_entries(original_mem, replayed_log_ops).unwrap(),
        //     ensures
        //         Self::apply_physical_log_entries(current_mem, remaining_log_ops) is Some,
        //         final_mem == Self::apply_physical_log_entries(current_mem, remaining_log_ops).unwrap()
        // {
        //     assume(false);
        // }


        // pub proof fn lemma_apply_phys_log_entries_to_index(mem: Seq<u8>, index: int, phys_log: Seq<AbstractPhysicalOpLogEntry>)
        //     requires 
        //         0 < index <= phys_log.len(),
        //         Self::apply_physical_log_entries(mem, phys_log.subrange(0, index - 1)) is Some,
        //         Self::apply_physical_log_entries(mem, phys_log.subrange(0, index)) is Some,
        //         ({
        //             let mem1 = Self::apply_physical_log_entries(mem, phys_log.subrange(0, index - 1)).unwrap();
        //             let mem2 = Self::apply_physical_log_entry(mem1, phys_log[index - 1]);
        //             mem2 is Some
        //         }),
        //     ensures 
        //         ({
        //             let mem1 = Self::apply_physical_log_entries(mem, phys_log.subrange(0, index - 1)).unwrap();
        //             let mem2 = Self::apply_physical_log_entry(mem1, phys_log[index - 1]).unwrap();
        //             let final_mem = Self::apply_physical_log_entries(mem, phys_log.subrange(0, index)).unwrap();
        //             final_mem == mem2
        //         })
        //     decreases index
        // {
        //     if index == 1 {
        //         let mem1 = Self::apply_physical_log_entries(mem, phys_log.subrange(0, index - 1)).unwrap();
        //         assert(mem1 == mem);
        //         let mem2 = Self::apply_physical_log_entry(mem1, phys_log[index - 1]);
        //         assert(mem2 == Self::apply_physical_log_entries(mem, phys_log.subrange(0, index)));

        //     } else {
        //         // Self::lemma_apply_phys_log_entries_to_index(mem, index - 1, phys_log);
        //         assume(false);
        //     }
        // }

        pub proof fn lemma_log_replay_preserves_size(
            mem: Seq<u8>, 
            phys_log: Seq<AbstractPhysicalOpLogEntry>, 
        ) 
            requires
                Self::apply_physical_log_entries(mem, phys_log) is Some 
            ensures
                ({ 
                    let replay_mem = Self::apply_physical_log_entries(mem, phys_log).unwrap();
                    replay_mem.len() == mem.len()
                })
            decreases phys_log.len()
        {
            if phys_log.len() == 0 {
                // trivial
            } else {
                let current_entry = phys_log[0];
                let new_log = phys_log.drop_first();

                let mem1 = Self::apply_physical_log_entry(mem, current_entry).unwrap();
                assert(mem1.len() == mem.len());

                Self::lemma_log_replay_preserves_size(mem1, new_log);
            }
        }

        // This lemma proves that replaying a log of valid entries will always result in a Some return value
        pub proof fn lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(
            mem: Seq<u8>, 
            overall_metadata: OverallMetadata,
            phys_log: Seq<AbstractPhysicalOpLogEntry>, 
        )
            requires 
                AbstractPhysicalOpLogEntry::log_inv(phys_log, overall_metadata),
                mem.len() == overall_metadata.region_size,
                overall_metadata.log_area_addr < overall_metadata.log_area_addr + overall_metadata.log_area_size <= overall_metadata.region_size,
            ensures 
                Self::apply_physical_log_entries(mem, phys_log) is Some 
            decreases phys_log.len()
        {
            if phys_log.len() == 0 {
                // trivial -- empty log always returns Some
            } else {
                let current_entry = phys_log[0];
                let new_log = phys_log.drop_first();

                // Note that we have to apply the current entry before the recursive call
                // to make sure memory contents are correct for this point in replay
                assert(Self::apply_physical_log_entry(mem, current_entry) is Some);

                let mem1 = Self::apply_physical_log_entry(mem, current_entry).unwrap();

                assert(mem1.len() == mem.len());
                Self::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(
                    mem1,
                    overall_metadata,
                    new_log
                );
            }
        }

        pub proof fn lemma_mem_equal_after_recovery(
            mem1: Seq<u8>, 
            mem2: Seq<u8>,
            overall_metadata: OverallMetadata,
            phys_log: Seq<AbstractPhysicalOpLogEntry>, 
        )
            requires
                mem1.len() == mem2.len(),
                mem1.len() == overall_metadata.region_size,
                Self::apply_physical_log_entries(mem1, phys_log) is Some,
                Self::apply_physical_log_entries(mem2, phys_log) is Some,
                AbstractPhysicalOpLogEntry::log_inv(phys_log, overall_metadata),
                forall |i: int| 0 <= i < mem1.len() && mem1[i] != mem2[i] ==> addr_modified_by_recovery(phys_log, i),
            ensures
                ({
                    let replay1 = DurableKvStore::<PM, K, I, L>::apply_physical_log_entries(mem1, phys_log).unwrap();
                    let replay2 = DurableKvStore::<PM, K, I, L>::apply_physical_log_entries(mem2, phys_log).unwrap();
                    replay1 == replay2
                })
            decreases phys_log.len()
        {
            let replay1 = DurableKvStore::<PM, K, I, L>::apply_physical_log_entries(mem1, phys_log).unwrap();
            let replay2 = DurableKvStore::<PM, K, I, L>::apply_physical_log_entries(mem2, phys_log).unwrap();

            Self::lemma_log_replay_preserves_size(mem1, phys_log);
            Self::lemma_log_replay_preserves_size(mem2, phys_log);

            assert_seqs_equal!(replay1 == replay2, addr => {
                if mem1[addr] == mem2[addr] {
                    Self::lemma_byte_equal_before_recovery_implies_byte_equal_after_recovery(addr, mem1, mem2, overall_metadata, phys_log);
                } else {
                    Self::lemma_byte_modified_by_recovery_implies_byte_equal_after_recovery(addr, mem1, mem2, overall_metadata, phys_log);
                }
            });
        }

        pub proof fn lemma_byte_equal_before_recovery_implies_byte_equal_after_recovery(
            addr: int,
            mem1: Seq<u8>, 
            mem2: Seq<u8>,
            overall_metadata: OverallMetadata,
            phys_log: Seq<AbstractPhysicalOpLogEntry>,
        )
            requires
                mem1.len() == mem2.len(),
                mem1.len() == overall_metadata.region_size,
                Self::apply_physical_log_entries(mem1, phys_log) is Some,
                Self::apply_physical_log_entries(mem2, phys_log) is Some,
                AbstractPhysicalOpLogEntry::log_inv(phys_log, overall_metadata),
                mem1[addr] == mem2[addr],
                0 <= addr < mem1.len(),
            ensures
                ({
                    let replay1 = DurableKvStore::<PM, K, I, L>::apply_physical_log_entries(mem1, phys_log).unwrap();
                    let replay2 = DurableKvStore::<PM, K, I, L>::apply_physical_log_entries(mem2, phys_log).unwrap();
                    replay1[addr] == replay2[addr]
                })
            decreases phys_log.len()
        {
            if phys_log.len() == 0 {
                // trivial
            } else {
                let current_entry = phys_log[0];
                let remaining_log_entries = phys_log.drop_first();

                let mem1_prime = DurableKvStore::<PM, K, I, L>::apply_physical_log_entry(mem1, current_entry).unwrap();
                let mem2_prime = DurableKvStore::<PM, K, I, L>::apply_physical_log_entry(mem2, current_entry).unwrap();

                Self::lemma_byte_equal_before_recovery_implies_byte_equal_after_recovery(addr, mem1_prime, mem2_prime, overall_metadata, remaining_log_entries);
            }
        }

        pub proof fn lemma_byte_modified_by_recovery_implies_byte_equal_after_recovery(
            addr: int,
            mem1: Seq<u8>, 
            mem2: Seq<u8>,
            overall_metadata: OverallMetadata,
            phys_log: Seq<AbstractPhysicalOpLogEntry>,
        )
            requires
                mem1.len() == mem2.len(),
                mem1.len() == overall_metadata.region_size,
                Self::apply_physical_log_entries(mem1, phys_log) is Some,
                Self::apply_physical_log_entries(mem2, phys_log) is Some,
                AbstractPhysicalOpLogEntry::log_inv(phys_log, overall_metadata),
                addr_modified_by_recovery(phys_log, addr),
                0 <= addr < mem1.len(),
            ensures
                ({
                    let replay1 = DurableKvStore::<PM, K, I, L>::apply_physical_log_entries(mem1, phys_log).unwrap();
                    let replay2 = DurableKvStore::<PM, K, I, L>::apply_physical_log_entries(mem2, phys_log).unwrap();
                    replay1[addr] == replay2[addr]
                })
            decreases phys_log.len()
        {
            if phys_log.len() == 0 {
                // trivial
            } else {
                let current_entry = phys_log[0];
                let remaining_log_entries = phys_log.drop_first();

                let mem1_prime = DurableKvStore::<PM, K, I, L>::apply_physical_log_entry(mem1, current_entry).unwrap();
                let mem2_prime = DurableKvStore::<PM, K, I, L>::apply_physical_log_entry(mem2, current_entry).unwrap();

                if current_entry.absolute_addr <= addr < current_entry.absolute_addr + current_entry.len {
                    Self::lemma_byte_equal_before_recovery_implies_byte_equal_after_recovery(addr, mem1_prime, mem2_prime, overall_metadata, remaining_log_entries);
                } else {
                    let log_index = choose |i: int| 0 <= i < phys_log.len() && (#[trigger] phys_log[i]).absolute_addr <= addr < phys_log[i].absolute_addr + phys_log[i].len;
                    assert(remaining_log_entries[log_index - 1] == phys_log[log_index]);
                    Self::lemma_byte_modified_by_recovery_implies_byte_equal_after_recovery(addr, mem1_prime, mem2_prime, overall_metadata, remaining_log_entries);
                }
            }
        }

        pub proof fn lemma_apply_op(
            mem: Seq<u8>,
            ops: Seq<AbstractPhysicalOpLogEntry>,
            overall_metadata: OverallMetadata,
        )
            requires
                ops.len() > 0,
                overall_metadata.region_size == mem.len(),
                AbstractPhysicalOpLogEntry::log_inv(ops, overall_metadata),
                overall_metadata.log_area_addr < overall_metadata.log_area_addr + overall_metadata.log_area_size <= overall_metadata.region_size,
                ({
                    let last_op = ops[ops.len() - 1];
                    let prefix_ops = ops.subrange(0, ops.len() - 1);
                    &&& Self::apply_physical_log_entries(mem, prefix_ops) matches Some(m2)
                    &&& Self::apply_physical_log_entry(m2, last_op) is Some
                })
            ensures 
                ({
                    let last_op = ops[ops.len() - 1];
                    let prefix_ops = ops.subrange(0, ops.len() - 1);
                    let prefix_mem = Self::apply_physical_log_entries(mem, prefix_ops).unwrap();
                    let full_mem = Self::apply_physical_log_entry(prefix_mem, last_op).unwrap();
                    &&& Self::apply_physical_log_entries(mem, ops) is Some
                    &&& Self::apply_physical_log_entries(mem, ops).unwrap() == full_mem
                })
            decreases ops.len()
        {
            if ops.len() == 1 {
                // Base case -- applying one op then an empty log is the same as just applying that op
                let op = ops[0];
                let mem1 = Self::apply_physical_log_entry(mem, op).unwrap();
                let new_ops = ops.drop_first();
                assert(new_ops.len() == 0);
                assert(Self::apply_physical_log_entries(mem1, new_ops).unwrap() == mem1);
            } else {
                let first_op = ops[0];
                let last_op = ops[ops.len() - 1];
                // note -- you NEED to use drop_first here to hit the trigger
                let middle_ops = ops.subrange(0, ops.len() - 1).drop_first();
                let prefix_ops = ops.subrange(0, ops.len() - 1);
                let suffix_ops = ops.drop_first();

                // by def of apply, applying first then middle is equivalent to applying prefix
                let apply_first = Self::apply_physical_log_entry(mem, first_op).unwrap();
                let apply_middle_to_first = Self::apply_physical_log_entries(apply_first, middle_ops).unwrap();
                let apply_prefix = Self::apply_physical_log_entries(mem, prefix_ops).unwrap();
                assert(apply_middle_to_first == apply_prefix);

                // applying first, then middle, then last is equivalent to applying prefix then last
                let apply_last_to_middle_to_first = Self::apply_physical_log_entry(apply_middle_to_first, last_op).unwrap();
                let apply_last_to_prefix = Self::apply_physical_log_entry(apply_prefix, last_op).unwrap();
                assert(apply_last_to_middle_to_first == apply_last_to_prefix);

                Self::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(mem, overall_metadata, seq![first_op]);
                Self::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(apply_first, overall_metadata, suffix_ops);

                // the prefix considered on the next iteration will be the current `middle_ops`
                assert(middle_ops == suffix_ops.subrange(0, suffix_ops.len() - 1));

                assert(Self::apply_physical_log_entries(apply_first, suffix_ops) is Some);

                // shrink from the front and apply the first op each time; by the base case, 
                // the prefix will be empty and we can easily apply the last one.
                // we apply the first op and pass in just the suffix (i.e. with the first op removed)
                Self::lemma_apply_op(apply_first, suffix_ops, overall_metadata);
            }
        }

        // pub proof fn lemma_apply_op(
        //     // start: nat,
        //     // mid: nat, 
        //     // end: nat,
        //     original_mem: Seq<u8>,
        //     current_mem: Seq<u8>,
        //     phys_ops: Seq<AbstractPhysicalOpLogEntry>,
        //     // current_op: AbstractPhysicalOpLogEntry,
        // )
        //     // requires
        //     //     ({
        //     //         let mem = Self::apply_physical_log_entries(original_mem, phys_ops.drop_last());
        //     //         &&& mem is Some 
        //     //         &&& current_mem == mem.unwrap()
        //     //     }),
        //     //     ({
        //     //         let mem = Self::apply_physical_log_entries(original_mem, phys_ops);
        //     //         mem is Some
        //     //     }),
        //     //     ({
        //     //         let mem = Self::apply_physical_log_entry(current_mem, phys_ops[phys_ops.len() - 1]);
        //     //         &&& mem is Some 
        //     //     })
        //     // ensures 
        //     //     ({
        //     //         let mem1 = Self::apply_physical_log_entries(original_mem, phys_ops).unwrap();
        //     //         let mem2 = Self::apply_physical_log_entry(current_mem, phys_ops[phys_ops.len() - 1]).unwrap();
        //     //         mem1 == mem2
        //     //     })
        //     // decreases phys_ops.len() 
        // {
        //     // if phys_ops.len() == 1 {
        //     //     // not trivial
        //     //     assume(false);
        //     // } else {
        //     //     // // assume(false);
        //     //     // let new_current_op = phys_ops[phys_ops.len() - 1];
        //     //     // let new_phys_ops = phys_ops.subrange(0, phys_ops.len() - 1);
                
        //     //     // Self::lemma_apply_op(original_mem, new_current_mem, new_phys_ops, new_current_op);
        //     // }
        // }

        // pub proof fn lemma_addrs_not_modified_by_recovery_do_not_change(
        //     mem: Seq<u8>, 
        //     overall_metadata: OverallMetadata,
        //     phys_log: Seq<AbstractPhysicalOpLogEntry>, 
        //     // addr_modified_by_recovery: spec_fn(int) -> bool
        // ) 
        //     requires
        //         // forall |i: int| 0 <= i < phys_log.len() ==> {
        //         //     forall |j: int| 0 <= j < mem.len() && #[trigger] phys_log[i].absolute_addr <= j < phys_log[i].absolute_addr + #[trigger] phys_log[i].len <==> {
        //         //         #[trigger] addr_modified_by_recovery(j)
        //         //     }
        //         // },
        //         // ({
        //         //     let current_addr_modified_by_recovery = |i: int| 0 <= i < mem.len() ==> {
        //         //         exists |j: int| 0 <= j < phys_log.len() ==> {
        //         //             #[trigger] phys_log[j].absolute_addr <= i < phys_log[j].absolute_addr + #[trigger] phys_log[j].bytes.len()
        //         //         }
        //         //     };
        //         //     forall |i: int| 0 <= i < mem.len() && !#[trigger]addr_modified_by_recovery(i) ==> !#[trigger]current_addr_modified_by_recovery(i)
        //         // }),
        //         // 0 <= i < mem.len(),
        //         Self::apply_physical_log_entries(mem, phys_log) is Some,
        //         forall |i: int| 0 <= i < phys_log.len() ==> {
        //             let op = #[trigger] phys_log[i];
        //             &&& op.absolute_addr < op.absolute_addr + op.len < overall_metadata.region_size 
        //             &&& op.len == op.bytes.len()
        //         },
        //         mem.len() == overall_metadata.region_size,
        //     ensures 
        //         ({
        //             let addr_modified_by_recovery = |i: int| 0 <= i < mem.len() ==> {
        //                 exists |j: int| 0 <= j < phys_log.len() ==> {
        //                     #[trigger] phys_log[j].absolute_addr <= i < phys_log[j].absolute_addr + #[trigger] phys_log[j].bytes.len()
        //                 }
        //             };
        //             let replay_mem = Self::apply_physical_log_entries(mem, phys_log).unwrap();
        //             forall |i: int| 0 <= i < mem.len() && !addr_modified_by_recovery(i) ==> mem[i] == replay_mem[i]
        //         })
        //     decreases phys_log.len()
        // {
        //     if phys_log.len() == 0 {
        //         // trivial
        //     } else {
        //         let addr_modified_by_recovery = |i: int| 0 <= i < mem.len() ==> {
        //             exists |j: int| 0 <= j < phys_log.len() ==> {
        //                 #[trigger] phys_log[j].absolute_addr <= i < phys_log[j].absolute_addr + #[trigger] phys_log[j].bytes.len()
        //             }
        //         };

        //         let current_entry = phys_log[0];
        //         let new_log = phys_log.drop_first();

        //         let mem1 = Self::apply_physical_log_entry(mem, current_entry).unwrap();
        //         assert(forall |i: int| 0 <= i < mem.len() && !addr_modified_by_recovery(i) ==> mem[i] == mem1[i]);

        //         Self::lemma_addrs_not_modified_by_recovery_do_not_change(mem1, overall_metadata, new_log);

        //         let new_addr_modified_by_recovery = |i: int| 0 <= i < mem1.len() ==> {
        //             exists |j: int| 0 <= j < new_log.len() ==> {
        //                 #[trigger] new_log[j].absolute_addr <= i < new_log[j].absolute_addr + #[trigger] new_log[j].bytes.len()
        //             }
        //         };

        //         let replay_mem = Self::apply_physical_log_entries(mem1, new_log).unwrap();
        //         assert(forall |i: int| 0 <= i < replay_mem.len() && !new_addr_modified_by_recovery(i) ==> mem1[i] == replay_mem[i]);
        //         assert(replay_mem == Self::apply_physical_log_entries(mem, phys_log).unwrap());

        //         // missing a step here... if it's not modified by either operation then it's not modified at all?
            

        //         assert(forall |i: int| 0 <= i < mem.len() && !addr_modified_by_recovery(i) ==> mem[i] == replay_mem[i]);


        //         // // this is literally in the precondition?? why can't we prove it? 
        //         // assert(forall |i: int| 0 <= i < phys_log.len() ==> {
        //         //     forall |j: int| 0 <= j < mem.len() && #[trigger] phys_log[i].absolute_addr <= j < phys_log[i].absolute_addr + #[trigger] phys_log[i].len ==> {
        //         //         #[trigger] addr_modified_by_recovery(j)
        //         //     }
        //         // });

        //         // assert forall |i: int| 0 <= i < mem.len() && current_entry.absolute_addr <= i < current_entry.absolute_addr + current_entry.len implies {
        //         //     #[trigger] addr_modified_by_recovery(i)
        //         // } by {
                    
        //         // }

        //         // assert forall |i: int| 0 <= i < mem.len() && !addr_modified_by_recovery(i) implies mem1[i] == mem[i] by {
        //         //     assert(!(current_entry.absolute_addr <= i < current_entry.absolute_addr + current_entry.len));
        //         //     if current_entry.absolute_addr <= i < current_entry.absolute_addr + current_entry.len {
        //         //         assert(addr_modified_by_recovery(i));
        //         //         // assert(false);
        //         //     }
        //         //     // assert(i < current_entry.absolute_addr || current_entry.absolute_addr + current_entry.len <= i);
                    
        //         // }

        //         // assume(false);

        //         // Self::lemma_addrs_not_modified_by_recovery_do_not_change(mem1, overall_metadata, new_log, addr_modified_by_recovery);
        //         // // assume(false);
        //         // // assert(mem1[i] == mem[i]);

        //         // // addrs modified by ops in new log are a subset of those modified by the current log
        //         // let old_addr_modified_by_recovery = |i: int| 0 <= i < mem.len() ==> {
        //         //     exists |j: int| 0 <= j < phys_log.len() ==> {
        //         //         #[trigger] phys_log[j].absolute_addr <= i < phys_log[j].absolute_addr + #[trigger] phys_log[j].bytes.len()
        //         //     }
        //         // };
        //         // let new_addr_modified_by_recovery = |i: int| 0 <= i < mem.len() ==> {
        //         //     exists |j: int| 0 <= j < new_log.len() ==> {
        //         //         #[trigger] new_log[j].absolute_addr <= i < new_log[j].absolute_addr + #[trigger] new_log[j].bytes.len()
        //         //     }
        //         // };
        //         // let addrs_modified_by_current_entry = |i: int| current_entry.absolute_addr <= i < current_entry.absolute_addr + current_entry.len;
                
        //         // let old_addrs = Set::new(|i: int| old_addr_modified_by_recovery(i));
        //         // let new_addrs = Set::new(|i: int| new_addr_modified_by_recovery(i));
        //         // let current_addrs = Set::new(|i: int| addrs_modified_by_current_entry(i));
                
        //         // assert(old_addrs == new_addrs + current_addrs);

        //         // Self::lemma_addrs_not_modified_by_recovery_do_not_change(mem1, overall_metadata, new_log, i);
        //     }
        // }
                



        // pub proof fn lemma_apply_phys_log_succeeds_if_recover_succeeds(
        //     mem: Seq<u8>, 
        //     overall_metadata: OverallMetadata,
        //     phys_log: Seq<AbstractPhysicalOpLogEntry>, 
        // )
        //     requires
        //         Self::physical_recover(mem, overall_metadata) is Some,
        //         phys_log == UntrustedOpLog::<K, L>::recover(mem, overall_metadata).unwrap().physical_op_list,
        //     ensures 
        //         Self::apply_physical_log_entries(mem, phys_log) is Some,
        // {}

        // pub proof fn lemma_recover_fails_if_apply_phys_log_fails(
        //     mem: Seq<u8>, 
        //     overall_metadata: OverallMetadata,
        //     phys_log: Seq<AbstractPhysicalOpLogEntry>, 
        // )
        //     ensures
        //         Self::apply_physical_log_entries(mem, phys_log) is None ==> 
        //             Self::physical_recover(mem, overall_metadata) is None,
        //     decreases phys_log.len(),
        // {
        //     if phys_log.len() == 0 {
        //         // trivial -- we always succeed in this case
        //     } else {
        //         let current_entry = phys_log[0];
        //         let new_log = phys_log.drop_first();

        //         // let mem1 = Self::apply_physical_log_entry(mem, current_entry);
        //         // if let Some(mem1) = mem1 {
        //         //     Self::lemma_recover_fails_if_apply_phys_log_fails(
        //         //         mem1,
        //         //         overall_metadata,
        //         //         new_log
        //         //     );
        //         //     assume(false);
        //         // } else {
        //         //     assert(mem1 is None);
        //         //     assert(Self::apply_physical_log_entries(mem, phys_log) is None);
        //         //     assert(Self::physical_recover(mem, overall_metadata) is None);
        //         // }
        //     }
        // }


        // In logical recovery, we replay logical log entries based on replay functions provided by each component
        // TODO: might be useful to return mem from here?
        pub open spec fn logical_recover(mem: Seq<u8>, overall_metadata: OverallMetadata) -> Option<DurableKvStoreView<K, I, L>> 
        {
            let recovered_log = UntrustedOpLog::<K, L>::recover(mem, overall_metadata);
            if let Some(recovered_log) = recovered_log {
                let logical_log_entries = recovered_log.logical_op_list;
                // recover main table from logical log
                let main_table_region = extract_bytes(mem, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let main_table_region = MetadataTable::<K>::spec_replay_log_metadata_table(main_table_region, logical_log_entries);
                let main_table_view = parse_metadata_table::<K>(
                    main_table_region, 
                    overall_metadata.num_keys,
                    overall_metadata.metadata_node_size
                );
                if let Some(main_table_view) = main_table_view {
                    // recover item table. This does not involve the logical log, so we can just directly parse it
                    let item_table_region = extract_bytes(mem, overall_metadata.item_table_addr as nat, overall_metadata.item_table_size as nat);
                    let item_table_view = parse_item_table::<I, K>(
                        item_table_region,
                        overall_metadata.num_keys as nat,
                        main_table_view.valid_item_indices()
                    );
                    if let Some(item_table_view) = item_table_view {
                        // recover the list area from logical log
                        let list_area_region = extract_bytes(mem, overall_metadata.list_area_addr as nat, overall_metadata.list_area_size as nat);
                        let list_area_region = DurableList::<K, L>::replay_log_list_nodes(list_area_region, overall_metadata.list_node_size, logical_log_entries);
                        let list_view = DurableList::<K, L>::parse_all_lists(
                            main_table_view,
                            list_area_region,
                            overall_metadata.list_node_size,
                            overall_metadata.num_list_entries_per_node
                        );
                        if let Some(list_view) = list_view {
                            Some(Self::recover_from_component_views(recovered_log, main_table_view, item_table_view, list_view))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            }
        }

        // Note: this fn assumes that the item and list head in the main table entry point 
        // to valid entries in the corresponding structures.
        pub open spec fn recover_from_component_views(
            recovered_log: AbstractOpLogState<L>, 
            recovered_main_table: MetadataTableView<K>, 
            recovered_item_table: DurableItemTableView<I>,
            recovered_lists: DurableListView<K, L>
        ) -> DurableKvStoreView<K, I, L>
        {
            let contents = Map::new(
                |i: int| 0 <= i < recovered_main_table.durable_metadata_table.len() && recovered_main_table.durable_metadata_table[i] matches DurableEntry::Valid(_),
                |i: int| {
                    let main_table_entry = recovered_main_table.durable_metadata_table[i].unwrap_valid();
                    let item_index = main_table_entry.item_index();
                    let list_head_index = main_table_entry.list_head_index();
                    let key = main_table_entry.key();
                    
                    let item = recovered_item_table.durable_item_table[item_index as int].unwrap_valid().get_item();
                    let list_view = recovered_lists.durable_lists[key];
                    let list = DurableKvStoreList {
                            list: Seq::new(
                                    list_view.len(),
                                    |i: int| list_view[i].unwrap_valid().list_element()
                                )
                    };
                    DurableKvStoreViewEntry { key, item, list }
                }
            );
            DurableKvStoreView { contents }
        }

        pub closed spec fn valid(self) -> bool
        {
            // TODO
            true
        }

        pub exec fn get_elements_per_node(&self) -> u64 {
            self.durable_list.get_elements_per_node()
        }

        pub fn setup(
            pm_region: &mut PM,
            overall_metadata: OverallMetadata,
            overall_metadata_addr: u64,
            kvstore_id: u128,
        ) -> (result: Result<(), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                old(pm_region).inv(),
                old(pm_region)@.no_outstanding_writes(),
                overall_metadata.region_size == old(pm_region)@.len(),
                memory_correctly_set_up_on_region::<K, I, L>(old(pm_region)@.committed(), kvstore_id),
                overall_metadata_valid::<K, I, L>(overall_metadata, overall_metadata_addr, kvstore_id),
            ensures 
                pm_region.inv(),
                match result {
                    Ok(()) => {
                        &&& Self::physical_recover(pm_region@.committed(), overall_metadata) matches Some(recovered_view)
                        &&& Self::physical_recover(pm_region@.committed(), overall_metadata) == Self::logical_recover(pm_region@.committed(), overall_metadata)
                        &&& recovered_view == DurableKvStoreView::<K, I, L>::init()
                    }
                    Err(_) => true
                }
        {
            let num_keys = overall_metadata.num_keys;

            // Define subregions for each durable component and call setup on each one
            let ghost writable_addr_fn = |addr: int| true;
            let main_table_subregion = WritablePersistentMemorySubregion::new(
                pm_region, 
                overall_metadata.main_table_addr, 
                Ghost(overall_metadata.main_table_size as nat),
                Ghost(writable_addr_fn)
            );
            MetadataTable::<K>::setup::<PM, L>(&main_table_subregion, pm_region, num_keys, overall_metadata.metadata_node_size)?;
            proof { main_table_subregion.lemma_reveal_opaque_inv(pm_region); }

            proof {
                let bytes = pm_region@.flush().committed();
                let main_table_bytes = extract_bytes(bytes, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                assert(main_table_bytes == main_table_subregion.view(pm_region).flush().committed());
            }

            // Both the item table and list region do not require any writes in setup; we just need to prove that regardless of the contents of 
            // the PM in those areas, if we set up the item table correctly then 
            let item_table_subregion = WritablePersistentMemorySubregion::new(
                pm_region, 
                overall_metadata.item_table_addr, 
                Ghost(overall_metadata.item_table_size as nat),
                Ghost(writable_addr_fn)
            );
            proof { DurableItemTable::<K, I>::lemma_table_is_empty_at_setup::<PM, L>(&item_table_subregion, pm_region, Set::empty(), num_keys); }
            let list_area_subregion = WritablePersistentMemorySubregion::new(
                pm_region, 
                overall_metadata.list_area_addr, 
                Ghost(overall_metadata.list_area_size as nat),
                Ghost(writable_addr_fn)
            );
            proof { DurableList::lemma_list_is_empty_at_setup(&list_area_subregion, pm_region, AbstractOpLogState::<L>::initialize(), num_keys, 
                overall_metadata.list_node_size, overall_metadata.num_list_entries_per_node, overall_metadata.num_list_nodes, MetadataTableView::<K>::init(num_keys)) }

            let ghost pre_log_setup_bytes = pm_region@.flush().committed();

            UntrustedLogImpl::setup::<PM, K>(pm_region, overall_metadata.log_area_addr, overall_metadata.log_area_size)?;

            pm_region.flush();

            proof {
                // TODO: refactor this into a lemma
                let bytes = pm_region@.committed();
                let recovered_view = Self::physical_recover(bytes, overall_metadata);
                lemma_establish_extract_bytes_equivalence(pre_log_setup_bytes, bytes);

                // First, prove that the recovered view is Some if recovery of all of the other components succeeds.
                // For most of these, we just need to prove that the log setup function didn't modify the corresponding bytes,
                // which is already part of log setup's postcondition, but we need to invoke lemma_subrange_of_extract_bytes_equal
                // to make Verus do the required reasoning about subranges.

                // Op log recovery succeeds
                let recovered_log = UntrustedOpLog::<K, L>::recover(bytes, overall_metadata);
                let recovered_log = recovered_log.unwrap();

                // Main table recovery succeeds
                let main_table_bytes = extract_bytes(bytes, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let post_install_main_table_bytes = MetadataTable::<K>::spec_replay_log_metadata_table(main_table_bytes, recovered_log.logical_op_list);
                let recovered_main_table = parse_metadata_table::<K>(post_install_main_table_bytes, overall_metadata.num_keys, overall_metadata.metadata_node_size);
                lemma_subrange_of_extract_bytes_equal(bytes, 0, overall_metadata.main_table_addr as nat, overall_metadata.log_area_addr as nat, overall_metadata.main_table_size as nat);

                // Item table recover succeeds
                let item_table_bytes = extract_bytes(bytes, overall_metadata.item_table_addr as nat, overall_metadata.item_table_size as nat);
                let valid_indices = recovered_main_table.unwrap().valid_item_indices();
                lemma_subrange_of_extract_bytes_equal(bytes, 0, overall_metadata.item_table_addr as nat, overall_metadata.log_area_addr as nat, overall_metadata.item_table_size as nat);

                // List recover succeeds
                let list_area_bytes = extract_bytes(bytes, overall_metadata.list_area_addr as nat, overall_metadata.list_area_size as nat);
                lemma_subrange_of_extract_bytes_equal(bytes, 0, overall_metadata.list_area_addr as nat, overall_metadata.log_area_addr as nat, overall_metadata.list_area_size as nat);
                

                DurableList::<K, L>::lemma_parse_each_list_succeeds_if_no_valid_metadata_entries(
                    recovered_main_table.unwrap().get_durable_metadata_table(),
                    list_area_bytes,
                    Map::empty(),
                    overall_metadata.list_node_size,
                    overall_metadata.num_list_entries_per_node,
                );

                // Now need to prove that the recovered view matches init, i.e. that it results in an empty map.
                assert(recovered_view.unwrap().contents =~= Map::<int, DurableKvStoreViewEntry<K, I, L>>::empty());
            }

            Ok(())
        }


        fn start(
            mut wrpm_region: WriteRestrictedPersistentMemoryRegion<TrustedKvPermission<PM>, PM>,
            overall_metadata: OverallMetadata,
            version_metadata: VersionMetadata,
            Tracked(perm): Tracked<&TrustedKvPermission<PM>>,
            Ghost(state): Ghost<DurableKvStoreView<K, I, L>>,
        ) -> (result: Result<Self, KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires
                wrpm_region.inv(),
                wrpm_region@.no_outstanding_writes(),
                Self::physical_recover(wrpm_region@.committed(), overall_metadata) == Some(state),
                overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr, overall_metadata.kvstore_id),
                overall_metadata.log_area_addr + overall_metadata.log_area_size <= wrpm_region@.len() <= u64::MAX,
                overall_metadata.log_area_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
                forall |s| #[trigger] perm.check_permission(s) <==> Self::physical_recover(s, overall_metadata) == Some(state),
                wrpm_region@.len() == overall_metadata.region_size,
                ({
                    let base_log_state = UntrustedLogImpl::recover(wrpm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
                    let phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
                    let abstract_op_log = UntrustedOpLog::<K, L>::parse_log_ops(phys_op_log_buffer, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat);
                    &&& abstract_op_log matches Some(abstract_log)
                    &&& 0 < abstract_log.len() <= u64::MAX
                }),
                // TODO: move these into one of the metadata validity spec fns
                0 < spec_log_header_area_size() <= spec_log_area_pos() < overall_metadata.log_area_size,
                0 <= overall_metadata.log_area_addr < overall_metadata.log_area_addr + overall_metadata.log_area_size < overall_metadata.region_size,
            ensures
                match result {
                    Ok(kvstore) => {
                        &&& kvstore@ == state
                        &&& kvstore.inv(wrpm_region@.committed())
                    }
                    Err(KvError::CRCMismatch) => !wrpm_region.constants().impervious_to_corruption,
                    Err(KvError::LogErr { log_err }) => true, // TODO: better handling for this and PmemErr
                    Err(KvError::PmemErr { pmem_err }) => true,
                    Err(KvError::InternalError) => true,
                    Err(_) => false
                }
        {
            // 1. Start the log and obtain logged operations (if any)
            // We obtain physical log entries in an unparsed vector as parsing them would require an additional copy in DRAM
            let (op_log, phys_log) = UntrustedOpLog::<K, L>::start(&wrpm_region, overall_metadata)?;

            // 2. Replay the log onto the entire PM region
            // Log entries are replayed blindly onto bytes; components do not have their own
            // replay functions. We only parse them after finishing log replay
            if phys_log.len() > 0 {
                proof {
                    PhysicalOpLogEntry::lemma_abstract_log_inv_implies_concrete_log_inv(phys_log, overall_metadata);
                }
                Self::install_log(&mut wrpm_region, overall_metadata, version_metadata, phys_log, Tracked(perm));
            }

            // assert(wrpm_region@.committed())
            
            
            assume(false);
            Err(KvError::NotImplemented)
        }

        // This function installs the log by blindly replaying physical log entries onto the WRPM region. All writes
        // made by this function are crash-safe; if we crash during this operation, replaying the full log on the resulting
        // crash state gets us to the final desired state. This function does not return a Result because it cannot fail
        // as long as the log is well-formed, which is required by the precondition.
        fn install_log<Perm>(
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
            overall_metadata: OverallMetadata,
            version_metadata: VersionMetadata,
            phys_log: Vec<PhysicalOpLogEntry>,
            Tracked(perm): Tracked<&Perm>,
        ) 
            where 
                PM: PersistentMemoryRegion,
                Perm: CheckPermission<Seq<u8>>,
            requires
                old(wrpm_region).inv(),
                old(wrpm_region)@.no_outstanding_writes(),
                old(wrpm_region)@.len() == overall_metadata.region_size,
                PhysicalOpLogEntry::log_inv(phys_log, overall_metadata),
                phys_log.len() > 0,
                UntrustedLogImpl::recover(old(wrpm_region)@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat) is Some,
                ({
                    let abstract_op_log = UntrustedOpLog::<K, L>::recover(old(wrpm_region)@.committed(), overall_metadata);
                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                    &&& abstract_op_log matches Some(abstract_op_log)
                    &&& abstract_op_log.physical_op_list == phys_log_view
                    &&& AbstractPhysicalOpLogEntry::log_inv(phys_log_view, overall_metadata)
                }),
                forall |s| DurableKvStore::<PM, K, I, L>::physical_recover(old(wrpm_region)@.committed(), overall_metadata) == DurableKvStore::<PM, K, I, L>::physical_recover(s, overall_metadata) 
                    ==> perm.check_permission(s),
                0 <= overall_metadata.log_area_addr < overall_metadata.log_area_addr + overall_metadata.log_area_size < overall_metadata.region_size,
                0 < spec_log_header_area_size() <= spec_log_area_pos() < overall_metadata.log_area_size,
                DurableKvStore::<PM, K, I, L>::physical_recover(old(wrpm_region)@.committed(), overall_metadata) is Some,
            ensures 
                ({
                    // is this postcond strong enough? no.. it's trivial
                    let true_recovery_state = DurableKvStore::<PM, K, I, L>::physical_recover(old(wrpm_region)@.committed(), overall_metadata).unwrap();
                    let recovery_state = DurableKvStore::<PM, K, I, L>::physical_recover(wrpm_region@.committed(), overall_metadata);
                    &&& recovery_state matches Some(recovery_state)
                    &&& recovery_state == true_recovery_state
                }),
                ({
                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                    let true_final_state = Self::apply_physical_log_entries(old(wrpm_region)@.committed(), phys_log_view);
                    wrpm_region@.committed() == true_final_state.unwrap()
                })
        {
            let log_start_addr = overall_metadata.log_area_addr;
            let log_size = overall_metadata.log_area_size;
            let region_size = overall_metadata.region_size;

            let ghost old_phys_log = phys_log;
            let ghost old_wrpm = wrpm_region@.committed();

            let ghost final_recovery_state = DurableKvStore::<PM, K, I, L>::physical_recover(old(wrpm_region)@.committed(), overall_metadata).unwrap();

            let mut index = 0;

            proof {
                let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                let replayed_ops = phys_log_view.subrange(0, index as int);
                let remaining_ops = phys_log_view.subrange(index as int, phys_log.len() as int);
                let final_mem = Self::apply_physical_log_entries(old_wrpm, phys_log_view).unwrap();
                let current_mem = Self::apply_physical_log_entries(old_wrpm, replayed_ops).unwrap();

                assert(replayed_ops.len() == 0);
                assert(remaining_ops == phys_log_view);
                assert(current_mem == old_wrpm);
                assert(Self::apply_physical_log_entries(old_wrpm, remaining_ops).unwrap() == final_mem);
            }

            while index < phys_log.len() 
                invariant
                    old_wrpm.len() == wrpm_region@.len(),
                    PhysicalOpLogEntry::log_inv(phys_log, overall_metadata),
                    forall |s|  DurableKvStore::<PM, K, I, L>::physical_recover(s, overall_metadata) == 
                        Some(final_recovery_state) ==> #[trigger] perm.check_permission(s),
                    DurableKvStore::<PM, K, I, L>::physical_recover(wrpm_region@.committed(), overall_metadata) == 
                        Some(final_recovery_state),
                    old_phys_log == phys_log,
                    ({
                        let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                        let replayed_ops = phys_log_view.subrange(0, index as int);
                        let current_mem = Self::apply_physical_log_entries(old_wrpm, replayed_ops);
                        &&& current_mem is Some 
                        &&& current_mem.unwrap() == wrpm_region@.committed()
                        &&& recovery_write_region_invariant::<PM, K, I, L, Perm>(*wrpm_region, overall_metadata, phys_log_view)
                    }),
                    0 <= index <= phys_log.len(),
            {
                let op = &phys_log[index];

                proof {
                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);

                    // These two assertions are obvious from the loop invariant, but we need them to for triggers
                    assert(op.inv(overall_metadata)); 
                    assert({
                        ||| op.absolute_addr + op.len <= overall_metadata.log_area_addr
                        ||| overall_metadata.log_area_addr + overall_metadata.log_area_size <= op.absolute_addr
                    });

                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                    assert(phys_log_view[index as int] == phys_log[index as int]@);
                    assert(forall |i: int| op.absolute_addr <= i < op.absolute_addr + op.len ==> 
                        #[trigger] addr_modified_by_recovery(phys_log_view, i));

                    
                    // Prove that any write to an address modified by recovery is crash-safe
                    lemma_safe_recovery_writes::<PM, K, I, L, Perm>(*wrpm_region, overall_metadata, phys_log_view, op.absolute_addr as int, op.bytes@);
                }

                proof {
                    
                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                    let replayed_ops = phys_log_view.subrange(0, index as int);
                    // let remaining_ops = phys_log_view.subrange(index as int, phys_log.len() as int);
                    // let final_mem = Self::apply_physical_log_entries(old_wrpm, phys_log_view);
                    let current_mem = Self::apply_physical_log_entries(old_wrpm, replayed_ops);

                    // From the loop invariant
                    assert(current_mem is Some);
                    assert(current_mem.unwrap() == wrpm_region@.committed());

                    let new_wrpm = wrpm_region@.write(op.absolute_addr as int, op.bytes@).flush();
                    let new_replayed_ops = phys_log_view.subrange(0, index + 1);
                    let new_mem = Self::apply_physical_log_entries(old_wrpm, new_replayed_ops);

                    Self::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(old_wrpm, overall_metadata, new_replayed_ops);
                    assert(new_mem is Some);

                    // Self::lemma_write_log_entry_equivalent_to_spec_apply(wrpm_region@, op@);

                    let step_mem = Self::apply_physical_log_entry(current_mem.unwrap(), op@);

                    assert(step_mem is Some);
                    assert(new_replayed_ops == replayed_ops + seq![op@]);

                    assert(Self::apply_physical_log_entries(old_wrpm, replayed_ops) is Some);
                    assert(replayed_ops == new_replayed_ops.subrange(0, new_replayed_ops.len() - 1));
                    Self::lemma_apply_op(old_wrpm, new_replayed_ops, overall_metadata);

                    assert(step_mem.unwrap() == new_wrpm.committed());
                    assert(step_mem.unwrap() == new_mem.unwrap());

                    assert(new_mem.unwrap() == new_wrpm.committed());
                }

                let ghost pre_write_wrpm = wrpm_region@;

                // write the current op's updates to the specified location on storage
                wrpm_region.write(op.absolute_addr, op.bytes.as_slice(), Tracked(perm));
                wrpm_region.flush();

                index += 1;
            }

            proof {
                let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                assert(phys_log_view.subrange(0, index as int) == phys_log_view);
            }
        }


/*

        pub fn start(
            mut metadata_wrpm: WriteRestrictedPersistentMemoryRegion<TrustedMetadataPermission, PM>,
            mut item_table_wrpm: WriteRestrictedPersistentMemoryRegion<TrustedItemTablePermission, PM>,
            mut list_wrpm: WriteRestrictedPersistentMemoryRegion<TrustedListPermission, PM>,
            mut log_wrpm: WriteRestrictedPersistentMemoryRegion<TrustedPermission, PM>,
            kvstore_id: u128,
            num_keys: u64,
            node_size: u32,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L>>,
            // Ghost(state): Ghost<DurableKvStoreView<K, I, L>>
        ) -> (result: Result<(Self, Vec<(Box<K>, u64)>), KvError<K>>)
            where
                PM: PersistentMemoryRegion,
            requires
                metadata_wrpm.inv(),
                item_table_wrpm.inv(),
                list_wrpm.inv(),
                log_wrpm.inv(),
                L::spec_size_of() + u64::spec_size_of() <= u32::MAX
                // TODO
            ensures
                metadata_wrpm.inv(),
                item_table_wrpm.inv(),
                list_wrpm.inv(),
                log_wrpm.inv(),
                // TODO
        {
            assume(false);

            // TEMPORARY, NOT CORRECT: make up a permissions struct for each component to start with. since we aren't 
            // writing any proofs yet, we don't need the perm to be correct.
            // These perms should actually be derived from the higher-level kv permission
            let tracked fake_metadata_perm = TrustedMetadataPermission::fake_metadata_perm();
            let tracked fake_item_table_perm = TrustedItemTablePermission::fake_item_perm();
            let tracked fake_list_perm = TrustedListPermission::fake_list_perm();
            let tracked fake_log_perm = TrustedPermission::fake_log_perm();

            let list_element_size = (L::size_of() + traits_t::size_of::<u64>()) as u32;

            // 1. Recover the log to get the list of log entries.
            // TODO: we only need to replay the log if we crashed? We don't have clean shutdown implemented right now anyway though
            let mut log: UntrustedOpLog<K, L> = UntrustedOpLog::start(&mut log_wrpm, kvstore_id, Tracked(&fake_log_perm))?;
            let log_entries = log.read_op_log(&log_wrpm, kvstore_id)?;
            // 2. start the rest of the components using the log
            let (metadata_table, key_index_pairs) = MetadataTable::start(&mut metadata_wrpm, kvstore_id, &log_entries, Tracked(&fake_metadata_perm), Ghost(MetadataTableView::init(list_element_size, node_size, num_keys)))?;
            let item_table: DurableItemTable<K, I> = DurableItemTable::start(&mut item_table_wrpm, kvstore_id, &log_entries, Tracked(&fake_item_table_perm), Ghost(DurableItemTableView::init(num_keys as int)))?;
            let durable_list = DurableList::start(&mut list_wrpm, kvstore_id, node_size, &log_entries, Tracked(&fake_list_perm), Ghost(DurableListView::init()))?;

            metadata_wrpm.flush();
            item_table_wrpm.flush();
            list_wrpm.flush();
            log_wrpm.flush();

            // 3. we've successfully replayed the log. clear it to free up space for a new transaction
            log.clear_log(&mut log_wrpm, kvstore_id, Tracked(&fake_log_perm))?;
            Ok((
                Self {
                    item_table,
                    durable_list,
                    log,
                    metadata_table,
                    item_table_wrpm,
                    list_wrpm,
                    log_wrpm,
                    metadata_wrpm,
                    pending_updates: Vec::new(),
                }, 
                key_index_pairs
            ))
        }

        // Commits all pending updates by committing the log and applying updates to 
        // each durable component.
        pub fn commit(
            &mut self,
            kvstore_id: u128,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L>>
        ) -> (result: Result<(), KvError<K>>)
            requires 
                // TODO 
            ensures 
                // TODO 
        {
            // 1. Commit the log
            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            self.log.commit_log(&mut self.log_wrpm, kvstore_id, Tracked(&fake_log_perm))?;

            // 2. Play the log on each durable component
            let tracked fake_metadata_perm = TrustedMetadataPermission::fake_metadata_perm();
            let tracked fake_item_perm = TrustedItemTablePermission::fake_item_perm();
            let tracked fake_list_perm = TrustedListPermission::fake_list_perm();
            // TODO: handle the ghost states properly here
            self.metadata_table.play_metadata_log(&mut self.metadata_wrpm, kvstore_id, 
                &self.pending_updates, Tracked(&fake_metadata_perm), Ghost(self.metadata_table@))?;
            self.item_table.play_item_log(&mut self.item_table_wrpm, kvstore_id, 
                &self.pending_updates, Tracked(&fake_item_perm), Ghost(self.item_table@))?;
            self.durable_list.play_log_list(&mut self.list_wrpm, kvstore_id, &self.pending_updates, 
                Tracked(&fake_list_perm), Ghost(self.durable_list@))?;

            // 3. Clear the log
            self.log.clear_log(&mut self.log_wrpm, kvstore_id, Tracked(&fake_log_perm))?;

            // 4. Clear the local pending log updates list
            self.pending_updates.clear();

            Ok(())
        }

        // Creates a new durable record in the KV store. Note that since the durable KV store 
        // identifies records by their metadata table index, rather than their key, this 
        // function does NOT return an error if you attempt to create two records with the same 
        // key. Returns the metadata index and the location of the list head node.
        // TODO: Should require caller to prove that the key doesn't already exist in order to create it.
        // The caller should do this because this can be done quickly with the volatile info.
        pub fn tentative_create(
            &mut self,
            key: &K,
            item: &I,
            kvstore_id: u128,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L>>
        ) -> (result: Result<(u64, u64), KvError<K>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                ({
                    match result {
                        Ok((offset, head_node)) => {
                            let spec_result = old(self)@.create(offset as int, *key, *item);
                            match spec_result {
                                Ok(spec_result) => {
                                    &&& self@.len() == old(self)@.len() + 1
                                    &&& self@ == spec_result
                                    &&& 0 <= offset < self@.len()
                                    &&& self@[offset as int].is_Some()
                                }
                                Err(_) => false
                            }
                        }
                        Err(_) => false
                    }
                })
        {
            assume(false);

            // 1. find a free slot in the item table and tentatively write the new item there
            let tracked fake_item_table_perm = TrustedItemTablePermission::fake_item_perm();
            let item_index = self.item_table.tentatively_write_item(
                &mut self.item_table_wrpm, 
                Ghost(kvstore_id), 
                &item, 
                Tracked(&fake_item_table_perm)
            )?;

            // 2. allocate and initialize a head node for this entry; this is tentative since the node is 
            // not yet accessible 
            let tracked fake_list_perm = TrustedListPermission::fake_list_perm();
            let head_index = self.durable_list.alloc_and_init_list_node(
                &mut self.list_wrpm, 
                Ghost(kvstore_id), 
                Tracked(&fake_list_perm)
            )?;

            // 3. find a free slot in the metadata table and tentatively write a new entry to it
            let tracked fake_metadata_perm = TrustedMetadataPermission::fake_metadata_perm();
            let metadata_index = self.metadata_table.tentative_create(
                &mut self.metadata_wrpm, 
                Ghost(kvstore_id), 
                head_index, 
                item_index, 
                key,
                Tracked(&fake_metadata_perm)
            )?;

            // 4. tentatively append the new item's commit op to the log. Metadata entry commit 
            // implies item commit and also makes the list accessible so we can append to it
            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            let tracked fake_item_table_perm = TrustedItemTablePermission::fake_item_perm();
            let tracked fake_metadata_table_perm = TrustedMetadataPermission::fake_metadata_perm();

            let item_log_entry: OpLogEntryType<L> = OpLogEntryType::ItemTableEntryCommit { item_index };
            let metadata_log_entry: OpLogEntryType<L> = OpLogEntryType::CommitMetadataEntry { metadata_index };

            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &item_log_entry, Tracked(&fake_log_perm))?;
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &metadata_log_entry, Tracked(&fake_log_perm))?;

            // 5. Add log entries to pending list
            self.pending_updates.push(item_log_entry);
            self.pending_updates.push(metadata_log_entry);

            // 6. Return the index of the metadata entry so it can be used in the volatile index.
            Ok((metadata_index, head_index))
        }

        // This function takes an offset into the METADATA table, looks up the corresponding item,
        // and returns it if it exists.
        pub fn read_item(
            &self,
            kvstore_id: u128,
            metadata_index: u64
        ) -> (result: Result<Box<I>, KvError<K>>)
            requires
                self.valid(),
            ensures
                match result {
                    Ok(item) => {
                        match self@[metadata_index as int] {
                            Some(entry) => entry.item() == item,
                            None => false
                        }
                    }
                    Err(_) => self@[metadata_index as int].is_None()
                }
        {
            assume(false);
            let (key, metadata) = self.metadata_table.get_key_and_metadata_entry_at_index(
                self.metadata_wrpm.get_pm_region_ref(), kvstore_id, metadata_index)?;
            let item_index = metadata.item_index;
            self.item_table.read_item(self.item_table_wrpm.get_pm_region_ref(), kvstore_id, item_index)
        }

        pub fn get_list_len(
            &self,
            kvstore_id: u128,
            metadata_index: u64
        ) -> Result<u64, KvError<K>>
            requires 
                // TODO 
            ensures 
                // TODO 
        {
            assume(false);
            let (_, metadata) = self.metadata_table.get_key_and_metadata_entry_at_index(
                self.metadata_wrpm.get_pm_region_ref(), kvstore_id, metadata_index)?;
            Ok(metadata.length)
        }

        // TODO: should this require a check to make sure we are reading 
        // from a valid list node and from the key that we expect?
        pub fn read_list_entry_at_index(
            &self,
            node_location: u64,
            index_in_node: u64,
            kvstore_id: u128,
        ) -> (result: Result<Box<L>, KvError<K>>)
            requires
                self.valid(),
            ensures
                match (result, self@[node_location as int]) {
                    (Ok(output_list_entry), Some(spec_entry)) => {
                        let spec_list_entry = spec_entry.list()[index_in_node as int];
                        &&& spec_list_entry is Some
                        &&& spec_list_entry.unwrap() == output_list_entry
                    }
                    (Err(KvError::IndexOutOfRange), _) => {
                        &&& self@[node_location as int] is Some
                        &&& self@[node_location as int].unwrap().list()[index_in_node as int] is None
                    }
                    (Err(_), Some(spec_entry)) => false,
                    (Ok(output_list_entry), None) => false,
                    (_, _) => false
                }
        {
            assume(false);
            self.durable_list.read_element_at_index(self.list_wrpm.get_pm_region_ref(), kvstore_id, node_location, index_in_node)
        }

        pub fn tentative_update_item(
            &mut self,
            metadata_index: u64,
            kvstore_id: u128,
            new_item: &I,
        ) -> (result: Result<(), KvError<K>>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        match (old(self)@[metadata_index as int], self@[metadata_index as int]) {
                            (Some(old_entry), Some(entry)) => {
                                &&& entry.key() == old_entry.key()
                                &&& entry.item() == new_item
                                &&& entry.list() == old_entry.list()
                            }
                            (_, _) => false
                        }
                    }
                    Err(KvError::KeyNotFound) => self@[metadata_index as int].is_None(),
                    Err(_) => true // TODO
                }
        {
            assume(false);
            // 1. Look up current index of the item via the metadata table
            let (key, mut metadata) = self.metadata_table.get_key_and_metadata_entry_at_index(
                self.metadata_wrpm.get_pm_region_ref(), kvstore_id, metadata_index)?;

            let old_item_index = metadata.item_index;

            // 2. Tentatively allocate a new item slot and write the new item to it
            let tracked fake_item_table_perm = TrustedItemTablePermission::fake_item_perm();
            let new_item_index = self.item_table.tentatively_write_item(
                &mut self.item_table_wrpm, 
                Ghost(kvstore_id), 
                &new_item, 
                Tracked(&fake_item_table_perm)
            )?;

            // 3. Update the metadata structure with the new item index
            metadata.item_index = new_item_index;

            // 4. Calculate the CRC for the updated metadata together with the key. We cannot 
            // trust that the CRC, key, or metadata are correct during replay in general, so we 
            // either need to log the new CRC or the key so that we can make sure to update the 
            // entry with the correct CRC when we apply the update at commit time. 

            let mut digest = CrcDigest::new();
            digest.write(&*metadata);
            digest.write(&*key);
            let new_crc = digest.sum64();

            // 5. Log the metadata update, the new item commit, and the old item invalidate
            let metadata_update = OpLogEntryType::UpdateMetadataEntry { metadata_index, new_metadata: *metadata, new_crc };
            let new_item_commit = OpLogEntryType::ItemTableEntryCommit { item_index: new_item_index };
            let old_item_invalid = OpLogEntryType::ItemTableEntryInvalidate { item_index: old_item_index };

            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &metadata_update, Tracked(&fake_log_perm))?;
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &new_item_commit, Tracked(&fake_log_perm))?;
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &old_item_invalid, Tracked(&fake_log_perm))?;

            // 6. Add pending log entries to list
            self.pending_updates.push(metadata_update);
            self.pending_updates.push(new_item_commit);
            self.pending_updates.push(old_item_invalid);

            Ok(())
        }

        pub fn tentative_delete(
            &mut self,
            metadata_index: u64,
            kvstore_id: u128,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L>>,
        ) -> (result: Result<(), KvError<K>>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        self@[metadata_index as int].is_None()
                    }
                    Err(_) => true // TODO
                }
        {
            assume(false);

            // TODO: could get rid of item valid/invalid IF we had another way to determine 
            // if they are allocated (like getting that info from the metadata table)

            // TODO: DEALLOCATE LIST NODES

            // 1. look up the item index so that we can invalidate it 
            let (key, mut metadata) = self.metadata_table.get_key_and_metadata_entry_at_index(
                self.metadata_wrpm.get_pm_region_ref(), kvstore_id, metadata_index)?;
            let item_index = metadata.item_index;

            // 2. Log the item and metadata invalidation
            let item_invalidate = OpLogEntryType::ItemTableEntryInvalidate { item_index };
            let metadata_invalidate = OpLogEntryType::InvalidateMetadataEntry { metadata_index };

            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &item_invalidate, Tracked(&fake_log_perm))?;
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &metadata_invalidate, Tracked(&fake_log_perm))?;

            // 3. Add pending log entries to list
            self.pending_updates.push(item_invalidate);
            self.pending_updates.push(metadata_invalidate);

            Ok(())
        }

        // This function appends a new list entry *without* allocating a new list node.
        // It fails if there is no space left in the tail node.
        // TODO: write a variant of this that allows atomically appending an arbitrary number 
        // of list elements (potentially with allocation) in a single transaction
        pub fn tentative_append(
            &mut self,
            metadata_index: u64,
            new_entry: &L,
            node_location: u64, 
            index_in_node: u64, 
            kvstore_id: u128,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L>>,
        ) -> (result: Result<(), KvError<K>>)
            requires
                old(self).valid(),
                // should require that there is enough space in the tail node
                // and that the given node is in fact the tail
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        let old_record = old(self)@.contents[metadata_index as int];
                        let new_record = self@.contents[metadata_index as int];
                        &&& new_record.list().list == old_record.list().list.push(*new_entry)
                    }
                    Err(_) => false // TODO
                }
        {   
            // TODO: add error handling or use preconditions that prevent errors

            assume(false);
            // 1. look up list metadata
            let (key, mut metadata) = self.metadata_table.get_key_and_metadata_entry_at_index(
                self.metadata_wrpm.get_pm_region_ref(), kvstore_id, metadata_index)?;
            
            // 2. append the new list element to the list. This is a tentative write and does not need to be logged.
            let tracked fake_list_perm = TrustedListPermission::fake_list_perm();
            self.durable_list.append_element(&mut self.list_wrpm, kvstore_id, node_location, 
                index_in_node, &new_entry, Tracked(&fake_list_perm))?;

            // 3. Calculate the new CRC
            metadata.length = metadata.length + 1;
            let mut digest = CrcDigest::new();
            digest.write(&*metadata);
            digest.write(&*key);
            let new_crc = digest.sum64();

            // 4. Log the length update to the metadata
            let list_len_update = OpLogEntryType::UpdateMetadataEntry { metadata_index, new_crc, new_metadata: *metadata };
            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &list_len_update, Tracked(&fake_log_perm))?;

            // 5. Add pending log entry to list
            self.pending_updates.push(list_len_update);

            Ok(())
        }

        pub fn tentative_alloc_list_node(
            &mut self,
            metadata_index: u64,
            kvstore_id: u128,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L>>,
        ) -> (result: Result<u64, KvError<K>>)
            requires 
                // TODO 
            ensures 
                // TODO 
        {
            assume(false);
            // 1. Look up metadata
            let (key, mut metadata) = self.metadata_table.get_key_and_metadata_entry_at_index(
                self.metadata_wrpm.get_pm_region_ref(), kvstore_id, metadata_index)?;

            // 2. Tentatively allocate and initialize an unused list node
            let tracked fake_list_perm = TrustedListPermission::fake_list_perm();
            let new_list_node_loc = self.durable_list.alloc_and_init_list_node(&mut self.list_wrpm, Ghost(kvstore_id), Tracked(&fake_list_perm))?;

            // 3. Update the metadata with the new tail node and calculate the new crc
            let old_tail = metadata.tail;
            metadata.tail = new_list_node_loc;
            let mut digest = CrcDigest::new();
            digest.write(&*metadata);
            digest.write(&*key);
            let new_crc = digest.sum64();

            // 4. Log metadata update and list node append 
            let tail_update = OpLogEntryType::UpdateMetadataEntry { metadata_index, new_crc, new_metadata: *metadata };
            let node_append = OpLogEntryType::AppendListNode { metadata_index, old_tail, new_tail: new_list_node_loc };

            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &tail_update, Tracked(&fake_log_perm))?;
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &node_append, Tracked(&fake_log_perm))?;

            // 5. Add pending log entries to list
            self.pending_updates.push(tail_update);
            self.pending_updates.push(node_append);

            Ok(new_list_node_loc)
        }

        pub fn tentative_update_list_entry_at_index(
            &mut self,
            node_offset: u64,
            index_in_node: u64,
            new_entry: L,
            kvstore_id: u128,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L>>,
        ) -> (result: Result<(), KvError<K>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                // TODO
                // match result {
                //     Ok(()) => {
                //         let old_record = old(self)@.contents[item_offset as int];
                //         let new_record = self@.contents[item_offset as int];
                //         let list_index = new_record.list().node_offset_map[entry_offset as int];
                //         &&& list_index == old_record.list().node_offset_map[entry_offset as int]
                //         &&& new_record.list()[list_index as int] is Some
                //         &&& new_record.list()[list_index as int].unwrap() == new_entry
                //     }
                //     Err(_) => false // TODO
                // }
        {
            assume(false);
            
            // Log entry update involves writing to a live list element, so the actual updates are handled by playing the log forward.
            // This operation just creates the log entry and puts it in the tentative transaction
            
            // 1. Create the log entry
            let log_entry = OpLogEntryType::InsertListElement { node_offset, index_in_node, list_element: new_entry };

            // 2. Append the log entry to the log
            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &log_entry, Tracked(&fake_log_perm))?;

            // 3. Add the pending log entry to the list
            self.pending_updates.push(log_entry);

            Ok(())
        }

        pub fn tentative_trim_list(
            &mut self,
            metadata_index: u64,
            old_head: u64,
            new_head: u64,
            new_skip: u64, // TODO: who is in charge of figuring this out?
            trim_len: u64,
            kvstore_id: u128,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L>>,
        ) -> (result: Result<(), KvError<K>>)
            requires
                old(self).valid(),
                // TODO: caller needs to prove that the provided head will actually be the head
                // when trimming `trim_len` entries
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        let old_record = old(self)@.contents[metadata_index as int];
                        let new_record = self@.contents[metadata_index as int];
                        &&& new_record.list().list == old_record.list().list.subrange(trim_len as int, old_record.list().len() as int)
                        // offset map entries pointing to trimmed indices should have been removed from the view
                        &&& forall |i: int| 0 <= old_record.list().node_offset_map[i] < trim_len ==> {
                            new_record.list().offset_index(i) is None
                        }
                    }
                    Err(_) => false // TODO
                }
        {
            assume(false);

            // 1. Look up list metadata
            let (key, mut metadata) = self.metadata_table.get_key_and_metadata_entry_at_index(
                self.metadata_wrpm.get_pm_region_ref(), kvstore_id, metadata_index)?;

            if trim_len > metadata.length {
                return Err(KvError::IndexOutOfRange);
            }

            // 2. Update the metadata structure 
            metadata.head = new_head;
            metadata.length = metadata.length - trim_len;
            metadata.first_entry_offset = new_skip;
            
            // 3. Calculate the new CRC 
            let mut digest = CrcDigest::new();
            digest.write(&*metadata);
            digest.write(&*key);
            let new_crc = digest.sum64();

            // 4. Append the update to the log 
            let metadata_update = OpLogEntryType::UpdateMetadataEntry { metadata_index, new_crc, new_metadata: *metadata };
            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &metadata_update, Tracked(&fake_log_perm))?;

            // 5. Add the pending log entry to the list
            self.pending_updates.push(metadata_update);

            // We don't deallocate any nodes here, since nodes that will be trimmed off are in use until we commit
            // the transaction.
            // We'll use a special in-memory-only log entry enum variant to record the old and new heads and 
            // deallocate everything between them during log replay in commit. We don't log this information,
            // but that's ok, because after crash/restart we will replay the log and then rebuild the allocators,
            // which is equivalent to deallocating from the in-memory entry
            let node_dealloc = OpLogEntryType::NodeDeallocInMemory { old_head, new_head };
            self.pending_updates.push(node_dealloc);

            Ok(())
        }
        */
    }
        
}
