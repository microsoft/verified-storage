use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::log2::inv_v::lemma_same_bytes_recover_to_same_state;
use crate::{kv::layout_v::OverallMetadata, pmem::pmemspec_t::*, DurableKvStore};
use crate::kv::durable::oplog::oplogspec_t::*;
use crate::kv::durable::oplog::oplogimpl_v::*;
use crate::kv::durable::metadata::layout_v::*;
use crate::kv::durable::itemtable::layout_v::*;
use crate::kv::durable::durablelist::durablelistimpl_v::*;
use crate::log2::{logimpl_v::*, layout_v::*};
use crate::kv::kvspec_t::*;
use crate::pmem::{pmemutil_v::*, pmcopy_t::*, wrpm_t::*};
use std::hash::Hash;

use super::oplog::logentry_v::PhysicalOpLogEntry;

verus! {
    // This lemma proves that an index that is less than num_keys (i.e., within bounds of the table) 
    // represents a valid table entry that we can read and parse.
    pub proof fn lemma_valid_entry_index(index: nat, num_keys: nat, size: nat)
        requires
            index < num_keys
        ensures 
            (index + 1) * size == index * size + size <= num_keys * size
    {
        vstd::arithmetic::mul::lemma_mul_inequality(index + 1 as int, num_keys as int, size as int);
        vstd::arithmetic::mul::lemma_mul_basics(size as int);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(size as int,
                                                                        index as int, 1);
    }

    // This lemma proves that a subrange of a subrange is equal to just obtaining the final subrange using its 
    // absolute start index. This is obvious and requires no body, but having a dedicated lemma helps
    // Z3 establish the equality
    // TODO: do this about subranges rather than extract_bytes -- should be equivalent and more useful
    pub proof fn lemma_subrange_of_extract_bytes_equal(mem: Seq<u8>, start1: nat, start2: nat, len1: nat, len2: nat)
        requires 
            start1 <= start2 <= start2 + len2 <= start1 + len1 <= mem.len()
        ensures 
            ({
                let start_offset = start2 - start1;
                extract_bytes(extract_bytes(mem, start1, len1), start_offset as nat, len2) =~= 
                    extract_bytes(mem, start2, len2)
            })
    {}

    pub open spec fn addr_modified_by_recovery(
        log: Seq<AbstractPhysicalOpLogEntry>,
        addr: int,
    ) -> bool
    {
        exists |j: int| 0 <= j < log.len() &&
            (#[trigger] log[j]).absolute_addr <= addr < log[j].absolute_addr + log[j].bytes.len()
    }

    pub open spec fn recovery_write_invariant<PM, K, I, L, Perm>(
        wrpm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        overall_metadata: OverallMetadata,
        phys_log: Seq<AbstractPhysicalOpLogEntry>,
        addr: int,
        bytes: Seq<u8>
    ) -> bool 
        where 
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
            Perm: CheckPermission<Seq<u8>>,
    {
        &&& 0 <= addr < addr + bytes.len() <= wrpm_region@.len()
        &&& UntrustedLogImpl::recover(wrpm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat) is Some
        &&& forall |i: int| addr <= i < addr + bytes.len() ==> #[trigger] addr_modified_by_recovery(phys_log, i)
        &&& addr + bytes.len() <= overall_metadata.log_area_addr || overall_metadata.log_area_addr + overall_metadata.log_area_size <= addr
        &&& recovery_write_region_invariant::<PM, K, I, L, Perm>(wrpm_region, overall_metadata, phys_log)
    }

    pub open spec fn recovery_write_region_invariant<PM, K, I, L, Perm>(
        wrpm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        overall_metadata: OverallMetadata,
        phys_log: Seq<AbstractPhysicalOpLogEntry>,
    ) -> bool 
        where 
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
            Perm: CheckPermission<Seq<u8>>,
    {
        let abstract_op_log = UntrustedOpLog::<K, L>::recover(wrpm_region@.committed(), overall_metadata);
        &&& wrpm_region.inv()
        &&& wrpm_region@.no_outstanding_writes()
        &&& wrpm_region@.len() == overall_metadata.region_size
        &&& phys_log.len() > 0
        &&& UntrustedLogImpl::recover(wrpm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat) is Some
        &&& DurableKvStore::<PM, K, I, L>::physical_recover(wrpm_region@.committed(), overall_metadata) is Some
        &&& 0 <= overall_metadata.log_area_addr < overall_metadata.log_area_addr + overall_metadata.log_area_size < overall_metadata.region_size
        &&& 0 < spec_log_header_area_size() <= spec_log_area_pos() < overall_metadata.log_area_size
        &&& abstract_op_log matches Some(abstract_op_log)
        &&& abstract_op_log.physical_op_list == phys_log
        &&& AbstractPhysicalOpLogEntry::log_inv(phys_log, overall_metadata)
    }

    pub proof fn lemma_safe_recovery_writes<PM, K, I, L, Perm>(
        wrpm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        overall_metadata: OverallMetadata,
        phys_log: Seq<AbstractPhysicalOpLogEntry>,
        addr: int,
        bytes: Seq<u8>
    )
        where 
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
            Perm: CheckPermission<Seq<u8>>,
        requires
            recovery_write_invariant::<PM, K, I, L, Perm>(wrpm_region, overall_metadata, phys_log, addr, bytes)
        ensures
            ({
                // for all states s that this write may crash into, recovering s is equivalent
                // to recovering from the original state
                forall |s| wrpm_region@.write(addr, bytes).can_crash_as(s) ==> {
                    &&& DurableKvStore::<PM, K, I, L>::physical_recover(s, overall_metadata) matches Some(crash_recover_state)
                    &&& crash_recover_state == DurableKvStore::<PM, K, I, L>::physical_recover(wrpm_region@.committed(), overall_metadata).unwrap()
                }
            }),
            ({
                let new_wrpm_region = wrpm_region@.write(addr, bytes).flush();
                &&& DurableKvStore::<PM, K, I, L>::physical_recover(new_wrpm_region.committed(), overall_metadata) is Some
                &&& DurableKvStore::<PM, K, I, L>::physical_recover(wrpm_region@.committed(), overall_metadata).unwrap() == 
                        DurableKvStore::<PM, K, I, L>::physical_recover(new_wrpm_region.committed(), overall_metadata).unwrap()
            }),
            ({
                let new_wrpm_region = wrpm_region@.write(addr, bytes).flush();
                let abstract_op_log = UntrustedOpLog::<K, L>::recover(new_wrpm_region.committed(), overall_metadata);
                &&& abstract_op_log matches Some(abstract_op_log)
                &&& abstract_op_log.physical_op_list == phys_log
                &&& AbstractPhysicalOpLogEntry::log_inv(phys_log, overall_metadata)
            }),
    {
        let new_wrpm_region = wrpm_region@.write(addr, bytes);
        let new_wrpm_region_flushed = new_wrpm_region.flush();

        let log_start_addr = overall_metadata.log_area_addr as nat;
        let log_size = overall_metadata.log_area_size as nat;
        let region_size = overall_metadata.region_size as nat;

        // The current pm state has the same log as the original pm state
        lemma_log_bytes_unchanged_during_recovery_write::<PM, K, I, L, Perm>(wrpm_region, overall_metadata, phys_log, addr, bytes);
        lemma_same_bytes_recover_to_same_state(wrpm_region@.committed(), new_wrpm_region_flushed.committed(), overall_metadata);

        // all crash states from this write recover to the same durable kvstore state
        lemma_crash_states_recover_to_same_state::<PM, K, I, L, Perm>(wrpm_region, overall_metadata, phys_log, addr, bytes);

        // We've just proven that all possible crash states recover to the desired state, and new_wrpm_region_flushed is a possible crash state,
        // so it also recovers to the desired state.
        assert(new_wrpm_region.can_crash_as(new_wrpm_region_flushed.committed()));
    }

    proof fn lemma_log_bytes_unchanged_during_recovery_write<PM, K, I, L, Perm>(
        wrpm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        overall_metadata: OverallMetadata,
        phys_log: Seq<AbstractPhysicalOpLogEntry>,
        addr: int,
        bytes: Seq<u8>
    )
        where 
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
            Perm: CheckPermission<Seq<u8>>,
        requires
            recovery_write_invariant::<PM, K, I, L, Perm>(wrpm_region, overall_metadata, phys_log, addr, bytes)
        ensures
            ({
                let new_wrpm_region = wrpm_region@.write(addr, bytes);
                let new_wrpm_region_flushed = new_wrpm_region.flush();
                extract_bytes(wrpm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat) == 
                    extract_bytes(new_wrpm_region_flushed.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
            })
    {
        let new_wrpm_region = wrpm_region@.write(addr, bytes);
        let new_wrpm_region_flushed = new_wrpm_region.flush();
        let log_start_addr = overall_metadata.log_area_addr as nat;
        let log_size = overall_metadata.log_area_size as nat;
        let region_size = overall_metadata.region_size as nat;

        // bytes that were not updated by the write remain the same
        assert(new_wrpm_region.no_outstanding_writes_in_range(log_start_addr as int, (log_start_addr + log_size) as int));
        assert(forall |i: int| log_start_addr <= i < log_start_addr + log_size ==> 
            wrpm_region@.committed()[i] == #[trigger] new_wrpm_region_flushed.committed()[i]);
    
        // Since the bytes cannot modify the log, the log's recovery state is unchanged by the write.
        assert(extract_bytes(wrpm_region@.committed(), log_start_addr, log_size) =~= 
            extract_bytes(new_wrpm_region_flushed.committed(), log_start_addr, log_size));
    }

    proof fn lemma_crash_states_recover_to_same_state<PM, K, I, L, Perm>(
        wrpm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        overall_metadata: OverallMetadata,
        phys_log: Seq<AbstractPhysicalOpLogEntry>,
        addr: int,
        bytes: Seq<u8>
    )
        where 
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
            Perm: CheckPermission<Seq<u8>>,
        requires
            recovery_write_invariant::<PM, K, I, L, Perm>(wrpm_region, overall_metadata, phys_log, addr, bytes)
        ensures 
            ({
                let new_wrpm_region = wrpm_region@.write(addr, bytes);
                forall |s| new_wrpm_region.can_crash_as(s) ==> {
                    &&& DurableKvStore::<PM, K, I, L>::physical_recover(s, overall_metadata) matches Some(crash_recover_state)
                    &&& crash_recover_state == DurableKvStore::<PM, K, I, L>::physical_recover(wrpm_region@.committed(), overall_metadata).unwrap()
                }
            })
    {
        let new_wrpm_region = wrpm_region@.write(addr, bytes);
        let new_wrpm_region_flushed = new_wrpm_region.flush();

        let log_start_addr = overall_metadata.log_area_addr as nat;
        let log_size = overall_metadata.log_area_size as nat;
        let region_size = overall_metadata.region_size as nat;

        assert forall |s| new_wrpm_region.can_crash_as(s) implies {
            &&& DurableKvStore::<PM, K, I, L>::physical_recover(s, overall_metadata) matches Some(crash_recover_state)
            &&& crash_recover_state == DurableKvStore::<PM, K, I, L>::physical_recover(wrpm_region@.committed(), overall_metadata).unwrap()
        } by {
            lemma_establish_extract_bytes_equivalence(wrpm_region@.committed(), s);
            
            // 1. Prove that physical recovery on s succeeds
            // 2. Prove that it is equivalent to recovery on the original state

            // addrs in log region are unchanged by the write 
            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(new_wrpm_region);
            assert(forall |i: int| log_start_addr <= i < log_start_addr + log_size ==> wrpm_region@.committed()[i] == #[trigger] s[i]);
            // which means that the original log and s's log recover to the same state
            assert(extract_bytes(wrpm_region@.committed(), log_start_addr, log_size) == extract_bytes(s, log_start_addr, log_size));
            let original_log = UntrustedOpLog::<K, L>::recover(wrpm_region@.committed(), overall_metadata);
            let crashed_log = UntrustedOpLog::<K, L>::recover(s, overall_metadata);
            lemma_same_bytes_recover_to_same_state(wrpm_region@.committed(), s, overall_metadata);
            assert(crashed_log is Some);
            assert(crashed_log == original_log);
            assert(original_log.unwrap().physical_op_list == phys_log);

            // applying the log entries obtained from the log succeeds
            // the only way this can fail is if one of the log entries is ill-formed, but we know that is not the case
            DurableKvStore::<PM, K, I, L>::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(s, overall_metadata, phys_log);
            
            assert(DurableKvStore::<PM, K, I, L>::apply_physical_log_entries(s, phys_log) is Some);
            assert(DurableKvStore::<PM, K, I, L>::apply_physical_log_entries(wrpm_region@.committed(), phys_log) is Some);

            // Applying the log to both s and the original state result in the same sequence of bytes
            assert(DurableKvStore::<PM, K, I, L>::apply_physical_log_entries(s, phys_log) == 
                DurableKvStore::<PM, K, I, L>::apply_physical_log_entries(wrpm_region@.committed(), phys_log)) 
            by {
                let mem = wrpm_region@.committed();
                let crash_replay = DurableKvStore::<PM, K, I, L>::apply_physical_log_entries(s, phys_log);
                let reg_replay = DurableKvStore::<PM, K, I, L>::apply_physical_log_entries(mem, phys_log);
                assert(crash_replay is Some);
                assert(reg_replay is Some);
                let crash_replay = crash_replay.unwrap();
                let reg_replay = reg_replay.unwrap();

                DurableKvStore::<PM, K, I, L>::lemma_log_replay_preserves_size(mem, phys_log);
                DurableKvStore::<PM, K, I, L>::lemma_log_replay_preserves_size(s, phys_log);

                assert(s.len() == mem.len());

                // the only bytes that differ between s and mem are ones that will be overwritten by recovery
                assert(forall |i: int| 0 <= i < s.len() && s[i] != mem[i] ==> addr_modified_by_recovery(phys_log, i));

                DurableKvStore::<PM, K, I, L>::lemma_mem_equal_after_recovery(mem, s, overall_metadata, phys_log);
            }

            assert(DurableKvStore::<PM, K, I, L>::physical_recover(s, overall_metadata) is Some);
            // s can only differ from the original state in locations that are overwritten by recovery
            assert(forall |i: int| 0 <= i < s.len() && #[trigger] s[i] != #[trigger] wrpm_region@.committed()[i] ==> #[trigger] addr_modified_by_recovery(phys_log, i));

            assert(DurableKvStore::<PM, K, I, L>::physical_recover(s, overall_metadata).unwrap() == DurableKvStore::<PM, K, I, L>::physical_recover(wrpm_region@.committed(), overall_metadata).unwrap());
        }
    }

    pub proof fn lemma_physical_recover_succeeds_implies_component_parse_succeeds<PM, K, I, L>(
        mem: Seq<u8>,
        overall_metadata: OverallMetadata,
    )
        where
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
        requires
            DurableKvStore::<PM, K, I, L>::physical_recover(mem, overall_metadata) is Some, 
        ensures 
            ({
                let recovered_log = UntrustedOpLog::<K, L>::recover(mem, overall_metadata).unwrap();
                let physical_log_entries = recovered_log.physical_op_list;
                let mem_with_log_installed = DurableKvStore::<PM, K, I, L>::apply_physical_log_entries(mem, physical_log_entries).unwrap();
                let main_table_region = extract_bytes(mem_with_log_installed, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let item_table_region = extract_bytes(mem_with_log_installed, overall_metadata.item_table_addr as nat, overall_metadata.item_table_size as nat);
                let list_area_region = extract_bytes(mem_with_log_installed, overall_metadata.list_area_addr as nat, overall_metadata.list_area_size as nat);
                &&& parse_metadata_table::<K>(
                        main_table_region, 
                        overall_metadata.num_keys,
                        overall_metadata.metadata_node_size
                    ) matches Some(main_table)
                &&& parse_item_table::<I, K>(
                        item_table_region,
                        overall_metadata.num_keys as nat,
                        main_table.valid_item_indices()
                    ) is Some
                &&& DurableList::<K, L>::parse_all_lists(
                    main_table,
                    list_area_region,
                    overall_metadata.list_node_size,
                    overall_metadata.num_list_entries_per_node
                ) is Some
            })

    {}
            
}