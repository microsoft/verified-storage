use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;
use crate::log2::inv_v::*;
use crate::{kv::layout_v::*, pmem::pmemspec_t::*, DurableKvStore};
use crate::kv::durable::oplog::oplogimpl_v::*;
use crate::kv::durable::maintablelayout_v::*;
use crate::kv::durable::itemtablelayout_v::*;
use crate::kv::durable::list_v::*;
use crate::kv::durable::recovery_v::*;
use crate::log2::{logimpl_v::*, layout_v::*};
use crate::kv::{kvspec_t::*, setup_v::*};
use crate::pmem::{pmemutil_v::*, pmcopy_t::*, wrpm_t::*};
use std::hash::Hash;

use super::oplog::logentry_v::PhysicalOpLogEntry;

verus! {

    pub open spec fn recovery_write_invariant<Perm, PM, K, I, L>(
        wrpm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        version_metadata: VersionMetadata,
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
        &&& UntrustedLogImpl::recover(wrpm_region@.durable_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat) is Some
        &&& forall |i: int| addr <= i < addr + bytes.len() ==> #[trigger] addr_modified_by_recovery(phys_log, i)
        &&& addr + bytes.len() <= overall_metadata.log_area_addr || overall_metadata.log_area_addr + overall_metadata.log_area_size <= addr
        &&& recovery_write_region_invariant::<Perm, PM, K, I, L>(wrpm_region, version_metadata, overall_metadata, phys_log)
    }

    pub open spec fn recovery_write_region_invariant<Perm, PM, K, I, L>(
        wrpm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        version_metadata: VersionMetadata,
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
        let abstract_op_log = UntrustedOpLog::<K, L>::recover(wrpm_region@.durable_state, version_metadata, overall_metadata);
        &&& wrpm_region.inv()
        &&& wrpm_region@.flush_predicted()
        &&& wrpm_region@.len() == overall_metadata.region_size
        &&& phys_log.len() > 0
        &&& UntrustedLogImpl::recover(wrpm_region@.durable_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat) is Some
        &&& DurableKvStore::<Perm, PM, K, I, L>::physical_recover(wrpm_region@.durable_state, version_metadata, overall_metadata) is Some
        &&& 0 <= overall_metadata.log_area_addr < overall_metadata.log_area_addr + overall_metadata.log_area_size <= overall_metadata.region_size
        &&& 0 < spec_log_header_area_size() <= spec_log_area_pos() < overall_metadata.log_area_size
        &&& abstract_op_log matches Some(abstract_op_log)
        &&& abstract_op_log.physical_op_list == phys_log
        &&& AbstractPhysicalOpLogEntry::log_inv(phys_log, version_metadata, overall_metadata)
    }

    pub proof fn lemma_safe_recovery_writes<Perm, PM, K, I, L>(
        wrpm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        version_metadata: VersionMetadata,
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
            recovery_write_invariant::<Perm, PM, K, I, L>(wrpm_region, version_metadata, overall_metadata, phys_log, addr, bytes)
        ensures
            ({
                // for all states s that this write may crash into, recovering s is equivalent
                // to recovering from the original state
                forall |s| can_result_from_partial_write(s, wrpm_region@.durable_state, addr, bytes) ==> {
                    &&& DurableKvStore::<Perm, PM, K, I, L>::physical_recover(s, version_metadata, overall_metadata) matches Some(crash_recover_state)
                    &&& crash_recover_state == DurableKvStore::<Perm, PM, K, I, L>::physical_recover(wrpm_region@.durable_state, version_metadata, overall_metadata).unwrap()
                }
            }),
            ({
                let new_wrpm_region = update_bytes(wrpm_region@.read_state, addr, bytes);
                &&& DurableKvStore::<Perm, PM, K, I, L>::physical_recover(new_wrpm_region, version_metadata, overall_metadata) is Some
                &&& DurableKvStore::<Perm, PM, K, I, L>::physical_recover(wrpm_region@.durable_state, version_metadata, overall_metadata).unwrap() == 
                        DurableKvStore::<Perm, PM, K, I, L>::physical_recover(new_wrpm_region, version_metadata, overall_metadata).unwrap()
            }),
            ({
                let new_wrpm_region = update_bytes(wrpm_region@.read_state, addr, bytes);
                let abstract_op_log = UntrustedOpLog::<K, L>::recover(new_wrpm_region, version_metadata, overall_metadata);
                &&& abstract_op_log matches Some(abstract_op_log)
                &&& abstract_op_log.physical_op_list == phys_log
                &&& AbstractPhysicalOpLogEntry::log_inv(phys_log, version_metadata, overall_metadata)
            }),
    {
        let new_wrpm_region_flushed = update_bytes(wrpm_region@.read_state, addr, bytes);

        let log_start_addr = overall_metadata.log_area_addr as nat;
        let log_size = overall_metadata.log_area_size as nat;
        let region_size = overall_metadata.region_size as nat;

        // The current pm state has the same log as the original pm state
        lemma_log_bytes_unchanged_during_recovery_write::<Perm, PM, K, I, L>(wrpm_region, version_metadata, overall_metadata, phys_log, addr, bytes);
        lemma_same_log_bytes_recover_to_same_state(wrpm_region@.durable_state, new_wrpm_region_flushed,
            overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat);

        // all crash states from this write recover to the same durable kvstore state
        lemma_crash_states_recover_to_same_state::<Perm, PM, K, I, L>(wrpm_region, version_metadata, overall_metadata, phys_log, addr, bytes);

        // We've just proven that all possible crash states recover to the desired state, and new_wrpm_region_flushed is a possible crash state,
        // so it also recovers to the desired state.
//        assert(new_wrpm_region.can_crash_as(new_wrpm_region_flushed.durable_state));
    }

    proof fn lemma_log_bytes_unchanged_during_recovery_write<Perm, PM, K, I, L>(
        wrpm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        version_metadata: VersionMetadata,
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
            recovery_write_invariant::<Perm, PM, K, I, L>(wrpm_region, version_metadata, overall_metadata, phys_log, addr, bytes)
        ensures
            ({
                let new_wrpm_region_flushed = update_bytes(wrpm_region@.read_state, addr, bytes);
                extract_bytes(wrpm_region@.durable_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat) == 
                    extract_bytes(new_wrpm_region_flushed, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
            })
    {
        let new_wrpm_region_flushed = update_bytes(wrpm_region@.read_state, addr, bytes);
        let log_start_addr = overall_metadata.log_area_addr as nat;
        let log_size = overall_metadata.log_area_size as nat;
        let region_size = overall_metadata.region_size as nat;

        // bytes that were not updated by the write remain the same
//        assert(new_wrpm_region.no_outstanding_writes_in_range(log_start_addr as int, (log_start_addr + log_size) as int));
        assert(forall |i: int| log_start_addr <= i < log_start_addr + log_size ==> 
            wrpm_region@.durable_state[i] == #[trigger] new_wrpm_region_flushed[i]);
    
        // Since the bytes cannot modify the log, the log's recovery state is unchanged by the write.
        assert(extract_bytes(wrpm_region@.durable_state, log_start_addr, log_size) =~= 
            extract_bytes(new_wrpm_region_flushed, log_start_addr, log_size));
    }

    proof fn lemma_crash_states_recover_to_same_state<Perm, PM, K, I, L>(
        wrpm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        version_metadata: VersionMetadata,
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
            recovery_write_invariant::<Perm, PM, K, I, L>(wrpm_region, version_metadata, overall_metadata, phys_log, addr, bytes)
        ensures 
            ({
                let new_wrpm_region = wrpm_region@.write(addr, bytes);
                forall |s| new_wrpm_region.can_crash_as(s) ==> {
                    &&& DurableKvStore::<Perm, PM, K, I, L>::physical_recover(s, version_metadata, overall_metadata) matches Some(crash_recover_state)
                    &&& crash_recover_state == DurableKvStore::<Perm, PM, K, I, L>::physical_recover(wrpm_region@.durable_state, version_metadata, overall_metadata).unwrap()
                }
            })
    {
        let new_wrpm_region = wrpm_region@.write(addr, bytes);
        let new_wrpm_region_flushed = new_wrpm_region.flush();

        let log_start_addr = overall_metadata.log_area_addr as nat;
        let log_size = overall_metadata.log_area_size as nat;
        let region_size = overall_metadata.region_size as nat;

        assert forall |s| new_wrpm_region.can_crash_as(s) implies {
            &&& DurableKvStore::<Perm, PM, K, I, L>::physical_recover(s, version_metadata, overall_metadata) matches Some(crash_recover_state)
            &&& crash_recover_state == DurableKvStore::<Perm, PM, K, I, L>::physical_recover(wrpm_region@.durable_state, version_metadata, overall_metadata).unwrap()
        } by {
            lemma_establish_extract_bytes_equivalence(wrpm_region@.durable_state, s);
            
            // 1. Prove that physical recovery on s succeeds
            // 2. Prove that it is equivalent to recovery on the original state

            // addrs in log region are unchanged by the write 
//            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(new_wrpm_region);
            assert(forall |i: int| log_start_addr <= i < log_start_addr + log_size ==> wrpm_region@.durable_state[i] == #[trigger] s[i]);
            // which means that the original log and s's log recover to the same state
            assert(extract_bytes(wrpm_region@.durable_state, log_start_addr, log_size) == extract_bytes(s, log_start_addr, log_size));
            let original_log = UntrustedOpLog::<K, L>::recover(wrpm_region@.durable_state, version_metadata, overall_metadata);
            let crashed_log = UntrustedOpLog::<K, L>::recover(s, version_metadata, overall_metadata);
            lemma_same_log_bytes_recover_to_same_state(wrpm_region@.durable_state, s, overall_metadata.log_area_addr as nat,
                overall_metadata.log_area_size as nat, overall_metadata.region_size as nat);
            assert(crashed_log is Some);
            assert(crashed_log == original_log);
            assert(original_log.unwrap().physical_op_list == phys_log);

            // applying the log entries obtained from the log succeeds
            // the only way this can fail is if one of the log entries is ill-formed, but we know that is not the case
            lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(s, version_metadata, overall_metadata, phys_log);
            
            assert(apply_physical_log_entries(s, phys_log) is Some);
            assert(apply_physical_log_entries(wrpm_region@.durable_state, phys_log) is Some);

            // Applying the log to both s and the original state result in the same sequence of bytes
            assert(apply_physical_log_entries(s, phys_log) == 
                apply_physical_log_entries(wrpm_region@.durable_state, phys_log)) 
            by {
                let mem = wrpm_region@.durable_state;
                let crash_replay = apply_physical_log_entries(s, phys_log);
                let reg_replay = apply_physical_log_entries(mem, phys_log);
                assert(crash_replay is Some);
                assert(reg_replay is Some);
                let crash_replay = crash_replay.unwrap();
                let reg_replay = reg_replay.unwrap();

                lemma_log_replay_preserves_size(mem, phys_log);
                lemma_log_replay_preserves_size(s, phys_log);

                assert(s.len() == mem.len());

                // the only bytes that differ between s and mem are ones that will be overwritten by recovery
                assert(forall |i: int| 0 <= i < s.len() && s[i] != mem[i] ==> addr_modified_by_recovery(phys_log, i));

                lemma_mem_equal_after_recovery(mem, s, version_metadata, overall_metadata, phys_log);
            }

            assert(DurableKvStore::<Perm, PM, K, I, L>::physical_recover(s, version_metadata, overall_metadata) is Some);
            // s can only differ from the original state in locations that are overwritten by recovery
            assert(forall |i: int| 0 <= i < s.len() && #[trigger] s[i] != #[trigger] wrpm_region@.durable_state[i] ==> #[trigger] addr_modified_by_recovery(phys_log, i));

            assert(DurableKvStore::<Perm, PM, K, I, L>::physical_recover(s, version_metadata, overall_metadata).unwrap() == 
                DurableKvStore::<Perm, PM, K, I, L>::physical_recover(wrpm_region@.durable_state, version_metadata, overall_metadata).unwrap());
        }
    }

    pub proof fn lemma_physical_recover_succeeds_implies_component_parse_succeeds<Perm, PM, K, I, L>(
        mem: Seq<u8>,
        version_metadata: VersionMetadata,
        overall_metadata: OverallMetadata,
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
        requires
            DurableKvStore::<Perm, PM, K, I, L>::physical_recover(mem, version_metadata, overall_metadata) is Some, 
        ensures 
            ({
                let recovered_log = UntrustedOpLog::<K, L>::recover(mem, version_metadata, overall_metadata).unwrap();
                let physical_log_entries = recovered_log.physical_op_list;
                let mem_with_log_installed = apply_physical_log_entries(mem, physical_log_entries).unwrap();
                let main_table_region = extract_bytes(mem_with_log_installed, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let item_table_region = extract_bytes(mem_with_log_installed, overall_metadata.item_table_addr as nat, overall_metadata.item_table_size as nat);
                let list_area_region = extract_bytes(mem_with_log_installed, overall_metadata.list_area_addr as nat, overall_metadata.list_area_size as nat);
                &&& parse_main_table::<K>(
                        main_table_region, 
                        overall_metadata.num_keys,
                        overall_metadata.main_table_entry_size
                    ) matches Some(main_table)
                &&& parse_item_table::<I, K>(
                        item_table_region,
                        overall_metadata.num_keys as nat,
                        main_table.valid_item_indices()
                    ) is Some
              /* REMOVED UNTIL WE IMPLEMENT LISTS
                &&& DurableList::<K, L>::parse_all_lists(
                    main_table,
                    list_area_region,
                    overall_metadata.list_node_size,
                    overall_metadata.num_list_entries_per_node
                ) is Some
              */
            })
    {}
    
    pub open spec fn no_outstanding_writes_to_version_metadata(
        pm_region: PersistentMemoryRegionView,
    ) -> bool 
    {
        &&& pm_region.no_outstanding_writes_in_range(0, VersionMetadata::spec_size_of() as int)
        &&& pm_region.no_outstanding_writes_in_range(VersionMetadata::spec_size_of() as int, (VersionMetadata::spec_size_of() + u64::spec_size_of()) as int)
    }

    pub open spec fn no_outstanding_writes_to_overall_metadata(
        pm_region: PersistentMemoryRegionView,
        overall_metadata_addr: int,
    ) -> bool 
    {
        &&& pm_region.no_outstanding_writes_in_range(overall_metadata_addr, overall_metadata_addr + OverallMetadata::spec_size_of() as int)
        &&& pm_region.no_outstanding_writes_in_range(overall_metadata_addr + OverallMetadata::spec_size_of() as int, (overall_metadata_addr + OverallMetadata::spec_size_of() + u64::spec_size_of()) as int)
    }

    pub open spec fn version_and_overall_metadata_match<K, L>(
        mem1: Seq<u8>,
        mem2: Seq<u8>,
        overall_metadata_addr: nat
    ) -> bool
    {
        &&& extract_bytes(mem1, 0, VersionMetadata::spec_size_of() + u64::spec_size_of()) == 
                extract_bytes(mem2, 0, VersionMetadata::spec_size_of()+ u64::spec_size_of())
        &&& extract_bytes(mem1, overall_metadata_addr, OverallMetadata::spec_size_of() + u64::spec_size_of()) == 
                extract_bytes(mem2, overall_metadata_addr, OverallMetadata::spec_size_of() + u64::spec_size_of())
    }

    pub open spec fn version_and_overall_metadata_match_deserialized(
        mem1: Seq<u8>,
        mem2: Seq<u8>,
    ) -> bool
    {
        let version_metadata1 = deserialize_version_metadata(mem1);
        let version_crc1 = deserialize_version_crc(mem1);
        let version_metadata2 = deserialize_version_metadata(mem2);
        let version_crc2 = deserialize_version_crc(mem2);
        let overall_metadata1 = deserialize_overall_metadata(mem1, version_metadata1.overall_metadata_addr);
        let overall_crc1 = deserialize_overall_crc(mem1, version_metadata1.overall_metadata_addr);
        let overall_metadata2 = deserialize_overall_metadata(mem2, version_metadata2.overall_metadata_addr);
        let overall_crc2 = deserialize_overall_crc(mem2, version_metadata2.overall_metadata_addr);

        &&& version_metadata1 == version_metadata2 
        &&& version_crc1 == version_crc2 
        &&& overall_metadata1 == overall_metadata2 
        &&& overall_crc1 == overall_crc2
    }

    // TODO: remove the generics and only require the parts of overall_metadata_valid in the 
    // precondition that are necessary to prove the lemma 
    pub proof fn lemma_non_log_components_match_when_states_differ_only_in_log_region<K, I, L>(
        s1: Seq<u8>,
        s2: Seq<u8>,
        version_metadata: VersionMetadata,
        overall_metadata: OverallMetadata,
    )
        where 
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
        requires 
            states_differ_only_in_log_region(s1, s2, overall_metadata.log_area_addr as nat,
                overall_metadata.log_area_size as nat),
            s1.len() == s2.len(),
            overall_metadata.list_area_addr + overall_metadata.list_area_size <= s1.len(),
            overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr, overall_metadata.kvstore_id),
        ensures 
            extracted_regions_match(s1, s2, overall_metadata),
            deserialize_version_metadata(s1) == deserialize_version_metadata(s2),
            deserialize_overall_metadata(s1, version_metadata.overall_metadata_addr) == 
                deserialize_overall_metadata(s2, version_metadata.overall_metadata_addr)
    {
        lemma_establish_extract_bytes_equivalence(s1, s2);
    }

    pub open spec fn extracted_regions_match(
        s1: Seq<u8>,
        s2: Seq<u8>,
        overall_metadata: OverallMetadata, 
    ) -> bool 
    {
        let main_table_region1 = extract_bytes(s1, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
        let item_table_region1 = extract_bytes(s1, overall_metadata.item_table_addr as nat, overall_metadata.item_table_size as nat);
        let list_area_region1 = extract_bytes(s1, overall_metadata.list_area_addr as nat, overall_metadata.list_area_size as nat);

        let main_table_region2 = extract_bytes(s2, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
        let item_table_region2 = extract_bytes(s2, overall_metadata.item_table_addr as nat, overall_metadata.item_table_size as nat);
        let list_area_region2 = extract_bytes(s2, overall_metadata.list_area_addr as nat, overall_metadata.list_area_size as nat);
    
        &&& main_table_region1 == main_table_region2
        &&& item_table_region1 == item_table_region2
        &&& list_area_region1 == list_area_region2
    }

    // TODO: combine this with the log-specific one
    pub proof fn lemma_crash_state_differing_only_in_log_region_exists2(
        v1: PersistentMemoryRegionView,
        v2: PersistentMemoryRegionView,
        version_metadata: VersionMetadata,
        overall_metadata: OverallMetadata,
    )
        requires 
            views_differ_only_in_log_region(v1, v2, 
                overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat),
            v1.len() == v2.len(),
            v1.len() == overall_metadata.region_size,
            v1.len() >= version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of(),
            version_metadata.overall_metadata_addr >= VersionMetadata::spec_size_of(),
            forall|s| #[trigger] v1.can_crash_as(s) ==> version_metadata == deserialize_version_metadata(s),
            forall|s| #[trigger] v1.can_crash_as(s) ==>
                overall_metadata == deserialize_overall_metadata(s, version_metadata.overall_metadata_addr),
            forall|addr: int| 0 <= addr < VersionMetadata::spec_size_of() ==> v1.state[addr] == v2.state[addr],
            forall|addr: int| version_metadata.overall_metadata_addr <= addr
                        < version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() ==>
                v1.state[addr] == v2.state[addr],
            overall_metadata.log_area_addr as int % const_persistence_chunk_size() == 0,
            overall_metadata.log_area_size as int % const_persistence_chunk_size() == 0,
        ensures
            forall |s2: Seq<u8>| v2.can_crash_as(s2) ==> 
                exists |s1: Seq<u8>| {
                    &&& v1.can_crash_as(s1)
                    &&& #[trigger] s1.len() == s2.len()
                    &&& states_differ_only_in_log_region(s1, s2, 
                            overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
                }
    {
        let log_start_addr = overall_metadata.log_area_addr as nat;
        let log_size = overall_metadata.log_area_size as nat;

        lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(v1, v2,
            version_metadata, overall_metadata);

        assert forall |s2: Seq<u8>| v2.can_crash_as(s2) implies 
            exists |s1: Seq<u8>| {
                &&& v1.can_crash_as(s1)
                &&& #[trigger] s1.len() == s2.len()
                &&& states_differ_only_in_log_region(s1, s2, log_start_addr, log_size)
            }
        by {
            // We need to construct a state that is a valid crash state of v1, and matches
            // s2 in all addresses except for the log addrs.
            // It doesn't really matter what we put in the log, so we'll just use 
            // the post-flush byte for each of those addresses.
            // The rest of this proof is focused on proving that v1 can in fact
            // crash into this witness state.
            let witness = Seq::new(v1.len(), |addr: int| {
                if log_start_addr <= addr < log_start_addr + log_size {
                    v1.state[addr].flush_byte()
                } else {
                    // outside of the log
                    s2[addr]
                }
            });

            // Then we have to prove that this witness is, in fact, a crash state of v1. This is not trivial
            // because we defined the witness in terms of bytes, but crash states are reasoned about in 
            // terms of 8-byte chunks.
            assert(v1.can_crash_as(witness)) by {
                // We'll prove that the chunks outside of the log and the chunks inside the log are valid
                // separately.
                
                // First, prove that the bytes outside the log represent a valid crash state for v1
                assert forall |chunk: int| {
                    ||| 0 <= chunk * const_persistence_chunk_size() < log_start_addr 
                    ||| log_start_addr + log_size <= chunk * const_persistence_chunk_size() < v1.len()
                } implies {
                    ||| v1.chunk_corresponds_ignoring_outstanding_writes(chunk, witness)
                    ||| v1.chunk_corresponds_after_flush(chunk, witness)
                } by {
                    // From definition of `can_crash_as`. We already know this, but asserting it 
                    // here helps Verus with triggers.
                    assert({
                        ||| v2.chunk_corresponds_after_flush(chunk, s2)
                        ||| v2.chunk_corresponds_ignoring_outstanding_writes(chunk, s2)
                    });

                    // Either all addrs for this chunk are flushed or they are all not. 
                    // This comes from the definitions of chunk_corresponds_{after_flush, ignoring_outstanding_writes}
                    assert({
                        ||| forall |addr: int| {
                                &&& 0 <= addr < v1.len()
                                &&& addr_in_chunk(chunk, addr)
                            } ==> #[trigger] s2[addr] == v2.state[addr].flush_byte()
                        ||| forall |addr: int| {
                                &&& 0 <= addr < v1.len()
                                &&& addr_in_chunk(chunk, addr)
                            } ==> #[trigger] s2[addr] == v2.state[addr].state_at_last_flush
                    });

                    // Finally, we have to establish that the addresses in this chunk
                    // correspond to addresses that we already know something about,
                    // which just requires making Verus do some arithmetic.
                    assert forall |addr: int| {
                        &&& 0 <= addr < v1.len()
                        &&& addr_in_chunk(chunk, addr)
                    } implies #[trigger] witness[addr] == s2[addr] by {    
                        lemma_fundamental_div_mod(log_start_addr as int, const_persistence_chunk_size());
                        lemma_fundamental_div_mod(log_size as int, const_persistence_chunk_size());
                    }
                }

                // Second, prove that the bytes inside the log are also part of a valid crash state.
                // This one is slightly simpler because there is only one valid state for each chunk.
                // We just have to do the arithmetic to prove that these bytes corresond to locations that 
                // we know have been set to v1's flushed bytes
                assert forall |chunk: int| {
                    0 <= log_start_addr <= chunk * const_persistence_chunk_size() < log_start_addr + log_size < v1.len()
                } implies {
                    v1.chunk_corresponds_after_flush(chunk, witness)
                } by {
                    assert forall |addr: int| {
                        &&& 0 <= addr < v1.len()
                        &&& addr_in_chunk(chunk, addr)
                    } implies #[trigger] witness[addr] == v1.state[addr].flush_byte() by {
                        lemma_fundamental_div_mod(log_start_addr as int, const_persistence_chunk_size());
                        lemma_fundamental_div_mod(log_size as int, const_persistence_chunk_size());
                    }
                }
            }
        }
    }

    pub proof fn lemma_writing_does_not_change_committed_view(
        pm: PersistentMemoryRegionView,
        addr: int,
        bytes: Seq<u8>,
    )
        requires 
            0 <= addr <= addr + bytes.len() <= pm.len(),
            // pm.no_outstanding_writes_in_range(addr, addr + bytes.len())
        ensures 
            ({
                let new_pm = pm.write(addr, bytes);
                pm.durable_state == new_pm.durable_state
            })
    {
        let new_pm = pm.write(addr, bytes);
        assert(forall |i: int| 0 <= i < pm.len() ==>
            new_pm.state[i].state_at_last_flush == #[trigger] pm.state[i].state_at_last_flush);
        assert(forall |i: int| 0 <= i < new_pm.len() ==>
            #[trigger] new_pm.state[i].state_at_last_flush == new_pm.durable_state[i]);
        assert(forall |i: int| 0 <= i < pm.len() ==>
            #[trigger] pm.state[i].state_at_last_flush == pm.durable_state[i]);
        assert(pm.durable_state == new_pm.durable_state);
    }
}
