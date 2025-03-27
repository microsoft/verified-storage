use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::size_of;
use crate::pmem::wrpm_t::*;
use crate::common::align_v::*;
use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use super::entry_v::*;
use super::impl_v::*;
use super::inv_v::*;
use super::recover_v::*;
use super::spec_v::*;
use vstd::bytes::u64_from_le_bytes;
use vstd::slice::slice_subrange;

verus! {

impl <Perm, PM> Journal<Perm, PM>
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
{
    exec fn read_version_metadata(pm: &PM) -> (result: Option<JournalVersionMetadata>)
        requires
            pm.inv(),
            recover_version_metadata(pm@.read_state).is_some(),
            pm@.len() <= u64::MAX,
        ensures
            match result {
                None => !pm.constants().impervious_to_corruption(),
                Some(vm) => recover_version_metadata(pm@.read_state) == Some(vm),
            }
    {
        let journal_version_metadata_end = size_of::<JournalVersionMetadata>() as u64;
        let journal_version_metadata_crc_addr = exec_round_up_to_alignment::<u64>(journal_version_metadata_end);
    
        assert(spec_journal_version_metadata_start() == 0);
        exec_recover_object(pm, 0, journal_version_metadata_crc_addr)
    }
    
    exec fn read_static_metadata(pm: &PM, vm: &JournalVersionMetadata) -> (result: Option<JournalStaticMetadata>)
        requires
            pm.inv(),
            validate_version_metadata(*vm),
            recover_static_metadata(pm@.read_state, *vm).is_some(),
            pm@.len() <= u64::MAX,
        ensures
            match result {
                None => !pm.constants().impervious_to_corruption(),
                Some(sm) => recover_static_metadata(pm@.read_state, *vm) == Some(sm),
            }
    {
        if vm.version_number != 1 {
            assert(false);
            return None;
        }
    
        if vm.program_guid != JOURNAL_PROGRAM_GUID {
            assert(false);
            return None;
        }
    
        let journal_version_metadata_end = size_of::<JournalVersionMetadata>() as u64;
        let journal_version_metadata_crc_addr = exec_round_up_to_alignment::<u64>(journal_version_metadata_end);
        assert(journal_version_metadata_crc_addr == spec_journal_version_metadata_crc_start());
        let journal_version_metadata_crc_end = journal_version_metadata_crc_addr + size_of::<u64>() as u64;
        assert(journal_version_metadata_crc_end == spec_journal_version_metadata_crc_end());
        let journal_static_metadata_start =
            exec_round_up_to_alignment::<JournalStaticMetadata>(journal_version_metadata_crc_end);
        assert(journal_static_metadata_start == spec_journal_static_metadata_start());
        let journal_static_metadata_end = journal_static_metadata_start + size_of::<JournalStaticMetadata>() as u64;
        assert(journal_static_metadata_end == spec_journal_static_metadata_end());
        let journal_static_metadata_crc_start = exec_round_up_to_alignment::<u64>(journal_static_metadata_end);
        assert(journal_static_metadata_crc_start == spec_journal_static_metadata_crc_start());
    
        exec_recover_object(pm, journal_static_metadata_start, journal_static_metadata_crc_start)
    }
    
    exec fn read_committed_cdb(pm: &PM, vm: &JournalVersionMetadata, sm: &JournalStaticMetadata)
                               -> (result: Option<bool>)
        requires
            pm.inv(),
            pm@.len() <= u64::MAX,
            recover_committed_cdb(pm@.read_state, *sm).is_some(),
            validate_metadata(*vm, *sm, pm@.len()),
        ensures
            match result {
                None => !pm.constants().impervious_to_corruption(),
                Some(b) => recover_committed_cdb(pm@.read_state, *sm) == Some(b),
            }
    {
        exec_recover_cdb(pm, sm.committed_cdb_start)
    }
    
    exec fn read_journal_length(
        pm: &PM,
        Ghost(vm): Ghost<JournalVersionMetadata>,
        sm: &JournalStaticMetadata
    ) -> (result: Option<u64>)
        requires
            pm.inv(),
            recover_journal_length(pm@.read_state, *sm).is_some(),
            validate_metadata(vm, *sm, pm@.len()),
            pm@.len() <= u64::MAX,
        ensures
            match result {
                None => !pm.constants().impervious_to_corruption(),
                Some(journal_length) => recover_journal_length(pm@.read_state, *sm) == Some(journal_length),
            }
    {
        exec_recover_object(pm, sm.journal_length_start, sm.journal_length_crc_start)
    }
    
    exec fn read_journal_entries_bytes(
        pm: &PM,
        Ghost(vm): Ghost<JournalVersionMetadata>,
        sm: &JournalStaticMetadata,
        journal_length: u64,
    ) -> (result: Option<Vec<u8>>)
        requires
            pm.inv(),
            validate_metadata(vm, *sm, pm@.len()),
            recover_journal_length(pm@.read_state, *sm) == Some(journal_length),
            recover_journal_entries_bytes(pm@.read_state, *sm, journal_length) is Some,
            pm@.len() <= u64::MAX,
        ensures
            match result {
                None => !pm.constants().impervious_to_corruption(),
                Some(b) => {
                    &&& recover_journal_entries_bytes(pm@.read_state, *sm, journal_length) == Some(b@)
                    &&& b.len() == journal_length
                },
            }
    {
        exec_recover_bytes(pm, sm.journal_entries_start, journal_length, sm.journal_entries_crc_start)
    }
    
    exec fn install_journal_entry_during_start(
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        Tracked(perm): Tracked<&Perm>,
        Ghost(vm): Ghost<JournalVersionMetadata>,
        sm: &JournalStaticMetadata,
        start: usize,
        write_addr: u64,
        bytes_to_write: &[u8],
        Ghost(entries_bytes): Ghost<Seq<u8>>,
        Ghost(num_entries_installed): Ghost<int>,
        Ghost(entries): Ghost<Seq<JournalEntry>>,
        Ghost(commit_state): Ghost<Seq<u8>>,
    )
        requires
            old(wrpm).inv(),
            old(wrpm)@.valid(),
            0 <= sm.app_area_end <= old(wrpm)@.len(),
            recover_version_metadata(old(wrpm)@.durable_state) == Some(vm),
            recover_static_metadata(old(wrpm)@.durable_state, vm) == Some(*sm),
            recover_committed_cdb(old(wrpm)@.durable_state, *sm) == Some(true),
            recover_journal_length(old(wrpm)@.durable_state, *sm) == Some(entries_bytes.len() as u64),
            recover_journal_entries_bytes(old(wrpm)@.durable_state, *sm, entries_bytes.len() as u64)
                == Some(entries_bytes),
            journal_entries_valid(entries, *sm),
            apply_journal_entries(old(wrpm)@.read_state, entries.skip(num_entries_installed), *sm)
                == Some(commit_state),
            parse_journal_entries(entries_bytes) == Some(entries),
            recover_journal(old(wrpm)@.durable_state) is Some,
            0 <= start < entries_bytes.len(),
            0 <= num_entries_installed < entries.len(),
            entries[num_entries_installed as int].start == write_addr,
            entries[num_entries_installed as int].bytes_to_write == bytes_to_write@,
            forall|s: Seq<u8>| recover_journal(s) == recover_journal(old(wrpm)@.durable_state)
                ==> #[trigger] perm.check_permission(s),
        ensures
            wrpm.inv(),
            wrpm.constants() == old(wrpm).constants(),
            wrpm@.len() == old(wrpm)@.len(),
            wrpm@.valid(),
            recover_journal(wrpm@.durable_state) == recover_journal(old(wrpm)@.durable_state),
            apply_journal_entries(wrpm@.read_state, entries.skip(num_entries_installed + 1), *sm) == Some(commit_state),
            seqs_match_in_range(old(wrpm)@.durable_state, wrpm@.durable_state, 0, sm.app_area_start as int),
            seqs_match_in_range(old(wrpm)@.read_state, wrpm@.read_state, 0, sm.app_area_start as int),
    {
        proof {
            lemma_addresses_in_entry_dont_affect_recovery(wrpm@.durable_state, vm, *sm,
                                                          entries_bytes, entries, num_entries_installed);
            assert(entries[num_entries_installed].fits(*sm)) by {
                lemma_journal_entries_valid_implies_one_valid(entries, *sm, num_entries_installed);
            }
            assert forall|s| can_result_from_partial_write(s, wrpm@.durable_state, write_addr as int, bytes_to_write@)
                implies #[trigger] perm.check_permission(s) by {
                lemma_if_addresses_unreachable_in_recovery_then_recovery_unchanged_by_write(
                    s, wrpm@.durable_state, write_addr as int, bytes_to_write@,
                    entries[num_entries_installed as int].addrs(),
                    |s| recover_journal(s),
                );
                assert(recover_journal(s) == recover_journal(wrpm@.durable_state));
            }
        }
        wrpm.write(write_addr, bytes_to_write, Tracked(perm));
        proof {
            broadcast use group_can_result_from_write_effect;
            assert(recover_journal(wrpm@.durable_state) == recover_journal(old(wrpm)@.durable_state)) by {
                lemma_if_addresses_unreachable_in_recovery_then_recovery_unchanged_by_write(
                    wrpm@.durable_state, old(wrpm)@.durable_state, write_addr as int, bytes_to_write@,
                    entries[num_entries_installed as int].addrs(),
                    |s| recover_journal(s),
                );
            }
            assert(Some(wrpm@.read_state) ==
                   apply_journal_entry(old(wrpm)@.read_state, entries[num_entries_installed], *sm));
            assert(recover_journal(wrpm@.durable_state) == recover_journal(old(wrpm)@.durable_state));
            assert(recover_journal_length(wrpm@.durable_state, *sm) == Some(entries_bytes.len() as u64));
    
            assert(entries.skip(num_entries_installed)[0] =~= entries[num_entries_installed]);
            assert(entries.skip(num_entries_installed).skip(1) =~= entries.skip(num_entries_installed + 1));
        }
    }
    
    exec fn install_journal_entries_during_start(
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        Tracked(perm): Tracked<&Perm>,
        Ghost(vm): Ghost<JournalVersionMetadata>,
        sm: &JournalStaticMetadata,
        entries_bytes: &Vec<u8>,
        Ghost(entries): Ghost<Seq<JournalEntry>>,
    )
        requires
            old(wrpm).inv(),
            old(wrpm)@.valid(),
            old(wrpm)@.flush_predicted(),
            recover_version_metadata(old(wrpm)@.read_state) == Some(vm),
            recover_static_metadata(old(wrpm)@.read_state, vm) == Some(*sm),
            recover_committed_cdb(old(wrpm)@.read_state, *sm) == Some(true),
            recover_journal_length(old(wrpm)@.read_state, *sm) == Some(entries_bytes.len() as u64),
            recover_journal_entries_bytes(old(wrpm)@.read_state, *sm, entries_bytes.len() as u64)
                == Some(entries_bytes@),
            parse_journal_entries(entries_bytes@) == Some(entries),
            apply_journal_entries(old(wrpm)@.read_state, entries, *sm) is Some,
            recover_journal(old(wrpm)@.read_state) is Some,
            forall|s: Seq<u8>| recover_journal(old(wrpm)@.durable_state) == recover_journal(s)
                ==> #[trigger] perm.check_permission(s),
        ensures
            wrpm.inv(),
            wrpm.constants() == old(wrpm).constants(),
            wrpm@.len() == old(wrpm)@.len(),
            wrpm@.flush_predicted(),
            recover_version_metadata(wrpm@.read_state) == Some(vm),
            recover_static_metadata(wrpm@.read_state, vm) == Some(*sm),
            recover_committed_cdb(wrpm@.read_state, *sm) == Some(true),
            recover_journal_length(wrpm@.read_state, *sm) == Some(entries_bytes.len() as u64),
            recover_journal_entries_bytes(wrpm@.read_state, *sm, entries_bytes.len() as u64) == Some(entries_bytes@),
            apply_journal_entries(wrpm@.durable_state, entries, *sm) == Some(wrpm@.read_state),
            apply_journal_entries(old(wrpm)@.read_state, entries, *sm) == Some(wrpm@.read_state),
            recover_journal(wrpm@.durable_state) == recover_journal(old(wrpm)@.durable_state),
    {
        let mut start: usize = 0;
        let end: usize = entries_bytes.len();
        let ghost mut num_entries_installed: int = 0;
        let u64_size: usize = size_of::<u64>();
        let twice_u64_size: usize = u64_size + u64_size;
        let ghost commit_state = apply_journal_entries(wrpm@.read_state, entries, *sm).unwrap();
    
        assert(entries.skip(0) =~= entries);
        assert(entries_bytes@.skip(0) =~= entries_bytes@);
        proof {
            lemma_apply_journal_entries_some_iff_journal_entries_valid(old(wrpm)@.read_state, entries, *sm);
        }
    
        while start < end
            invariant
                wrpm.inv(),
                wrpm.constants() == old(wrpm).constants(),
                wrpm@.valid(),
                wrpm@.len() == old(wrpm)@.len(),
                start <= end == entries_bytes.len(),
                u64_size == u64::spec_size_of(),
                twice_u64_size == u64_size + u64_size,
                0 <= num_entries_installed <= entries.len(),
                num_entries_installed == entries.len() <==> start == end,
                old(wrpm)@.read_state == old(wrpm)@.durable_state,
                recover_version_metadata(old(wrpm)@.read_state) == Some(vm),
                recover_static_metadata(old(wrpm)@.read_state, vm) == Some(*sm),
                recover_committed_cdb(old(wrpm)@.read_state, *sm) == Some(true),
                recover_journal_length(old(wrpm)@.read_state, *sm) == Some(entries_bytes.len() as u64),
                recover_journal_entries_bytes(old(wrpm)@.read_state, *sm, entries_bytes.len() as u64)
                    == Some(entries_bytes@),
                parse_journal_entries(entries_bytes@) == Some(entries),
                journal_entries_valid(entries, *sm),
                apply_journal_entries(old(wrpm)@.read_state, entries, *sm) is Some,
                recover_journal(old(wrpm)@.read_state) is Some,
                recover_version_metadata(wrpm@.durable_state) == Some(vm),
                recover_static_metadata(wrpm@.durable_state, vm) == Some(*sm),
                recover_committed_cdb(wrpm@.durable_state, *sm) == Some(true),
                recover_journal_length(wrpm@.durable_state, *sm) == Some(entries_bytes.len() as u64),
                recover_journal_entries_bytes(wrpm@.durable_state, *sm, entries_bytes.len() as u64)
                    == Some(entries_bytes@),
                recover_journal(wrpm@.durable_state) == recover_journal(old(wrpm)@.durable_state),
                forall|s: Seq<u8>| recover_journal(s) == recover_journal(old(wrpm)@.durable_state)
                    ==> #[trigger] perm.check_permission(s),
                parse_journal_entries(entries_bytes@.skip(start as int)) == Some(entries.skip(num_entries_installed)),
                seqs_match_in_range(old(wrpm)@.durable_state, wrpm@.durable_state, 0, sm.app_area_start as int),
                seqs_match_in_range(old(wrpm)@.read_state, wrpm@.read_state, 0, sm.app_area_start as int),
                apply_journal_entries(wrpm@.read_state, entries.skip(num_entries_installed), *sm)
                    == Some(commit_state),
        {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            broadcast use pmcopy_axioms;
            
            let ghost durable_state_at_start_of_loop = wrpm@.durable_state;
    
            assert(start + twice_u64_size <= end);
            assert(parse_journal_entry(entries_bytes@.skip(start as int)) is Some);
            assert(parse_journal_entry(entries_bytes@.skip(start as int)).unwrap().0 == entries[num_entries_installed]);
            let entries_bytes_slice = entries_bytes.as_slice();
            let addr = u64_from_le_bytes(slice_subrange(entries_bytes_slice, start, start + u64_size));
            let len = u64_from_le_bytes(slice_subrange(entries_bytes_slice, start + u64_size, start + twice_u64_size));
            assert(entries_bytes_slice@.subrange(start as int, (start + u64_size) as int) ==
                   extract_section(entries_bytes@.skip(start as int), 0, u64::spec_size_of()));
            assert(addr == u64::spec_from_bytes(extract_section(entries_bytes@.skip(start as int),
                                                                0, u64::spec_size_of())));
            assert(entries_bytes_slice@.subrange((start + u64_size) as int, (start + u64_size + u64_size) as int) ==
                   extract_section(entries_bytes@.skip(start as int), u64::spec_size_of() as int, u64::spec_size_of()));
            assert(len == u64::spec_from_bytes(extract_section(entries_bytes@.skip(start as int),
                                                               u64::spec_size_of() as int, u64::spec_size_of())));
            assert(start + twice_u64_size + len as usize <= end);
            let bytes_to_write = slice_subrange(entries_bytes_slice, start + twice_u64_size,
                                                start + twice_u64_size + len as usize);
            assert(bytes_to_write@ == extract_section(entries_bytes@.skip(start as int),
                                                     (u64::spec_size_of() + u64::spec_size_of()) as int,
                                                     len as nat));
            let ghost entry = JournalEntry{ start: addr as int, bytes_to_write: bytes_to_write@ };
            proof {
                lemma_parse_journal_entry_implications(entries_bytes@, entries, start as int, num_entries_installed);
                assert(entries[num_entries_installed as int] == entry);
            }
            Self::install_journal_entry_during_start(wrpm, Tracked(perm), Ghost(vm), sm, start, addr, bytes_to_write,
                                                     Ghost(entries_bytes@), Ghost(num_entries_installed),
                                                     Ghost(entries), Ghost(commit_state));
            proof {
                assert(entries.skip(num_entries_installed) =~= seq![entries[num_entries_installed as int]] +
                       entries.skip(num_entries_installed + 1));
                num_entries_installed = num_entries_installed + 1;
            }
            
            start += twice_u64_size + len as usize;
        }
    
        wrpm.flush();
    }
    
    pub(super) exec fn clear_log(
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        Tracked(perm): Tracked<&Perm>,
        Ghost(vm): Ghost<JournalVersionMetadata>,
        sm: &JournalStaticMetadata,
    )
        requires
            old(wrpm).inv(),
            old(wrpm)@.valid(),
            old(wrpm)@.flush_predicted(),
            recover_version_metadata(old(wrpm)@.read_state) == Some(vm),
            recover_static_metadata(old(wrpm)@.read_state, vm) == Some(*sm),
            recover_committed_cdb(old(wrpm)@.read_state, *sm) == Some(true),
            ({
                &&& recover_journal(old(wrpm)@.read_state) matches Some(j)
                &&& j.state == old(wrpm)@.read_state
            }),
            forall|s: Seq<u8>| spec_recovery_equivalent_for_app(s, old(wrpm)@.durable_state)
                ==> #[trigger] perm.check_permission(s),
        ensures
            wrpm.inv(),
            wrpm.constants() == old(wrpm).constants(),
            wrpm@.len() == old(wrpm)@.len(),
            wrpm@.flush_predicted(),
            recover_version_metadata(wrpm@.read_state) == Some(vm),
            recover_static_metadata(wrpm@.read_state, vm) == Some(*sm),
            recover_committed_cdb(wrpm@.read_state, *sm) == Some(false),
            spec_recovery_equivalent_for_app(wrpm@.durable_state, old(wrpm)@.durable_state),
    {
        let new_cdb: u64 = CDB_FALSE;
        let ghost new_state = update_bytes(wrpm@.durable_state, sm.committed_cdb_start as int,
            new_cdb.spec_to_bytes());
        proof {
            broadcast use pmcopy_axioms;
            broadcast use group_update_bytes_effect;
            assert(sm.committed_cdb_start as int % const_persistence_chunk_size() == 0);
            assert(new_cdb.spec_to_bytes().len() == const_persistence_chunk_size()); // uses pmcopy_axioms
            assert(spec_recovery_equivalent_for_app(wrpm@.durable_state, wrpm@.durable_state));
            assert(perm.check_permission(wrpm@.durable_state));
            assert(recover_version_metadata(new_state) == Some(vm));
            assert(recover_static_metadata(new_state, vm) == Some(*sm));
            assert(recover_committed_cdb(new_state, *sm) == Some(false)); // uses pmcopy_axioms
            assert(spec_recovery_equivalent_for_app(new_state, old(wrpm)@.durable_state));
            lemma_auto_only_two_crash_states_introduced_by_aligned_chunk_write();
        }
        wrpm.serialize_and_write::<u64>(sm.committed_cdb_start, &new_cdb, Tracked(perm));
        wrpm.flush();
        assert(wrpm@.read_state == new_state);
    }

    pub exec fn start(
        wrpm: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        Tracked(perm): Tracked<&Perm>
    ) -> (result: Result<Self, JournalError>)
        requires
            wrpm.inv(),
            Self::recover(wrpm@.durable_state).is_some(),
            forall|s: Seq<u8>| Self::recovery_equivalent_for_app(s, wrpm@.durable_state)
                ==> #[trigger] perm.check_permission(s),
        ensures
            match result {
                Ok(j) => {
                    &&& j.valid()
                    &&& j.recover_idempotent()
                    &&& j@.valid()
                    &&& j@.constants == Self::recover(wrpm@.durable_state).unwrap().constants
                    &&& j@.pm_constants == wrpm.constants()
                    &&& j@.remaining_capacity == j@.constants.journal_capacity
                    &&& j@.journaled_addrs == Set::<int>::empty()
                    &&& j@.durable_state == j@.read_state
                    &&& j@.read_state == j@.commit_state
                    &&& Self::recovery_equivalent_for_app(j@.durable_state, wrpm@.durable_state)
                },
                Err(JournalError::CRCError) => !wrpm.constants().impervious_to_corruption(),
                _ => false,
            }
    {
        let ghost old_durable_state = wrpm@.durable_state;
        assert(wrpm.constants().valid()) by {
            wrpm.lemma_inv_implies_view_valid();
        }
        let mut wrpm = wrpm;
        wrpm.flush();

        let pm = wrpm.get_pm_region_ref();
        let pm_size = pm.get_region_size(); // This establishes that `pm@.len() <= u64::MAX`
 
        let vm = Self::read_version_metadata(pm).ok_or(JournalError::CRCError)?;
        let sm = Self::read_static_metadata(pm, &vm).ok_or(JournalError::CRCError)?;
        let cdb = Self::read_committed_cdb(pm, &vm, &sm).ok_or(JournalError::CRCError)?;
        let constants = JournalConstants {
            app_version_number: sm.app_version_number,
            app_program_guid: sm.app_program_guid,
            journal_capacity: sm.journal_entries_end - sm.journal_entries_start,
            app_area_start: sm.app_area_start,
            app_area_end: sm.app_area_end,
        };

        assert(Self::recover(wrpm@.durable_state).unwrap().constants.app_area_end == wrpm@.len());
        if cdb {
            let journal_length = Self::read_journal_length(pm, Ghost(vm), &sm).ok_or(JournalError::CRCError)?;
            let entries_bytes =
                Self::read_journal_entries_bytes(pm, Ghost(vm), &sm, journal_length).ok_or(JournalError::CRCError)?;
            let ghost entries = parse_journal_entries(entries_bytes@).unwrap();
            assert forall|s: Seq<u8>| recover_journal(wrpm@.durable_state) == recover_journal(s)
                implies #[trigger] perm.check_permission(s) by {
                Self::lemma_recover_doesnt_change_size(wrpm@.durable_state);
            }
            Self::install_journal_entries_during_start(&mut wrpm, Tracked(perm), Ghost(vm), &sm, &entries_bytes,
                                                       Ghost(entries));
            Self::clear_log(&mut wrpm, Tracked(perm), Ghost(vm), &sm);
        }
        let j = Self {
            wrpm,
            vm: Ghost(vm),
            sm,
            status: Ghost(JournalStatus::Quiescent),
            constants: constants.clone(),
            journal_length: 0,
            journaled_addrs: Ghost(Set::<int>::empty()),
            entries: ConcreteJournalEntries::new(),
        };
        Ok(j)
    }
}

}
