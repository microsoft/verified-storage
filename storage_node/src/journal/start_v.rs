use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::{size_of, align_of};
use crate::pmem::wrpm_t::*;
use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
use crate::common::util_v::*;
use super::journal_v::*;
use super::layout_v::*;
use super::spec_v::*;
use deps_hack::PmCopy;

verus! {

impl <Perm, PM> Journal<Perm, PM>
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
{
    pub(super) exec fn read_version_metadata(pm: &PM) -> (result: Option<JournalVersionMetadata>)
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
        reveal(opaque_subrange);

        let journal_version_metadata_end = size_of::<JournalVersionMetadata>() as u64;
        let journal_version_metadata_crc_addr = exec_round_up_to_alignment::<u64>(journal_version_metadata_end);

        assert(spec_journal_version_metadata_start() == 0);
        let ghost true_vm_bytes = opaque_section(pm@.read_state, 0, JournalVersionMetadata::spec_size_of());
        let ghost true_vm = JournalVersionMetadata::spec_from_bytes(true_vm_bytes);
        let maybe_corrupted_vm = match pm.read_aligned::<JournalVersionMetadata>(0) {
            Ok(bytes) => bytes,
            Err(_) => { assert(false); return None; }
        };

        assert(journal_version_metadata_crc_addr == spec_journal_version_metadata_crc_start());
        let maybe_corrupted_vm_crc = match pm.read_aligned::<u64>(journal_version_metadata_crc_addr) {
            Ok(bytes) => bytes,
            Err(_) => { assert(false); return None; }
        };

        if !check_crc(maybe_corrupted_vm.as_slice(), maybe_corrupted_vm_crc.as_slice(),
            Ghost(true_vm_bytes),
            Ghost(pm.constants()),
            Ghost(spec_journal_version_metadata_start()),
            Ghost(spec_journal_version_metadata_crc_start()),
        ) {
            return None;
        }

        Some(*maybe_corrupted_vm.extract_init_val(Ghost(true_vm)))
    }

    pub(super) exec fn read_static_metadata(pm: &PM, vm: &JournalVersionMetadata) -> (result: Option<JournalStaticMetadata>)
        requires
            pm.inv(),
            recover_static_metadata(pm@.read_state, *vm).is_some(),
            validate_version_metadata(*vm),
            pm@.len() <= u64::MAX,
        ensures
            match result {
                None => !pm.constants().impervious_to_corruption(),
                Some(sm) => recover_static_metadata(pm@.read_state, *vm) == Some(sm),
            }
    {
        reveal(opaque_subrange);

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

        let ghost true_sm_bytes = opaque_subrange(pm@.read_state, journal_static_metadata_start as int,
                                                  journal_static_metadata_end as int);
        let ghost true_sm = JournalStaticMetadata::spec_from_bytes(true_sm_bytes);
        let maybe_corrupted_sm = match pm.read_aligned::<JournalStaticMetadata>(journal_static_metadata_start) {
            Ok(bytes) => bytes,
            Err(_) => { assert(false); return None; }
        };

        let maybe_corrupted_sm_crc = match pm.read_aligned::<u64>(journal_static_metadata_crc_start) {
            Ok(bytes) => bytes,
            Err(_) => { assert(false); return None; }
        };

        if !check_crc(maybe_corrupted_sm.as_slice(), maybe_corrupted_sm_crc.as_slice(),
            Ghost(true_sm_bytes),
            Ghost(pm.constants()),
            Ghost(spec_journal_static_metadata_start()),
            Ghost(spec_journal_static_metadata_crc_start()),
        ) {
            return None;
        }

        Some(*maybe_corrupted_sm.extract_init_val(Ghost(true_sm)))
    }

    pub(super) exec fn read_committed_cdb(pm: &PM, vm: &JournalVersionMetadata, sm: &JournalStaticMetadata) -> (result: Option<bool>)
        requires
            pm.inv(),
            pm@.len() <= u64::MAX,
            recover_cdb(pm@.read_state, sm.committed_cdb_start as int).is_some(),
            validate_version_metadata(*vm),
            validate_static_metadata(*sm, *vm),
            sm.app_dynamic_area_end <= pm@.len(),
        ensures
            match result {
                None => !pm.constants().impervious_to_corruption(),
                Some(b) => recover_cdb(pm@.read_state, sm.committed_cdb_start as int) == Some(b),
            }
    {
        reveal(opaque_subrange);

        let ghost true_cdb_bytes = opaque_subrange(pm@.read_state, sm.committed_cdb_start as int,
                                                   sm.committed_cdb_start as int + u64::spec_size_of() as int);
        let cdb_bytes = match pm.read_aligned::<u64>(sm.committed_cdb_start) {
            Ok(bytes) => bytes,
            Err(_) => { assert(false); return None; }
        };

        check_cdb(
            cdb_bytes,
            Ghost(true_cdb_bytes),
            Ghost(pm.constants()),
            Ghost(sm.committed_cdb_start as int)
        )
    }

    pub(super) exec fn install_journal_entries(
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        Tracked(perm): Tracked<&Perm>,
        vm: Ghost<JournalVersionMetadata>,
        sm: JournalStaticMetadata,
        start: u64,
        end: u64,
        entries: Ghost<Seq<JournalEntry>>,
        journal_length: u64,
    ) -> (result: Result<(), JournalError>)
        requires
            old(wrpm).inv(),
            recover_version_metadata(old(wrpm)@.durable_state) == Some(vm@),
            recover_version_metadata(old(wrpm)@.read_state) == Some(vm@),
            recover_static_metadata(old(wrpm)@.durable_state, vm@) == Some(sm),
            recover_static_metadata(old(wrpm)@.read_state, vm@) == Some(sm),
            recover_app_static_area(old(wrpm)@.durable_state, sm) is Some,
            recover_app_static_area(old(wrpm)@.read_state, sm) == recover_app_static_area(old(wrpm)@.durable_state, sm),
            recover_cdb(old(wrpm)@.durable_state, sm.committed_cdb_start as int) == Some(true),
            recover_cdb(old(wrpm)@.read_state, sm.committed_cdb_start as int) == Some(true),
            recover_journal_length(old(wrpm)@.durable_state, sm) == Some(journal_length),
            recover_journal_length(old(wrpm)@.read_state, sm) == Some(journal_length),
            end == sm.journal_entries_start + journal_length,
            sm.app_dynamic_area_end <= old(wrpm)@.len(),
            sm.journal_entries_start <= start <= end <= sm.journal_entries_end,
            recover_journal_entries(old(wrpm)@.read_state, sm, journal_length) == Some(entries@),
            apply_journal_entries(old(wrpm)@.read_state, entries@, 0, sm) is Some,
            recover_journal(old(wrpm)@.durable_state) is Some,
            forall|s: Seq<u8>| recover_journal(s) == recover_journal(old(wrpm)@.durable_state)
                ==> #[trigger] perm.check_permission(s),
        ensures
            wrpm.inv(),
            match result {
                Ok(_) => {
                    &&& recover_version_metadata(wrpm@.durable_state) == Some(vm@)
                    &&& recover_version_metadata(wrpm@.read_state) == Some(vm@)
                    &&& recover_static_metadata(wrpm@.durable_state, vm@) == Some(sm)
                    &&& recover_static_metadata(wrpm@.read_state, vm@) == Some(sm)
                    &&& recover_app_static_area(wrpm@.durable_state, sm) ==
                            recover_app_static_area(old(wrpm)@.durable_state, sm)
                    &&& recover_app_static_area(wrpm@.read_state, sm) == recover_app_static_area(wrpm@.durable_state, sm)
                    &&& recover_cdb(wrpm@.durable_state, sm.committed_cdb_start as int) == Some(true)
                    &&& recover_cdb(wrpm@.read_state, sm.committed_cdb_start as int) == Some(true)
                    &&& recover_journal_length(wrpm@.durable_state, sm) == Some(journal_length)
                    &&& recover_journal_length(wrpm@.read_state, sm) == Some(journal_length)
                    &&& recover_journal_entries(wrpm@.read_state, sm, journal_length) == Some(entries@)
                    &&& apply_journal_entries(wrpm@.read_state, entries@, 0, sm) is Some
                    &&& opaque_subrange(wrpm@.read_state, sm.app_dynamic_area_start as int,
                                        sm.app_dynamic_area_end as int) ==
                            apply_journal_entries(old(wrpm)@.read_state, entries@, 0, sm).unwrap()
                },
                Err(JournalError::CRCError) => !wrpm.constants().impervious_to_corruption(),
                Err(_) => false,
            },
    {
        assume(false);
        Err(JournalError::NotEnoughSpace)
    }
}

}
