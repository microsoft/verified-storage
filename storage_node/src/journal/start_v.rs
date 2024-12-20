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

    exec fn read_static_metadata(pm: &PM, vm: &JournalVersionMetadata) -> (result: Option<JournalStaticMetadata>)
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

    exec fn read_committed_cdb(pm: &PM, vm: &JournalVersionMetadata, sm: &JournalStaticMetadata) -> (result: Option<bool>)
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

    pub exec fn start(
        wrpm: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        Tracked(perm): Tracked<&Perm>
    ) -> (result: Result<Self, JournalError>)
        requires
            wrpm.inv(),
            recover_journal(wrpm.view().read_state).is_some(),
            forall|s: Seq<u8>| recover_journal(s) == recover_journal(wrpm.view().durable_state)
                ==> #[trigger] perm.check_permission(s),
        ensures
            match result {
                Err(JournalError::CRCError) => !wrpm.constants().impervious_to_corruption(),
                _ => true,
            }
    {
        let pm = wrpm.get_pm_region_ref();
        let pm_size = pm.get_region_size(); // This establishes that `pm@.len() <= u64::MAX`
    
        reveal(recover_journal);
        let vm = Self::read_version_metadata(pm).ok_or(JournalError::CRCError)?;
        let sm = Self::read_static_metadata(pm, &vm).ok_or(JournalError::CRCError)?;
        let cdb = Self::read_committed_cdb(pm, &vm, &sm).ok_or(JournalError::CRCError)?;
        Err(JournalError::NotEnoughSpace)
    }
}

}
