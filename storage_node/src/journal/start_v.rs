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
use super::entry_v::*;
use super::journal_v::*;
use super::recover_v::*;
use super::spec_v::*;
use deps_hack::PmCopy;
use vstd::bytes::u64_from_le_bytes;
use vstd::slice::slice_subrange;

verus! {

pub(super) exec fn read_version_metadata<PM>(pm: &PM) -> (result: Option<JournalVersionMetadata>)
    where
        PM: PersistentMemoryRegion,
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

pub(super) exec fn read_static_metadata<PM>(pm: &PM, vm: &JournalVersionMetadata)
                                            -> (result: Option<JournalStaticMetadata>)
    where
        PM: PersistentMemoryRegion,
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

pub(super) exec fn read_committed_cdb<PM>(pm: &PM, vm: &JournalVersionMetadata, sm: &JournalStaticMetadata)
                                          -> (result: Option<bool>)
    where
        PM: PersistentMemoryRegion,
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

pub(super) exec fn read_journal_length<PM>(
    pm: &PM,
    Ghost(vm): Ghost<JournalVersionMetadata>,
    sm: &JournalStaticMetadata
) -> (result: Option<u64>)
    where
        PM: PersistentMemoryRegion,
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
    reveal(opaque_subrange);

    let ghost true_journal_length_bytes =
         opaque_section(pm@.read_state, sm.journal_length_start as int, u64::spec_size_of());
    let ghost true_journal_length = u64::spec_from_bytes(true_journal_length_bytes);
    let maybe_corrupted_journal_length = match pm.read_aligned::<u64>(sm.journal_length_start) {
        Ok(bytes) => bytes,
        Err(_) => { assert(false); return None; }
    };

    let maybe_corrupted_journal_length_crc = match pm.read_aligned::<u64>(sm.journal_length_crc_start) {
        Ok(bytes) => bytes,
        Err(_) => { assert(false); return None; }
    };

    if !check_crc(
        maybe_corrupted_journal_length.as_slice(),
        maybe_corrupted_journal_length_crc.as_slice(),
        Ghost(true_journal_length_bytes),
        Ghost(pm.constants()),
        Ghost(sm.journal_length_start as int),
        Ghost(sm.journal_length_crc_start as int),
    ) {
        return None;
    }

    Some(*maybe_corrupted_journal_length.extract_init_val(Ghost(true_journal_length)))
}

pub(super) exec fn read_journal_entries_bytes<PM>(
    pm: &PM,
    Ghost(vm): Ghost<JournalVersionMetadata>,
    sm: &JournalStaticMetadata,
    journal_length: u64,
) -> (result: Option<Vec<u8>>)
    where
        PM: PersistentMemoryRegion,
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
    reveal(opaque_subrange);

    let ghost true_journal_entries_bytes =
         opaque_section(pm@.read_state, sm.journal_entries_start as int, journal_length as nat);
    let maybe_corrupted_journal_entries = match pm.read_unaligned(sm.journal_entries_start, journal_length) {
        Ok(bytes) => bytes,
        Err(_) => { assert(false); return None; }
    };

    let maybe_corrupted_journal_entries_crc = match pm.read_aligned::<u64>(sm.journal_entries_crc_start) {
        Ok(bytes) => bytes,
        Err(_) => { assert(false); return None; }
    };

    if !check_crc(
        maybe_corrupted_journal_entries.as_slice(),
        maybe_corrupted_journal_entries_crc.as_slice(),
        Ghost(true_journal_entries_bytes),
        Ghost(pm.constants()),
        Ghost(sm.journal_entries_start as int),
        Ghost(sm.journal_entries_crc_start as int),
    ) {
        return None;
    }

    Some(maybe_corrupted_journal_entries)
}

exec fn install_journal_entry<Perm, PM>(
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
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
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
        opaque_subrange(wrpm@.durable_state, 0, sm.app_area_start as int) ==
            opaque_subrange(old(wrpm)@.durable_state, 0, sm.app_area_start as int),
        opaque_subrange(wrpm@.read_state, 0, sm.app_area_start as int) ==
            opaque_subrange(old(wrpm)@.read_state, 0, sm.app_area_start as int),
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
        assert(recover_journal(wrpm@.durable_state) == recover_journal(old(wrpm)@.durable_state)) by {
            lemma_if_addresses_unreachable_in_recovery_then_recovery_unchanged_by_write(
                wrpm@.durable_state, old(wrpm)@.durable_state, write_addr as int, bytes_to_write@,
                entries[num_entries_installed as int].addrs(),
                |s| recover_journal(s),
            );
        }
        assert(Some(wrpm@.read_state) ==
               apply_journal_entry(old(wrpm)@.read_state, entries[num_entries_installed], *sm)) by {
            reveal(opaque_update_bytes);
        }
        lemma_auto_can_result_from_partial_write_effect_on_opaque();
        lemma_auto_opaque_subrange_subrange(wrpm@.durable_state, 0, write_addr as int);
        lemma_auto_opaque_subrange_subrange(old(wrpm)@.durable_state, 0, write_addr as int);
        assert(recover_journal(wrpm@.durable_state) == recover_journal(old(wrpm)@.durable_state));
        assert(recover_journal_length(wrpm@.durable_state, *sm) == Some(entries_bytes.len() as u64));
        lemma_auto_can_result_from_write_effect_on_read_state();
        lemma_auto_opaque_subrange_subrange(wrpm@.read_state, 0, write_addr as int);
        lemma_auto_opaque_subrange_subrange(old(wrpm)@.read_state, 0, write_addr as int);

        assert(entries.skip(num_entries_installed)[0] =~= entries[num_entries_installed]);
        assert(entries.skip(num_entries_installed).skip(1) =~= entries.skip(num_entries_installed + 1));
    }
}

pub(super) exec fn install_journal_entries<Perm, PM>(
    wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
    Tracked(perm): Tracked<&Perm>,
    Ghost(vm): Ghost<JournalVersionMetadata>,
    sm: &JournalStaticMetadata,
    entries_bytes: &Vec<u8>,
    Ghost(entries): Ghost<Seq<JournalEntry>>,
)
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
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
        forall|s: Seq<u8>| recover_journal(s) == recover_journal(old(wrpm)@.durable_state)
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
            opaque_subrange(wrpm@.durable_state, 0, sm.app_area_start as int) ==
                opaque_subrange(old(wrpm)@.durable_state, 0, sm.app_area_start as int),
            opaque_subrange(wrpm@.read_state, 0, sm.app_area_start as int) ==
                opaque_subrange(old(wrpm)@.read_state, 0, sm.app_area_start as int),
            apply_journal_entries(wrpm@.read_state, entries.skip(num_entries_installed), *sm)
                == Some(commit_state),
    {
        reveal(opaque_subrange);
        broadcast use pmcopy_axioms;
        let ghost durable_state_at_start_of_loop = wrpm@.durable_state;

        assert(start + twice_u64_size <= end);
        assert(parse_journal_entry(entries_bytes@.skip(start as int)) is Some);
        assert(parse_journal_entry(entries_bytes@.skip(start as int)).unwrap().0 == entries[num_entries_installed]);
        let entries_bytes_slice = entries_bytes.as_slice();
        let addr = u64_from_le_bytes(slice_subrange(entries_bytes_slice, start, start + u64_size));
        let len = u64_from_le_bytes(slice_subrange(entries_bytes_slice, start + u64_size, start + twice_u64_size));
        assert(entries_bytes_slice@.subrange(start as int, (start + u64_size) as int) ==
               opaque_section(entries_bytes@.skip(start as int), 0, u64::spec_size_of()));
        assert(addr == u64::spec_from_bytes(opaque_section(entries_bytes@.skip(start as int), 0, u64::spec_size_of())));
        assert(entries_bytes_slice@.subrange((start + u64_size) as int, (start + u64_size + u64_size) as int) ==
               opaque_section(entries_bytes@.skip(start as int), u64::spec_size_of() as int, u64::spec_size_of()));
        assert(len == u64::spec_from_bytes(opaque_section(entries_bytes@.skip(start as int), u64::spec_size_of() as int,
                                                          u64::spec_size_of())));
        assert(start + twice_u64_size + len as usize <= end);
        let bytes_to_write = slice_subrange(entries_bytes_slice, start + twice_u64_size,
                                            start + twice_u64_size + len as usize);
        assert(bytes_to_write@ == opaque_section(entries_bytes@.skip(start as int),
                                                 (u64::spec_size_of() + u64::spec_size_of()) as int,
                                                 len as nat));
        let ghost entry = JournalEntry{ start: addr as int, bytes_to_write: bytes_to_write@ };
        proof {
            lemma_parse_journal_entry_implications(entries_bytes@, entries, start as int, num_entries_installed);
            assert(entries[num_entries_installed as int] == entry);
        }
        install_journal_entry(wrpm, Tracked(perm), Ghost(vm), sm, start, addr, bytes_to_write,
                              Ghost(entries_bytes@), Ghost(num_entries_installed), Ghost(entries),
                              Ghost(commit_state));
        proof {
            assert(entries.skip(num_entries_installed) =~= seq![entries[num_entries_installed as int]] +
                   entries.skip(num_entries_installed + 1));
            num_entries_installed = num_entries_installed + 1;
            lemma_auto_opaque_subrange_subrange(durable_state_at_start_of_loop, 0, sm.app_area_start as int);
            lemma_auto_opaque_subrange_subrange(wrpm@.durable_state, 0, sm.app_area_start as int);
        }
        
        start += (twice_u64_size + len as usize);
    }

    wrpm.flush();

    proof {
        lemma_auto_opaque_subrange_subrange(wrpm@.read_state, 0, sm.app_area_start as int);
        lemma_auto_opaque_subrange_subrange(old(wrpm)@.read_state, 0, sm.app_area_start as int);
    }
}

pub(super) exec fn clear_log<Perm, PM>(
    wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
    Tracked(perm): Tracked<&Perm>,
    Ghost(vm): Ghost<JournalVersionMetadata>,
    sm: &JournalStaticMetadata,
)
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
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
        assert(sm.committed_cdb_start as int % const_persistence_chunk_size() == 0) by {
            reveal(opaque_aligned);
        }
        assert(new_cdb.spec_to_bytes().len() == const_persistence_chunk_size()); // uses pmcopy_axioms
        assert(spec_recovery_equivalent_for_app(wrpm@.durable_state, wrpm@.durable_state));
        assert(perm.check_permission(wrpm@.durable_state));
        lemma_auto_effect_of_update_bytes_on_opaque_subranges();
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

}
