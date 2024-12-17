use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::{pmcopy_t::*, pmemspec_t::*, pmemutil_v::*, traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe}};
use crate::pmem::traits_t::*;
use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
use crate::common::util_v::*;
use super::spec_v::*;
use deps_hack::PmCopy;

verus! {

    pub const ABSOLUTE_POS_OF_VERSION_METADATA: u64 = 0;

    // This GUID was generated randomly and is meant to describe the
    // journal module, even if it has future versions.

    pub const JOURNAL_PROGRAM_GUID: u128 = 0xf41bb8dd3ccc4a77bb76c8f3a5319d6a;

    // The current version number, and the only one whose contents
    // this program can read, is the following:

    pub const JOURNAL_PROGRAM_VERSION_NUMBER: u64 = 1;

    #[repr(C)]
    #[derive(PmCopy, Copy, Default)]
    pub struct JournalVersionMetadata {
        pub version_number: u64,
        pub static_metadata_addr: u64,
        pub program_guid: u128,
    }

    #[repr(C)]
    #[derive(PmCopy, Copy, Default, Debug)]
    pub struct JournalStaticMetadata {
        pub app_version_number: u64,
        pub app_program_guid: u128,
        pub committed_cdb_addr: u64,
        pub journal_length_addr: u64,
        pub journal_data_start: u64,
        pub journal_data_end: u64,
        pub app_static_area_start: u64,
        pub app_static_area_end: u64,
        pub app_dynamic_area_start: u64,
        pub app_dynamic_area_end: u64,
    }

    pub struct JournalEntry
    {
        pub addr: int,
        pub bytes: Seq<u8>,
    }

    pub closed spec fn validate_version_metadata(m: JournalVersionMetadata) -> bool
    {
        &&& m.version_number == JOURNAL_PROGRAM_VERSION_NUMBER
        &&& JournalVersionMetadata::spec_size_of() + u64::spec_size_of() <= m.static_metadata_addr
        &&& m.program_guid == JOURNAL_PROGRAM_GUID
    }

    pub closed spec fn recover_version_metadata(bytes: Seq<u8>) -> Option<JournalVersionMetadata>
    {
        match recover_object::<JournalVersionMetadata>(bytes, 0) {
            Some(m) => if validate_version_metadata(m) { Some(m) } else { None },
            None => None,
        }
    }

    pub closed spec fn validate_static_metadata(m: JournalStaticMetadata, addr: int, len: nat) -> bool
    {
        &&& addr + JournalStaticMetadata::spec_size_of() <= m.committed_cdb_addr
        &&& m.committed_cdb_addr + u64::spec_size_of() <= m.journal_length_addr
        &&& m.journal_length_addr + u64::spec_size_of() + u64::spec_size_of() <= m.journal_data_start
        &&& m.journal_data_start + u64::spec_size_of() <= m.journal_data_end
        &&& m.journal_data_end <= m.app_static_area_start
        &&& m.app_static_area_start <= m.app_static_area_end
        &&& m.app_static_area_end <= m.app_dynamic_area_start
        &&& m.app_dynamic_area_start <= m.app_dynamic_area_end
        &&& m.app_dynamic_area_end <= len
        &&& opaque_aligned(m.committed_cdb_addr as int, const_persistence_chunk_size() as int)
    }

    pub closed spec fn recover_static_metadata(bytes: Seq<u8>, addr: int) -> Option<JournalStaticMetadata>
    {
        match recover_object::<JournalStaticMetadata>(bytes, addr) {
            Some(m) => if validate_static_metadata(m, addr, bytes.len()) { Some(m) } else { None },
            None => None,
        }
    }

    pub closed spec fn recover_app_static_area(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<Seq<u8>>
    {
        if sm.app_static_area_start <= sm.app_static_area_end && sm.app_static_area_end <= bytes.len() {
            Some(opaque_subrange(bytes, sm.app_static_area_start as int, sm.app_static_area_end as int))
        }
        else {
            None
        }
    }

    pub open spec fn recover_journal_data(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<Seq<u8>>
    {
        match recover_object::<u64>(bytes, sm.journal_length_addr as int) {
            None => None,
            Some(journal_length) => {
                if {
                    &&& 0 <= sm.journal_data_start
                    &&& sm.journal_data_start + journal_length + u64::spec_size_of() <= sm.journal_data_end
                    &&& sm.journal_data_end <= bytes.len()
                } {
                    let journal_data = opaque_section(bytes, sm.journal_data_start as int, journal_length as nat);
                    let journal_data_crc = opaque_section(bytes, sm.journal_data_start + journal_length,
                                                          u64::spec_size_of());
                    if journal_data_crc == spec_crc_bytes(journal_data) {
                        Some(journal_data)
                    }
                    else {
                        None
                    }
                }
                else {
                    None
                }
            },
        }
    }

    pub open spec fn parse_journal_data(journal_data: Seq<u8>, start: int) -> Option<Seq<JournalEntry>>
        decreases
            journal_data.len() - start
    {
        if !(0 <= start <= journal_data.len()) {
            None
        }
        else if journal_data.len() == start {
            Some(Seq::<JournalEntry>::empty())
        }
        else if start + u64::spec_size_of() + u64::spec_size_of() > journal_data.len() {
            None
        }
        else {
            let addr_bytes = opaque_section(journal_data, start, u64::spec_size_of());
            let addr = u64::spec_from_bytes(addr_bytes);
            let length_offset = start + u64::spec_size_of();
            let length_bytes = opaque_section(journal_data, length_offset, u64::spec_size_of());
            let length = u64::spec_from_bytes(length_bytes);
            let data_offset = length_offset + u64::spec_size_of();
            if data_offset + length > journal_data.len() {
                None
            }
            else {
                let data = opaque_section(journal_data, data_offset, length as nat);
                let entry = JournalEntry { addr: addr as int, bytes: data };
                match parse_journal_data(journal_data, data_offset + length) {
                    None => None,
                    Some(remaining_journal) => Some(seq![entry] + remaining_journal),
                }
            }
        }
    }

    pub open spec fn apply_journal_entry(bytes: Seq<u8>, entry: JournalEntry, sm: JournalStaticMetadata)
                                         -> Option<Seq<u8>>
    {
        if {
            &&& 0 <= sm.app_dynamic_area_start <= entry.addr
            &&& entry.addr + bytes.len() <= sm.app_dynamic_area_end
        } {
            Some(opaque_update_bytes(bytes, entry.addr, entry.bytes))
        }
        else {
            None
        }
    }

    pub open spec fn apply_journal_entries(bytes: Seq<u8>, entries: Seq<JournalEntry>, starting_entry: int,
                                           sm: JournalStaticMetadata) -> Option<Seq<u8>>
        decreases
            entries.len() - starting_entry
    {
        if starting_entry < 0 || starting_entry > entries.len() {
            None
        }
        else if entries.len() == starting_entry {
            Some(bytes)
        }
        else {
            match apply_journal_entry(bytes, entries[starting_entry], sm) {
                None => None,
                Some(updated_bytes) => apply_journal_entries(updated_bytes, entries, starting_entry + 1, sm),
            }
        }
    }

    pub closed spec fn recover_journal_case_committed(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<Seq<u8>>
    {
        match recover_journal_data(bytes, sm) {
            None => None,
            Some(journal_data) => {
                match parse_journal_data(journal_data, 0) {
                    None => None,
                    Some(journal_entries) => {
                        match apply_journal_entries(bytes, journal_entries, 0, sm) {
                            None => None,
                            Some(updated_bytes) => {
                                let app_bytes = opaque_subrange(updated_bytes, sm.app_dynamic_area_start as int,
                                                                sm.app_dynamic_area_end as int);
                                Some(app_bytes)
                            },
                        }
                    },
                }
            },
        }
    }

    #[verifier::opaque]
    pub open spec fn recover_journal(bytes: Seq<u8>) -> Option<Seq<u8>>
    {
        match recover_version_metadata(bytes) {
            None => None,
            Some(version_metadata) => {
                match recover_static_metadata(bytes, version_metadata.static_metadata_addr as int) {
                    None => None,
                    Some(sm) => {
                        match recover_cdb(bytes, sm.committed_cdb_addr as int) {
                            None => None,
                            Some(committed) => {
                                if committed {
                                    recover_journal_case_committed(bytes, sm)
                                }
                                else {
                                    Some(opaque_subrange(bytes, sm.app_dynamic_area_start as int, sm.app_dynamic_area_end as int))
                                }
                            },
                        }
                    },
                }
            },
        }
    }

    pub closed spec fn spec_space_needed_for_setup(
        max_journal_entries: usize,
        max_journaled_bytes: usize,
        app_static_area_size: usize,
        app_static_area_alignment: usize,
        app_dynamic_area_size: usize,
        app_dynamic_area_alignment: usize,
    ) -> int
        recommends
            0 < app_static_area_alignment,
            0 < app_dynamic_area_alignment,
    {
        let journal_size = max_journaled_bytes as int + // journal data
                           max_journal_entries * (u64::spec_size_of() as int +
                                                  u64::spec_size_of() as int) + // entry headers
                           u64::spec_size_of() as int; // journal CRC
        let version_addr: int = 0;
        let version_crc_addr = version_addr + JournalVersionMetadata::spec_size_of();
        let static_metadata_addr = round_up_to_alignment(version_crc_addr + u64::spec_size_of(),
                                                         JournalStaticMetadata::spec_align_of() as int);
        let static_crc_addr = static_metadata_addr + JournalStaticMetadata::spec_size_of();
        let committed_cdb_addr = round_up_to_alignment(static_crc_addr + u64::spec_size_of(),
                                                       const_persistence_chunk_size() as int);
        let journal_length_addr = committed_cdb_addr + u64::spec_size_of();
        let journal_length_crc_addr = journal_length_addr + u64::spec_size_of();
        let journal_data_start = journal_length_crc_addr + u64::spec_size_of();
        let journal_data_end = round_up_to_alignment(journal_data_start + journal_size,
                                                     app_static_area_alignment as int);
        let app_static_area_start = journal_data_end;
        let app_static_area_end = app_static_area_start + app_static_area_size;
        let app_dynamic_area_start = round_up_to_alignment(app_static_area_end, app_dynamic_area_alignment as int);
        let app_dynamic_area_end = app_dynamic_area_start + app_dynamic_area_size;
        app_dynamic_area_end
    }

    pub exec fn get_space_needed_for_setup(
        max_journal_entries: usize,
        max_journaled_bytes: usize,
        app_static_area_size: usize,
        app_static_area_alignment: usize,
        app_dynamic_area_size: usize,
        app_dynamic_area_alignment: usize,
    ) -> (result: Option<u64>)
        requires
            0 < app_static_area_alignment,
            0 < app_dynamic_area_alignment,
        ensures
            ({
                let space_needed = spec_space_needed_for_setup(
                    max_journal_entries, max_journaled_bytes,
                    app_static_area_size, app_static_area_alignment,
                    app_dynamic_area_size, app_dynamic_area_alignment
                );
                match result {
                    Some(v) => v == space_needed,
                    None => space_needed >= u64::MAX,
                }
            })
    {
        let max_journal_header_bytes = SaturatingU64::new(max_journal_entries as u64).mul(16);
        let journal_size = max_journal_header_bytes.add_usize(max_journaled_bytes).add(8);
        let version_addr = SaturatingU64::new(0);
        let version_crc_addr = version_addr.add_usize(size_of::<JournalVersionMetadata>());
        let static_metadata_addr = version_crc_addr.add_usize(size_of::<u64>())
                                                   .align(align_of::<JournalStaticMetadata>());
        let static_crc_addr = static_metadata_addr.add_usize(size_of::<JournalStaticMetadata>());
        let committed_cdb_addr = static_crc_addr.add_usize(size_of::<u64>()).align(persistence_chunk_size());
        let journal_length_addr = committed_cdb_addr.add_usize(size_of::<u64>());
        let journal_length_crc_addr = journal_length_addr.add_usize(size_of::<u64>());
        let journal_data_start = journal_length_crc_addr.add_usize(size_of::<u64>());
        let journal_data_end = journal_data_start.add_saturating_u64(&journal_size).align(app_static_area_alignment);
        let app_static_area_start = journal_data_end;
        let app_static_area_end = app_static_area_start.add_usize(app_static_area_size);
        let app_dynamic_area_start = app_static_area_end.align(app_dynamic_area_alignment);
        let app_dynamic_area_end = app_dynamic_area_start.add_usize(app_dynamic_area_size);

        assert(u64::spec_size_of() == 8) by {
            broadcast use pmcopy_axioms;
        }

        app_dynamic_area_end.to_option()
    }

    proof fn lemma_setup_works(bytes: Seq<u8>, vm: JournalVersionMetadata, sm: JournalStaticMetadata)
        requires
            validate_version_metadata(vm),
            validate_static_metadata(sm, vm.static_metadata_addr as int, bytes.len()),
            opaque_section(bytes, 0, JournalVersionMetadata::spec_size_of()) == vm.spec_to_bytes(),
        ensures
            recover_journal(bytes) matches Some(app_dynamic_area) && app_dynamic_area.len() == sm.app_dynamic_area_end - sm.app_dynamic_area_start,
    {
        assume(false);
    }

    pub exec fn setup<PM>(
        pm: &mut PM,
        app_version_number: u64,
        app_program_guid: u128,
        max_journal_entries: usize,
        max_journaled_bytes: usize,
        app_static_area_size: usize,
        app_static_area_alignment: usize,
        app_dynamic_area_size: usize,
        app_dynamic_area_alignment: usize,
    ) -> (result: Result<u64, JournalError>)
        where
            PM: PersistentMemoryRegion
        requires
            old(pm).inv(),
        ensures
            match result {
                Ok(app_dynamic_area_size) => {
                    &&& 0 < app_static_area_alignment
                    &&& 0 < app_dynamic_area_alignment
                    &&& pm@.flush_predicted()
                    &&& recover_journal(pm@.read_state) matches Some(app_dynamic_area)
                    &&& app_dynamic_area.len() == app_dynamic_area_size
                },
                Err(JournalError::InvalidAlignment) => {
                    ||| app_static_area_alignment == 0
                    ||| app_dynamic_area_alignment == 0
                },
                Err(JournalError::NotEnoughSpace) => {
                    let space_needed = spec_space_needed_for_setup(max_journal_entries, max_journaled_bytes,
                                                                   app_static_area_size, app_static_area_alignment,
                                                                   app_dynamic_area_size, app_dynamic_area_alignment);
                    &&& 0 < app_static_area_alignment
                    &&& 0 < app_dynamic_area_alignment
                    &&& pm@.len() < space_needed || space_needed >= u64::MAX
                },
                Err(_) => false,
            }
    {
        if app_static_area_alignment == 0 || app_dynamic_area_alignment == 0 {
            return Err(JournalError::InvalidAlignment);
        }

        broadcast use pmcopy_axioms;

        let max_journal_header_bytes = SaturatingU64::new(max_journal_entries as u64).mul(16);
        let journal_size = max_journal_header_bytes.add_usize(max_journaled_bytes).add(8);
        let version_addr = SaturatingU64::new(0);
        let version_crc_addr = version_addr.add_usize(size_of::<JournalVersionMetadata>());
        let static_metadata_addr = version_crc_addr.add_usize(size_of::<u64>())
                                                   .align(align_of::<JournalStaticMetadata>());
        let static_crc_addr = static_metadata_addr.add_usize(size_of::<JournalStaticMetadata>());
        let committed_cdb_addr = static_crc_addr.add_usize(size_of::<u64>()).align(persistence_chunk_size());
        let journal_length_addr = committed_cdb_addr.add_usize(size_of::<u64>());
        let journal_length_crc_addr = journal_length_addr.add_usize(size_of::<u64>());
        let journal_data_start = journal_length_crc_addr.add_usize(size_of::<u64>());
        let journal_data_end = journal_data_start.add_saturating_u64(&journal_size).align(app_static_area_alignment);
        let app_static_area_start = journal_data_end.clone();
        let app_static_area_end = app_static_area_start.add_usize(app_static_area_size);
        let app_dynamic_area_start = app_static_area_end.align(app_dynamic_area_alignment);
        let app_dynamic_area_end = app_dynamic_area_start.add_usize(app_dynamic_area_size);

        assert(u64::spec_size_of() == 8) by {
            broadcast use pmcopy_axioms;
        }
        
        if app_dynamic_area_end.is_saturated() {
            return Err(JournalError::NotEnoughSpace);
        }
        if app_dynamic_area_end.unwrap() > pm.get_region_size() {
            return Err(JournalError::NotEnoughSpace);
        }
        assert(app_dynamic_area_end.unwrap() <= pm@.len());

        let version_addr = version_addr.unwrap();
        let version_crc_addr = version_crc_addr.unwrap();
        let static_metadata_addr = static_metadata_addr.unwrap();
        let static_crc_addr = static_crc_addr.unwrap();
        let committed_cdb_addr = committed_cdb_addr.unwrap();
        let journal_length_addr = journal_length_addr.unwrap();
        let journal_length_crc_addr = journal_length_crc_addr.unwrap();
        let journal_data_start = journal_data_start.unwrap();
        let journal_data_end = journal_data_end.unwrap();
        let app_static_area_start = app_static_area_start.unwrap();
        let app_static_area_end = app_static_area_end.unwrap();
        let app_dynamic_area_start = app_dynamic_area_start.unwrap();
        let app_dynamic_area_end = app_dynamic_area_end.unwrap();

        let vm = JournalVersionMetadata{
            version_number: JOURNAL_PROGRAM_VERSION_NUMBER,
            static_metadata_addr,
            program_guid: JOURNAL_PROGRAM_GUID
        };
        pm.serialize_and_write(version_addr, &vm);
        let sm = JournalStaticMetadata{
            app_version_number,
            app_program_guid,
            committed_cdb_addr,
            journal_length_addr,
            journal_data_start,
            journal_data_end,
            app_static_area_start,
            app_static_area_end,
            app_dynamic_area_start,
            app_dynamic_area_end,
        };
        pm.serialize_and_write(static_metadata_addr, &sm);
        let committed_cdb = CDB_FALSE;
        pm.serialize_and_write(committed_cdb_addr, &committed_cdb);

        pm.flush();

        proof {
            lemma_auto_can_result_from_partial_write_effect_on_opaque();
            assume(false);
            lemma_setup_works(pm@.read_state, vm, sm);
        }
        Ok(app_dynamic_area_end - app_dynamic_area_start)
    }
}
