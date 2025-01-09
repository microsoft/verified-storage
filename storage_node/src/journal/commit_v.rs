use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::size_of;
use crate::pmem::wrpm_t::*;
use crate::common::align_v::*;
use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use deps_hack::PmCopy;
use super::*;
use super::entry_v::*;
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
    #[inline]
    exec fn write_journal_entry(
        &mut self,
        Tracked(perm): Tracked<&Perm>,
        Ghost(original_durable_state): Ghost<Seq<u8>>,
        Ghost(original_read_state): Ghost<Seq<u8>>,
        current_entry_index: usize,
        current_pos: u64,
        crc_digest: &mut CrcDigest,
    ) -> (next_pos: u64)
        where
            PM: PersistentMemoryRegion,
            Perm: CheckPermission<Seq<u8>>,
        requires
            old(self).inv(),
            old(self).status@ is WritingJournal,
            forall|s: Seq<u8>| spec_recovery_equivalent_for_app(s, original_durable_state)
                ==> #[trigger] perm.check_permission(s),
            recovers_to(original_durable_state, old(self).vm@, old(self).sm, old(self).constants),
            old(self).sm.journal_entries_start <= current_pos <= old(self).wrpm@.read_state.len(),
            parse_journal_entries(
                old(self).wrpm@.read_state.subrange(old(self).sm.journal_entries_start as int, current_pos as int)
            ) == Some(old(self).entries@.take(current_entry_index as int)),
            0 <= current_entry_index < old(self).entries@.len(),
            current_pos == old(self).sm.journal_entries_start +
                           space_needed_for_journal_entries_list(old(self).entries@.take(current_entry_index as int)),
            seqs_match_in_range(original_durable_state, old(self).wrpm@.durable_state,
                                  old(self).sm.app_area_start as int, old(self).sm.app_area_end as int),
            seqs_match_in_range(original_read_state, old(self).wrpm@.read_state,
                                  old(self).sm.app_area_start as int, old(self).sm.app_area_end as int),
            old(crc_digest).bytes_in_digest() ==
                old(self).wrpm@.read_state.subrange(old(self).sm.journal_entries_start as int, current_pos as int),
        ensures
            self.inv(),
            self == (Self{
                wrpm: self.wrpm,
                ..*old(self)
            }),
            self.wrpm.constants() == old(self).wrpm.constants(),
            next_pos == current_pos + self.entries@[current_entry_index as int].space_needed(),
            seqs_match_in_range(original_durable_state, self.wrpm@.durable_state,
                                  self.sm.app_area_start as int, self.sm.app_area_end as int),
            seqs_match_in_range(original_read_state, self.wrpm@.read_state,
                                self.sm.app_area_start as int, self.sm.app_area_end as int),
            parse_journal_entries(self.wrpm@.read_state.subrange(self.sm.journal_entries_start as int,
                                                                 next_pos as int))
                == Some(self.entries@.take(current_entry_index + 1)),
            current_pos < next_pos <= self.sm.journal_entries_start + self.journal_length,
            next_pos == self.sm.journal_entries_start +
                       space_needed_for_journal_entries_list(self.entries@.take(current_entry_index + 1)),
            next_pos == self.sm.journal_entries_start + self.journal_length
                <==> current_entry_index == self.entries@.len() - 1,
            crc_digest.bytes_in_digest() ==
                self.wrpm@.read_state.subrange(self.sm.journal_entries_start as int, next_pos as int),
    {
        broadcast use axiom_bytes_len;
        broadcast use group_can_result_from_write_effect;
        
        let entry: &ConcreteJournalEntry = &self.entries.entries[current_entry_index];
        let num_bytes: u64 = entry.bytes_to_write.len() as u64;

        assert({
            &&& current_pos + entry@.space_needed() ==
                self.sm.journal_entries_start +
                space_needed_for_journal_entries_list(self.entries@.take(current_entry_index + 1))
            &&& 0 <= current_pos
            &&& current_pos + entry@.space_needed() <= self.sm.journal_entries_start + self.journal_length
            &&& current_pos + entry@.space_needed() == self.sm.journal_entries_start + self.journal_length <==>
                 current_entry_index == self.entries@.len() - 1
        }) by {
            lemma_space_needed_for_journal_entries_list_increases(self.entries@, current_entry_index as int);
            lemma_space_needed_for_journal_entries_list_at_least_num_entries(
                self.entries@.take(current_entry_index as int));
            lemma_space_needed_for_journal_entries_list_monotonic(self.entries@, current_entry_index + 1,
                                                             self.entries@.len() as int);
            if current_entry_index < self.entries@.len() - 1 {
                lemma_space_needed_for_journal_entries_list_increases(self.entries@, current_entry_index + 1);
                lemma_space_needed_for_journal_entries_list_monotonic(self.entries@, current_entry_index + 1,
                                                                 current_entry_index + 2);
                lemma_space_needed_for_journal_entries_list_monotonic(self.entries@, current_entry_index + 2,
                                                                 self.entries@.len() as int);
            }
            assert(self.entries@ =~= self.entries@.take(self.entries@.len() as int));
            assert(entry@ == self.entries@[current_entry_index as int]);
        }

        // First, write the `start` field of the entry, which is the address that the entry
        // is referring to, to the next position in the journal.
    
        self.wrpm.serialize_and_write::<u64>(current_pos, &entry.start, Tracked(perm));
        crc_digest.write(&entry.start);
        assert(crc_digest.bytes_in_digest() ==
               self.wrpm@.read_state.subrange(self.sm.journal_entries_start as int,
                                              current_pos + u64::spec_size_of())) by {
            lemma_concatenate_subranges(self.wrpm@.read_state, self.sm.journal_entries_start as int,
                                        current_pos as int, current_pos + u64::spec_size_of());
        }
    
        // Next, write the `num_bytes` field of the entry.
    
        let num_bytes_addr = current_pos + size_of::<u64>() as u64;
        self.wrpm.serialize_and_write::<u64>(num_bytes_addr, &num_bytes, Tracked(perm));
        crc_digest.write(&num_bytes);
        assert(crc_digest.bytes_in_digest() ==
               self.wrpm@.read_state.subrange(self.sm.journal_entries_start as int,
                                              num_bytes_addr + u64::spec_size_of())) by {
            lemma_concatenate_subranges(self.wrpm@.read_state, self.sm.journal_entries_start as int,
                                        num_bytes_addr as int, num_bytes_addr + u64::spec_size_of());
        }
    
        // Next, write the `bytes_to_write` field of the entry.
    
        let bytes_to_write_addr = num_bytes_addr + size_of::<u64>() as u64;
        let bytes_to_write_as_slice = entry.bytes_to_write.as_slice();
        self.wrpm.write(bytes_to_write_addr, bytes_to_write_as_slice, Tracked(perm));
        crc_digest.write_bytes(bytes_to_write_as_slice);
        assert(crc_digest.bytes_in_digest() ==
                  self.wrpm@.read_state.subrange(self.sm.journal_entries_start as int,
                                                 bytes_to_write_addr + num_bytes)) by {
            lemma_concatenate_subranges(self.wrpm@.read_state, self.sm.journal_entries_start as int,
                                        bytes_to_write_addr as int, bytes_to_write_addr + num_bytes);
        }
    
        let next_pos = bytes_to_write_addr + num_bytes;
        assert(parse_journal_entries(self.wrpm@.read_state.subrange(self.sm.journal_entries_start as int,
                                                                    next_pos as int))
                == Some(self.entries@.take(current_entry_index + 1))) by {
            let old_entries_bytes = self.wrpm@.read_state.subrange(self.sm.journal_entries_start as int,
                                                                   current_pos as int);
            let new_entries_bytes = self.wrpm@.read_state.subrange(self.sm.journal_entries_start as int,
                                                                   next_pos as int);
            assert(old_entries_bytes ==
                   old(self).wrpm@.read_state.subrange(self.sm.journal_entries_start as int,
                                                     current_pos as int)) by {
            }
            assert(new_entries_bytes =~= old_entries_bytes + entry.start.spec_to_bytes()
                                         + num_bytes.spec_to_bytes() + entry.bytes_to_write@);
            assert(parse_journal_entries(new_entries_bytes) ==
                   Some(self.entries@.take(current_entry_index as int).push(entry@))) by {
                lemma_parse_journal_entries_append(old_entries_bytes,
                                                   self.entries@.take(current_entry_index as int), entry@);
            }
            assert(self.entries@.take(current_entry_index as int).push(entry@) =~=
                   self.entries@.take(current_entry_index + 1));
        }

        proof {
            lemma_apply_journal_entries_doesnt_change_size(self@.read_state, self.entries@, self.sm);
        }

        next_pos
    }

    #[inline]
    exec fn write_journal_entries(
        &mut self,
        Tracked(perm): Tracked<&Perm>,
    ) -> (journal_entries_crc: u64)
        where
            PM: PersistentMemoryRegion,
            Perm: CheckPermission<Seq<u8>>,
        requires
            old(self).inv(),
            old(self).status@ is WritingJournal,
            forall|s: Seq<u8>| spec_recovery_equivalent_for_app(s, old(self).wrpm@.durable_state)
                ==> #[trigger] perm.check_permission(s),
        ensures
            self.inv(),
            self == (Self{
                wrpm: self.wrpm,
                ..*old(self)
            }),
            self.wrpm.constants() == old(self).wrpm.constants(),
            seqs_match_in_range(old(self).wrpm@.durable_state, self.wrpm@.durable_state,
                                  self.sm.app_area_start as int, self.sm.app_area_end as int),
            seqs_match_in_range(old(self).wrpm@.read_state, self.wrpm@.read_state,
                                  self.sm.app_area_start as int, self.sm.app_area_end as int),
            parse_journal_entries(extract_section(self.wrpm@.read_state, self.sm.journal_entries_start as int,
                                                 self.journal_length as nat))
                == Some(self.entries@),
            journal_entries_crc ==
                spec_crc_u64(extract_section(self.wrpm@.read_state, self.sm.journal_entries_start as int,
                                            self.journal_length as nat)),
    {
        let mut current_entry_index: usize = 0;
        let mut current_pos = self.sm.journal_entries_start;
        let end_pos = current_pos + self.journal_length;
        let ghost original_durable_state = self.wrpm@.durable_state;
        let ghost original_read_state = self.wrpm@.read_state;
        assert(self.wrpm@.read_state.subrange(self.sm.journal_entries_start as int, current_pos as int)
               =~= Seq::<u8>::empty());
        assert(self.entries@.take(current_entry_index as int) =~= Seq::<JournalEntry>::empty());
        let mut crc_digest = CrcDigest::new();
        proof {
            lemma_space_needed_for_journal_entries_list_zero_iff_journal_empty(self.entries@);
        }
        while current_pos < end_pos
            invariant
                self.inv(),
                self.status@ is WritingJournal,
                self.wrpm.constants() == old(self).wrpm.constants(),
                end_pos == self.sm.journal_entries_start + self.journal_length,
                forall|s: Seq<u8>| spec_recovery_equivalent_for_app(s, original_durable_state)
                    ==> #[trigger] perm.check_permission(s),
                recovers_to(original_durable_state, self.vm@, self.sm, self.constants),
                parse_journal_entries(
                    self.wrpm@.read_state.subrange(self.sm.journal_entries_start as int, current_pos as int)
                ) == Some(self.entries@.take(current_entry_index as int)),
                0 <= current_entry_index <= self.entries@.len(),
                self.sm.journal_entries_start <= current_pos <= end_pos,
                current_pos == end_pos <==> current_entry_index == self.entries@.len(),
                current_pos == self.sm.journal_entries_start +
                               space_needed_for_journal_entries_list(self.entries@.take(current_entry_index as int)),
                seqs_match_in_range(original_durable_state, self.wrpm@.durable_state,
                                  self.sm.app_area_start as int, self.sm.app_area_end as int),
                seqs_match_in_range(original_read_state, self.wrpm@.read_state,
                self.sm.app_area_start as int, self.sm.app_area_end as int),
                self == (Self{ wrpm: self.wrpm, ..*old(self) }),
                crc_digest.bytes_in_digest() ==
                    self.wrpm@.read_state.subrange(self.sm.journal_entries_start as int, current_pos as int),
        {
            current_pos = self.write_journal_entry(Tracked(perm),
                                                   Ghost(original_durable_state), Ghost(original_read_state),
                                                   current_entry_index, current_pos,
                                                   &mut crc_digest);
            assert(current_entry_index < u64::MAX) by {
                lemma_space_needed_for_journal_entries_list_at_least_num_entries(self.entries@);
            }
            current_entry_index = current_entry_index + 1;
        }
        assert(self.entries@ == self.entries@.take(current_entry_index as int));
        crc_digest.sum64()
    }

    exec fn write_journal_metadata(
        &mut self,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            PM: PersistentMemoryRegion,
            Perm: CheckPermission<Seq<u8>>,
        requires
            old(self).inv(),
            old(self).status@ is WritingJournal,
            forall|s: Seq<u8>| spec_recovery_equivalent_for_app(s, old(self).wrpm@.durable_state)
                ==> #[trigger] perm.check_permission(s),
        ensures
            self.inv(),
            self.wrpm.constants() == old(self).wrpm.constants(),
            self == (Self{
                wrpm: self.wrpm,
                ..*old(self)
            }),
            self.wrpm@.flush_predicted(),
            seqs_match_in_range(old(self).wrpm@.durable_state, self.wrpm@.durable_state,
                                self.sm.app_area_start as int, self.sm.app_area_end as int),
            seqs_match_in_range(old(self).wrpm@.read_state, self.wrpm@.read_state,
                                self.sm.app_area_start as int, self.sm.app_area_end as int),
            recover_journal_length(self.wrpm@.read_state, self.sm) == Some(self.journal_length),
            recover_journal_entries(self.wrpm@.read_state, self.sm, self.journal_length) == Some(self.entries@),
    {
        broadcast use group_can_result_from_write_effect;
        broadcast use pmcopy_axioms;

        let journal_length_crc = {
            let mut digest = CrcDigest::new();
            digest.write(&self.journal_length);
            digest.sum64()
        };

        let journal_entries_crc = self.write_journal_entries(Tracked(perm));
        self.wrpm.serialize_and_write::<u64>(self.sm.journal_length_start, &self.journal_length, Tracked(perm));
        self.wrpm.serialize_and_write::<u64>(self.sm.journal_length_crc_start, &journal_length_crc, Tracked(perm));
        self.wrpm.serialize_and_write::<u64>(self.sm.journal_entries_crc_start, &journal_entries_crc, Tracked(perm));
        self.wrpm.flush();

        proof {
            lemma_apply_journal_entries_doesnt_change_size(self@.read_state, self.entries@, self.sm);
        }
    }

    exec fn mark_journal_committed(
        &mut self,
        Ghost(original_durable_state): Ghost<Seq<u8>>,
        Ghost(original_read_state): Ghost<Seq<u8>>,
        Ghost(original_commit_state): Ghost<Seq<u8>>,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            PM: PersistentMemoryRegion,
            Perm: CheckPermission<Seq<u8>>,
        requires
            old(self).inv(),
            old(self).status@ is WritingJournal,
            old(self).wrpm@.flush_predicted(),
            recovers_to(original_durable_state, old(self).vm@, old(self).sm, old(self).constants),
            seqs_match_except_in_range(original_durable_state, original_read_state,
                                       old(self).sm.app_area_start as int, old(self).sm.app_area_end as int),
            seqs_match_in_range(original_durable_state, old(self).wrpm@.durable_state,
                                old(self).sm.app_area_start as int, old(self).sm.app_area_end as int),
            seqs_match_in_range(original_read_state, old(self).wrpm@.read_state,
                                old(self).sm.app_area_start as int, old(self).sm.app_area_end as int),
            apply_journal_entries(original_read_state, old(self).entries@, old(self).sm) == Some(original_commit_state),
            recover_committed_cdb(original_read_state, old(self).sm) == Some(false),
            recovers_to(original_read_state, old(self).vm@, old(self).sm, old(self).constants),
            recover_journal_length(old(self).wrpm@.read_state, old(self).sm) == Some(old(self).journal_length),
            recover_journal_entries(old(self).wrpm@.read_state, old(self).sm, old(self).journal_length) ==
                Some(old(self).entries@),
            forall|s: Seq<u8>| spec_recovery_equivalent_for_app(s, original_durable_state)
                ==> #[trigger] perm.check_permission(s),
            forall|s: Seq<u8>| spec_recovery_equivalent_for_app(s, original_commit_state)
                ==> #[trigger] perm.check_permission(s),
            recovers_to(original_commit_state, old(self).vm@, old(self).sm, old(self).constants),
        ensures
            self.inv(),
            self.wrpm.constants() == old(self).wrpm.constants(),
            self == (Self{
                status: Ghost(JournalStatus::Committed),
                wrpm: self.wrpm,
                ..*old(self)
            }),
            seqs_match_in_range(original_durable_state, self.wrpm@.durable_state,
                                self.sm.app_area_start as int, self.sm.app_area_end as int),
            seqs_match_in_range(original_read_state, self.wrpm@.read_state,
                                self.sm.app_area_start as int, self.sm.app_area_end as int),
            self.wrpm@.flush_predicted(),
            recover_committed_cdb(self.wrpm@.read_state, self.sm) == Some(true),
            recover_journal_length(self.wrpm@.read_state, self.sm) == Some(self.journal_length),
            recover_journal_entries(self.wrpm@.read_state, self.sm, self.journal_length) == Some(self.entries@),
            ({
                &&& recover_journal(self.wrpm@.read_state) matches Some(j)
                &&& j.constants == self.constants
                &&& seqs_match_in_range(j.state, original_commit_state, self.sm.app_area_start as int,
                                      self.sm.app_area_end as int)
            }),
    {
        broadcast use group_update_bytes_effect;
        broadcast use pmcopy_axioms;

        let cdb = CDB_TRUE;
        
        let ghost desired_state = update_bytes(self.wrpm@.durable_state, self.sm.committed_cdb_start as int,
                                               cdb.spec_to_bytes());
        assert({
            &&& recover_journal(desired_state) matches Some(j)
            &&& j.constants == self.constants
            &&& seqs_match_in_range(j.state, original_commit_state, self.sm.app_area_start as int,
                                  self.sm.app_area_end as int)
        }) by {
            let s = desired_state;
            assert(recover_committed_cdb(s, self.sm) == Some(true));
            assert(recover_storage_state(s, self.sm) == apply_journal_entries(s, self.entries@, self.sm));
            lemma_apply_journal_entries_maintains_matching_app_areas(original_read_state, s, self.vm@,
                                                                     self.sm, self.entries@);
        }

        assert forall |s| #[trigger] can_result_from_partial_write(s, self.wrpm@.durable_state,
                                                              self.sm.committed_cdb_start as int,
                                                              cdb.spec_to_bytes())
            implies perm.check_permission(s) by {
            assert(s == self.wrpm@.durable_state || s == desired_state) by {
                assert(self.sm.committed_cdb_start as int % const_persistence_chunk_size() == 0);
                lemma_only_two_crash_states_introduced_by_aligned_chunk_write(s, self.wrpm@.durable_state,
                                                                              self.sm.committed_cdb_start as int,
                                                                              cdb.spec_to_bytes());
            }
        }

        self.wrpm.serialize_and_write::<u64>(self.sm.committed_cdb_start, &cdb, Tracked(perm));
        self.wrpm.flush();
        assert(self.wrpm@.read_state == desired_state);
        self.status = Ghost(JournalStatus::Committed);
    }

    #[inline]
    exec fn install_journal_entry_during_commit(
        &mut self,
        num_entries_installed: usize,
        Ghost(original_read_state): Ghost<Seq<u8>>,
        Ghost(original_commit_state): Ghost<Seq<u8>>,
        Ghost(desired_commit_state): Ghost<Seq<u8>>,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            PM: PersistentMemoryRegion,
            Perm: CheckPermission<Seq<u8>>,
        requires
            old(self).inv(),
            old(self).status@ is Committed,
            num_entries_installed < old(self).entries@.len(),
            recover_version_metadata(original_read_state) == Some(old(self).vm@),
            recover_static_metadata(original_read_state, old(self).vm@) == Some(old(self).sm),
            recover_committed_cdb(original_read_state, old(self).sm) == Some(true),
            recover_journal_length(original_read_state, old(self).sm) == Some(old(self).journal_length),
            recover_journal_entries(original_read_state, old(self).sm, old(self).journal_length)
                == Some(old(self).entries@),
            journal_entries_valid(old(self).entries@, old(self).sm),
            apply_journal_entries(original_read_state, old(self).entries@, old(self).sm) is Some,
            recover_journal(original_read_state) is Some,
            recover_version_metadata(old(self).wrpm@.durable_state) == Some(old(self).vm@),
            recover_static_metadata(old(self).wrpm@.durable_state, old(self).vm@) == Some(old(self).sm),
            recover_committed_cdb(old(self).wrpm@.durable_state, old(self).sm) == Some(true),
            recover_journal_length(old(self).wrpm@.durable_state, old(self).sm) == Some(old(self).journal_length),
            recover_journal_entries(old(self).wrpm@.durable_state, old(self).sm, old(self).journal_length)
                == Some(old(self).entries@),
            recover_journal(old(self).wrpm@.durable_state) == recover_journal(original_read_state),
            forall|s: Seq<u8>| spec_recovery_equivalent_for_app(s, original_commit_state)
                ==> #[trigger] perm.check_permission(s),
            seqs_match_except_in_range(original_read_state, old(self).wrpm@.durable_state,
                                       old(self).sm.app_area_start as int, old(self).sm.app_area_end as int),
            seqs_match_except_in_range(original_read_state, old(self).wrpm@.read_state,
                                       old(self).sm.app_area_start as int, old(self).sm.app_area_end as int),
            apply_journal_entries(old(self).wrpm@.read_state, old(self).entries@.skip(num_entries_installed as int),
                                  old(self).sm) == Some(desired_commit_state),
            desired_commit_state == apply_journal_entries(original_read_state, old(self).entries@, old(self).sm).unwrap(),
            seqs_match_in_range(original_commit_state, desired_commit_state,
                                old(self).sm.app_area_start as int, old(self).sm.app_area_end as int),
            recovers_to(original_commit_state, old(self).vm@, old(self).sm, old(self).constants),
        ensures
            self.inv(),
            self == (Self{
                wrpm: self.wrpm,
                ..*old(self)
            }),
            self.wrpm.constants() == old(self).wrpm.constants(),
            journal_entries_valid(self.entries@, self.sm),
            apply_journal_entries(original_read_state, self.entries@, self.sm) is Some,
            recover_version_metadata(self.wrpm@.durable_state) == Some(self.vm@),
            recover_static_metadata(self.wrpm@.durable_state, self.vm@) == Some(self.sm),
            recover_committed_cdb(self.wrpm@.durable_state, self.sm) == Some(true),
            recover_journal_length(self.wrpm@.durable_state, self.sm) == Some(self.journal_length),
            recover_journal_entries(self.wrpm@.durable_state, self.sm, self.journal_length) == Some(self.entries@),
            recover_journal(self.wrpm@.durable_state) == recover_journal(original_read_state),
            seqs_match_except_in_range(original_read_state, self.wrpm@.durable_state,
                                       self.sm.app_area_start as int, self.sm.app_area_end as int),
            seqs_match_except_in_range(original_read_state, self.wrpm@.read_state,
                                       self.sm.app_area_start as int, self.sm.app_area_end as int),
            apply_journal_entries(self.wrpm@.read_state, self.entries@.skip(num_entries_installed + 1), self.sm)
                == Some(desired_commit_state),
    {
        broadcast use group_can_result_from_write_effect;
            
        let entry: &ConcreteJournalEntry = &self.entries.entries[num_entries_installed];
        let ghost entries_bytes = recover_journal_entries_bytes(self.wrpm@.durable_state, self.sm,
                                                                self.journal_length).unwrap();
        assert(parse_journal_entries(entries_bytes) == Some(self.entries@));
        
        proof {
            lemma_addresses_in_entry_dont_affect_recovery(self.wrpm@.durable_state, self.vm@, self.sm,
                                                          entries_bytes, self.entries@, num_entries_installed as int);
            assert(entry@.fits(self.sm)) by {
                lemma_journal_entries_valid_implies_one_valid(self.entries@, self.sm, num_entries_installed as int);
            }
            assert forall|s| can_result_from_partial_write(s, self.wrpm@.durable_state, entry.start as int,
                                                      entry.bytes_to_write@)
                implies #[trigger] perm.check_permission(s) by {
                lemma_if_addresses_unreachable_in_recovery_then_recovery_unchanged_by_write(
                    s, self.wrpm@.durable_state, entry.start as int, entry.bytes_to_write@,
                    entry@.addrs(),
                    |s| recover_journal(s),
                );
                assert(recover_journal(s) == recover_journal(self.wrpm@.durable_state));
            }
        }
        self.wrpm.write(entry.start, entry.bytes_to_write.as_slice(), Tracked(perm));
        proof {
            assert(recover_journal(self.wrpm@.durable_state) == recover_journal(old(self).wrpm@.durable_state)) by {
                lemma_if_addresses_unreachable_in_recovery_then_recovery_unchanged_by_write(
                    self.wrpm@.durable_state, old(self).wrpm@.durable_state, entry.start as int, entry.bytes_to_write@,
                    entry@.addrs(),
                    |s| recover_journal(s),
                );
            }
            assert(Some(self.wrpm@.read_state) == apply_journal_entry(old(self).wrpm@.read_state, entry@, self.sm));
            assert(recover_journal(self.wrpm@.durable_state) == recover_journal(old(self).wrpm@.durable_state));
            assert(recover_journal_length(self.wrpm@.durable_state, self.sm) == Some(self.journal_length));
    
            assert(self.entries@.skip(num_entries_installed as int)[0] =~= self.entries@[num_entries_installed as int]);
            assert(self.entries@.skip(num_entries_installed as int).skip(1)
                   =~= self.entries@.skip(num_entries_installed + 1));
            lemma_apply_journal_entries_doesnt_change_size(self@.read_state, self.entries@, self.sm);
        }
    }

    exec fn install_journal_entries_during_commit(
        &mut self,
        Ghost(original_commit_state): Ghost<Seq<u8>>,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            PM: PersistentMemoryRegion,
            Perm: CheckPermission<Seq<u8>>,
        requires
            old(self).inv(),
            old(self).status@ is Committed,
            old(self).wrpm@.flush_predicted(),
            recover_journal_length(old(self).wrpm@.read_state, old(self).sm) == Some(old(self).journal_length),
            recover_journal_entries(old(self).wrpm@.read_state, old(self).sm, old(self).journal_length)
                == Some(old(self).entries@),
            ({
                &&& recover_journal(old(self).wrpm@.read_state) matches Some(j)
                &&& j.constants == old(self).constants
                &&& seqs_match_in_range(j.state, original_commit_state, old(self).sm.app_area_start as int,
                                      old(self).sm.app_area_end as int)
            }),
            recovers_to(original_commit_state, old(self).vm@, old(self).sm, old(self).constants),
            forall|s: Seq<u8>| spec_recovery_equivalent_for_app(s, original_commit_state)
                ==> #[trigger] perm.check_permission(s),
        ensures
            self.inv(),
            self == (Self{
                wrpm: self.wrpm,
                ..*old(self)
            }),
            self.wrpm.constants() == old(self).wrpm.constants(),
            self.wrpm@.flush_predicted(),
            seqs_match_in_range(self.wrpm@.read_state, original_commit_state, self.sm.app_area_start as int,
                                self.sm.app_area_end as int),
            ({
                &&& recover_journal(self.wrpm@.read_state) matches Some(j)
                &&& j.constants == self.constants
                &&& j.state == self.wrpm@.read_state
            }),
    {
        let mut num_entries_installed: usize = 0;
        let end: usize = self.entries.len();
        let ghost desired_commit_state = apply_journal_entries(self.wrpm@.read_state, self.entries@, self.sm).unwrap();
    
        assert(self.entries@.skip(0) =~= self.entries@);
    
        while num_entries_installed < end
            invariant
                self.inv(),
                self.status@ is Committed,
                num_entries_installed <= end == self.entries@.len(),
                recover_version_metadata(old(self).wrpm@.read_state) == Some(self.vm@),
                recover_static_metadata(old(self).wrpm@.read_state, self.vm@) == Some(self.sm),
                recover_committed_cdb(old(self).wrpm@.read_state, self.sm) == Some(true),
                recover_journal_length(old(self).wrpm@.read_state, self.sm) == Some(self.journal_length),
                recover_journal_entries(old(self).wrpm@.read_state, self.sm, self.journal_length) == Some(self.entries@),
                journal_entries_valid(self.entries@, self.sm),
                apply_journal_entries(old(self).wrpm@.read_state, self.entries@, self.sm) is Some,
                recover_journal(old(self).wrpm@.read_state) is Some,
                recover_version_metadata(self.wrpm@.durable_state) == Some(self.vm@),
                recover_static_metadata(self.wrpm@.durable_state, self.vm@) == Some(self.sm),
                recover_committed_cdb(self.wrpm@.durable_state, self.sm) == Some(true),
                recover_journal_length(self.wrpm@.durable_state, self.sm) == Some(self.journal_length),
                recover_journal_entries(self.wrpm@.durable_state, self.sm, self.journal_length) == Some(self.entries@),
                recover_journal(self.wrpm@.durable_state) == recover_journal(old(self).wrpm@.read_state),
                forall|s: Seq<u8>| spec_recovery_equivalent_for_app(s, original_commit_state)
                    ==> #[trigger] perm.check_permission(s),
                seqs_match_except_in_range(old(self).wrpm@.read_state, self.wrpm@.durable_state,
                                           self.sm.app_area_start as int, self.sm.app_area_end as int),
                seqs_match_except_in_range(old(self).wrpm@.read_state, self.wrpm@.read_state,
                                           self.sm.app_area_start as int, self.sm.app_area_end as int),
                apply_journal_entries(self.wrpm@.read_state, self.entries@.skip(num_entries_installed as int), self.sm)
                    == Some(desired_commit_state),
                desired_commit_state ==
                    apply_journal_entries(old(self).wrpm@.read_state, self.entries@, self.sm).unwrap(),
                seqs_match_in_range(original_commit_state, desired_commit_state,
                                    self.sm.app_area_start as int, self.sm.app_area_end as int),
                recovers_to(original_commit_state, old(self).vm@, old(self).sm, old(self).constants),
                self == (Self{ wrpm: self.wrpm, ..*old(self) }),
                self.wrpm.constants() == old(self).wrpm.constants(),
        {
            let ghost durable_state_at_start_of_loop = self.wrpm@.durable_state;
    
            self.install_journal_entry_during_commit(num_entries_installed, Ghost(old(self).wrpm@.read_state),
                                                     Ghost(original_commit_state), Ghost(desired_commit_state),
                                                     Tracked(perm));
            assert(self.entries@.skip(num_entries_installed as int)
                   =~= seq![self.entries@[num_entries_installed as int]]
                       + self.entries@.skip(num_entries_installed + 1));

            num_entries_installed = num_entries_installed + 1;
        }

        self.wrpm.flush();
    }

    proof fn lemma_commit_initial_conditions(&self)
        requires
            self.valid(),
        ensures
            apply_journal_entries(self.wrpm@.read_state, self.entries@, self.sm) is Some,
            recover_committed_cdb(self.wrpm@.read_state, self.sm) == Some(false),
            recovers_to(self.wrpm@.read_state, self.vm@, self.sm, self.constants),
            recovers_to(self@.commit_state, self.vm@, self.sm, self.constants),
    {
        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        
        lemma_apply_journal_entries_some_iff_journal_entries_valid(self.wrpm@.read_state, self.entries@, self.sm);
        assert({
            &&& recover_committed_cdb(self.wrpm@.read_state, self.sm) == Some(false)
            &&& recovers_to(self.wrpm@.read_state, self.vm@, self.sm, self.constants)
        }) by {
            assert(recover_version_metadata(self.wrpm@.durable_state) ==
                   recover_version_metadata(self.wrpm@.read_state));
            assert(recover_static_metadata(self.wrpm@.durable_state, self.vm@) ==
                   recover_static_metadata(self.wrpm@.read_state, self.vm@));
            assert(recover_committed_cdb(self.wrpm@.durable_state, self.sm) ==
                   recover_committed_cdb(self.wrpm@.read_state, self.sm));
        }

        assert(recovers_to(self@.commit_state, self.vm@, self.sm, self.constants)) by {
            lemma_apply_journal_entries_only_affects_app_area(self.wrpm@.read_state, self.vm@, self.sm, self.entries@);
            assert(recover_version_metadata(self.wrpm@.read_state) == recover_version_metadata(self@.commit_state));
            assert(recover_static_metadata(self.wrpm@.read_state, self.vm@) ==
                   recover_static_metadata(self@.commit_state, self.vm@));
            assert(recover_committed_cdb(self.wrpm@.read_state, self.sm) ==
                   recover_committed_cdb(self@.commit_state, self.sm));
        }
    }

    pub exec fn commit(&mut self, Tracked(perm): Tracked<&Perm>)
        requires
            old(self).valid(),
            forall|s: Seq<u8>| Self::recovery_equivalent_for_app(s, old(self)@.durable_state)
                ==> #[trigger] perm.check_permission(s),
            forall|s: Seq<u8>| Self::recovery_equivalent_for_app(s, old(self)@.commit_state)
                ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(),
            self@.valid(),
            self@.constants == old(self)@.constants,
            self.recover_successful(),
            self@ == (JournalView{
                durable_state: self@.commit_state,
                read_state: self@.commit_state,
                commit_state: self@.commit_state,
                remaining_capacity: self@.constants.journal_capacity as int,
                journaled_addrs: Set::<int>::empty(),
                ..old(self)@
            }),
            seqs_match_in_range(old(self)@.commit_state, self@.commit_state, self@.constants.app_area_start as int,
                                self@.constants.app_area_end as int),
    {
        proof {
            self.lemma_commit_initial_conditions();
        }
        self.status = Ghost(JournalStatus::WritingJournal);
        self.write_journal_metadata(Tracked(perm));
        self.mark_journal_committed(Ghost(old(self).wrpm@.durable_state), Ghost(old(self).wrpm@.read_state),
                                    Ghost(old(self)@.commit_state), Tracked(perm));
        self.install_journal_entries_during_commit(Ghost(old(self)@.commit_state), Tracked(perm));
        Self::clear_log(&mut self.wrpm, Tracked(perm), self.vm, &self.sm);
        self.status = Ghost(JournalStatus::Quiescent);
        self.journal_length = 0;
        self.journaled_addrs = Ghost(Set::<int>::empty());
        self.entries.clear();
    }
}

}
