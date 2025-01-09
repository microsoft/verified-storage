use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::size_of;
use crate::pmem::wrpm_t::*;
use super::entry_v::*;
use super::*;
use super::inv_v::*;
use super::recover_v::*;
use super::setup_v::*;
use super::spec_v::*;
use super::start_v::*;

verus! {

impl <Perm, PM> Journal<Perm, PM>
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
{
    pub open spec fn write_preconditions(self, addr: u64, bytes_to_write: Seq<u8>, perm: Perm) -> bool
    {
        &&& self.valid()
        &&& self@.constants.app_area_start <= addr
        &&& addr + bytes_to_write.len() <= self@.constants.app_area_end
        &&& forall|s: Seq<u8>| {
            &&& seqs_match_except_in_range(s, self@.durable_state, addr as int, addr + bytes_to_write.len())
            &&& Self::recover(s) matches Some(j)
            &&& j.constants == self@.constants
            &&& j.state == s
        } ==> #[trigger] perm.check_permission(s)
        &&& forall|i: int| #![trigger self@.journaled_addrs.contains(i)]
            addr <= i < addr + bytes_to_write.len() ==> !self@.journaled_addrs.contains(i)
    }

    pub open spec fn write_postconditions(self, old_self: Self, addr: u64, bytes_to_write: Seq<u8>) -> bool
    {
        &&& self.valid()
        &&& self@.constants == old_self@.constants
        &&& self@.valid()
        &&& self.recover_successful()
        &&& self@ == (JournalView{
                read_state: update_bytes(old_self@.read_state, addr as int, bytes_to_write),
                commit_state: update_bytes(old_self@.commit_state, addr as int, bytes_to_write),
                durable_state: self@.durable_state,
                ..old_self@
            })
        &&& old_self@.matches_except_in_range(self@, addr as int, addr + bytes_to_write.len())
    }

    pub exec fn write_slice(
        &mut self,
        addr: u64,
        bytes_to_write: &[u8],
        Tracked(perm): Tracked<&Perm>,
    )
        requires
            old(self).write_preconditions(addr, bytes_to_write@, *perm),
        ensures
            self.write_postconditions(*old(self), addr, bytes_to_write@),
    {
        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        broadcast use broadcast_update_bytes_effect;
        broadcast use group_can_result_from_write_effect;
        
        proof {
            assert forall|s| can_result_from_partial_write(s, self.wrpm@.durable_state, addr as int, bytes_to_write@)
                implies #[trigger] perm.check_permission(s) by {
                assert(seqs_match_except_in_range(s, self.wrpm@.durable_state, addr as int,
                                                    addr + bytes_to_write@.len()));
            }
        }
        self.wrpm.write(addr, bytes_to_write, Tracked(perm));
        assert({
            &&& apply_journal_entries(self.wrpm@.read_state, self.entries@, self.sm) == Some(self@.commit_state)
            &&& self@.commit_state == update_bytes(old(self)@.commit_state, addr as int, bytes_to_write@)
        }) by {
            lemma_apply_journal_entries_some_iff_journal_entries_valid(old(self).wrpm@.read_state, self.entries@,
                                                                       self.sm);
            assert forall|i: int| #![trigger self.journaled_addrs@.contains(i)]
                addr <= i < addr + bytes_to_write@.len() implies !self.journaled_addrs@.contains(i) by {
                assert(self.journaled_addrs@.contains(i) <==> old(self)@.journaled_addrs.contains(i)); // trigger
            }
            lemma_apply_journal_entries_commutes_with_update_bytes(
                old(self).wrpm@.read_state, self.entries@, self.journaled_addrs@, addr as int,
                bytes_to_write@, self.sm
            );
        }

        assert(old(self)@.matches_except_in_range(self@, addr as int, addr + bytes_to_write.len()));
    }

    pub exec fn write_vec(
        &mut self,
        addr: u64,
        bytes_to_write: Vec<u8>,
        Tracked(perm): Tracked<&Perm>,
    )
        requires
            old(self).write_preconditions(addr, bytes_to_write@, *perm),
        ensures
            self.write_postconditions(*old(self), addr, bytes_to_write@),
    {
        self.write_slice(addr, bytes_to_write.as_slice(), Tracked(perm))
    }

    pub exec fn write_object<S>(
        &mut self,
        addr: u64,
        object: &S,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            S: PmCopy,
        requires
            old(self).write_preconditions(addr, object.spec_to_bytes(), *perm),
        ensures
            self.write_postconditions(*old(self), addr, object.spec_to_bytes()),
    {
        broadcast use pmcopy_axioms;
        self.write_slice(addr, object.as_byte_slice(), Tracked(perm))
    }

    pub exec fn journal_write(
        &mut self,
        addr: u64,
        bytes_to_write: Vec<u8>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), JournalError>)
        requires
            old(self).valid(),
            old(self)@.constants.app_area_start <= addr,
            addr + bytes_to_write.len() <= old(self)@.constants.app_area_end,
        ensures
            self.valid(),
            self@.valid(),
            self@.constants == old(self)@.constants,
            self.recover_successful(),
            ({
                let space_needed = Self::spec_journal_entry_overhead() + bytes_to_write@.len();
                match result {
                    Ok(_) => {
                        &&& space_needed <= old(self)@.remaining_capacity
                        &&& self@ == (JournalView{
                               durable_state: self@.durable_state,
                               read_state: self@.read_state,
                               commit_state: self@.commit_state,
                               journaled_addrs: old(self)@.journaled_addrs +
                                                Set::<int>::new(|i: int| addr <= i < addr + bytes_to_write.len()),
                               remaining_capacity: old(self)@.remaining_capacity - space_needed,
                               ..old(self)@
                           })
                        &&& extract_section(self@.commit_state, addr as int, bytes_to_write.len() as nat) == bytes_to_write@
                        &&& seqs_match_in_range(old(self)@.durable_state, self@.durable_state,
                                              self@.constants.app_area_start as int, self@.constants.app_area_end as int)
                        &&& seqs_match_in_range(old(self)@.read_state, self@.read_state,
                                              self@.constants.app_area_start as int, self@.constants.app_area_end as int)
                        &&& self@.matches_except_in_range(old(self)@, addr as int, addr + bytes_to_write.len())
                    },
                    Err(JournalError::NotEnoughSpace) => {
                        &&& space_needed > old(self)@.remaining_capacity
                        &&& self == old(self)
                    },
                    Err(_) => false,
                }
            }),
    {
        broadcast use pmcopy_axioms;
        broadcast use broadcast_update_bytes_effect;

        // Compute how much space is needed for this entry, and return an error
        // if there isn't enough space. Do this before doing anything else so that
        // we can ensure `self` hasn't changed if we return this error.
        
        let overhead = Self::journal_entry_overhead();
        if self.sm.journal_entries_end - self.sm.journal_entries_start - self.journal_length < overhead {
            return Err(JournalError::NotEnoughSpace);
        }
        if bytes_to_write.len() as u64 >
           self.sm.journal_entries_end - self.sm.journal_entries_start - self.journal_length - overhead {
            return Err(JournalError::NotEnoughSpace);
        }

        // Update the relevant in-memory fields of `self`:
        // `journal_length`, `journaled_addrs`, and `entries`.
        
        self.journal_length = self.journal_length + overhead + bytes_to_write.len() as u64;
        self.journaled_addrs = Ghost(self.journaled_addrs@ +
                                     Set::<int>::new(|i: int| addr <= i < addr + bytes_to_write.len()));
        let concrete_entry = ConcreteJournalEntry::new(addr, bytes_to_write);
        self.entries.push(concrete_entry);

        assert({
            &&& apply_journal_entries(self.wrpm@.read_state, self.entries@, self.sm) == Some(self@.commit_state)
            &&& self@.commit_state == update_bytes(old(self)@.commit_state, addr as int, bytes_to_write@)
        }) by {
            lemma_apply_journal_entries_some_iff_journal_entries_valid(old(self).wrpm@.read_state,
                                                                       old(self).entries@, self.sm);
            lemma_effect_of_append_on_apply_journal_entries(old(self).wrpm@.read_state, old(self).entries@,
                                                            concrete_entry@, self.sm);
        }

        assert(journaled_addrs_complete(self.entries@, self.journaled_addrs@)) by {
            assert forall|entry, addr| #![trigger self.entries@.contains(entry), self.journaled_addrs@.contains(addr)]
                   self.entries@.contains(entry) && entry.start <= addr < entry.end()
                   implies self.journaled_addrs@.contains(addr) by {
                if !old(self).entries@.contains(entry) { // triggers journaled_addrs_complete(old(self).entries@, ...)
                    assert(entry == concrete_entry@);
                }
            }
        }

        assert(space_needed_for_journal_entries_list(self.entries@) ==
               space_needed_for_journal_entries_list(old(self).entries@) + concrete_entry@.space_needed()) by {
            assert(self.entries@.last() == concrete_entry@);
            assert(self.entries@.drop_last() =~= old(self).entries@);
        }

        proof {
            lemma_apply_journal_entries_some_iff_journal_entries_valid(self.wrpm@.read_state, self.entries@, self.sm);
        }

        broadcast use broadcast_seqs_match_in_range_can_narrow_range;

        Ok(())
    }
}

}

