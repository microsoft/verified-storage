use builtin::*;
use builtin_macros::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse};
use vstd::arithmetic::mul::*;
use vstd::set_lib::*;
use vstd::slice::*;
use vstd::seq_lib::*;
use std::fs::Metadata;
use std::hash::Hash;
use std::collections::HashMap;
use vstd::prelude::*;
use vstd::bytes::*;
use crate::kv::durable::commonlayout_v::*;
use crate::kv::durable::oplog::logentry_v::*;
use crate::kv::durable::maintablelayout_v::*;
use crate::kv::durable::inv_v::*;
use crate::kv::durable::oplog::oplogimpl_v::*;
use crate::kv::durable::recovery_v::*;
use crate::kv::durable::util_v::*;
use crate::kv::kvimpl_t::*;
use crate::kv::layout_v::*;
use crate::kv::setup_v::*;
use crate::pmem::crc_t::*;
use crate::pmem::subregion_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::subregion_v::*;
use crate::pmem::traits_t;
use crate::pmem::wrpm_t::*;
use crate::util_v::*;

verus! {
    pub struct MainTableViewEntry<K> {
        pub entry: ListEntryMetadata,
        pub key: K,
    }

    impl<K> MainTableViewEntry<K> {
        pub open spec fn new(entry: ListEntryMetadata, key: K) -> Self {
            Self {
                entry,
                key,
            }
        }

        pub closed spec fn list_head_index(self) -> u64 {
            self.entry.head
        }

        pub open spec fn item_index(self) -> u64 {
            self.entry.item_index
        }

        pub closed spec fn len(self) -> u64 
        {
            self.entry.length
        }

        pub open spec fn key(self) -> K {
            self.key
        }
    }

    #[verifier::ext_equal]
    pub struct MainTableView<K> {
        pub durable_main_table: Seq<Option<MainTableViewEntry<K>>>,
    }

    impl<K> MainTableView<K>
        where
            K: PmCopy,
    {
        pub open spec fn init(num_keys: u64) -> Self {
            Self {
                durable_main_table: Seq::new(num_keys as nat, |i: int| None),
            }
        }

        pub open spec fn inv(self, overall_metadata: OverallMetadata) -> bool
        {
            &&& forall |i: nat, j: nat| i < overall_metadata.num_keys && j < overall_metadata.num_keys && i != j ==> {
                    &&& self.durable_main_table[i as int] is Some
                    &&& self.durable_main_table[j as int] is Some
                } ==> #[trigger] self.durable_main_table[i as int].unwrap().item_index() != 
                    #[trigger] self.durable_main_table[j as int].unwrap().item_index()
        }

        pub open spec fn len(self) -> nat
        {
            self.durable_main_table.len()
        }

        pub open spec fn new(
            main_table: Seq<Option<MainTableViewEntry<K>>>
        ) -> Self {
            Self {
                durable_main_table: main_table,
            }
        }

        pub open spec fn update(self, index: int, entry: MainTableViewEntry<K>) -> Self
        {
            Self{
                durable_main_table: self.durable_main_table.update(index, Some(entry))
            }
        }

        pub open spec fn delete(self, index: int) -> Option<Self>
        {
            if index < 0 || index >= self.durable_main_table.len() {
                None 
            } else {
                Some(Self {
                    durable_main_table: self.durable_main_table.update(index, None)
                })
            }
        }

        pub open spec fn update_item_index(self, index: int, item_index: u64) -> Option<Self>
        {
            if index < 0 || index >= self.durable_main_table.len() {
                None 
            } else {
                let current_entry = self.durable_main_table[index as int].unwrap();
                let updated_entry = ListEntryMetadata {
                    item_index,
                    ..current_entry.entry
                };
                let new_durable_entry = Some(MainTableViewEntry {
                    entry: updated_entry,
                    key: current_entry.key,
                });
                Some(Self {
                    durable_main_table: self.durable_main_table.update(index, new_durable_entry)
                })
            }
        }

        pub open spec fn valid_item_indices(self) -> Set<u64> {
            Set::new(|i: u64| exists |j: int| {
                    &&& 0 <= j < self.durable_main_table.len() 
                    &&& #[trigger] self.durable_main_table[j] matches Some(entry)
                    &&& entry.item_index() == i
                }
            )
        }
    }

    // An `OutstandingEntry` represents an update to the main table 
    // that has not yet been committed. We keep track of the last-written
    // contents of each entry along with an `EntryStatus` enum indicating the 
    // type of the last operation on that entry.
    #[verifier::reject_recursive_types(K)]
    pub struct OutstandingEntry<K> 
    {
        pub status: EntryStatus,
        pub entry: ListEntryMetadata,
        pub key: K
    }

    impl<K> OutstandingEntry<K> 
    {
        pub open spec fn view(self) -> MainTableViewEntry<K>
        {
            MainTableViewEntry {
                entry: self.entry,
                key: self.key
            }
        }
    }

    // `OutstandingEntries` maintains a *runtime* hashmap of main table
    // indexes to the most recent update to that index. This is used
    // to handle operations on entries that have already been updated in 
    // the current transaction and to help reason about pending 
    // changes.
    #[verifier::reject_recursive_types(K)]
    pub struct OutstandingEntries<K> 
    {
        pub contents: HashMap<u64, OutstandingEntry<K>>,
    }

    impl<K> OutstandingEntries<K> 
    {
        pub open spec fn inv(self) -> bool 
        {
            self.contents@.dom().finite()
        }

        pub open spec fn view(self) -> Map<u64, OutstandingEntry<K>>
        {
            self.contents@
        }

        pub open spec fn len(self) -> nat 
        {
            self.contents@.len()
        }

        pub open spec fn spec_index(self, i: u64) -> Option<OutstandingEntry<K>>
        {
            if self@.contains_key(i) {
                Some(self@[i])
            } else {
                None
            }
        }

        pub exec fn new() -> (out: Self) 
            ensures 
                out.contents@.len() == 0,
                out.inv(),
        {
            Self { contents: HashMap::new() }
        }

        pub exec fn clear(&mut self) 
            requires 
                old(self).inv(),
            ensures 
                self.contents@.len() == 0,
                self.inv(),
        {
            self.contents.clear();
        }

        pub exec fn get(&self, i: u64) -> (out: Option<&OutstandingEntry<K>>)
            requires
                vstd::std_specs::hash::obeys_key_model::<K>(),
            ensures 
                self.contents@.contains_key(i) ==> out == Some(&self@[i]),
                !self.contents@.contains_key(i) ==> out == None::<&OutstandingEntry<K>>,
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            self.contents.get(&i)
        }

        // Returns the status to be used when recording an update to 
        // the entry at `index`. If we create and then update an entry in 
        // the same transaction, we want to keep the `Created` status
        // so the allocator is updated properly; otherwise, it becomes
        // `Updated`.
        pub open spec fn get_update_status(self, index: u64) -> EntryStatus 
        {
            if self@.contains_key(index) {
                self@[index].status
            } else {
                EntryStatus::Updated
            }
        }

        // Returns the status to be used when recording deletion of an
        // entry at `index`. Deleting a preexisting entry is slightly different
        // from creating and deleting the same entry within a transaction
        // because the free list has to be handled differently, so we
        // differentiate between them with the entry status.
        pub open spec fn get_delete_status(self, index: u64) -> EntryStatus 
        {
            if self@.contains_key(index) && self@[index].status is Created {
                EntryStatus::CreatedThenDeleted
            } else {
                EntryStatus::Deleted
            }
        }
    }

    #[verifier::reject_recursive_types(K)]
    pub struct MainTable<K> {
        pub main_table_entry_size: u32,
        pub main_table_free_list: Vec<u64>,
        pub state: Ghost<MainTableView<K>>,
        pub outstanding_entries: OutstandingEntries<K>,
        // `modified_indices` is equivalent to the domain of `outstanding_entries`
        // (this is part of the main table invariant). We maintain it as a separate 
        // vector to make it easier to iterate over the modified entries 
        pub modified_indices: Vec<u64>,
    }

    pub open spec fn subregion_grants_access_to_main_table_entry<K>(
        subregion: WriteRestrictedPersistentMemorySubregion,
        idx: u64
    ) -> bool
        where 
            K: PmCopy + Sized,
    {
        let entry_size = ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of();
        forall|addr: u64| idx * entry_size + u64::spec_size_of() <= addr < idx * entry_size + entry_size ==>
            subregion.is_writable_relative_addr(addr as int)
    }

    impl<K> MainTable<K>
        where 
            K: PmCopy + std::fmt::Debug,
    {
        pub open spec fn view(self) -> MainTableView<K> 
        {
            self.state@
        }

        // The tentative view of a main table is its durable view with any outstanding entries
        // applied. We maintain as an invariant in kvimpl_v.rs that this is equivalent 
        // to the tentative view obtained by installing the current log and parsing the main table.
        pub open spec fn tentative_view(self) -> MainTableView<K>
        {
            Self::tentative_view_from_outstanding_entries(self@, self.outstanding_entries@)
        }

        pub open spec fn tentative_view_from_outstanding_entries(current_main_table: MainTableView<K>, 
            outstanding_entries: Map<u64, OutstandingEntry<K>>) -> MainTableView<K>
        {
            MainTableView {
                durable_main_table: current_main_table.durable_main_table.map(|i: int, e| {
                    if outstanding_entries.contains_key(i as u64) {
                        // if there is an outstanding entry, apply it
                        let outstanding_entry = outstanding_entries[i as u64];
                        match outstanding_entry.status {
                            EntryStatus::Created | EntryStatus::Updated => {
                                // put the new entry in the view
                                Some(outstanding_entry@)
                            }
                            EntryStatus::Deleted | EntryStatus::CreatedThenDeleted => {
                                // leave the entry as None
                                None
                            }
                        }
                    } else {
                        e
                    }
                })
            }
        }

        pub open spec fn free_list(self) -> Set<u64>
        {
            self.main_table_free_list@.to_set()
        }

        pub open spec fn no_outstanding_writes_to_index(self, idx: u64) -> bool
        {
            self.outstanding_entries[idx] is None
        }

        pub open spec fn no_outstanding_writes(self) -> bool
        {
            forall|i| 0 <= i < self@.durable_main_table.len() ==> self.no_outstanding_writes_to_index(i)
        }

        pub open spec fn get_latest_entry(self, index: u64) -> Option<MainTableViewEntry<K>>
        {
            if self.outstanding_entries@.contains_key(index) {
                Some(self.outstanding_entries[index].unwrap()@)
            } else if self@.durable_main_table[index as int] is Some {
                self@.durable_main_table[index as int]
            } else { 
                None
            }
        }

        // We return the free indices as a set, not a seq, because the order they are listed in
        // doesn't actually matter, and then we don't have to worry about matching the order
        // they are kept in in executable code.
        // An index is only considered free if it is free in the durable view of the table and
        // if it has no outstanding writes.
        pub open spec fn free_indices(self) -> Set<u64> {
            Set::new(|i: u64| {
                &&& 0 <= i < self@.durable_main_table.len() 
                &&& self.outstanding_entries[i] is None
                &&& self@.durable_main_table[i as int] is None
            })
        }

        // This function updates `outstanding_entries` and `modified_indices` to 
        // reflect the creation of a new entry
        pub exec fn outstanding_entry_create(&mut self, index: u64, entry: ListEntryMetadata, key: K)
            requires
                old(self).outstanding_entries.inv(),
                !old(self).outstanding_entries@.contains_key(index)
            ensures 
                self.outstanding_entries.inv(),
                self@ == old(self)@,
                self.free_list() == old(self).free_list(),
                forall|idx| self.free_indices().contains(idx) ==> old(self).free_indices().contains(idx),
                forall|idx| old(self).free_indices().contains(idx) && idx != index ==> self.free_indices().contains(idx),
                ({
                    let new_entry = OutstandingEntry {
                        status: EntryStatus::Created,
                        entry, 
                        key
                    };
                    self.outstanding_entries@ == old(self).outstanding_entries@.insert(index, new_entry)
                })
        {
            let new_outstanding_entry = OutstandingEntry {
                status: EntryStatus::Created,
                entry,
                key
            };
            self.outstanding_entries.contents.insert(index, new_outstanding_entry);
            broadcast use vstd::std_specs::hash::group_hash_axioms;
        }

        // This function updates `outstanding_entries` and `modified_indices` to 
        // reflect an update to an existing entry (e.g., an update to its item index)
        pub exec fn outstanding_entry_update(&mut self, index: u64, entry: ListEntryMetadata, key: K, overall_metadata: OverallMetadata)
            requires 
                old(self).outstanding_entries.inv(),
                old(self).opaquable_inv(overall_metadata),
                ({
                    // update can only apply to an existing entry, so either 
                    // there already has to be an outstanding entry or there
                    // has to be a valid durable entry at this index
                    ||| {
                        &&& old(self).outstanding_entries[index] matches Some(entry)
                        &&& (entry.status is Created || entry.status is Updated)
                    }
                    ||| {
                        &&& old(self).outstanding_entries[index] is None
                        &&& old(self)@.durable_main_table[index as int] is Some
                    }
                }),
                old(self).outstanding_entries@.contains_key(index) ==> old(self).outstanding_entries@[index].key == key,
                old(self)@.durable_main_table[index as int] is Some && !old(self).outstanding_entries@.contains_key(index) ==> 
                    old(self)@.durable_main_table[index as int].unwrap().key == key,
                index < overall_metadata.num_keys,
                !old(self).tentative_view().valid_item_indices().contains(entry.item_index),
            ensures 
                self.opaquable_inv(overall_metadata),
                self.outstanding_entries.inv(),
                self@ == old(self)@,
                self.main_table_free_list@ == old(self).main_table_free_list@,
                self@.valid_item_indices() == old(self)@.valid_item_indices(),
                self.main_table_entry_size == old(self).main_table_entry_size,
                old(self).outstanding_entries@.contains_key(index) ==> 
                    old(self).outstanding_entries@[index].status == self.outstanding_entries@[index].status,
                !old(self).outstanding_entries@.contains_key(index) ==> self.outstanding_entries@[index].status is Updated,
                ({
                    let status = self.outstanding_entries.get_update_status(index);
                    let new_entry = OutstandingEntry {
                        status,
                        entry, 
                        key
                    };
                    self.outstanding_entries@ == old(self).outstanding_entries@.insert(index, new_entry)
                })
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            let new_outstanding_entry = if self.outstanding_entries.contents.contains_key(&index) {
                let old_entry = self.outstanding_entries.contents.get(&index).unwrap();
                OutstandingEntry {
                    status: old_entry.status,
                    entry,
                    key,
                }
            } else {
                assert(!self.outstanding_entries@.contains_key(index));
                assert(!self.modified_indices@.contains(index));

                self.modified_indices.push(index);

                assert forall |idx: u64| self.modified_indices@.contains(idx) implies
                    idx < overall_metadata.num_keys
                by {
                    if idx == index { assert(index < overall_metadata.num_keys); } 
                    else { assert(old(self).modified_indices@.contains(idx)); }
                }
                assert(self.modified_indices@.subrange(0, self.modified_indices@.len() - 1) == old(self).modified_indices@);
                assert(self.modified_indices@[self.modified_indices@.len() - 1] == index);

                OutstandingEntry {
                    status: EntryStatus::Updated,
                    entry,
                    key
                }
            };
            assert(new_outstanding_entry.status is Updated || new_outstanding_entry.status is Created);
            self.outstanding_entries.contents.insert(index, new_outstanding_entry);
            assert(self.outstanding_entries@[index].status is Updated || self.outstanding_entries@[index].status is Created);
            
            // TODO: Refactor with outstanding_entry_delete?
            assert(self.opaquable_inv(overall_metadata)) by {
                // Prove that outstanding_entries and modified_indices still contain
                // the same indices
                assert forall |idx: u64| self.outstanding_entries@.contains_key(idx) implies 
                    #[trigger] self.modified_indices@.contains(idx)
                by {
                    if idx != index {
                        assert(old(self).outstanding_entries@.contains_key(idx));
                        assert(old(self).modified_indices@.contains(idx));
                        assert(self.modified_indices@.contains(idx));
                    } // else, trivial -- we know modified_indices contains index
                }
                assert forall |idx: u64| #[trigger] self.modified_indices@.contains(idx) implies 
                    self.outstanding_entries@.contains_key(idx)
                by {
                    if idx != index {
                        assert(old(self).modified_indices@.contains(idx));
                        assert(old(self).outstanding_entries@.contains_key(idx));
                    } // else, trivial
                }


                // Prove that all non-free indices are either valid on durable storage or have an outstanding update
                assert forall |idx: u64| 0 <= idx < self@.durable_main_table.len() && !self.main_table_free_list@.contains(idx) implies
                    self@.durable_main_table[idx as int] is Some || #[trigger] self.modified_indices@.contains(idx)
                by {
                    assert(!self.main_table_free_list@.contains(idx));
                    assert(!old(self).main_table_free_list@.contains(idx));
                    if old(self)@.durable_main_table[idx as int] is Some {
                        assert(self@.durable_main_table[idx as int] is Some);
                    } else {
                        assert(old(self).modified_indices@.contains(idx));
                    }
                }

                assert(self.modified_indices@.len() <= self@.durable_main_table.len()) by {
                    if self.modified_indices@.len() != old(self).modified_indices@.len() {
                        // if we increased the length of the modified indices list, we have to prove
                        // that it still hasn't grown beyond the length of the table itself
                        assert(self.modified_indices@.len() == old(self).modified_indices@.len() + 1);
                        // we need to temporarily view modified_indices as ints rather than u64s so we can invoke
                        // the lemma that proves that its length is still less than num_keys
                        let temp_view = self.modified_indices@.map_values(|e| e as int);
                        assert forall |idx: int| temp_view.contains(idx) implies 0 <= idx < overall_metadata.num_keys by {
                            assert(self.modified_indices@.contains(idx as u64))
                        }
                        // this lemma proves that a sequence with values between 0 and num keys and no duplicates
                        // cannot have a length longer than num_keys
                        lemma_seq_len_when_no_dup_and_all_values_in_range(temp_view, 0, overall_metadata.num_keys as int);
                    } 
                }
                
                assert(no_duplicate_item_indexes(self.tentative_view().durable_main_table)) by {
                    assert(no_duplicate_item_indexes(old(self).tentative_view().durable_main_table));
                    assert(forall |i: int| 0 <= i < self.tentative_view().durable_main_table.len() ==> {
                        &&& i != index ==> #[trigger] self.tentative_view().durable_main_table[i] == old(self).tentative_view().durable_main_table[i]
                        &&& i == index ==> self.tentative_view().durable_main_table[i].unwrap().item_index() == entry.item_index
                    });
                }
            }

        }

        // This function updates `outstanding_entries` and `modified_indices` to 
        // reflect a deletion operation
        // It's kind of janky to pass in the entry and key that we're deleting, but we need 
        // to keep track of them for deallocations later, so presumably the caller has 
        // already read them anyway.
        pub exec fn outstanding_entry_delete(&mut self, index: u64, entry: ListEntryMetadata, 
                key: K, Ghost(overall_metadata): Ghost<OverallMetadata>) 
            requires 
                old(self).outstanding_entries.inv(),
                old(self).opaquable_inv(overall_metadata),
                index < overall_metadata.num_keys,
                ({
                    // we can only delete an existing entry, so either 
                    // there already has to be an outstanding entry or there
                    // has to be a valid durable entry at this index
                    ||| {
                            &&& old(self).outstanding_entries@.contains_key(index)
                            &&& old(self).outstanding_entries@[index].key == key
                            &&& old(self).outstanding_entries@[index].entry == entry
                            &&& (old(self).outstanding_entries@[index].status is Updated || 
                                    old(self).outstanding_entries@[index].status is Created)
                        }
                    ||| {
                            &&& old(self)@.durable_main_table[index as int] is Some
                            &&& !old(self).outstanding_entries@.contains_key(index)
                            &&& old(self)@.durable_main_table[index as int].unwrap().key == key
                            &&& old(self)@.durable_main_table[index as int].unwrap().entry == entry
                        }
                }),
            ensures 
                self.outstanding_entries.inv(),
                self.opaquable_inv(overall_metadata),
                ({
                    let status = old(self).outstanding_entries.get_delete_status(index);
                    let new_entry = OutstandingEntry {
                        status,
                        entry, 
                        key
                    };
                    self.outstanding_entries@ == old(self).outstanding_entries@.insert(index, new_entry)
                }),
                old(self)@ == self@,
                old(self).free_list() == self.free_list(),
                self.free_indices() == old(self).free_indices(),
                old(self).main_table_entry_size == self.main_table_entry_size,
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            if !self.outstanding_entries.contents.contains_key(&index) {    
                assert(!self.outstanding_entries@.contains_key(index));
                assert(!self.modified_indices@.contains(index));

                self.modified_indices.push(index);

                assert forall |idx: u64| self.modified_indices@.contains(idx) implies
                    idx < overall_metadata.num_keys
                by {
                    if idx == index { assert(index < overall_metadata.num_keys); } 
                    else { assert(old(self).modified_indices@.contains(idx)); }
                }
                assert(self.modified_indices@.subrange(0, self.modified_indices@.len() - 1) == old(self).modified_indices@);
                assert(self.modified_indices@[self.modified_indices@.len() - 1] == index);
            } else {
                assert(self.modified_indices@.contains(index));
            }

            let status = if self.outstanding_entries.contents.contains_key(&index) {
                match self.outstanding_entries.contents.get(&index).unwrap().status {
                    EntryStatus::Created => EntryStatus::CreatedThenDeleted,
                    _ => EntryStatus::Deleted,
                }
            } else {
                EntryStatus::Deleted
            };
            assert(status == self.outstanding_entries.get_delete_status(index));

            let new_outstanding_entry = OutstandingEntry { status, entry, key };
            self.outstanding_entries.contents.insert(index, new_outstanding_entry);

            // Reestablish the invariant
            assert(self.opaquable_inv(overall_metadata)) by {
                // Prove that outstanding_entries and modified_indices still contain
                // the same indices
                assert forall |idx: u64| self.outstanding_entries@.contains_key(idx) implies 
                    #[trigger] self.modified_indices@.contains(idx)
                by {
                    if idx != index {
                        assert(old(self).outstanding_entries@.contains_key(idx));
                        assert(old(self).modified_indices@.contains(idx));
                        assert(self.modified_indices@.contains(idx));
                    } // else, trivial -- we know modified_indices contains index
                }
                assert forall |idx: u64| #[trigger] self.modified_indices@.contains(idx) implies 
                    self.outstanding_entries@.contains_key(idx)
                by {
                    if idx != index {
                        assert(old(self).modified_indices@.contains(idx));
                        assert(old(self).outstanding_entries@.contains_key(idx));
                    } // else, trivial
                }

                // Prove that all non-free indices are either valid on durable storage or have an outstanding update
                assert forall |idx: u64| 0 <= idx < self@.durable_main_table.len() && !self.main_table_free_list@.contains(idx) implies
                    self@.durable_main_table[idx as int] is Some || #[trigger] self.modified_indices@.contains(idx)
                by {
                    assert(!self.main_table_free_list@.contains(idx));
                    assert(!old(self).main_table_free_list@.contains(idx));
                    if old(self)@.durable_main_table[idx as int] is Some {
                        assert(self@.durable_main_table[idx as int] is Some);
                    } else {
                        assert(old(self).modified_indices@.contains(idx));
                    }
                }

                assert(self.modified_indices@.len() <= self@.durable_main_table.len()) by {
                    if self.modified_indices@.len() != old(self).modified_indices@.len() {
                        // if we increased the length of the modified indices list, we have to prove
                        // that it still hasn't grown beyond the length of the table itself
                        assert(self.modified_indices@.len() == old(self).modified_indices@.len() + 1);
                        // we need to temporarily view modified_indices as ints rather than u64s so we can invoke
                        // the lemma that proves that its length is still less than num_keys
                        let temp_view = self.modified_indices@.map_values(|e| e as int);
                        assert forall |idx: int| temp_view.contains(idx) implies 0 <= idx < overall_metadata.num_keys by {
                            assert(self.modified_indices@.contains(idx as u64))
                        }
                        // this lemma proves that a sequence with values between 0 and num keys and no duplicates
                        // cannot have a length longer than num_keys
                        lemma_seq_len_when_no_dup_and_all_values_in_range(temp_view, 0, overall_metadata.num_keys as int);
                    } 
                }

                assert(no_duplicate_item_indexes(self.tentative_view().durable_main_table)) by {
                    assert(no_duplicate_item_indexes(old(self).tentative_view().durable_main_table));
                    assert(forall |i: int| 0 <= i < self.tentative_view().durable_main_table.len() ==> {
                        &&& i != index ==> self.tentative_view().durable_main_table[i] == old(self).tentative_view().durable_main_table[i]
                        &&& i == index ==> self.tentative_view().durable_main_table[i] is None
                    });
                }
            }

            assert forall|idx: u64| self.free_indices().contains(idx) <==> old(self).free_indices().contains(idx) by {
                if 0 <= idx < self@.durable_main_table.len() && idx != index {
                    assert(self.outstanding_entries[idx] == old(self).outstanding_entries[idx]);
                    assert(self@.durable_main_table[idx as int] == old(self)@.durable_main_table[idx as int]);
                }
            }
            assert(self.free_indices() =~= old(self).free_indices());
        }

        pub open spec fn no_outstanding_writes_to_entry(
            self, 
            pm: PersistentMemoryRegionView, 
            i: u64,
            main_table_entry_size: u32
        ) -> bool 
        {
            let start = index_to_offset(i as nat, main_table_entry_size as nat) as int;
            pm.no_outstanding_writes_in_range(start, start + main_table_entry_size)
        }

        pub open spec fn opaquable_inv(self, overall_metadata: OverallMetadata) -> bool
        {
            &&& self.main_table_free_list@.no_duplicates()
            &&& self.modified_indices@.no_duplicates()
            &&& no_duplicate_item_indexes(self.tentative_view().durable_main_table)
            &&& no_duplicate_item_indexes(self@.durable_main_table)
            &&& self@.durable_main_table.len() == overall_metadata.num_keys

            &&& forall |idx: u64| self.main_table_free_list@.contains(idx) ==> 0 <= idx < overall_metadata.num_keys
            &&& forall |idx: u64| self.modified_indices@.contains(idx) ==> 0 <= idx < overall_metadata.num_keys

            &&& forall |idx: u64| self.outstanding_entries@.contains_key(idx) <==> 
                    #[trigger] self.modified_indices@.contains(idx)
            &&& self.outstanding_entries@.len() == self.modified_indices@.len()

            // free list and list of modified indices are always disjoint
            &&& forall |idx: u64| #[trigger] self.modified_indices@.contains(idx) ==>
                    !self.main_table_free_list@.contains(idx)
            &&& forall |idx: u64| self.main_table_free_list@.contains(idx) ==>
                    !(#[trigger] self.modified_indices@.contains(idx))

            // if an entry is not free, it is valid or has an outstanding update
            &&& forall |idx: u64| 0 <= idx < self@.durable_main_table.len() && !self.main_table_free_list@.contains(idx) ==>
                    self@.durable_main_table[idx as int] is Some || #[trigger] self.modified_indices@.contains(idx)

            // if idx has an outstanding write that is not from a create, the idx
            // was allocated in a previous transaction and is currently valid
            &&& forall |idx: u64| {
                    &&& #[trigger] self.outstanding_entries@.contains_key(idx) 
                    &&& !((self.outstanding_entries@[idx].status is Created || 
                                self.outstanding_entries@[idx].status is CreatedThenDeleted)) 
                } ==> self@.durable_main_table[idx as int] is Some

            // if an entry is valid in the durable main table, it is not free
            &&& forall |idx: u64| {
                    &&& 0 <= idx < self@.durable_main_table.len() 
                    &&& {
                        ||| self@.durable_main_table[idx as int] is Some
                        ||| self.outstanding_entries[idx] is Some
                    }
                } ==> !(#[trigger] self.main_table_free_list@.contains(idx))
            
            // if idx has an outstanding write that is from a create, the idx is 
            // currently invalid in the durable state 
            &&& forall |idx: u64| {
                    &&& #[trigger] self.outstanding_entries@.contains_key(idx) 
                    &&& (self.outstanding_entries@[idx].status is Created || 
                                self.outstanding_entries@[idx].status is CreatedThenDeleted)
                } ==> self@.durable_main_table[idx as int] is None

            &&& self.outstanding_entries.inv()
            &&& vstd::std_specs::hash::obeys_key_model::<K>()
            &&& self.modified_indices@.len() <= self@.durable_main_table.len()
        }

        pub open spec fn inv(self, pm: PersistentMemoryRegionView, overall_metadata: OverallMetadata) -> bool
        {
            &&& self.opaquable_inv(overall_metadata)
            &&& overall_metadata.main_table_size >= overall_metadata.num_keys * overall_metadata.main_table_entry_size
            &&& pm.no_outstanding_writes_in_range(overall_metadata.num_keys * overall_metadata.main_table_entry_size,
                                                overall_metadata.main_table_size as int)
            &&& pm.len() >= overall_metadata.main_table_size
            &&& self.main_table_entry_size == overall_metadata.main_table_entry_size
            &&& overall_metadata.main_table_entry_size ==
                    ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of()
            &&& forall |s| #[trigger] pm.can_crash_as(s) ==> 
                    parse_main_table::<K>(s, overall_metadata.num_keys, overall_metadata.main_table_entry_size) == Some(self@)
            &&& self@.durable_main_table.len() == overall_metadata.num_keys
            &&& self@.inv(overall_metadata)
            &&& forall |idx: u64| self.free_list().contains(idx) ==> idx < overall_metadata.num_keys
            &&& forall |idx: u64| self.free_list().contains(idx) ==> self.free_indices().contains(idx)
            &&& forall |i| 0 <= i < self@.durable_main_table.len() ==>
                   (#[trigger] self@.durable_main_table[i] matches Some(entry) ==>
                    entry.entry.item_index < overall_metadata.num_keys)
            &&& forall |idx: u64| self.outstanding_entries@.contains_key(idx) <==> #[trigger] self.modified_indices@.contains(idx)
            &&& forall |idx: u64| 0 <= idx < self@.durable_main_table.len() && !(#[trigger] self.outstanding_entries@.contains_key(idx)) ==>
                    self.no_outstanding_writes_to_entry(pm, idx, overall_metadata.main_table_entry_size)
        }

        pub open spec fn valid(self, pm: PersistentMemoryRegionView, overall_metadata: OverallMetadata) -> bool
        {
            &&& self.inv(pm, overall_metadata)
        }

        pub open spec fn subregion_grants_access_to_free_slots(
            self,
            subregion: WriteRestrictedPersistentMemorySubregion
        ) -> bool
        {
            forall|idx: u64| {
                &&& idx < self@.len()
                &&& self.free_list().contains(idx)
            } ==> #[trigger] subregion_grants_access_to_main_table_entry::<K>(subregion, idx)
        }

        pub proof fn lemma_establish_bytes_parseable_for_valid_entry(
            self,
            pm: PersistentMemoryRegionView,
            overall_metadata: OverallMetadata,
            index: u64,
        )
            requires
                self.inv(pm, overall_metadata),
                0 <= index < overall_metadata.num_keys,
                self@.durable_main_table[index as int] is Some,
            ensures
                ({
                    let cdb_bytes = extract_bytes(
                        pm.committed(),
                        index_to_offset(index as nat, overall_metadata.main_table_entry_size as nat),
                        u64::spec_size_of() as nat,
                    );
                    let cdb = u64::spec_from_bytes(cdb_bytes);
                    let crc_bytes = extract_bytes(
                        pm.committed(),
                        index_to_offset(index as nat, overall_metadata.main_table_entry_size as nat) + u64::spec_size_of(),
                        u64::spec_size_of() as nat,
                    );
                    let crc = u64::spec_from_bytes(crc_bytes);
                    let entry_bytes = extract_bytes(
                        pm.committed(),
                        index_to_offset(index as nat, overall_metadata.main_table_entry_size as nat) + u64::spec_size_of() * 2,
                        ListEntryMetadata::spec_size_of() as nat,
                    );
                    let entry = ListEntryMetadata::spec_from_bytes(entry_bytes);
                    let key_bytes = extract_bytes(
                        pm.committed(),
                        index_to_offset(index as nat, overall_metadata.main_table_entry_size as nat) + u64::spec_size_of() * 2 +
                            ListEntryMetadata::spec_size_of(),
                        K::spec_size_of() as nat,
                    );
                    let key = K::spec_from_bytes(key_bytes);
                    let meta = self@.durable_main_table[index as int].unwrap();
                    &&& u64::bytes_parseable(cdb_bytes)
                    &&& u64::bytes_parseable(crc_bytes)
                    &&& ListEntryMetadata::bytes_parseable(entry_bytes)
                    &&& K::bytes_parseable(key_bytes)
                    &&& cdb == CDB_TRUE
                    &&& crc_bytes == spec_crc_bytes(entry_bytes + key_bytes)
                    &&& entry == meta.entry
                    &&& key == meta.key
                }),
        {
            assert(pm.can_crash_as(pm.committed()));
            let main_table_entry_size = overall_metadata.main_table_entry_size;
            lemma_valid_entry_index(index as nat, overall_metadata.num_keys as nat, main_table_entry_size as nat);
            let entry_bytes = extract_bytes(pm.committed(), (index * main_table_entry_size) as nat, main_table_entry_size as nat);
            assert(extract_bytes(entry_bytes, 0, u64::spec_size_of()) =~=
                   extract_bytes(pm.committed(), index_to_offset(index as nat, overall_metadata.main_table_entry_size as nat),
                                 u64::spec_size_of()));
            assert(extract_bytes(entry_bytes, u64::spec_size_of(), u64::spec_size_of()) =~=
                   extract_bytes(pm.committed(),
                        index_to_offset(index as nat, overall_metadata.main_table_entry_size as nat) + u64::spec_size_of(),
                                 u64::spec_size_of()));
            assert(extract_bytes(entry_bytes, u64::spec_size_of() * 2, ListEntryMetadata::spec_size_of()) =~=
                   extract_bytes(pm.committed(),
                                index_to_offset(index as nat, overall_metadata.main_table_entry_size as nat) + u64::spec_size_of() * 2,
                                 ListEntryMetadata::spec_size_of()));
            assert(extract_bytes(entry_bytes, u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of(),
                                 K::spec_size_of()) =~=
                   extract_bytes(pm.committed(),
                                index_to_offset(index as nat, overall_metadata.main_table_entry_size as nat)+ u64::spec_size_of() * 2
                                 + ListEntryMetadata::spec_size_of(),
                                 K::spec_size_of()));
        }

        pub open spec fn spec_replay_log_main_table<L>(mem: Seq<u8>, op_log: Seq<LogicalOpLogEntry<L>>) -> Seq<u8>
            where 
                L: PmCopy,
            decreases op_log.len()
        {
            if op_log.len() == 0 {
                mem 
            } else {
                let current_op = op_log[0];
                let op_log = op_log.drop_first();
                let mem = Self::apply_log_op_to_main_table_mem(mem, current_op);
                Self::spec_replay_log_main_table(mem, op_log)
            }
        }

        // main table-related log entries store the CRC that the entry *will* have when all updates are written to it.
        // this ensures that we end up with the correct CRC even if updates to this entry were interrupted by a crash or 
        // if corruption has occurred. So, we don't check CRCs here, we just overwrite the current CRC with the new one and 
        // update relevant fields.
        pub open spec fn apply_log_op_to_main_table_mem<L>(mem: Seq<u8>, op: LogicalOpLogEntry<L>) -> Seq<u8>
            where 
                L: PmCopy,
        {
            let table_entry_slot_size = ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of();
            match op {
                LogicalOpLogEntry::CommitMainTableEntry { index } => {
                    let entry_offset = index * table_entry_slot_size;
                    let cdb_bytes = CDB_TRUE.spec_to_bytes();
                    // Note: the cdb is written at offset 0 in the entry
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if entry_offset <= pos < entry_offset + u64::spec_size_of() {
                            cdb_bytes[pos - entry_offset]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                LogicalOpLogEntry::InvalidateMainTableEntry { index } => {
                    let entry_offset = index * table_entry_slot_size;
                    let cdb_bytes = CDB_FALSE.spec_to_bytes();
                    // Note: the cdb is written at offset 0 in the entry
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if entry_offset <= pos < entry_offset + u64::spec_size_of() {
                            cdb_bytes[pos - entry_offset]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                LogicalOpLogEntry::UpdateMainTableEntry { index, new_crc, new_metadata } => {
                    let entry_offset = index * table_entry_slot_size;
                    let crc_addr = entry_offset + u64::spec_size_of();
                    let metadata_addr = crc_addr + u64::spec_size_of();
                    let new_crc_bytes = new_crc.spec_to_bytes();
                    let new_metadata_bytes = new_metadata.spec_to_bytes();
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if crc_addr <= pos < crc_addr + u64::spec_size_of() {
                            new_crc_bytes[pos - crc_addr]
                        } else if metadata_addr <= pos < metadata_addr + ListEntryMetadata::spec_size_of() {
                            new_metadata_bytes[pos - metadata_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                _ => mem // all other log ops do not modify the main table
            }
        }

        spec fn extract_cdb_for_entry(mem: Seq<u8>, k: nat, main_table_entry_size: u32) -> u64
        {
            u64::spec_from_bytes(extract_bytes(mem, index_to_offset(k, main_table_entry_size as nat), u64::spec_size_of()))
        }

        pub exec fn setup<PM, L>(
            subregion: &WritablePersistentMemorySubregion,
            pm_region: &mut PM,
            num_keys: u64,
            main_table_entry_size: u32,
        ) -> (result: Result<(), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
                L: PmCopy
            requires
                subregion.inv(&*old(pm_region)),
                forall |addr: int| subregion.start() <= addr < subregion.end() ==>
                     #[trigger] subregion.is_writable_absolute_addr_fn()(addr),
                subregion.view(&*(old(pm_region))).no_outstanding_writes(),
                num_keys * main_table_entry_size <= subregion.view(&*(old(pm_region))).len() <= u64::MAX,
                main_table_entry_size == ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() +
                                      K::spec_size_of(),
            ensures
                subregion.inv(pm_region),
                pm_region.inv(),
                pm_region@.len() == old(pm_region)@.len(),
                match result {
                    Ok(()) => {
                        let replayed_bytes = Self::spec_replay_log_main_table(subregion.view(pm_region).flush().committed(), Seq::<LogicalOpLogEntry<L>>::empty());
                        &&& parse_main_table::<K>(subregion.view(pm_region).flush().committed(), num_keys, main_table_entry_size) matches Some(recovered_view)
                        &&& recovered_view == MainTableView::<K>::init(num_keys)
                    }
                    Err(_) => true // TODO
                }
        {
            assert(main_table_entry_size >= u64::spec_size_of());
            let ghost original_pm_len = pm_region@.len();

            // invalidate all of the entries
            let mut entry_offset: u64 = 0;
            assert(entry_offset == 0 * main_table_entry_size) by {
                vstd::arithmetic::mul::lemma_mul_basics(main_table_entry_size as int);
            }
            for index in 0..num_keys 
                invariant
                    subregion.inv(pm_region),
                    subregion.view(pm_region).no_outstanding_writes_in_range(entry_offset as int,
                                                                             subregion.view(pm_region).len() as int),
                    num_keys * main_table_entry_size <= subregion.view(pm_region).len() <= u64::MAX,
                    // entry_offset == index * main_table_entry_size,
                    entry_offset == index_to_offset(index as nat, main_table_entry_size as nat),
                    main_table_entry_size >= u64::spec_size_of(),
                    forall |addr: int| subregion.start() <= addr < subregion.end() ==>
                     #[trigger] subregion.is_writable_absolute_addr_fn()(addr),
                    forall |k: nat| k < index ==> #[trigger] Self::extract_cdb_for_entry(
                        subregion.view(pm_region).flush().committed(), k, main_table_entry_size
                    ) == CDB_FALSE,
                    ({
                        let mem = subregion.view(pm_region).flush().committed();
                        forall |k: nat| k < index ==> u64::bytes_parseable(#[trigger] extract_bytes(
                            mem,
                            index_to_offset(k, main_table_entry_size as nat),
                            u64::spec_size_of())
                        )
                    }),
                    pm_region@.len() == original_pm_len,
            {
                proof {lemma_valid_entry_index(index as nat, num_keys as nat, main_table_entry_size as nat);}
                let ghost v1 = subregion.view(pm_region);
                subregion.serialize_and_write_relative(pm_region, entry_offset, &CDB_FALSE);
                assert(CDB_FALSE.spec_to_bytes().len() == u64::spec_size_of()) by {
                    broadcast use pmcopy_axioms;
                }
                assert forall |k: nat| k < index + 1 implies #[trigger] Self::extract_cdb_for_entry(
                        subregion.view(pm_region).flush().committed(), k, main_table_entry_size
                    ) == CDB_FALSE 
                by {
                    let mem = subregion.view(pm_region).flush().committed();
                    if k < index {
                        assert(Self::extract_cdb_for_entry(v1.flush().committed(), k, main_table_entry_size) == CDB_FALSE);
                        assert(index_to_offset(k, main_table_entry_size as nat) + u64::spec_size_of() <= entry_offset) by {
                            lemma_metadata_fits::<K>(k as int, index as int, main_table_entry_size as int);
                        }
                        assert(extract_bytes(mem, index_to_offset(k, main_table_entry_size as nat), u64::spec_size_of()) =~= 
                               extract_bytes(v1.flush().committed(), index_to_offset(k, main_table_entry_size as nat), u64::spec_size_of()));
                    }
                    else {
                        assert(extract_bytes(mem, index_to_offset(k, main_table_entry_size as nat), u64::spec_size_of()) ==
                               CDB_FALSE.spec_to_bytes());
                        broadcast use axiom_to_from_bytes;
                    }
                }

                // TODO: refactor this if you can -- the proof is the same as the above assertion, but we can't have
                // triggers on k in both arithmetic and non arithmetic contexts, so the two conjuncts have to be asserted
                // separately.
                assert forall |k: nat| k < index + 1 implies 
                    #[trigger] u64::bytes_parseable(extract_bytes(subregion.view(pm_region).flush().committed(), k * main_table_entry_size as nat, u64::spec_size_of())) 
                by {
                    let mem = subregion.view(pm_region).flush().committed();
                    if k < index {
                        assert(Self::extract_cdb_for_entry(v1.flush().committed(), k, main_table_entry_size) == CDB_FALSE);
                        assert(index_to_offset(k, main_table_entry_size as nat) + u64::spec_size_of() <= entry_offset) by {
                            lemma_metadata_fits::<K>(k as int, index as int, main_table_entry_size as int);
                        }
                        assert(extract_bytes(mem, index_to_offset(k, main_table_entry_size as nat), u64::spec_size_of()) =~= 
                            extract_bytes(v1.flush().committed(), k * main_table_entry_size as nat, u64::spec_size_of()));
                    }
                    else {
                        assert(extract_bytes(mem, index_to_offset(k, main_table_entry_size as nat), u64::spec_size_of()) ==
                            CDB_FALSE.spec_to_bytes());
                        broadcast use axiom_to_from_bytes;
                    }
                }
                
                entry_offset += main_table_entry_size as u64;
            }

            let ghost mem = subregion.view(pm_region).flush().committed();
            let ghost op_log = Seq::<LogicalOpLogEntry<L>>::empty();
            let ghost replayed_mem = Self::spec_replay_log_main_table(mem, op_log);
            let ghost recovered_view = parse_main_table::<K>(mem, num_keys, main_table_entry_size);
            let ghost table_entry_slot_size = ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of();

            // Prove that all of the entries are valid. We need to establish this to prove that the recovery view
            // of the table is Some so that we can then reason about its contents.
            assert forall |k: nat| k < num_keys implies {
                validate_main_entry::<K>(#[trigger] extract_bytes(mem, (k * main_table_entry_size) as nat,
                        main_table_entry_size as nat), num_keys as nat)
            } by {
                assert(u64::bytes_parseable(extract_bytes(mem, index_to_offset(k, main_table_entry_size as nat), u64::spec_size_of())));
                assert(Self::extract_cdb_for_entry(mem, k, main_table_entry_size) == CDB_FALSE);
                // Prove that k is a valid index in the table
                lemma_valid_entry_index(k, num_keys as nat, main_table_entry_size as nat);
                // Prove that the subranges used by validate_main_entry and extract_cdb_for_entry to check CDB are the same
                lemma_subrange_of_extract_bytes_equal(mem, index_to_offset(k, main_table_entry_size as nat), 
                        index_to_offset(k, main_table_entry_size as nat), main_table_entry_size as nat, u64::spec_size_of());
            }

            proof {
                let entries = parse_main_entries::<K>(mem, num_keys as nat, main_table_entry_size as nat);
                assert forall |i: nat| 0 <= i < entries.len() implies #[trigger] entries[i as int] is None by {
                    lemma_valid_entry_index(i, num_keys as nat, main_table_entry_size as nat);
                    lemma_subrange_of_extract_bytes_equal(mem, index_to_offset(i, main_table_entry_size as nat), 
                        index_to_offset(i, main_table_entry_size as nat), main_table_entry_size as nat, u64::spec_size_of());
                    assert(Self::extract_cdb_for_entry(mem, i, main_table_entry_size) == CDB_FALSE);
                    assert(Self::extract_cdb_for_entry(mem, i, main_table_entry_size) == CDB_FALSE ==> 
                           entries[i as int] is None);
                }
                assert(no_duplicate_item_indexes(entries));
            }

            // Prove that entries with CDB of false are None in the recovery view of the table. We already know that all of the entries
            // have CDB_FALSE, so this proves the postcondition that the recovery view is equivalent to fresh initialized table view
            // since all entries in both are None
            let ghost main_table = recovered_view.unwrap().durable_main_table;
            assert forall |k: nat| k < num_keys implies #[trigger] main_table[k as int] is None by {
                // Prove that k is a valid index in the table
                lemma_valid_entry_index(k, num_keys as nat, main_table_entry_size as nat);
                // Prove that the subranges used by validate_main_entry and extract_cdb_for_entry to check CDB are the same
                lemma_subrange_of_extract_bytes_equal(mem, (k * main_table_entry_size) as nat, (k * main_table_entry_size) as nat, main_table_entry_size as nat, u64::spec_size_of());
            
                assert(Self::extract_cdb_for_entry(mem, k, main_table_entry_size) == CDB_FALSE);
            }
            // We need to reveal the opaque lemma at some point to be able to prove that the general PM invariant holds;
            // it's cleaner to do that here than in the caller
            proof { subregion.lemma_reveal_opaque_inv(pm_region); }
            assert({
                &&& recovered_view matches Some(recovered_view)
                &&& recovered_view =~= MainTableView::<K>::init(num_keys)
            });
            
            Ok(())
        }

        pub exec fn start<PM, I, L>(
            subregion: &PersistentMemorySubregion,
            pm_region: &PM,
            overall_metadata: OverallMetadata,
            version_metadata: VersionMetadata,
        ) -> (result: Result<(Self, Vec<(Box<K>, u64, u64)>), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
                I: PmCopy + Sized + std::fmt::Debug,
                L: PmCopy + std::fmt::Debug,
            requires
                subregion.inv(pm_region),
                pm_region@.no_outstanding_writes(),
                overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr, overall_metadata.kvstore_id),
                parse_main_table::<K>(
                    subregion.view(pm_region).committed(),
                    overall_metadata.num_keys, 
                    overall_metadata.main_table_entry_size 
                ) is Some,
                ListEntryMetadata::spec_size_of() + u64::spec_size_of() * 2 + K::spec_size_of() <= u64::MAX,
                subregion.len() == overall_metadata.main_table_size,
                subregion.view(pm_region).no_outstanding_writes(),
                K::spec_size_of() > 0,
                vstd::std_specs::hash::obeys_key_model::<K>(),
            ensures 
                match result {
                    Ok((main_table, entry_list)) => {
                        let table = parse_main_table::<K>(
                            subregion.view(pm_region).committed(),
                            overall_metadata.num_keys, 
                            overall_metadata.main_table_entry_size
                        ).unwrap();
                        let key_entry_list_view = Set::new(
                            |val: (K, u64, u64)| {
                                exists |j: u64| {
                                    &&& 0 <= j < table.durable_main_table.len()
                                    &&& #[trigger] table.durable_main_table[j as int] matches Some(entry)
                                    &&& val == (entry.key(), j, entry.item_index())
                        }});
                        let entry_list_view = Seq::new(entry_list@.len(), |i: int| (*entry_list[i].0, entry_list[i].1, entry_list[i].2));
                        let item_index_view = Seq::new(entry_list@.len(), |i: int| entry_list[i].2);

                        &&& main_table.inv(subregion.view(pm_region), overall_metadata)
                        &&& main_table.no_outstanding_writes()
                        &&& table == main_table@
                        // the entry list corresponds to the table
                        &&& entry_list_view.to_set() == key_entry_list_view
                        // all indices in the entry list are valid
                        &&& forall |i: int| 0 <= i < entry_list.len() ==> {
                            &&& 0 <= (#[trigger] entry_list[i]).1 < overall_metadata.num_keys 
                            &&& 0 <= entry_list[i].2 < overall_metadata.num_keys
                        }
                        // no duplicate keys
                        &&& forall |k: int, l: int| {
                            &&& 0 <= k < entry_list.len()
                            &&& 0 <= l < entry_list.len()
                            &&& k != l
                        } ==> *(#[trigger] entry_list@[k]).0 != *(#[trigger] entry_list@[l]).0
                        &&& item_index_view.to_set() == main_table@.valid_item_indices()
                        &&& forall|idx: u64| 0 <= idx < main_table.outstanding_entries.len() ==>
                                main_table.outstanding_entries[idx] is None

                        &&& main_table@ == main_table.tentative_view()
                        &&& main_table@.valid_item_indices() == item_index_view.to_set()
                    }
                    Err(KvError::IndexOutOfRange) => {
                        let entry_slot_size = (ListEntryMetadata::spec_size_of() + u64::spec_size_of() * 2 + K::spec_size_of()) as u64;
                        overall_metadata.num_keys > overall_metadata.main_table_size / entry_slot_size
                    }
                    Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                    Err(KvError::PmemErr{ pmem_err }) => true,
                    Err(_) => false
                }
        {
            let num_keys = overall_metadata.num_keys;
            let main_table_entry_size = overall_metadata.main_table_entry_size;

            // Since we've already replayed the log, we just need to construct 
            // the allocator and determine which item indices are valid. 

            let mut metadata_allocator: Vec<u64> = Vec::with_capacity(num_keys as usize);
            let mut key_index_pairs: Vec<(Box<K>, u64, u64)> = Vec::new();
            let max_index = overall_metadata.main_table_size / (main_table_entry_size as u64);
            let ghost mem = subregion.view(pm_region).committed();
            let mut index = 0;
            let ghost table = parse_main_table::<K>(
                mem,
                overall_metadata.num_keys, 
                overall_metadata.main_table_entry_size 
            ).unwrap();
            let ghost old_pm_constants = pm_region.constants();

            proof {
                // proves that max_index * main_table_entry_size <= overall_metadata.main_table_size
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(overall_metadata.main_table_size as int, main_table_entry_size as int);
                // This helps Verus prove that we don't go out of bounds when reading the entry at index * main_table_entry_size
                assert(main_table_entry_size * max_index == max_index * main_table_entry_size) by {
                    vstd::arithmetic::mul::lemma_mul_is_commutative(main_table_entry_size as int, max_index as int);
                }

                // Proves that there is currently only one crash state, and it recovers to the current ghost table state.
                lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(subregion.view(pm_region));
                assert(forall |s| subregion.view(pm_region).can_crash_as(s) ==> s == mem);
                assert(parse_main_table::<K>(
                    mem,
                    overall_metadata.num_keys, 
                    overall_metadata.main_table_entry_size 
                ) == Some(table));
            }

            while index < num_keys
                invariant
                    subregion.inv(pm_region),
                    index <= num_keys,
                    index * main_table_entry_size <= overall_metadata.main_table_size <= u64::MAX,
                    max_index == overall_metadata.main_table_size / (main_table_entry_size as u64),
                    max_index * main_table_entry_size <= overall_metadata.main_table_size,
                    main_table_entry_size * max_index == max_index * main_table_entry_size, 
                    index <= max_index,
                    ListEntryMetadata::spec_size_of() + u64::spec_size_of() * 2 + K::spec_size_of() == main_table_entry_size,
                    num_keys == overall_metadata.num_keys,
                    subregion.len() == overall_metadata.main_table_size,
                    subregion.view(pm_region).no_outstanding_writes(),
                    mem == subregion.view(pm_region).committed(),
                    old_pm_constants == pm_region.constants(),
                    subregion.view(pm_region).can_crash_as(subregion.view(pm_region).committed()),
                    forall |s| #[trigger] subregion.view(pm_region).can_crash_as(s) ==>  
                        parse_main_table::<K>(
                            s,
                            overall_metadata.num_keys, 
                            overall_metadata.main_table_entry_size 
                        ) == Some(table),
                    main_table_entry_size == overall_metadata.main_table_entry_size,
                    forall |i: u64| 0 <= i < index ==> {
                        let entry = #[trigger] table.durable_main_table[i as int];
                        entry is None <==> metadata_allocator@.contains(i)
                    },
                    forall |i: int| 0 <= i < metadata_allocator.len() ==> #[trigger] metadata_allocator[i] < index,
                    forall |i: int, j: int| 0 <= i < metadata_allocator.len() && 0 <= j < metadata_allocator.len() && i != j ==>
                        metadata_allocator[i] != metadata_allocator[j],
                    ({
                        let entry_list_view = Seq::new(key_index_pairs@.len(), |i: int| (*key_index_pairs[i].0, key_index_pairs[i].1, key_index_pairs[i].2));
                        let item_index_view = Seq::new(key_index_pairs@.len(), |i: int| key_index_pairs[i].2);
                        &&& forall |i: u64| 0 <= i < index ==> {
                                let entry = #[trigger] table.durable_main_table[i as int];
                                entry matches Some(valid_entry) ==> entry_list_view.contains((valid_entry.key(), i, valid_entry.item_index()))
                            }
                        &&& forall |i: int| 0 <= i < entry_list_view.len() ==> {
                                let table_index = entry_list_view[i].1;
                                let item_index = entry_list_view[i].2;
                                &&& table.durable_main_table[table_index as int] matches Some(valid_entry)
                                &&& valid_entry.key() == #[trigger] entry_list_view[i].0
                                &&& valid_entry.item_index() == item_index
                                &&& 0 <= table_index < table.durable_main_table.len()
                                &&& 0 <= table_index < index
                                &&& table.valid_item_indices().contains(item_index)
                                &&& item_index_view.contains(item_index)
                            }
                        &&& item_index_view.to_set().subset_of(table.valid_item_indices())
                    }),
                    forall |i: int| 0 <= i < key_index_pairs.len() ==> {
                        &&& 0 <= (#[trigger] key_index_pairs[i]).1 < overall_metadata.num_keys 
                        &&& 0 <= key_index_pairs[i].2 < overall_metadata.num_keys
                    },
                    // no duplicate keys
                    forall |k: int, l: int| {
                        &&& 0 <= k < key_index_pairs.len()
                        &&& 0 <= l < key_index_pairs.len()
                        &&& k != l
                    } ==> *(#[trigger] key_index_pairs@[k]).0 != *(#[trigger] key_index_pairs@[l]).0,
                    K::spec_size_of() > 0,
                    metadata_allocator@.len() <= index,
                    metadata_allocator@.no_duplicates(),
                    // no duplicate item indexes in the main table
                    // TODO: could/should this go in `parse_main_table` instead?
                    forall |i: nat, j: nat| i < j < index ==> {
                        &&& #[trigger] table.durable_main_table[i as int] is Some
                        &&& #[trigger] table.durable_main_table[j as int] is Some
                    } ==> table.durable_main_table[i as int].unwrap().item_index() != 
                            table.durable_main_table[j as int].unwrap().item_index()
            {
                let ghost old_entry_list_view = Seq::new(key_index_pairs@.len(), |i: int| (*key_index_pairs[i].0, key_index_pairs[i].1, key_index_pairs[i].2));

                if index < max_index {
                    // This case proves that index * main_table_entry_size will not overflow or go out of bounds (here or at the end
                    // of the loop) if index < max_index
                    proof {
                        lemma_mul_strict_inequality(index as int, max_index as int, main_table_entry_size as int);
                        if index + 1 < max_index {
                            lemma_mul_strict_inequality(index + 1, max_index as int, main_table_entry_size as int);
                        }
                        // also prove that we can read the next entry at this index without going out of bounds
                        vstd::arithmetic::mul::lemma_mul_is_distributive_add(main_table_entry_size as int, index as int, 1int);
                        // asserting these here seems to help stabilize some arithmetic assertions later
                        assert(main_table_entry_size * (index + 1) == main_table_entry_size * index + main_table_entry_size);
                        assert(main_table_entry_size * (index + 1) <= main_table_entry_size * max_index);
                    }
                } else {
                    proof { lemma_fundamental_div_mod(overall_metadata.main_table_size as int, main_table_entry_size as int); }
                    return Err(KvError::IndexOutOfRange);
                }

                let entry_offset = index * (main_table_entry_size as u64);

                // Read the CDB at this slot. If it's valid, we need to read the rest of the 
                // entry to get the key and check its CRC
                let relative_cdb_addr = entry_offset;
                proof {
                    lemma_if_table_parseable_then_all_entries_parseable::<K>(
                        subregion.view(pm_region).committed(),
                        overall_metadata.num_keys, 
                        overall_metadata.main_table_entry_size
                    );
                    // trigger for CDB bytes parseable
                    assert(u64::bytes_parseable(extract_bytes(
                        subregion.view(pm_region).committed(),
                        index_to_offset(index as nat, main_table_entry_size as nat),
                        u64::spec_size_of()
                    )));
                }
                let cdb = match subregion.read_relative_aligned::<u64, _>(pm_region, relative_cdb_addr) {
                    Ok(cdb) => cdb,
                    Err(e) => return Err(KvError::PmemErr { pmem_err: e })
                };
                let ghost relative_cdb_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| relative_cdb_addr + i);
                let ghost true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem[relative_cdb_addrs[i]]);
                let ghost true_cdb = u64::spec_from_bytes(true_cdb_bytes);
                // Proving that true_cdb_bytes matches various ways of obtaining the CDB subrange from mem is useful later to prove whether 
                // an entry is valid or invalid based on the value of its CDB
                assert(true_cdb_bytes == extract_bytes(subregion.view(pm_region).committed(), relative_cdb_addr as nat, u64::spec_size_of()));
                assert(true_cdb_bytes == extract_bytes(
                    extract_bytes(mem, (index * overall_metadata.main_table_entry_size) as nat, overall_metadata.main_table_entry_size as nat),
                    0,
                    u64::spec_size_of()
                ));

                match check_cdb_in_subregion(cdb, subregion, pm_region, Ghost(pm_region.constants().impervious_to_corruption), Ghost(relative_cdb_addrs)) {
                    Some(false) => {
                        // Slot is free -- we just need to put it in the allocator
                        let ghost old_metadata_allocator = metadata_allocator@;
                        metadata_allocator.push(index);
                        proof {
                            // these assertions hit triggers needed by the loop invariants
                            assert(metadata_allocator@.subrange(0, metadata_allocator@.len() - 1) == old_metadata_allocator);
                            assert(metadata_allocator@[metadata_allocator@.len() - 1] == index);
                            // Invoking this lemma here proves that the CDB we just read is the same one checked by parse_main_entry
                            lemma_subrange_of_extract_bytes_equal(mem, relative_cdb_addr as nat, relative_cdb_addr as nat, main_table_entry_size as nat, u64::spec_size_of());
                        }
                    }, 
                    Some(true) => {
                        // TODO: refactor this into its own function
                        // We have to read the entry to get its key and item index
                        // We don't need the metadata here, but we have to read it so we can check the CRC
                        
                        let relative_crc_addr = relative_cdb_addr + traits_t::size_of::<u64>() as u64;
                        let relative_entry_addr = relative_crc_addr + traits_t::size_of::<u64>() as u64;
                        let relative_key_addr = relative_entry_addr + traits_t::size_of::<ListEntryMetadata>()  as u64;

                        let ghost relative_crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| relative_crc_addr + i);
                        let ghost relative_entry_addrs = Seq::new(ListEntryMetadata::spec_size_of() as nat, |i: int| relative_entry_addr + i);
                        let ghost relative_key_addrs = Seq::new(K::spec_size_of() as nat, |i: int| relative_key_addr + i);

                        let ghost true_crc_bytes = Seq::new(relative_crc_addrs.len(), |i: int| subregion.view(pm_region).committed()[relative_crc_addrs[i]]);
                        let ghost true_entry_bytes = Seq::new(relative_entry_addrs.len(), |i: int| subregion.view(pm_region).committed()[relative_entry_addrs[i]]);
                        let ghost true_key_bytes = Seq::new(relative_key_addrs.len(), |i: int| subregion.view(pm_region).committed()[relative_key_addrs[i]]);

                        let ghost true_crc = u64::spec_from_bytes(true_crc_bytes);
                        let ghost true_entry = ListEntryMetadata::spec_from_bytes(true_entry_bytes);
                        let ghost true_key = K::spec_from_bytes(true_key_bytes);

                        proof {
                            assert(index * main_table_entry_size + u64::spec_size_of() * 2 < subregion.len());

                            assert(true_crc_bytes == extract_bytes(subregion.view(pm_region).committed(), relative_crc_addr as nat, u64::spec_size_of()));
                            assert(true_entry_bytes == extract_bytes(subregion.view(pm_region).committed(), relative_entry_addr as nat, ListEntryMetadata::spec_size_of()));
                            assert(true_entry_bytes == extract_bytes(
                                extract_bytes(mem, (index * main_table_entry_size) as nat, main_table_entry_size as nat),
                                u64::spec_size_of() * 2,
                                ListEntryMetadata::spec_size_of()
                            ));
                            assert(true_key_bytes == extract_bytes(subregion.view(pm_region).committed(), relative_key_addr as nat, K::spec_size_of()));
                            assert(true_key_bytes == extract_bytes(
                                extract_bytes(mem, (index * main_table_entry_size) as nat, main_table_entry_size as nat),
                                u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of(),
                                K::spec_size_of()
                            ));

                            lemma_if_table_parseable_then_all_entries_parseable::<K>(
                                subregion.view(pm_region).committed(),
                                overall_metadata.num_keys, 
                                overall_metadata.main_table_entry_size
                            );
                        }
                        
                        let crc = match subregion.read_relative_aligned::<u64, PM>(pm_region, relative_crc_addr) {
                            Ok(crc) => crc,
                            Err(e) => return Err(KvError::PmemErr { pmem_err: e })
                        };
                        let entry = match subregion.read_relative_aligned::<ListEntryMetadata, PM>(pm_region,
                                                                                                   relative_entry_addr) {
                            Ok(entry) => entry,
                            Err(e) => return Err(KvError::PmemErr { pmem_err: e })
                        };
                        let key = match subregion.read_relative_aligned::<K, PM>(pm_region, relative_key_addr) {
                            Ok(key) => key,
                            Err(e) => return Err(KvError::PmemErr { pmem_err: e })
                        };
                        
                        if !check_crc_for_two_reads_in_subregion(
                            entry.as_slice(), key.as_slice(), crc.as_slice(), subregion, pm_region, 
                            Ghost(pm_region.constants().impervious_to_corruption), Ghost(relative_entry_addrs),
                            Ghost(relative_key_addrs), Ghost(relative_crc_addrs)) {
                            assert(!pm_region.constants().impervious_to_corruption);
                            return Err(KvError::CRCMismatch);
                        }

                        let ghost pre_entry_list = Seq::new(key_index_pairs@.len(), |i: int| (*key_index_pairs[i].0, key_index_pairs[i].1, key_index_pairs[i].2));

                        let crc = crc.extract_init_val(Ghost(true_crc));
                        let key = key.extract_init_val(Ghost(true_key));
                        let metadata = entry.extract_init_val(Ghost(true_entry));
                        
                        let ghost old_item_index_view = Seq::new(key_index_pairs@.len(), |i: int| key_index_pairs[i].2);
                        assert(old_item_index_view.to_set().subset_of(table.valid_item_indices()));
                        let ghost old_key_index_pairs = key_index_pairs;

                        let ghost old_entry_list_view = Seq::new(key_index_pairs@.len(), |i: int| (*key_index_pairs[i].0, key_index_pairs[i].1, key_index_pairs[i].2));
                        assert(forall |i: int| 0 <= i < old_entry_list_view.len() ==> {
                            let entry = #[trigger] old_entry_list_view[i];
                            let table_index = entry.1;
                            let item_index = entry.2;
                            &&& table.durable_main_table[table_index as int] matches Some(valid_entry)
                            &&& valid_entry.item_index() == item_index
                            &&& valid_entry.key() == entry.0
                        });

                        proof {
                            // Prove that adding this entry will maintain the invariant that there are no duplicate keys
                            let entries = parse_main_entries::<K>(
                                subregion.view(pm_region).committed(),
                                overall_metadata.num_keys as nat, 
                                overall_metadata.main_table_entry_size as nat 
                            );
                            assert(no_duplicate_keys(entries));

                            // all main table indexes we have added to key_index_pairs so far are for indexes less than
                            // the current one.
                            let entry_list_view = Seq::new(key_index_pairs@.len(), |i: int| (*key_index_pairs[i].0, key_index_pairs[i].1, key_index_pairs[i].2));
                            assert forall |i: int| 0 <= i < key_index_pairs.len() implies {
                                let entry = #[trigger] key_index_pairs[i];
                                let table_index = entry.1;
                                0 <= table_index < index
                            } by {
                                assert(#[trigger] entry_list_view[i] == (*key_index_pairs@[i].0, key_index_pairs@[i].1, key_index_pairs@[i].2));
                            }
    
                            // all keys in key_index_pairs are different from `key` because `key` is the key of the current
                            // index in the main table, which we haven't procesed yet and we know has a different 
                            // key than all other main table entries
                            assert forall |i: int| 0 <= i < key_index_pairs.len() implies
                                *(#[trigger] key_index_pairs[i]).0 != key 
                            by {
                                let entry = #[trigger] key_index_pairs[i];
                                assert((*entry.0, entry.1, entry.2) == old_entry_list_view[i]);
                                let cur_key = *entry.0;
                                let table_index = entry.1;
                                assert(table.durable_main_table[table_index as int] is Some);
                                let valid_entry = table.durable_main_table[table_index as int].unwrap();
                                assert(valid_entry.key() == cur_key);
                                assert(key == table.durable_main_table[index as int].unwrap().key());
                            }
                        }

                        key_index_pairs.push((key, index, metadata.item_index));

                        assert(key_index_pairs@.subrange(0, key_index_pairs.len() - 1) == old_key_index_pairs@);
                        assert(key_index_pairs@[key_index_pairs.len() - 1] == (key, index, metadata.item_index));
                        
                        proof {
                            let new_item_index_view = Seq::new(key_index_pairs@.len(), |i: int| key_index_pairs[i].2);
                            let entry_list_view = Seq::new(key_index_pairs@.len(), |i: int| (*key_index_pairs[i].0, key_index_pairs[i].1, key_index_pairs[i].2));
                            
                            assert(entry_list_view.subrange(0, entry_list_view.len() - 1) == old_entry_list_view);

                            assert forall |i: int| 0 <= i < entry_list_view.len() implies {
                                let entry = #[trigger] entry_list_view[i];
                                let table_index = entry.1;
                                let item_index = entry.2;
                                &&& table.durable_main_table[table_index as int] matches Some(valid_entry)
                                &&& valid_entry.key() == entry.0
                                &&& valid_entry.item_index() == item_index
                                &&& 0 <= table_index < table.durable_main_table.len()
                                &&& table.valid_item_indices().contains(item_index)
                                &&& new_item_index_view.contains(item_index)
                            } by {
                                let entry = entry_list_view[i];
                                let table_index = entry.1;
                                let item_index = entry.2;

                                assert(item_index == new_item_index_view[i]);
                                if i < entry_list_view.len() - 1 {
                                    assert(entry == old_entry_list_view[i]);
                                    assert(table.durable_main_table[table_index as int] matches Some(valid_entry));
                                }

                                assert(table.durable_main_table[table_index as int] matches Some(valid_entry));
                            }

                            // This witness and the following few assertions help us maintain the loop invariant that 
                            // the set of valid item indices we are constructing is a subset of table.valid_item_indices()
                            let witness = table.durable_main_table[index as int];
                            assert(witness matches Some(valid_entry));
                            if let Some(valid_entry) = witness {
                                assert(valid_entry.item_index() == metadata.item_index);
                            }
                            assert(exists |j: int| {
                                &&& 0 <= j < table.durable_main_table.len() 
                                &&& #[trigger] table.durable_main_table[j] matches Some(valid_entry) 
                                &&& valid_entry.item_index() == metadata.item_index
                            }); 
                            assert(table.valid_item_indices().contains(metadata.item_index));
                            assert(new_item_index_view == old_item_index_view.push(metadata.item_index));
                            assert(new_item_index_view.to_set().subset_of(table.valid_item_indices()));
                        }
                    }
                    None => return Err(KvError::CRCMismatch)
                }

                proof {
                    let entry_list_view = Seq::new(key_index_pairs@.len(), |i: int| (*key_index_pairs[i].0, key_index_pairs[i].1, key_index_pairs[i].2));
                
                    assert forall |i: u64| 0 <= i <= index implies {
                        let entry = #[trigger] table.durable_main_table[i as int];
                        entry matches Some(valid_entry) ==> entry_list_view.contains((valid_entry.key(), i, valid_entry.item_index()))
                    } by {
                        // We already know this is true for values less than index from the loop invariant.
                        // To help Verus prove this, we need to establish that the part of the entry list we are making an assertion about has not
                        // changed on this iteration.
                        assert(entry_list_view == old_entry_list_view || entry_list_view.subrange(0, entry_list_view.len() - 1) == old_entry_list_view);
                        // Prove that the assertion holds when i == index
                        if i == index {
                            let entry = table.durable_main_table[i as int];
                            if let Some(valid_entry) = entry {
                                assert(entry_list_view[entry_list_view.len() - 1] == (valid_entry.key(), index, valid_entry.item_index()));
                            }
                        }
                    }
                }
                index += 1;
            }

            let main_table = MainTable {
                main_table_entry_size,
                main_table_free_list: metadata_allocator,
                modified_indices: Vec::new(),
                state: Ghost(parse_main_table::<K>(
                    subregion.view(pm_region).committed(),
                    overall_metadata.num_keys, 
                    overall_metadata.main_table_entry_size 
                ).unwrap()),
                outstanding_entries: OutstandingEntries::new(),
            };
            proof {
                let key_entry_list_view = Set::new(
                    |val: (K, u64, u64)| {
                        exists |j: u64| {
                            &&& 0 <= j < table.durable_main_table.len()
                            &&& #[trigger] table.durable_main_table[j as int] matches Some(entry)
                            &&& val == (entry.key(), j, entry.item_index())
                }});
                let entry_list_view = Seq::new(key_index_pairs@.len(), |i: int| (*key_index_pairs[i].0, key_index_pairs[i].1, key_index_pairs[i].2));
                let item_index_view = Seq::new(key_index_pairs@.len(), |i: int| key_index_pairs[i].2);

                assert(entry_list_view.to_set() == key_entry_list_view);
                assert(item_index_view.to_set() == main_table@.valid_item_indices());

                metadata_allocator@.unique_seq_to_set();

                let pm_view = subregion.view(pm_region);
                
                assert(forall |s| #[trigger] pm_view.can_crash_as(s) ==>
                    parse_main_table::<K>(s, overall_metadata.num_keys, overall_metadata.main_table_entry_size) == Some(main_table@));
                assert forall |i: u64| 0 <= i < main_table@.durable_main_table.len() && !(#[trigger] main_table.outstanding_entries@.contains_key(i)) implies
                    main_table.no_outstanding_writes_to_entry(subregion.view(pm_region), i, overall_metadata.main_table_entry_size)
                by {
                    lemma_valid_entry_index(i as nat, overall_metadata.num_keys as nat, overall_metadata.main_table_entry_size as nat);
                }

                assert(main_table@ == main_table.tentative_view());
            }

            Ok((main_table, key_index_pairs))
        }

        pub exec fn get_key_and_metadata_entry_at_index<PM>(
            &self,
            subregion: &PersistentMemorySubregion,
            pm_region: &PM,
            metadata_index: u64,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        ) -> (result: Result<(Box<K>, Box<ListEntryMetadata>), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires
                subregion.inv(pm_region),
                self.inv(subregion.view(pm_region), overall_metadata),
                0 <= metadata_index < overall_metadata.num_keys,
                ({
                    // either there is an outstanding entry that we can read, 
                    // or there is no outstanding entry but there is a durable entry
                    ||| ({
                            &&& self.outstanding_entries[metadata_index] matches Some(entry)
                            &&& (entry.status is Created || entry.status is Updated)
                        })
                    ||| ({
                            &&& self.outstanding_entries[metadata_index] is None 
                            &&& self@.durable_main_table[metadata_index as int] is Some
                        })
                })
            ensures
                ({
                    match result {
                        Ok((key, entry)) => {
                            // if there is an outstanding create or update, the returned value should 
                            // match it. 
                            &&& ({
                                    &&& self.outstanding_entries[metadata_index] matches Some(e)
                                    &&& (e.status is Created || e.status is Updated)
                                }) ==> {
                                    &&& self.outstanding_entries[metadata_index] matches Some(e)
                                    &&& e.key == key
                                    &&& e.entry == entry
                                }
                            &&& ({
                                    &&& self.outstanding_entries[metadata_index] is None 
                                    &&& self@.durable_main_table[metadata_index as int] is Some
                                }) ==> {
                                    &&& self@.durable_main_table[metadata_index as int] matches Some(e)
                                    &&& e.key == key
                                    &&& e.entry == entry
                                }
                        },
                        Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                        _ => false,
                    }
                }),
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;

            let ghost pm_view = subregion.view(pm_region);
            let main_table_entry_size = self.main_table_entry_size;
            proof {
                lemma_valid_entry_index(metadata_index as nat, overall_metadata.num_keys as nat, main_table_entry_size as nat);
            }

            // first, check if there is an outstanding update to read. if there is, we can 
            // return it without reading from PM at all
            if self.outstanding_entries.contents.contains_key(&metadata_index) {
                
                let entry = self.outstanding_entries.get(metadata_index).unwrap();
                match entry.status {
                    EntryStatus::Created | EntryStatus::Updated => return Ok((Box::new(entry.key), Box::new(entry.entry))),
                    _ => {
                        assert(false);
                        return Err(KvError::InternalError);
                    }
                }
            } else {
                let slot_addr = metadata_index * (main_table_entry_size as u64);
                let cdb_addr = slot_addr;
                let crc_addr = cdb_addr + traits_t::size_of::<u64>() as u64;
                let entry_addr = crc_addr + traits_t::size_of::<u64>() as u64;
                let key_addr = entry_addr + traits_t::size_of::<ListEntryMetadata>() as u64;
    
                // 1. Read the CDB, metadata entry, key, and CRC at the index
                let ghost mem = pm_view.committed();
    
                let ghost true_cdb_bytes = extract_bytes(mem, cdb_addr as nat, u64::spec_size_of());
                let ghost true_crc_bytes = extract_bytes(mem, crc_addr as nat, u64::spec_size_of());
                let ghost true_entry_bytes = extract_bytes(mem, entry_addr as nat, ListEntryMetadata::spec_size_of());
                let ghost true_key_bytes = extract_bytes(mem, key_addr as nat, K::spec_size_of());
    
                let ghost true_cdb = u64::spec_from_bytes(true_cdb_bytes);
                let ghost true_crc = u64::spec_from_bytes(true_crc_bytes);
                let ghost true_entry = ListEntryMetadata::spec_from_bytes(true_entry_bytes);
                let ghost true_key = K::spec_from_bytes(true_key_bytes);
    
                let ghost cdb_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| cdb_addr + subregion.start() + i);
                let ghost entry_addrs = Seq::new(ListEntryMetadata::spec_size_of() as nat,
                                                 |i: int| entry_addr + subregion.start() + i);
                let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| crc_addr + subregion.start() + i);
                let ghost key_addrs = Seq::new(K::spec_size_of() as nat, |i: int| key_addr + subregion.start() + i);
    
                // 2. Check the CDB to determine whether the entry is valid
                proof {
                    self.lemma_establish_bytes_parseable_for_valid_entry(pm_view, overall_metadata, metadata_index);
                    assert(extract_bytes(pm_view.committed(), cdb_addr as nat, u64::spec_size_of()) =~=
                           Seq::new(u64::spec_size_of() as nat, |i: int| pm_region@.committed()[cdb_addrs[i]]));
                }
                let cdb = match subregion.read_relative_aligned::<u64, PM>(pm_region, cdb_addr) {
                    Ok(cdb) => cdb,
                    Err(_) => {
                        assert(false);
                        return Err(KvError::EntryIsNotValid);
                    }
                };
                let cdb_result = check_cdb(cdb, Ghost(pm_region@.committed()),
                                           Ghost(pm_region.constants().impervious_to_corruption), Ghost(cdb_addrs));
                match cdb_result {
                    Some(true) => {}, // continue 
                    Some(false) => { assert(false); return Err(KvError::EntryIsNotValid); },
                    None => { return Err(KvError::CRCMismatch); },
                }
    
                proof {
                    // assert(self.outstanding_entry_write_matches_pm_view(pm_view, metadata_index, main_table_entry_size));
                    assert(extract_bytes(pm_view.committed(), crc_addr as nat, u64::spec_size_of()) =~=
                           Seq::new(u64::spec_size_of() as nat, |i: int| pm_region@.committed()[crc_addrs[i]]));
                    assert(extract_bytes(pm_view.committed(), entry_addr as nat, ListEntryMetadata::spec_size_of()) =~=
                           Seq::new(ListEntryMetadata::spec_size_of() as nat, |i: int| pm_region@.committed()[entry_addrs[i]]));
                    assert(extract_bytes(pm_view.committed(), key_addr as nat, K::spec_size_of()) =~=
                           Seq::new(K::spec_size_of() as nat, |i: int| pm_region@.committed()[key_addrs[i]]));
                }
                let crc = match subregion.read_relative_aligned::<u64, PM>(pm_region, crc_addr) {
                    Ok(crc) => crc,
                    Err(e) => { assert(false); return Err(KvError::PmemErr { pmem_err: e }); },
                };
                let metadata_entry = match subregion.read_relative_aligned::<ListEntryMetadata, PM>(pm_region, entry_addr) {
                    Ok(metadata_entry) => metadata_entry,
                    Err(e) => { assert(false); return Err(KvError::PmemErr { pmem_err: e }); },
                };
                let key = match subregion.read_relative_aligned::<K, PM>(pm_region, key_addr) {
                    Ok(key) => key,
                    Err(e) => { assert(false); return Err(KvError::PmemErr {pmem_err: e }); },
                };
    
                // 3. Check for corruption
                if !check_crc_for_two_reads(
                    metadata_entry.as_slice(), key.as_slice(), crc.as_slice(), Ghost(pm_region@.committed()),
                    Ghost(pm_region.constants().impervious_to_corruption), Ghost(entry_addrs), Ghost(key_addrs),
                    Ghost(crc_addrs)) 
                {
                    return Err(KvError::CRCMismatch);
                }
    
                // 4. Return the metadata entry and key
                let metadata_entry = metadata_entry.extract_init_val(Ghost(true_entry));
                let key = key.extract_init_val(Ghost(true_key));
                Ok((key, metadata_entry))
            }
        }

        proof fn lemma_changing_invalid_entry_doesnt_affect_parse_main_table(
            self: Self,
            v1: PersistentMemoryRegionView,
            v2: PersistentMemoryRegionView,
            crash_state2: Seq<u8>,
            overall_metadata: OverallMetadata,
            which_entry: u64,
        )
            requires
                self.inv(v1, overall_metadata),
                self.free_list().contains(which_entry),
                v1.len() == v2.len(),
                v2.can_crash_as(crash_state2),
                forall|addr: int| {
                    let start_addr = which_entry * overall_metadata.main_table_entry_size;
                    let end_addr = start_addr + overall_metadata.main_table_entry_size;
                    &&& 0 <= addr < v1.len()
                    &&& !(start_addr + u64::spec_size_of() <= addr < end_addr)
                } ==> v2.state[addr] == v1.state[addr],
            ensures
                parse_main_table::<K>(crash_state2, overall_metadata.num_keys, overall_metadata.main_table_entry_size)
                    == Some(self@),
        {
            let num_keys = overall_metadata.num_keys;
            let main_table_entry_size = overall_metadata.main_table_entry_size;
            let start_addr = which_entry * main_table_entry_size;
            let end_addr = start_addr + main_table_entry_size;
            let crc_addr = start_addr + u64::spec_size_of();
            let can_views_differ_at_addr = |addr: int| crc_addr <= addr < end_addr;
            assert(which_entry < num_keys);
            let crash_state1 = lemma_get_crash_state_given_one_for_other_view_differing_only_at_certain_addresses(
                v2, v1, crash_state2, can_views_differ_at_addr
            );
            assert(parse_main_table::<K>(crash_state1, num_keys, main_table_entry_size) == Some(self@));
            lemma_valid_entry_index(which_entry as nat, num_keys as nat, main_table_entry_size as nat);
            let entry_bytes = extract_bytes(crash_state1,
                                            index_to_offset(which_entry as nat, main_table_entry_size as nat),
                                            main_table_entry_size as nat);
            assert(validate_main_entry::<K>(entry_bytes, num_keys as nat));
            lemma_subrange_of_subrange_forall(crash_state1);
            assert forall|addr: int| crc_addr <= addr < end_addr implies
                       address_belongs_to_invalid_main_table_entry(addr, crash_state1, num_keys, main_table_entry_size)
            by {
                assert(addr / main_table_entry_size as int == which_entry) by {
                    lemma_fundamental_div_mod_converse(
                        addr, main_table_entry_size as int, which_entry as int, addr - which_entry * main_table_entry_size
                    );
                }
            }
            assert forall|addr: int| 0 <= addr < crash_state1.len() && crash_state1[addr] != crash_state2[addr] implies
                   #[trigger] address_belongs_to_invalid_main_table_entry(addr, crash_state1, num_keys,
                                                                          main_table_entry_size) by {
                assert(can_views_differ_at_addr(addr));
            }
            lemma_parse_main_table_doesnt_depend_on_fields_of_invalid_entries::<K>(
                crash_state1, crash_state2, num_keys, main_table_entry_size
            );
        }

        // Since main table entries have a valid CDB, we can tentatively write the whole entry and log a commit op for it,
        // then flip the CDB once the log has been committed
        pub exec fn tentative_create<Perm, PM>(
            &mut self,
            subregion: &WriteRestrictedPersistentMemorySubregion,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
            list_node_index: u64,
            item_table_index: u64,
            key: &K,
            Tracked(perm): Tracked<&Perm>,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        ) -> (result: Result<u64, KvError<K>>)
            where 
                Perm: CheckPermission<Seq<u8>>,
                PM: PersistentMemoryRegion,
            requires 
                subregion.inv(old::<&mut _>(wrpm_region), perm),
                old(self).inv(subregion.view(old::<&mut _>(wrpm_region)), overall_metadata),
                subregion.len() >= overall_metadata.main_table_size,
                old(self).subregion_grants_access_to_free_slots(*subregion),
                // old(self).allocator_inv(),
            ensures
                subregion.inv(wrpm_region, perm),
                self.inv(subregion.view(wrpm_region), overall_metadata),
                // self.allocator_inv(),
                subregion.view(wrpm_region).committed() == subregion.view(old::<&mut _>(wrpm_region)).committed(),
                match result {
                    Ok(index) => {
                        &&& old(self).free_list().contains(index)
                        &&& old(self)@.durable_main_table[index as int] is None
                        &&& self.free_list() == old(self).free_list().remove(index)
                        &&& self@.durable_main_table == old(self)@.durable_main_table
                        &&& forall |i: u64| 0 <= i < overall_metadata.num_keys && i != index ==>
                            #[trigger] self.outstanding_entries[i] == old(self).outstanding_entries[i]
                        &&& self.outstanding_entries[index] matches Some(e)
                        &&& e.key == *key
                        &&& e.entry.head == list_node_index
                        &&& e.entry.tail == list_node_index
                        &&& e.entry.length == 0
                        &&& e.entry.first_entry_offset == 0
                        &&& e.entry.item_index == item_table_index
                    },
                    Err(KvError::OutOfSpace) => {
                        &&& self@ == old(self)@
                        &&& self.free_list() == old(self).free_list()
                        &&& self.free_indices() == old(self).free_indices()
                        // &&& self.pending_allocations_view() == old(self).pending_allocations_view()
                        // &&& self.pending_deallocations_view() == old(self).pending_deallocations_view()
                        &&& self.free_list().len() == 0
                        &&& wrpm_region == old(wrpm_region)
                    },
                    _ => false,
                }
        {
            let ghost old_pm_view = subregion.view(wrpm_region);
            assert(self.inv(old_pm_view, overall_metadata));

            // 1. pop an index from the free list
            // since this index is on the free list, its CDB is already false
            let free_index = match self.main_table_free_list.pop(){
                Some(index) => index,
                None => {
                    assert(self.main_table_free_list@.to_set().len() == 0) by {
                        self.main_table_free_list@.lemma_cardinality_of_set();
                    }
                    return Err(KvError::OutOfSpace);
                },
            };
            // self.pending_allocations.push(free_index);
            assert(self.free_list() == old(self).free_list().remove(free_index)
                   && self.main_table_free_list@.no_duplicates()) by {
                lemma_drop_last_from_seq_with_no_duplicates_removes_last_from_set(old(self).main_table_free_list@);
            }
            self.modified_indices.push(free_index);    

            assert(old(self).free_list().contains(free_index)) by {
                assert(old(self).main_table_free_list@.last() == free_index);
            }
            
            assert(self.free_list().len() < old(self).free_list().len()) by {
                assert(self.main_table_free_list@.len() < old(self).main_table_free_list@.len());
                self.main_table_free_list@.unique_seq_to_set();
                old(self).main_table_free_list@.unique_seq_to_set();
            }

            proof {
                assert forall |idx| self.main_table_free_list@.contains(idx) implies idx < overall_metadata.num_keys by {
                    assert(old(self).main_table_free_list@.contains(idx));
                }
            }

            // 2. construct the entry with list metadata and item index
            let entry = ListEntryMetadata::new(list_node_index, list_node_index, 0, 0, item_table_index);

            // 3. calculate the CRC of the entry + key 
            let mut digest = CrcDigest::new();
            digest.write(&entry);
            digest.write(key);
            proof {
                reveal_with_fuel(Seq::flatten, 3);
                assert(digest.bytes_in_digest().flatten() =~=
                       ListEntryMetadata::spec_to_bytes(entry) + K::spec_to_bytes(*key));
            }
            let crc = digest.sum64();
            assert(crc.spec_to_bytes() == spec_crc_bytes(ListEntryMetadata::spec_to_bytes(entry) +
                                                         K::spec_to_bytes(*key)));

            broadcast use pmcopy_axioms;
            
            // 4. write CRC and entry 
            let main_table_entry_size = self.main_table_entry_size;
            proof {
                lemma_valid_entry_index(free_index as nat, overall_metadata.num_keys as nat, main_table_entry_size as nat);
                assert(old(self).outstanding_entries[free_index] is None);
            }

            let slot_addr = free_index * main_table_entry_size as u64;
            // CDB is at slot addr -- we aren't setting that one yet
            let crc_addr = slot_addr + traits_t::size_of::<u64>() as u64;
            let entry_addr = crc_addr + traits_t::size_of::<u64>() as u64;
            let key_addr = entry_addr + traits_t::size_of::<ListEntryMetadata>() as u64;

            assert(subregion_grants_access_to_main_table_entry::<K>(*subregion, free_index));
            subregion.serialize_and_write_relative::<u64, Perm, PM>(wrpm_region, crc_addr, &crc, Tracked(perm));
            subregion.serialize_and_write_relative::<ListEntryMetadata, Perm, PM>(wrpm_region, entry_addr,
                                                                                  &entry, Tracked(perm));
            subregion.serialize_and_write_relative::<K, Perm, PM>(wrpm_region, key_addr, &key, Tracked(perm));

            let ghost main_table_entry = MainTableViewEntry{entry, key: *key };
            self.outstanding_entry_create(free_index, entry, *key);

            let ghost pm_view = subregion.view(wrpm_region);
            assert(pm_view.committed() == old_pm_view.committed());

            assert forall |s| #[trigger] pm_view.can_crash_as(s) implies
                parse_main_table::<K>(s, overall_metadata.num_keys,
                                      overall_metadata.main_table_entry_size) == Some(self@) by {
                old(self).lemma_changing_invalid_entry_doesnt_affect_parse_main_table(
                    old_pm_view, pm_view, s, overall_metadata, free_index
                );
                assert(self@ == old(self)@);
            }

            assert(subregion.view(wrpm_region).committed() =~= subregion.view(old::<&mut _>(wrpm_region)).committed());
            assert(self.free_list() == old(self).free_list().remove(free_index));

            // TODO @jay
            assume(self.main_table_free_list@.no_duplicates());
            assume(self.modified_indices@.no_duplicates());
            assume(no_duplicate_item_indexes(self.tentative_view().durable_main_table));
            assume(forall|idx| self.main_table_free_list.view().contains(idx) ==> 0 <= idx < overall_metadata.num_keys);
            assume(forall|idx| self.modified_indices@.contains(idx) ==> 0 <= idx < overall_metadata.num_keys);
            assume(forall|idx| self.outstanding_entries@.contains_key(idx) <==> 
                   #[trigger] self.modified_indices@.contains(idx));
            assume(self.outstanding_entries@.len() == self.modified_indices@.len());
            assume(forall |idx: u64| #[trigger] self.modified_indices@.contains(idx) ==>
                   !self.main_table_free_list@.contains(idx));
            assume(forall |idx: u64| 0 <= idx < self@.durable_main_table.len() && !self.main_table_free_list@.contains(idx) ==>
                    self@.durable_main_table[idx as int] is Some || #[trigger] self.modified_indices@.contains(idx));
            assume(forall |idx: u64| {
                    &&& #[trigger] self.outstanding_entries@.contains_key(idx) 
                    &&& !((self.outstanding_entries@[idx].status is Created || 
                                self.outstanding_entries@[idx].status is CreatedThenDeleted)) 
                } ==> self@.durable_main_table[idx as int] is Some);
            assume(forall |idx: u64| {
                    &&& 0 <= idx < self@.durable_main_table.len() 
                    &&& {
                        ||| self@.durable_main_table[idx as int] is Some
                        ||| self.outstanding_entries[idx] is Some
                    }
                } ==> !(#[trigger] self.main_table_free_list@.contains(idx)));
            assume(forall |idx: u64| {
                    &&& #[trigger] self.outstanding_entries@.contains_key(idx) 
                    &&& (self.outstanding_entries@[idx].status is Created || 
                                self.outstanding_entries@[idx].status is CreatedThenDeleted)
                } ==> self@.durable_main_table[idx as int] is None);
            assume(self.modified_indices@.len() <= self@.durable_main_table.len());
            assert(old(self).main_table_entry_size == overall_metadata.main_table_entry_size);
            assume(self.main_table_entry_size == overall_metadata.main_table_entry_size);
            assume(forall |idx: u64| 0 <= idx < self@.durable_main_table.len() && !(#[trigger] self.outstanding_entries@.contains_key(idx)) ==>
                    self.no_outstanding_writes_to_entry(subregion.view(wrpm_region), idx, overall_metadata.main_table_entry_size));

            Ok(free_index)
        }

        pub exec fn tentatively_deallocate_entry(
            &mut self,
            Ghost(pm_subregion): Ghost<PersistentMemoryRegionView>,
            index: u64,
            entry: ListEntryMetadata,
            key: K,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        )
            requires 
                old(self).inv(pm_subregion, overall_metadata),
                0 <= index < overall_metadata.num_keys,
                ({
                    &&& old(self).tentative_view().durable_main_table[index as int] matches Some(e)
                    &&& e.entry == entry 
                    &&& e.key == key
                }),
                !old(self).free_list().contains(index),
                old(self).outstanding_entries.inv(),
            ensures 
                self.inv(pm_subregion, overall_metadata),
                old(self).free_list() == self.free_list(),
                self.free_indices() == old(self).free_indices(),
                ({
                    let status = old(self).outstanding_entries.get_delete_status(index);
                    let new_entry = OutstandingEntry {
                        status,
                        entry, 
                        key
                    };
                    self.outstanding_entries@ == old(self).outstanding_entries@.insert(index, new_entry)
                }),
                old(self)@ == self@,
                old(self).main_table_entry_size == self.main_table_entry_size,
                Some(self.tentative_view()) == old(self).tentative_view().delete(index as int),
                ({
                    let old_item_index = old(self).get_latest_entry(index).unwrap().entry.item_index;
                    self.tentative_view().valid_item_indices() == old(self).tentative_view().valid_item_indices().remove(old_item_index)
                })
        {
            self.outstanding_entry_delete(index, entry, key, Ghost(overall_metadata));

            proof {
                assert(old(self).tentative_view().durable_main_table[index as int] is Some);
                assert(self.tentative_view().durable_main_table[index as int] is None);
                assert(self.tentative_view().durable_main_table == 
                    old(self).tentative_view().durable_main_table.update(index as int, None));

                assert(self.tentative_view().durable_main_table[index as int] is None);

                let old_item_index = old(self).get_latest_entry(index).unwrap().entry.item_index;
                assert(old(self).tentative_view().valid_item_indices().contains(old_item_index));

                assert(forall |i: int| 0 <= i < self.tentative_view().durable_main_table.len() ==> {
                    &&& i != index ==> self.tentative_view().durable_main_table[i] == old(self).tentative_view().durable_main_table[i]
                    &&& i == index ==> self.tentative_view().durable_main_table[i] is None
                });
                assert(forall |i: int| 0 <= i < self.tentative_view().durable_main_table.len() && i != index ==> 
                    #[trigger] old(self).tentative_view().durable_main_table[i] is Some ==> old(self).tentative_view().durable_main_table[i].unwrap().entry.item_index != old_item_index);
                assert(!self.tentative_view().valid_item_indices().contains(old_item_index));

                assert(self.tentative_view().valid_item_indices() =~= old(self).tentative_view().valid_item_indices().remove(old_item_index));
            }
        }

        exec fn finalize_outstanding_entries(
            &mut self,
            Ghost(pm): Ghost<PersistentMemoryRegionView>,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        )
            requires 
                old(self).outstanding_entries.inv(),
                old(self).modified_indices@.no_duplicates(),
                old(self).main_table_free_list@.no_duplicates(),
                no_duplicate_item_indexes(old(self).tentative_view().durable_main_table),
                no_duplicate_item_indexes(old(self)@.durable_main_table),
                old(self)@.durable_main_table.len() == overall_metadata.num_keys,
                forall |idx: u64| old(self).main_table_free_list@.contains(idx) ==> idx < overall_metadata.num_keys,
                forall |idx: u64| old(self).modified_indices@.contains(idx) ==> idx < overall_metadata.num_keys,
                forall |i: u64| 0 <= i < old(self).modified_indices.len() ==> { 
                    let j = #[trigger] old(self).modified_indices@[i as int];
                    &&& old(self).modified_indices@.contains(j) ==> !old(self).main_table_free_list@.contains(j)
                    &&& old(self).main_table_free_list@.contains(j) ==> !old(self).modified_indices@.contains(j)
                },
                forall |idx: u64| old(self).outstanding_entries@.contains_key(idx) <==> 
                    #[trigger]  old(self).modified_indices@.contains(idx),
                vstd::std_specs::hash::obeys_key_model::<K>(),

                forall |idx: u64| 0 <= idx < old(self)@.durable_main_table.len() && !old(self).main_table_free_list@.contains(idx) ==>
                    old(self)@.durable_main_table[idx as int] is Some || #[trigger] old(self).modified_indices@.contains(idx),

                // we have already committed the log when we finalize outstanding entries, so deleted entries
                // are invalid and created/updated entries are valid
                forall |idx: u64| old(self).outstanding_entries@.contains_key(idx) ==> {
                    let entry = old(self).outstanding_entries[idx].unwrap();
                    match entry.status {
                        EntryStatus::Created | EntryStatus::Updated => old(self)@.durable_main_table[idx as int] is Some,
                        EntryStatus::Deleted | EntryStatus::CreatedThenDeleted => old(self)@.durable_main_table[idx as int] is None
                    }
                },

                // we have not yet updated the free list, but all entries that are Some were either already valid or 
                // were created in this transaction, so they aren't in the free list
                forall |idx: u64| 0 <= idx < old(self)@.durable_main_table.len() && old(self)@.durable_main_table[idx as int] is Some ==>
                    !(#[trigger] old(self).main_table_free_list@.contains(idx)),

                old(self).modified_indices@.len() <= old(self)@.durable_main_table.len(),
            ensures 
                self.opaquable_inv(overall_metadata),
                self.outstanding_entries@.len() == 0,
                self.main_table_entry_size == old(self).main_table_entry_size,
                self@ == old(self)@,
                forall |idx: u64| {
                    // the free list contains idx if idx was already in the 
                    // free list or if idx was deleted/deallocated in this
                    // transaction. 
                    ||| old(self).main_table_free_list@.contains(idx)
                    ||| {
                        &&& old(self).modified_indices@.contains(idx)
                        &&& (old(self).outstanding_entries@[idx].status is Deleted || 
                                old(self).outstanding_entries@[idx].status is CreatedThenDeleted)
                    }
                } <==> #[trigger] self.main_table_free_list@.contains(idx)
        {
            // iterate over the modified indices and determine if
            // and how to update the free list.
            // deleted indices go back in the free list, created/updated
            // ones do not.
            let mut index = 0;
            while index < self.modified_indices.len() 
                invariant 
                    self.modified_indices@.no_duplicates(),
                    no_duplicate_item_indexes(self.tentative_view().durable_main_table),
                    no_duplicate_item_indexes(self@.durable_main_table),
                    self@ == old(self)@,
                    self.main_table_entry_size == old(self).main_table_entry_size,
                    forall |i: u64| index <= i < self.modified_indices.len() ==> { 
                        let j = #[trigger] self.modified_indices@[i as int];
                        &&& self.modified_indices@.contains(j) ==> !self.main_table_free_list@.contains(j)
                        &&& self.main_table_free_list@.contains(j) ==> !self.modified_indices@.contains(j)
                    },
                    forall |idx: u64| self.outstanding_entries@.contains_key(idx) <==> 
                        #[trigger] self.modified_indices@.contains(idx),
                    self.outstanding_entries@ == old(self).outstanding_entries@,
                    self.modified_indices@ == old(self).modified_indices@,
                    self.main_table_free_list@.no_duplicates(),
                    vstd::std_specs::hash::obeys_key_model::<K>(),
                    self@.durable_main_table == old(self)@.durable_main_table,
                    forall |idx: u64| self.modified_indices@.contains(idx) ==> idx < overall_metadata.num_keys,
                    forall |idx: u64| self.main_table_free_list@.contains(idx) ==> idx < overall_metadata.num_keys,
                    forall |idx: u64| 0 <= idx < self@.durable_main_table.len() && !self.main_table_free_list@.contains(idx) ==>
                        self@.durable_main_table[idx as int] is Some || #[trigger] self.modified_indices@.contains(idx),

                    self.modified_indices@.len() <= self@.durable_main_table.len(),

                    forall |i: int| {
                        let idx = #[trigger] self.modified_indices@[i];
                        &&& index <= i < self.modified_indices@.len()
                        &&& self@.durable_main_table[idx as int] is Some
                    } ==> {
                        let idx = self.modified_indices@[i];
                        !(self.main_table_free_list@.contains(idx))
                    },

                    forall |i: int| {
                        let idx = #[trigger] self.modified_indices@[i];
                        &&& 0 <= i < index
                        &&& self.outstanding_entries[idx] matches Some(entry)
                        &&& (entry.status is Deleted || entry.status is CreatedThenDeleted)
                    } ==> {
                        let idx = self.modified_indices@[i];
                        self.main_table_free_list@.contains(idx)
                    },

                    // no entries are removed from the free list
                    forall |idx: u64| old(self).main_table_free_list@.contains(idx) ==>
                        self.main_table_free_list@.contains(idx),

                    // all new free list elements are associated with a deleted entry
                    forall |idx: u64| !old(self).main_table_free_list@.contains(idx) && self.main_table_free_list@.contains(idx) ==> {
                        &&& self.outstanding_entries[idx] matches Some(entry)
                        &&& (entry.status is Deleted || entry.status is CreatedThenDeleted)
                    },

                    
            {
                let ghost free_list_at_top = self.main_table_free_list@;
                let current_index = self.modified_indices[index];
                assert(self.modified_indices@.contains(current_index)); // required for triggers
                assert(current_index < overall_metadata.num_keys);

                let current_entry = self.outstanding_entries.get(current_index).unwrap();
                match current_entry.status {
                    EntryStatus::Deleted | EntryStatus::CreatedThenDeleted => {
                        self.main_table_free_list.push(current_index);
                        assert(self.main_table_free_list@.subrange(0, free_list_at_top.len() as int) == free_list_at_top);
                        assert(self.main_table_free_list@[free_list_at_top.len() as int] == current_index);
                        assert(self.main_table_free_list@.contains(current_index));
                        assert forall |idx: u64| self.main_table_free_list@.contains(idx) implies idx < overall_metadata.num_keys by {
                            if idx != current_index {
                                assert(free_list_at_top.contains(idx));
                            }
                        }
                    }
                    // Otherwise, do nothing. newly created and updated indices 
                    // are not added back into the free list
                    _ => {}
                }
                index += 1;
            }

            self.modified_indices.clear();
            self.outstanding_entries.clear();

            assert forall |idx: u64| 0 <= idx < self@.durable_main_table.len() && !self.main_table_free_list@.contains(idx) implies
                self@.durable_main_table[idx as int] is Some || #[trigger] self.modified_indices@.contains(idx)
            by {
                if !old(self).main_table_free_list@.contains(idx) {
                    // neither the old nor new free list contain idx

                    // by opaquable_inv, if the free list does not contain idx, then it is either
                    // currently valid or has an outstanding write
                    if old(self)@.durable_main_table[idx as int] is Some {
                        assert(self@.durable_main_table[idx as int] is Some);
                    } else {
                        assert(old(self).modified_indices@.contains(idx));
                    }
                } // else, trivial
            }
        }

        #[verifier::rlimit(20)]
        pub exec fn create_validify_log_entry(
            &self,
            Ghost(subregion_view): Ghost<PersistentMemoryRegionView>,
            Ghost(mem): Ghost<Seq<u8>>,
            index: u64,
            Ghost(version_metadata): Ghost<VersionMetadata>,
            overall_metadata: &OverallMetadata,
            Ghost(op_log): Ghost<Seq<AbstractPhysicalOpLogEntry>>,
        ) -> (log_entry: PhysicalOpLogEntry)
            requires 
                self.inv(subregion_view, *overall_metadata),
                overall_metadata.main_table_size >= overall_metadata.num_keys * overall_metadata.main_table_entry_size,
                0 <= index < self@.len(),
                // the index must refer to a currently-invalid entry in the current durable table
                self@.durable_main_table[index as int] is None,
                self.outstanding_entries[index] is Some,
                parse_main_table::<K>(subregion_view.committed(), overall_metadata.num_keys,
                                      overall_metadata.main_table_entry_size) == Some(self@),
                overall_metadata.main_table_entry_size ==
                    ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
                mem.len() == overall_metadata.region_size,
                overall_metadata.main_table_addr + overall_metadata.main_table_size <= overall_metadata.log_area_addr
                    <= overall_metadata.region_size <= u64::MAX,
                // log_entries_do_not_modify_free_main_table_entries(op_log, self.free_indices(), *overall_metadata),
                apply_physical_log_entries(mem, op_log) is Some,
                ({
                    let current_tentative_state = apply_physical_log_entries(mem, op_log).unwrap();
                    let main_table_region = extract_bytes(current_tentative_state, 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    let main_table_view = parse_main_table::<K>(main_table_region,
                        overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                    let entry_bytes = extract_bytes(
                        main_table_region,
                        index_to_offset(index as nat, overall_metadata.main_table_entry_size as nat),
                        overall_metadata.main_table_entry_size as nat
                    );
                    let crc_bytes = extract_bytes(entry_bytes, u64::spec_size_of(), u64::spec_size_of());
                    let metadata_bytes = extract_bytes(entry_bytes, u64::spec_size_of() * 2,
                                                       ListEntryMetadata::spec_size_of());
                    let key_bytes = extract_bytes(
                        entry_bytes, u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of(), K::spec_size_of()
                    );
                    let crc = u64::spec_from_bytes(crc_bytes);
                    let metadata = ListEntryMetadata::spec_from_bytes(metadata_bytes);
                    let key = K::spec_from_bytes(key_bytes);
                    let entry = self.outstanding_entries[index].unwrap();
                    let item_index = entry.entry.item_index;
                    &&& main_table_view is Some
                    &&& main_table_view.unwrap().inv(*overall_metadata)
                    &&& forall|i| 0 <= i < overall_metadata.num_keys &&
                           #[trigger] main_table_view.unwrap().durable_main_table[i] is Some
                           ==> main_table_view.unwrap().durable_main_table[i].unwrap().key != entry.key
                    &&& metadata_bytes == entry.entry.spec_to_bytes()
                    &&& key_bytes == entry.key.spec_to_bytes()
                    &&& !main_table_view.unwrap().valid_item_indices().contains(item_index)
                    &&& crc == spec_crc_u64(metadata_bytes + key_bytes)
                    &&& u64::bytes_parseable(crc_bytes)
                    &&& ListEntryMetadata::bytes_parseable(metadata_bytes)
                    &&& K::bytes_parseable(key_bytes)
                    &&& 0 <= metadata.item_index < overall_metadata.num_keys
                    &&& key == entry.key
                    &&& metadata == entry.entry
                }),
                VersionMetadata::spec_size_of() <= version_metadata.overall_metadata_addr,
                version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() + u64::spec_size_of()
                    <= overall_metadata.main_table_addr,
            ensures 
                log_entry@.inv(version_metadata, *overall_metadata),
                overall_metadata.main_table_addr <= log_entry.absolute_addr,
                log_entry.absolute_addr + log_entry.len <=
                    overall_metadata.main_table_addr + overall_metadata.main_table_size,
                log_entry_does_not_modify_free_main_table_entries(log_entry@, self.free_indices(), *overall_metadata),
                ({
                    let current_tentative_state = apply_physical_log_entries(mem, op_log).unwrap();
                    let new_mem = apply_physical_log_entry(current_tentative_state, log_entry@);
                    let current_main_table_region = extract_bytes(current_tentative_state, 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    let current_main_table_view = parse_main_table::<K>(current_main_table_region,
                        overall_metadata.num_keys, overall_metadata.main_table_entry_size).unwrap();
                    let new_main_table_region = extract_bytes(new_mem.unwrap(), 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    let new_main_table_view = parse_main_table::<K>(new_main_table_region,
                        overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                    let entry = self.outstanding_entries@[index];
                    &&& new_mem is Some
                    &&& new_main_table_view == Some(current_main_table_view.update(index as int, entry@))
                    &&& new_main_table_view.unwrap().valid_item_indices() ==
                        current_main_table_view.valid_item_indices().insert(entry.entry.item_index)
                }),
        {
            assume(false); // TODO @jay
            let entry_slot_size = overall_metadata.main_table_entry_size;
            let ghost current_tentative_state = apply_physical_log_entries(mem, op_log).unwrap();
            let ghost entry = self.outstanding_entries[index].unwrap();
            let ghost item_index = entry.entry.item_index;
            // Proves that index * entry_slot_size will not overflow
            proof {
                lemma_valid_entry_index(index as nat, overall_metadata.num_keys as nat, entry_slot_size as nat);
                lemma_log_replay_preserves_size(mem, op_log);
            }
            
            let index_offset = index * entry_slot_size as u64;
            assert(index_offset == index_to_offset(index as nat, entry_slot_size as nat));

            let log_entry = PhysicalOpLogEntry {
                absolute_addr: overall_metadata.main_table_addr + index_offset,
                len: traits_t::size_of::<u64>() as u64,
                bytes: slice_to_vec(CDB_TRUE.as_byte_slice()),
            };

            proof {
                broadcast use pmcopy_axioms;

                let new_mem = current_tentative_state.map(|pos: int, pre_byte: u8|
                    if log_entry.absolute_addr <= pos < log_entry.absolute_addr + log_entry.len {
                        log_entry.bytes[pos - log_entry.absolute_addr]
                    } else {
                        pre_byte
                    }
                );
                assert(current_tentative_state.len() >= overall_metadata.main_table_addr + overall_metadata.main_table_size);
                assert(new_mem.len() == current_tentative_state.len());
                
                let old_main_table_region = extract_bytes(current_tentative_state, 
                    overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let new_main_table_region = extract_bytes(new_mem,
                    overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                lemma_establish_extract_bytes_equivalence(old_main_table_region, new_main_table_region);

                let committed_main_table_view = parse_main_table::<K>(subregion_view.committed(),
                    overall_metadata.num_keys, overall_metadata.main_table_entry_size).unwrap();
                let old_main_table_view = parse_main_table::<K>(old_main_table_region,
                    overall_metadata.num_keys, overall_metadata.main_table_entry_size).unwrap();
                let new_main_table_view = parse_main_table::<K>(new_main_table_region,
                    overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                
                assert forall |i: nat| #![trigger extract_bytes(new_main_table_region,
                                                         index_to_offset(i, entry_slot_size as nat),
                                                         entry_slot_size as nat)]
                           i < overall_metadata.num_keys implies {
                    let offset = index_to_offset(i, entry_slot_size as nat);
                    let old_entry_bytes = extract_bytes(old_main_table_region, offset,
                                                        entry_slot_size as nat);
                    let entry_bytes = extract_bytes(new_main_table_region, offset, entry_slot_size as nat);
                    &&& validate_main_entry::<K>(entry_bytes, overall_metadata.num_keys as nat)
                    &&& i == index ==>
                           parse_main_entry::<K>(entry_bytes, overall_metadata.num_keys as nat) ==
                           Some(entry@)
                    &&& i != index ==> parse_main_entry::<K>(entry_bytes, overall_metadata.num_keys as nat) == 
                           parse_main_entry::<K>(old_entry_bytes, overall_metadata.num_keys as nat)
                } by {
                    let offset = index_to_offset(i, entry_slot_size as nat);
                    let entry_bytes = extract_bytes(new_main_table_region, offset, entry_slot_size as nat);
                    lemma_valid_entry_index(i, overall_metadata.num_keys as nat, entry_slot_size as nat);
                    lemma_entries_dont_overlap_unless_same_index(i, index as nat, entry_slot_size as nat);
                    assert(new_main_table_region.len() >= offset + entry_slot_size);
                    // Handle the case where i != index separately from i == index.
                    if i != index {
                        assert(extract_bytes(new_main_table_region, offset, entry_slot_size as nat) =~=
                               extract_bytes(old_main_table_region, offset, entry_slot_size as nat));
                        assert(validate_main_entry::<K>(entry_bytes, overall_metadata.num_keys as nat));
                    } else {
                        // When `i == index`, the entry is valid because we just set its CDB to true,
                        // which makes its CDB a valid, parseable value. This also proves that this
                        // entry parses to an Valid entry, since we know that
                        // `log_entry.bytes@ == CDB_TRUE.spec_to_bytes()`
                        let entry_bytes = extract_bytes(new_main_table_region, offset, entry_slot_size as nat);
                        let cdb_bytes = extract_bytes(entry_bytes, 0, u64::spec_size_of());
                        let old_entry_bytes = extract_bytes(old_main_table_region, offset, entry_slot_size as nat);
                        assert(cdb_bytes =~= log_entry.bytes@);
                        lemma_establish_extract_bytes_equivalence(entry_bytes, old_entry_bytes);
                    }
                }

                assert(validate_main_entries::<K>(new_main_table_region, overall_metadata.num_keys as nat,
                    overall_metadata.main_table_entry_size as nat));
                let entries = parse_main_entries::<K>(new_main_table_region, overall_metadata.num_keys as nat,
                    overall_metadata.main_table_entry_size as nat);
                assert(new_main_table_region.len() >= overall_metadata.num_keys * overall_metadata.main_table_entry_size);
                
                let old_entries =
                    parse_main_entries::<K>(old_main_table_region, overall_metadata.num_keys as nat,
                                                overall_metadata.main_table_entry_size as nat);
                assert(old_entries[index as int] is None);

                assert(no_duplicate_item_indexes(entries)) by {
                    assert forall|i, j| {
                        &&& 0 <= i < entries.len()
                        &&& 0 <= j < entries.len()
                        &&& i != j
                        &&& #[trigger] entries[i] is Some
                        &&& #[trigger] entries[j] is Some
                    } implies entries[i].unwrap().item_index() != entries[j].unwrap().item_index() by {
                        assert(i == index ==> old_entries[j].unwrap().item_index() != item_index);
                        assert(j == index ==> old_entries[i].unwrap().item_index() != item_index);
                    }
                }

                assert(no_duplicate_keys(entries)) by {
                    assert forall|i, j| {
                        &&& 0 <= i < entries.len()
                        &&& 0 <= j < entries.len()
                        &&& i != j
                        &&& #[trigger] entries[i] is Some
                        &&& #[trigger] entries[j] is Some
                    } implies entries[i].unwrap().key() != entries[j].unwrap().key() by {
                        assert(i == index ==> old_entries[j].unwrap().key() != entry.key);
                        assert(j == index ==> old_entries[i].unwrap().key() != entry.key);
                    }
                }

                let updated_table = old_main_table_view.durable_main_table.update(
                    index as int,
                    Some(entry@)
                );
                assert(updated_table.len() == old_main_table_view.durable_main_table.len());
                assert(updated_table.len() == overall_metadata.num_keys);
                assert forall |i: nat| i < overall_metadata.num_keys && i != index implies 
                    #[trigger] updated_table[i as int] == new_main_table_view.unwrap().durable_main_table[i as int]
                by {
                    lemma_valid_entry_index(i, overall_metadata.num_keys as nat, entry_slot_size as nat);
                    let offset = index_to_offset(i, entry_slot_size as nat);
                    let entry_bytes = extract_bytes(new_main_table_region, offset, entry_slot_size as nat);
                    let new_entry = parse_main_entry::<K>(entry_bytes, overall_metadata.num_keys as nat);
                    assert(new_main_table_view.unwrap().durable_main_table[i as int] =~= new_entry);
                }
                let new_main_table_view = new_main_table_view.unwrap();

                assert(new_main_table_view =~= old_main_table_view.update(index as int, entry@));

                // In addition to proving that this log entry makes the entry at this index in valid, we also have to 
                // prove that it makes the corresponding item table index valid.
                
                assert(new_main_table_view.valid_item_indices() =~=
                       old_main_table_view.valid_item_indices().insert(item_index)) by {
                    assert(forall|i: u64| #[trigger] new_main_table_view.valid_item_indices().contains(i) ==>
                           old_main_table_view.valid_item_indices().insert(item_index).contains(i));
                    assert forall|i: u64| old_main_table_view.valid_item_indices().insert(item_index).contains(i) implies
                           #[trigger] new_main_table_view.valid_item_indices().contains(i) by {
                        if i == item_index {
                            assert(new_main_table_view.durable_main_table[index as int] is Some);
                        }
                        else {
                            let j = choose|j: int| {
                                &&& 0 <= j < old_main_table_view.durable_main_table.len() 
                                &&& #[trigger] old_main_table_view.durable_main_table[j] matches Some(entry)
                                &&& entry.item_index() == i
                            };
                            assert(new_main_table_view.durable_main_table[j as int] is Some);
                        }
                    }
                }
            }

            assert(log_entry_does_not_modify_free_main_table_entries(log_entry@, self.free_indices(),
                                                                     *overall_metadata)) by {
                assert forall|free_index: u64| #[trigger] self.free_indices().contains(free_index) implies
                       log_entry_does_not_modify_free_main_table_entry(log_entry@, free_index, *overall_metadata) by {
                    assert(free_index != index);
                    lemma_valid_entry_index(free_index as nat, overall_metadata.num_keys as nat, entry_slot_size as nat);
                    lemma_entries_dont_overlap_unless_same_index(free_index as nat, index as nat, entry_slot_size as nat);
                }
            }                                                                            


            log_entry
        }

        pub exec fn create_delete_log_entry(
            &self,
            Ghost(subregion_view): Ghost<PersistentMemoryRegionView>,
            Ghost(region_view): Ghost<PersistentMemoryRegionView>,
            index: u64,
            Ghost(version_metadata): Ghost<VersionMetadata>,
            overall_metadata: &OverallMetadata,
            Ghost(current_tentative_state): Ghost<Seq<u8>>, 
        ) -> (log_entry: PhysicalOpLogEntry)
            requires 
                self.inv(subregion_view, *overall_metadata),
                overall_metadata.main_table_size >= overall_metadata.num_keys * overall_metadata.main_table_entry_size,
                0 <= index < self@.len(),
                // the index must refer to a currently-valid entry in the current durable table
                parse_main_table::<K>(subregion_view.committed(), overall_metadata.num_keys,
                                          overall_metadata.main_table_entry_size) == Some(self@),
                overall_metadata.main_table_entry_size ==
                    ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
                region_view.len() == overall_metadata.region_size,
                overall_metadata.main_table_addr + overall_metadata.main_table_size <= overall_metadata.log_area_addr
                    <= overall_metadata.region_size <= region_view.len() <= u64::MAX,
                ({
                    let main_table_region = extract_bytes(current_tentative_state, 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    let main_table_view = parse_main_table::<K>(main_table_region,
                        overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                    &&& main_table_view matches Some(main_table_view)
                    &&& main_table_view.inv(*overall_metadata)
                    &&& self.tentative_view() == main_table_view
                }),
                ({
                    // either there is an outstanding entry that we can delete, 
                    // or there is no outstanding entry but there is a durable entry
                    ||| ({
                            &&& self.outstanding_entries[index] matches Some(entry)
                            &&& (entry.status is Created || entry.status is Updated)
                        })
                    ||| ({
                            &&& self.outstanding_entries[index] is None 
                            &&& self@.durable_main_table[index as int] is Some
                        })
                }),
                current_tentative_state.len() == overall_metadata.region_size,
                VersionMetadata::spec_size_of() <= version_metadata.overall_metadata_addr,
                version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() + u64::spec_size_of()
                    <= overall_metadata.main_table_addr,
            ensures 
                log_entry@.inv(version_metadata, *overall_metadata),
                overall_metadata.main_table_addr <= log_entry.absolute_addr,
                log_entry.absolute_addr + log_entry.len <=
                    overall_metadata.main_table_addr + overall_metadata.main_table_size,
                log_entry_does_not_modify_free_main_table_entries(log_entry@, self.free_indices(), *overall_metadata),
                ({
                    let new_mem = current_tentative_state.map(|pos: int, pre_byte: u8|
                        if log_entry.absolute_addr <= pos < log_entry.absolute_addr + log_entry.len {
                            log_entry.bytes[pos - log_entry.absolute_addr]
                        } else {
                            pre_byte
                        }
                    );
                    let new_main_table_region = extract_bytes(new_mem, 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    let new_main_table_view = parse_main_table::<K>(new_main_table_region,
                        overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                    new_main_table_view == self.tentative_view().delete(index as int)
                }),
        {
            let entry_slot_size = overall_metadata.main_table_entry_size;
            let ghost item_index = self.get_latest_entry(index).unwrap().item_index();

            // Proves that index * entry_slot_size will not overflow
            proof {
                lemma_valid_entry_index(index as nat, overall_metadata.num_keys as nat, entry_slot_size as nat);
            }
            
            let index_offset = index * entry_slot_size as u64;
            assert(index_offset == index_to_offset(index as nat, entry_slot_size as nat));

            let log_entry = PhysicalOpLogEntry {
                absolute_addr: overall_metadata.main_table_addr + index_offset,
                len: traits_t::size_of::<u64>() as u64,
                bytes: slice_to_vec(CDB_FALSE.as_byte_slice()),
            };

            proof {
                assert(log_entry.len == log_entry.bytes@.len()) by {
                    broadcast use pmcopy_axioms;
                }

                let new_mem = current_tentative_state.map(|pos: int, pre_byte: u8|
                    if log_entry.absolute_addr <= pos < log_entry.absolute_addr + log_entry.len {
                        log_entry.bytes[pos - log_entry.absolute_addr]
                    } else {
                        pre_byte
                    }
                );
                
                let old_main_table_region = extract_bytes(current_tentative_state, 
                    overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let new_main_table_region = extract_bytes(new_mem, 
                    overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let old_main_table_view = parse_main_table::<K>(old_main_table_region,
                    overall_metadata.num_keys, overall_metadata.main_table_entry_size).unwrap();
                let new_main_table_view = parse_main_table::<K>(new_main_table_region,
                    overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                lemma_establish_extract_bytes_equivalence(old_main_table_region, new_main_table_region);
                
                assert forall |i: nat| #![trigger extract_bytes(new_main_table_region,
                                                         index_to_offset(i, entry_slot_size as nat),
                                                         entry_slot_size as nat)]
                           i < overall_metadata.num_keys implies {
                    let offset = index_to_offset(i, entry_slot_size as nat);
                    let old_entry_bytes = extract_bytes(old_main_table_region, offset, entry_slot_size as nat);
                    let entry_bytes = extract_bytes(new_main_table_region, offset, entry_slot_size as nat);
                    &&& validate_main_entry::<K>(entry_bytes, overall_metadata.num_keys as nat)
                    &&& i == index ==>
                           parse_main_entry::<K>(entry_bytes, overall_metadata.num_keys as nat) is None
                    &&& i != index ==> parse_main_entry::<K>(entry_bytes, overall_metadata.num_keys as nat) == 
                           parse_main_entry::<K>(old_entry_bytes, overall_metadata.num_keys as nat)
                } by {
                    let offset = index_to_offset(i, entry_slot_size as nat);
                    lemma_valid_entry_index(i, overall_metadata.num_keys as nat, entry_slot_size as nat);
                    lemma_entries_dont_overlap_unless_same_index(i, index as nat, entry_slot_size as nat);
                    assert(new_main_table_region.len() >= offset + entry_slot_size);
                    
                    broadcast use pmcopy_axioms;

                    // Handle the case where i != index separately from i == index.
                    if i != index {
                        assert(extract_bytes(new_main_table_region, offset, entry_slot_size as nat) =~=
                               extract_bytes(old_main_table_region, offset, entry_slot_size as nat));
                    } else {
                        // When `i == index`, the entry is valid because we just set its CDB to false,
                        // which makes its CDB a valid, parseable value. This also proves that this
                        // entry parses to an Invalid entry, since we know that
                        // `log_entry.bytes@ == CDB_FALSE.spec_to_bytes()`
                        let entry_bytes = extract_bytes(new_main_table_region, offset, entry_slot_size as nat);
                        let cdb_bytes = extract_bytes(entry_bytes, 0, u64::spec_size_of());
                        assert(cdb_bytes =~= log_entry.bytes@);
                    }
                }

                assert(validate_main_entries::<K>(new_main_table_region, overall_metadata.num_keys as nat,
                    overall_metadata.main_table_entry_size as nat));
                let entries = parse_main_entries::<K>(new_main_table_region, overall_metadata.num_keys as nat,
                    overall_metadata.main_table_entry_size as nat);                
                let old_entries =
                    parse_main_entries::<K>(old_main_table_region, overall_metadata.num_keys as nat,
                                                overall_metadata.main_table_entry_size as nat);

                assert(no_duplicate_item_indexes(entries) && no_duplicate_keys(entries)) by {
                    assert forall|i, j| {
                        &&& 0 <= i < entries.len()
                        &&& 0 <= j < entries.len()
                        &&& i != j
                        &&& #[trigger] entries[i] is Some
                        &&& #[trigger] entries[j] is Some
                    } implies {
                        &&& entries[i].unwrap().item_index() != entries[j].unwrap().item_index() 
                        &&& entries[i].unwrap().key() != entries[j].unwrap().key() 
                    } by {
                        assert(i == index ==> old_entries[j].unwrap().item_index() != item_index);
                        assert(j == index ==> old_entries[i].unwrap().item_index() != item_index);
                        assert(entries[i].unwrap().key() == old_entries[i].unwrap().key());
                        assert(entries[j].unwrap().key() == old_entries[j].unwrap().key());
                    }
                }

                let updated_table = old_main_table_view.durable_main_table.update(index as int, None);
                assert(updated_table.len() == old_main_table_view.durable_main_table.len());
                assert(updated_table.len() == overall_metadata.num_keys);

                let new_main_table_view = new_main_table_view.unwrap();
                assert(new_main_table_view =~= old_main_table_view.delete(index as int).unwrap());

                lemma_log_entry_does_not_modify_free_main_table_entries(
                    log_entry@, index, self.free_indices(), *overall_metadata,
                );
            }
            log_entry
        }

        proof fn lemma_no_duplicate_item_indices_or_keys(
            old_entries: Seq<Option<MainTableViewEntry<K>>>,
            new_entries: Seq<Option<MainTableViewEntry<K>>>,
            index: int,
            new_item_index: u64,
        )
            requires
                no_duplicate_item_indexes(old_entries),
                no_duplicate_keys(old_entries),
                0 <= index < new_entries.len(),
                new_entries.len() == old_entries.len(),
                forall |i: int| {
                    &&& 0 <= i < new_entries.len()
                    &&& #[trigger] new_entries[i] is Some
                } ==> {
                    &&& old_entries[i] is Some
                    &&& new_entries[i].unwrap().key() == old_entries[i].unwrap().key()
                },
                forall |i: int| {
                    &&& 0 <= i < new_entries.len()
                    &&& #[trigger] new_entries[i] is Some
                } ==> {
                    &&& i != index ==> {
                            &&& old_entries[i] is Some
                            &&& new_entries[i].unwrap().item_index() == old_entries[i].unwrap().item_index()
                            &&& new_entries[i].unwrap().item_index() != new_item_index
                        }
                    &&& i == index ==> 
                            new_entries[i].unwrap().item_index() == new_item_index
                }
            ensures 
                forall |i: int, j: int| {
                    &&& 0 <= i < new_entries.len()
                    &&& 0 <= j < new_entries.len()
                    &&& i != j
                    &&& #[trigger] new_entries[i] is Some
                    &&& #[trigger] new_entries[j] is Some
                } ==> {
                    &&& new_entries[i].unwrap().item_index() != new_entries[j].unwrap().item_index() 
                    &&& new_entries[i].unwrap().key() != new_entries[j].unwrap().key()
                } 
        {
            assert forall |i: int, j: int| {
                &&& 0 <= i < new_entries.len()
                &&& 0 <= j < new_entries.len()
                &&& i != j
                &&& #[trigger] new_entries[i] is Some
                &&& #[trigger] new_entries[j] is Some
            } implies {
                new_entries[i].unwrap().item_index() != new_entries[j].unwrap().item_index() 
            } by {
                if i != index && j != index {
                    assert(new_entries[i].unwrap().item_index() == old_entries[i].unwrap().item_index());
                    assert(new_entries[j].unwrap().item_index() == old_entries[j].unwrap().item_index());
                }
            }
        }

        #[verifier::rlimit(25)] // TODO @hayley
        proof fn lemma_update_item_log_entry<PM>(
            self,
            subregion: &PersistentMemorySubregion,
            pm_region: &PM,
            index: u64,
            new_metadata_entry: ListEntryMetadata,
            key: K,
            crc: u64,
            log_entry: PhysicalOpLogEntry,
            overall_metadata: OverallMetadata,
            version_metadata: VersionMetadata,
            current_tentative_state: Seq<u8>, 
        )
            where 
                PM: PersistentMemoryRegion,
            requires 
                crc == spec_crc_u64(new_metadata_entry.spec_to_bytes() + key.spec_to_bytes()),
                log_entry@.inv(version_metadata, overall_metadata),
                log_entry.bytes@ == crc.spec_to_bytes() + new_metadata_entry.spec_to_bytes(),
                log_entry.absolute_addr == overall_metadata.main_table_addr + 
                    index_to_offset(index as nat, overall_metadata.main_table_entry_size as nat) + 
                    u64::spec_size_of(),
                log_entry.bytes@.len() == log_entry.len,
                ({
                    &&& self.outstanding_entries[index] matches Some(e)
                    &&& (e.status is Created || e.status is Updated)
                }) ==> ({
                    &&& self.outstanding_entries[index] matches Some(e)
                    &&& e.key == key
                    &&& e.entry.head == new_metadata_entry.head
                    &&& e.entry.tail == new_metadata_entry.tail
                    &&& e.entry.length == new_metadata_entry.length
                    &&& e.entry.first_entry_offset == new_metadata_entry.first_entry_offset
                }),
                ({
                    &&& self.outstanding_entries[index] is None 
                    &&& self@.durable_main_table[index as int] is Some
                }) ==> ({
                    &&& self@.durable_main_table[index as int] matches Some(e)
                    &&& e.key == key
                    &&& e.entry.head == new_metadata_entry.head
                    &&& e.entry.tail == new_metadata_entry.tail
                    &&& e.entry.length == new_metadata_entry.length
                    &&& e.entry.first_entry_offset == new_metadata_entry.first_entry_offset
                }),

                subregion.inv(pm_region),
                self.inv(subregion.view(pm_region), overall_metadata),
                subregion.len() == overall_metadata.main_table_size,
                subregion.start() == overall_metadata.main_table_addr,
                overall_metadata.main_table_size >= overall_metadata.num_keys * overall_metadata.main_table_entry_size,
                0 <= index < self@.len(),
                new_metadata_entry.item_index < overall_metadata.num_keys,
                pm_region@.len() == overall_metadata.region_size,
                // !self@.valid_item_indices().contains(new_metadata_entry.item_index),
                overall_metadata.main_table_entry_size ==
                    ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
                overall_metadata.main_table_addr + overall_metadata.main_table_size <= overall_metadata.log_area_addr
                    <= overall_metadata.region_size <= u64::MAX,
                ({
                    let main_table_region = extract_bytes(current_tentative_state, 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    let main_table_view = parse_main_table::<K>(main_table_region,
                        overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                    
                    // the tentative main table from the provided bytes should 
                    // match the current main table's own tentative view
                    &&& Some(self.tentative_view()) == main_table_view
                    &&& !main_table_view.unwrap().valid_item_indices().contains(new_metadata_entry.item_index)
                }),
                ({
                    // either there is an outstanding entry that we can read, 
                    // or there is no outstanding entry but there is a durable entry
                    ||| ({
                            &&& self.outstanding_entries[index] matches Some(entry)
                            &&& (entry.status is Created || entry.status is Updated)
                        })
                    ||| ({
                            &&& self.outstanding_entries[index] is None 
                            &&& self@.durable_main_table[index as int] is Some
                        })
                }),
                current_tentative_state.len() == overall_metadata.region_size,
                VersionMetadata::spec_size_of() <= version_metadata.overall_metadata_addr,
                version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of()
                    <= overall_metadata.main_table_addr,
            ensures 
                ({
                    let item_index = new_metadata_entry.item_index;
                    let new_mem = current_tentative_state.map(|pos: int, pre_byte: u8|
                        if log_entry.absolute_addr <= pos < log_entry.absolute_addr + log_entry.len {
                            log_entry.bytes[pos - log_entry.absolute_addr]
                        } else {
                            pre_byte
                        }
                    );
                    let current_main_table_region = extract_bytes(current_tentative_state, 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    let current_main_table_view = parse_main_table::<K>(current_main_table_region,
                        overall_metadata.num_keys, overall_metadata.main_table_entry_size).unwrap();
                    let new_main_table_region = extract_bytes(new_mem, 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    let new_main_table_view = parse_main_table::<K>(new_main_table_region,
                        overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                    let old_item_index = current_main_table_view.durable_main_table[index as int].unwrap().item_index();
                    
                    &&& overall_metadata.main_table_addr <= log_entry.absolute_addr
                    &&& log_entry.absolute_addr + log_entry.len <=
                            overall_metadata.main_table_addr + overall_metadata.main_table_size
                    &&& log_entry@.inv(version_metadata, overall_metadata)
                    &&& log_entry_does_not_modify_free_main_table_entries(log_entry@, self.free_indices(),
                                                                        overall_metadata)

                    // after applying this log entry to the current tentative state,
                    // this entry's metadata index has been updated
                    &&& new_main_table_view is Some
                    &&& new_main_table_view == current_main_table_view.update_item_index(index as int, item_index)
                    &&& new_main_table_view.unwrap().valid_item_indices() == 
                            current_main_table_view.valid_item_indices().insert(item_index).remove(old_item_index)
                })
        {
            let item_index = new_metadata_entry.item_index;

            lemma_valid_entry_index(index as nat, overall_metadata.num_keys as nat, overall_metadata.main_table_entry_size as nat);
            
            let new_mem = current_tentative_state.map(|pos: int, pre_byte: u8|
                if log_entry.absolute_addr <= pos < log_entry.absolute_addr + log_entry.len {
                    log_entry.bytes[pos - log_entry.absolute_addr]
                } else {
                    pre_byte
                }
            );

            let old_main_table_region = extract_bytes(current_tentative_state, 
                overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
            let new_main_table_region = extract_bytes(new_mem, 
                overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);

            let old_main_table_view = parse_main_table::<K>(old_main_table_region,
                overall_metadata.num_keys, overall_metadata.main_table_entry_size).unwrap();
            let new_main_table_view = parse_main_table::<K>(new_main_table_region,
                overall_metadata.num_keys, overall_metadata.main_table_entry_size);

            let new_entry_view = MainTableViewEntry {
                entry: new_metadata_entry,
                key: key,
            };

            // Prove that parsing each entry individually gives the expected entries.
            // This helps prove that parsing the entire table suceeds and also that we 
            // get the expected table contents.
            assert forall |i: nat| i < overall_metadata.num_keys implies {
                let new_bytes = extract_bytes(new_main_table_region,
                    #[trigger] index_to_offset(i, overall_metadata.main_table_entry_size as nat),
                    overall_metadata.main_table_entry_size as nat
                );
                let old_bytes = extract_bytes(old_main_table_region,
                    index_to_offset(i, overall_metadata.main_table_entry_size as nat),
                    overall_metadata.main_table_entry_size as nat
                );
                &&& validate_main_entry::<K>(new_bytes, overall_metadata.num_keys as nat)
                &&& i == index ==> parse_main_entry::<K>(new_bytes, overall_metadata.num_keys as nat) == 
                        Some(new_entry_view)
                &&& i != index ==> parse_main_entry::<K>(new_bytes, overall_metadata.num_keys as nat) == 
                        parse_main_entry::<K>(old_bytes, overall_metadata.num_keys as nat)
            } by {
                lemma_valid_entry_index(i, overall_metadata.num_keys as nat, overall_metadata.main_table_entry_size as nat);
                lemma_entries_dont_overlap_unless_same_index(i, index as nat, overall_metadata.main_table_entry_size as nat);
                lemma_establish_extract_bytes_equivalence(old_main_table_region, new_main_table_region);

                broadcast use pmcopy_axioms;
                if i == index {
                    let new_bytes = extract_bytes(new_main_table_region,
                        index_to_offset(i, overall_metadata.main_table_entry_size as nat),
                        overall_metadata.main_table_entry_size as nat
                    );
                    let old_bytes = extract_bytes(old_main_table_region,
                        index_to_offset(i, overall_metadata.main_table_entry_size as nat),
                        overall_metadata.main_table_entry_size as nat
                    );
                    lemma_establish_extract_bytes_equivalence(new_bytes, old_bytes);
                    assert(extract_bytes(new_bytes, u64::spec_size_of(), u64::spec_size_of()) == crc.spec_to_bytes());
                    assert(extract_bytes(new_bytes, u64::spec_size_of() * 2, ListEntryMetadata::spec_size_of()) == new_metadata_entry.spec_to_bytes());
                    assert(extract_bytes(new_bytes, u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of(), K::spec_size_of()) == key.spec_to_bytes());
                }
            }

            let old_entries = parse_main_entries::<K>(old_main_table_region, overall_metadata.num_keys as nat,
                overall_metadata.main_table_entry_size as nat);
            let new_entries = parse_main_entries::<K>(new_main_table_region, overall_metadata.num_keys as nat,
                overall_metadata.main_table_entry_size as nat);
            // Prove that there are no duplicate entries or keys. This is required
            // to prove that the table parses successfully.
            Self::lemma_no_duplicate_item_indices_or_keys(old_entries, new_entries, index as int, item_index);

            let new_main_table_view = new_main_table_view.unwrap();
            let updated_table_view = old_main_table_view.update_item_index(index as int, item_index).unwrap();

            // Prove that the new main table view is equivalent to updating the old table with the new item index.
            assert(forall |idx: int| 0 <= idx < new_main_table_view.durable_main_table.len() ==> 
                new_main_table_view.durable_main_table[idx] == updated_table_view.durable_main_table[idx]);
            assert(new_main_table_view == updated_table_view);

            let old_item_index = old_main_table_view.durable_main_table[index as int].unwrap().item_index();
            assert(new_main_table_view.valid_item_indices() =~= 
                old_main_table_view.valid_item_indices().insert(item_index).remove(old_item_index)) 
            by {
                // all indexes besides the one we are updating are unchanged
                assert(forall |i: int| 0 <= i < updated_table_view.durable_main_table.len() && i != index ==> 
                    old_main_table_view.durable_main_table[i] == updated_table_view.durable_main_table[i]);
                // the entry at index now contains the new item index, which means it has replaced the old item index
                // in new_main_table_view.valid_item_indices()
                assert({
                    &&& #[trigger] updated_table_view.durable_main_table[index as int] matches Some(entry)
                    &&& entry.item_index() == item_index
                });
            }

            lemma_log_entry_does_not_modify_free_main_table_entries(
                log_entry@, index, self.free_indices(), overall_metadata,
            );
        }

        pub exec fn add_tentative_item_update<PM>(
            &mut self,
            subregion: &PersistentMemorySubregion,
            pm_region: &PM,
            index: u64,
            new_entry: ListEntryMetadata,
            key: Box<K>,
            overall_metadata: OverallMetadata,
        )
            where 
                PM: PersistentMemoryRegion
            requires 
                old(self).inv(subregion.view(pm_region), overall_metadata),
                old(self).opaquable_inv(overall_metadata),
                old(self).tentative_view().durable_main_table[index as int] is Some,
                old(self).tentative_view().durable_main_table[index as int].unwrap().key == key,
                0 <= index < overall_metadata.num_keys,
                old(self)@.durable_main_table.len() == overall_metadata.num_keys,
                ({
                    let current_entry = old(self).get_latest_entry(index);
                    &&& current_entry matches Some(current_entry)
                    &&& current_entry.entry.head == new_entry.head
                    &&& current_entry.entry.tail == new_entry.tail
                    &&& current_entry.entry.length == new_entry.length
                    &&& current_entry.entry.first_entry_offset == new_entry.first_entry_offset
                }),
                !old(self).tentative_view().valid_item_indices().contains(new_entry.item_index),
            ensures 
                self.inv(subregion.view(pm_region), overall_metadata),
                self.opaquable_inv(overall_metadata),
                self@ == old(self)@,
                self.main_table_free_list@ == old(self).main_table_free_list@,
                forall|idx| self.free_indices().contains(idx) ==> old(self).free_indices().contains(idx),
                forall|idx| old(self).free_indices().contains(idx) && idx != index ==> self.free_indices().contains(idx),
                self@.valid_item_indices() == old(self)@.valid_item_indices(),
                Some(self.tentative_view()) == 
                    old(self).tentative_view().update_item_index(index as int, new_entry.item_index),
        {
            self.outstanding_entry_update(index, new_entry, *key, overall_metadata);

            proof {
                let updated_tentative_view = old(self).tentative_view().update_item_index(index as int, new_entry.item_index).unwrap();
                assert(self.tentative_view() == updated_tentative_view);
            }
        }

        pub exec fn create_update_item_index_log_entry<PM>(
            &self,
            subregion: &PersistentMemorySubregion,
            pm_region: &PM,
            index: u64,
            item_index: u64,
            overall_metadata: &OverallMetadata,
            Ghost(version_metadata): Ghost<VersionMetadata>,
            Ghost(current_tentative_state): Ghost<Seq<u8>>, 
        ) -> (result: Result<(PhysicalOpLogEntry, Box<ListEntryMetadata>, Box<K>), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                subregion.inv(pm_region),
                self.inv(subregion.view(pm_region), *overall_metadata),
                subregion.len() == overall_metadata.main_table_size,
                subregion.start() == overall_metadata.main_table_addr,
                overall_metadata.main_table_size >= overall_metadata.num_keys * overall_metadata.main_table_entry_size,
                0 <= index < self@.len(),
                item_index < overall_metadata.num_keys,
                pm_region@.len() == overall_metadata.region_size,
                !self.tentative_view().valid_item_indices().contains(item_index),
                overall_metadata.main_table_entry_size ==
                    ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
                overall_metadata.main_table_addr + overall_metadata.main_table_size <= overall_metadata.log_area_addr
                    <= overall_metadata.region_size <= u64::MAX,
                ({
                    let main_table_region = extract_bytes(current_tentative_state, 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    let main_table_view = parse_main_table::<K>(main_table_region,
                        overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                    
                    // the tentative main table from the provided bytes should 
                    // match the current main table's own tentative view
                    &&& Some(self.tentative_view()) == main_table_view
                    &&& !main_table_view.unwrap().valid_item_indices().contains(item_index)
                }),
                ({
                    // either there is an outstanding entry that we can read, 
                    // or there is no outstanding entry but there is a durable entry
                    ||| ({
                            &&& self.outstanding_entries[index] matches Some(entry)
                            &&& (entry.status is Created || entry.status is Updated)
                        })
                    ||| ({
                            &&& self.outstanding_entries[index] is None 
                            &&& self@.durable_main_table[index as int] is Some
                        })
                }),
                current_tentative_state.len() == overall_metadata.region_size,
                VersionMetadata::spec_size_of() <= version_metadata.overall_metadata_addr,
                version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of()
                    <= overall_metadata.main_table_addr,
            ensures 
                match result {
                    Ok((log_entry, old_entry, key)) => {
                        let new_mem = current_tentative_state.map(|pos: int, pre_byte: u8|
                            if log_entry.absolute_addr <= pos < log_entry.absolute_addr + log_entry.len {
                                log_entry.bytes[pos - log_entry.absolute_addr]
                            } else {
                                pre_byte
                            }
                        );
                        let current_main_table_region = extract_bytes(current_tentative_state, 
                            overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                        let current_main_table_view = parse_main_table::<K>(current_main_table_region,
                            overall_metadata.num_keys, overall_metadata.main_table_entry_size).unwrap();
                        let new_main_table_region = extract_bytes(new_mem, 
                            overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                        let new_main_table_view = parse_main_table::<K>(new_main_table_region,
                            overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                        
                        &&& overall_metadata.main_table_addr <= log_entry.absolute_addr
                        &&& log_entry.absolute_addr + log_entry.len <=
                                overall_metadata.main_table_addr + overall_metadata.main_table_size
                        &&& log_entry@.inv(version_metadata, *overall_metadata)
                        &&& log_entry_does_not_modify_free_main_table_entries(log_entry@, self.free_indices(),
                                                                            *overall_metadata)

                        // after applying this log entry to the current tentative state,
                        // this entry's metadata index has been updated
                        &&& new_main_table_view is Some
                        &&& new_main_table_view == current_main_table_view.update_item_index(index as int, item_index)
                        &&& new_main_table_view.unwrap().valid_item_indices() == 
                                current_main_table_view.valid_item_indices().insert(item_index).remove(old_entry.item_index)

                        &&& old_entry == self.get_latest_entry(index).unwrap().entry
                        &&& key == self.get_latest_entry(index).unwrap().key
                    }
                    Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                    _ => false,
                }
        {
            // For this operation, we have to log the whole new metadata table entry
            // we don't have to log the key, as it hasn't changed, but we do need
            // to log a CRC that covers both the metadata and the key. The CRC and 
            // metadata are contiguous, so we only need one log entry
            // To make things slightly easier on the caller, we'll read the required
            // metadata table info here; since this can fail, though, this operation
            // can return an error and require the caller to abort the transaction.
            let result = self.get_key_and_metadata_entry_at_index(subregion, pm_region, index, Ghost(*overall_metadata));
            let (key, metadata) = match result {
                Ok((key, metadata)) => (key, metadata),
                Err(e) => return Err(e),
            };
            let old_item_index = metadata.item_index;

            // Next, construct the new metadata entry and obtain the CRC
            let new_metadata_entry = ListEntryMetadata {
                item_index,
                ..*metadata
            };

            let mut digest = CrcDigest::new();
            digest.write(&new_metadata_entry);
            digest.write(&*key);
            let crc = digest.sum64();

            proof {
                // prove that the CRC is in fact the CRC of the new entry and key by invoking some lemmas
                // about flattening sequences of sequences
                lemma_seqs_flatten_equal_suffix(digest.bytes_in_digest());
                digest.bytes_in_digest().subrange(0, 1).lemma_flatten_one_element();
                assert(crc == spec_crc_u64(new_metadata_entry.spec_to_bytes() + key.spec_to_bytes())); 
            }

            // Proves that index * entry_slot_size will not overflow
            proof {
                lemma_valid_entry_index(index as nat, overall_metadata.num_keys as nat, overall_metadata.main_table_entry_size as nat);
            }

            // Construct the physical log entry out of the CRC and new metadata entry.
            let index_offset = index * overall_metadata.main_table_entry_size as u64;
            assert(index_offset == index_to_offset(index as nat, overall_metadata.main_table_entry_size as nat));

            let mut bytes_vec = slice_to_vec(crc.as_byte_slice());
            let mut entry_bytes_vec = slice_to_vec(new_metadata_entry.as_byte_slice());
            bytes_vec.append(&mut entry_bytes_vec);

            let log_entry = PhysicalOpLogEntry {
                absolute_addr: overall_metadata.main_table_addr + index_offset + traits_t::size_of::<u64>() as u64,
                len: (traits_t::size_of::<u64>() + traits_t::size_of::<ListEntryMetadata>()) as u64,
                bytes: bytes_vec,
            };

            proof {
                assert(log_entry.len == log_entry.bytes@.len()) by {
                    broadcast use pmcopy_axioms;
                }
                self.lemma_update_item_log_entry(subregion, pm_region, index, new_metadata_entry, 
                    *key, crc, log_entry, *overall_metadata, version_metadata, current_tentative_state);
            }

            Ok((log_entry, metadata, key))
        }

        exec fn clear_modified_indices_for_abort(&mut self, Ghost(overall_metadata): Ghost<OverallMetadata>)
            requires 
                old(self).opaquable_inv(overall_metadata),
                old(self).outstanding_entries.inv(),
            ensures 
                self.opaquable_inv(overall_metadata),
                self.outstanding_entries@.len() == 0,
                self.modified_indices@.len() == 0,
                self.main_table_entry_size == old(self).main_table_entry_size,
                self@ == old(self)@,
                forall |idx: u64| {
                    // the free list contains idx if either idx was already in the free list
                    // or idx had an outstanding entry indicating that it was allocated in
                    // this transaction 
                    ||| old(self).main_table_free_list@.contains(idx)
                    ||| {
                            &&& old(self).modified_indices@.contains(idx)
                            &&& (old(self).outstanding_entries@[idx].status is Created || 
                                    old(self).outstanding_entries@[idx].status is CreatedThenDeleted)
                        }
                } <==> #[trigger] self.main_table_free_list@.contains(idx)
        {
            // iterate over the modified indices and determine 
            // if and how to update the free list depending on 
            // the status of each index
            let mut index = 0;
            while index < self.modified_indices.len() 
                invariant
                    self.modified_indices@.no_duplicates(),
                    self@ == old(self)@,
                    self.main_table_entry_size == old(self).main_table_entry_size,
                    forall |i: u64| index <= i < self.modified_indices.len() ==> { 
                        let j = #[trigger] self.modified_indices@[i as int];
                        &&& self.modified_indices@.contains(j) ==> !self.main_table_free_list@.contains(j)
                        &&& self.main_table_free_list@.contains(j) ==> !self.modified_indices@.contains(j)
                    },
                    forall |idx: u64| self.outstanding_entries@.contains_key(idx) <==> 
                        #[trigger] self.modified_indices@.contains(idx),
                    self.outstanding_entries@ == old(self).outstanding_entries@,
                    self.modified_indices@ == old(self).modified_indices@,
                    self.main_table_free_list@.no_duplicates(),
                    forall |i: u64| {
                        let j = #[trigger] old(self).modified_indices[i as int];
                        &&& 0 <= i < index 
                        &&& old(self).outstanding_entries@.contains_key(j) 
                        &&& (old(self).outstanding_entries@[j].status is Created || old(self).outstanding_entries@[j].status is CreatedThenDeleted)
                    } ==> self.main_table_free_list@.contains(old(self).modified_indices[i as int]),
                    forall |idx: u64| self.modified_indices@.contains(idx) ==> idx < overall_metadata.num_keys,
                    forall |idx: u64| self.main_table_free_list@.contains(idx) ==> idx < overall_metadata.num_keys,
                    vstd::std_specs::hash::obeys_key_model::<K>(),
                    forall |idx: u64| 0 <= idx < self@.durable_main_table.len() && !self.main_table_free_list@.contains(idx) ==>
                        self@.durable_main_table[idx as int] is Some || #[trigger] self.modified_indices@.contains(idx),
                    self@.durable_main_table == old(self)@.durable_main_table,
                    forall |idx: u64| old(self).main_table_free_list@.contains(idx) ==> self.main_table_free_list@.contains(idx),
                    forall |idx: u64| #![trigger self.main_table_free_list@.contains(idx)] 
                                      #![trigger old(self).main_table_free_list@.contains(idx)]
                                      #![trigger old(self).modified_indices@.contains(idx)]
                        self.main_table_free_list@.contains(idx) ==> {
                            ||| old(self).main_table_free_list@.contains(idx)
                            ||| ({
                                    &&& old(self).modified_indices@.contains(idx)
                                    &&& (old(self).outstanding_entries@[idx].status is Created || 
                                            old(self).outstanding_entries@[idx].status is CreatedThenDeleted)
                                })
                        },
            {
                let ghost free_list_at_top = self.main_table_free_list@;
                let current_index = self.modified_indices[index];
                assert(self.modified_indices@.contains(current_index)); // required for triggers

                let current_entry = self.outstanding_entries.get(current_index).unwrap();
                match current_entry.status {
                    // if we allocated this index in the transaction, return it to the free list.
                    EntryStatus::Created | EntryStatus::CreatedThenDeleted => {
                        self.main_table_free_list.push(current_index);
                        assert(self.main_table_free_list@.subrange(0, free_list_at_top.len() as int) == free_list_at_top);
                        assert(self.main_table_free_list@[free_list_at_top.len() as int] == current_index);
                        assert forall |idx: u64| self.main_table_free_list@.contains(idx) implies idx < overall_metadata.num_keys by {
                            if idx != current_index {
                                assert(free_list_at_top.contains(idx));
                            }
                        }
                    },
                    // if we updated or deleted an existing entry, do nothing -- the index stays 
                    // valid.
                    _ => {}
                }

                index += 1;
            }

            self.modified_indices.clear();
            self.outstanding_entries.clear();

            assert forall |idx: u64| 0 <= idx < self@.durable_main_table.len() && !self.main_table_free_list@.contains(idx) implies
                self@.durable_main_table[idx as int] is Some || #[trigger] self.modified_indices@.contains(idx)
            by {
                if !old(self).main_table_free_list@.contains(idx) {
                    // neither the old nor new free list contain idx

                    // by opaquable_inv, if the free list does not contain idx, then it is either
                    // currently valid or has an outstanding write
                    if old(self)@.durable_main_table[idx as int] is Some {
                        assert(self@.durable_main_table[idx as int] is Some);
                    } else {
                        assert(old(self).modified_indices@.contains(idx));
                    }
                } // else, trivial
            }
        }

        pub exec fn abort_transaction(
            &mut self,
            Ghost(pm): Ghost<PersistentMemoryRegionView>,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        ) 
            requires
                old(self).opaquable_inv(overall_metadata),
                overall_metadata.main_table_size >= overall_metadata.num_keys * overall_metadata.main_table_entry_size,
                pm.len() >= overall_metadata.main_table_size,
                old(self).main_table_entry_size == overall_metadata.main_table_entry_size,
                overall_metadata.main_table_entry_size ==
                    ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
                forall |s| #[trigger] pm.can_crash_as(s) ==> 
                    parse_main_table::<K>(s, overall_metadata.num_keys, overall_metadata.main_table_entry_size) == Some(old(self)@),
                old(self)@.durable_main_table.len() == overall_metadata.num_keys,
                old(self)@.inv(overall_metadata),
                forall |i| 0 <= i < old(self)@.durable_main_table.len() ==> 
                    match #[trigger] old(self)@.durable_main_table[i] {
                        Some(entry) => entry.entry.item_index < overall_metadata.num_keys,
                        _ => true
                    },
                pm.no_outstanding_writes(),
                forall |idx: u64| old(self).free_list().contains(idx) ==> old(self).free_indices().contains(idx),
            ensures
                self.valid(pm, overall_metadata),
                self.outstanding_entries@.len() == 0,
                self@.valid_item_indices() == old(self)@.valid_item_indices(),
                self@ == old(self)@,
                self.tentative_view() == self@,
        {
            self.clear_modified_indices_for_abort(Ghost(overall_metadata));
            proof {
                assert forall |idx: u64| 0 <= idx < self@.durable_main_table.len() implies
                    self.no_outstanding_writes_to_entry(pm, idx, overall_metadata.main_table_entry_size)
                by {
                    let start = index_to_offset(idx as nat, overall_metadata.main_table_entry_size as nat) as int;
                    lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, overall_metadata.main_table_entry_size as nat);
                    assert(pm.no_outstanding_writes_in_range(start, start + overall_metadata.main_table_entry_size));
                }

                assert forall |idx: u64| self.free_list().contains(idx) implies
                    self.free_indices().contains(idx)
                by {
                    if old(self).free_list().contains(idx) {
                        assert(old(self).free_indices().contains(idx));
                        assert(self.free_indices().contains(idx));
                    } // else, trivial
                }

                assert(self.tentative_view() == self@);
            }
        }

        pub exec fn finalize_main_table(
            &mut self,
            Ghost(old_self): Ghost<Self>,
            Ghost(old_pm): Ghost<PersistentMemoryRegionView>,
            Ghost(pm): Ghost<PersistentMemoryRegionView>,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        )
            requires
                pm.no_outstanding_writes(),
                old(self).opaquable_inv(overall_metadata),
                ({
                    let subregion_view = get_subregion_view(pm, overall_metadata.main_table_addr as nat,
                        overall_metadata.main_table_size as nat);
                    let old_subregion_view = get_subregion_view(old_pm, overall_metadata.main_table_addr as nat,
                        overall_metadata.main_table_size as nat);
                    &&& parse_main_table::<K>(subregion_view.committed(), overall_metadata.num_keys, overall_metadata.main_table_entry_size) ==
                            Some(old(self).tentative_view())
                    &&& old_self.inv(old_subregion_view, overall_metadata)
                    &&& parse_main_table::<K>(old_subregion_view.committed(), overall_metadata.num_keys, overall_metadata.main_table_entry_size) is Some
                }),
                old(self)@.durable_main_table.len() == overall_metadata.num_keys,
                pm.len() >= overall_metadata.main_table_addr + overall_metadata.main_table_size,
                overall_metadata.main_table_size >= overall_metadata.num_keys * overall_metadata.main_table_entry_size,
                overall_metadata.main_table_entry_size ==
                    ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of(),
                old(self).main_table_entry_size == overall_metadata.main_table_entry_size,
                old_self.free_list() == old(self).free_list(),
                old_self.main_table_entry_size == overall_metadata.main_table_entry_size,
            ensures 
                ({
                    let subregion_view = get_subregion_view(pm, overall_metadata.main_table_addr as nat,
                        overall_metadata.main_table_size as nat);
                    &&& self.inv(subregion_view, overall_metadata)
                }),
                self.outstanding_entries@.len() == 0,
                self.state@ == old(self).tentative_view(),  
        {
            let ghost subregion_view = get_subregion_view(pm, overall_metadata.main_table_addr as nat,
                overall_metadata.main_table_size as nat);
            self.state = Ghost(parse_main_table::<K>(subregion_view.committed(), overall_metadata.num_keys, overall_metadata.main_table_entry_size).unwrap());
            assert(self.state@ == old(self).tentative_view());

            assert forall |idx: u64| self.outstanding_entries@.contains_key(idx) implies {
                let entry = self.outstanding_entries[idx].unwrap();
                match entry.status {
                    EntryStatus::Created | EntryStatus::Updated => self@.durable_main_table[idx as int] is Some,
                    EntryStatus::Deleted | EntryStatus::CreatedThenDeleted => self@.durable_main_table[idx as int] is None
                }
            } by {
                assert(self.modified_indices@.contains(idx));
                assert(idx < overall_metadata.num_keys);
            }

            
            self.finalize_outstanding_entries(Ghost(subregion_view), Ghost(overall_metadata));

            proof {
                assert(Some(self@) == parse_main_table::<K>(subregion_view.committed(), 
                    overall_metadata.num_keys, overall_metadata.main_table_entry_size));
                lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(subregion_view);
            
                assert forall |idx: u64| {
                    &&& 0 <= idx < self@.durable_main_table.len() 
                    && !(#[trigger] self.outstanding_entries@.contains_key(idx))
                } implies self.no_outstanding_writes_to_entry(subregion_view, idx, overall_metadata.main_table_entry_size) by {
                    lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, overall_metadata.main_table_entry_size as nat);
                }
            }
        }

        pub proof fn lemma_if_only_difference_is_entry_then_flushed_state_only_differs_there(
            self,
            main_table_region: PersistentMemoryRegionView,
            old_self: Self,
            old_main_table_region: PersistentMemoryRegionView,
            overall_metadata: OverallMetadata,
            index: u64,
        )
            requires
                self.inv(main_table_region, overall_metadata),
                old_self.inv(old_main_table_region, overall_metadata),
                index < overall_metadata.num_keys,
                main_table_region.len() == old_main_table_region.len() == overall_metadata.main_table_size,
                overall_metadata.main_table_size >=
                    index_to_offset(overall_metadata.num_keys as nat, overall_metadata.main_table_entry_size as nat),
                main_table_region.committed() == old_main_table_region.committed(),
                forall|i: u64| 0 <= i < overall_metadata.num_keys && i != index ==>
                    self.outstanding_entries[i] == old_self.outstanding_entries[i],
            ensures
                ({
                    let entry_size = overall_metadata.main_table_entry_size;
                    let start = index_to_offset(index as nat, entry_size as nat);
                    forall|addr: int| {
                        &&& #[trigger] trigger_addr(addr)
                        &&& 0 <= addr < main_table_region.len()
                        &&& !(start <= addr < start + entry_size)
                    } ==> main_table_region.flush().committed()[addr] == old_main_table_region.flush().committed()[addr]
                })
        {
            assume(false); // TODO @jay
            let entry_size = overall_metadata.main_table_entry_size;
            let start = index_to_offset(index as nat, entry_size as nat);
            assert forall|addr: u64| {
                       &&& #[trigger] trigger_addr(addr as int)
                       &&& 0 <= addr < main_table_region.len()
                       &&& !(start <= addr < start + entry_size)
                   } implies main_table_region.flush().committed()[addr as int] ==
                             old_main_table_region.flush().committed()[addr as int] by {

                assert(old_main_table_region.state[addr as int].state_at_last_flush ==
                       old_main_table_region.committed()[addr as int]);

                assert(main_table_region.state[addr as int].state_at_last_flush == main_table_region.committed()[addr as int]);

                if addr < index_to_offset(overall_metadata.num_keys as nat,
                                          overall_metadata.main_table_entry_size as nat) {
                    lemma_auto_addr_in_entry_divided_by_entry_size(index as nat, overall_metadata.num_keys as nat,
                                                                   entry_size as nat);
                    let i = addr / entry_size as u64;
                    // assert(old_self.outstanding_entry_write_matches_pm_view(old_main_table_region, i, entry_size));
                    // assert(self.outstanding_entry_write_matches_pm_view(main_table_region, i, entry_size));
                    broadcast use pmcopy_axioms;
                }
            }
        }
    }
}
