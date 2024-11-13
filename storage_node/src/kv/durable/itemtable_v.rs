use crate::kv::durable::commonlayout_v::*;
use crate::kv::durable::itemtablelayout_v::*;
use crate::kv::durable::oplog::logentry_v::*;
use crate::kv::durable::inv_v::*;
use crate::kv::durable::util_v::*;
use crate::kv::kvimpl_t::*;
use crate::kv::layout_v::*;
use crate::kv::setup_v::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::traits_t;
use crate::pmem::subregion_v::*;
use crate::util_v::*;
use builtin::*;
use builtin_macros::*;
use std::hash::Hash;
use vstd::assert_seqs_equal;
use vstd::hash_map::*;
use vstd::bytes::*;
use vstd::prelude::*;
use std::collections::HashMap;

verus! {
    #[verifier::ext_equal]
    pub struct DurableItemTableView<I>
    {
        pub durable_item_table: Seq<Option<I>>,
    }

    impl<I> DurableItemTableView<I>
    {
        pub open spec fn init(num_keys: int) -> Self
        {
            Self {
                durable_item_table: Seq::new(num_keys as nat, |i: int| None),
            }
        }

        pub open spec fn new(item_table: Seq<Option<I>>) -> Self
        {
            Self {
                durable_item_table: item_table,
            }
        }

        pub open spec fn len(self) -> nat 
        {
            self.durable_item_table.len()
        }

        pub open spec fn delete(self, index: int) -> Self {
            Self {
                durable_item_table: self.durable_item_table.update(index, None)
            }
        }

        pub open spec fn update(self, index: int, item: I) -> Self
        {
            if index < 0 || index >= self.len() {
                self
            }
            else {
                Self{ durable_item_table: self.durable_item_table.update(index, Some(item)) }
            }
        }
    }

    pub open spec fn key_index_info_contains_index<K>(key_index_info: Seq<(Box<K>, u64, u64)>, idx: u64) -> bool
    {
        exists|j: int| 0 <= j < key_index_info.len() && (#[trigger] key_index_info[j]).2 == idx
    }

    // An `OutstandingItem` represents an update to the item table that has not 
    // yet been committed. Unlike the in the main table, we never need to refer
    // to the contents of deleted items, so we only have to keep track of 
    // the item itself for newly-created items.
    // TODO: the current PM model does not allow reading uncommitted bytes,
    // but if that changes in the future we don't have to store the item
    // in the created case either, since items are always tentatively
    // written to their final locations (unlike main table entries);
    #[verifier::reject_recursive_types(I)]
    pub enum OutstandingItem<I> {
        Created(I),
        CreatedThenDeleted,
        Deleted,
    }

    // `OutstandingItems` maintains a *runtime* hashmap of main table
    // indexes to the most recent update to that index. This is used
    // to handle operations on entries that have already been updated in 
    // the current transaction and to help reason about pending 
    // changes.
    #[verifier::reject_recursive_types(I)]
    pub struct OutstandingItems<I> {
        pub contents: HashMap<u64, OutstandingItem<I>>,
    }

    impl<I> OutstandingItems<I> {
        pub open spec fn inv(self) -> bool 
        {
            self.contents@.dom().finite()
        }

        pub open spec fn view(self) -> Map<u64, OutstandingItem<I>>
        {
            self.contents@
        }

        pub exec fn new() -> (out: Self) 
            ensures 
                out.inv(),
                out.contents@.len() == 0,
        {
            Self { contents: HashMap::new() }
        }

        pub open spec fn len(self) -> nat 
        {
            self.contents@.len()
        }

        pub open spec fn spec_index(self, i: u64) -> Option<OutstandingItem<I>>
        {
            if self@.contains_key(i) {
                Some(self@[i])
            } else {
                None
            }
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
    }

    #[verifier::reject_recursive_types(I)]
    pub struct DurableItemTable<K, I>
        where
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
    {
        pub item_size: u64,
        pub entry_size: u64,
        pub num_keys: u64,
        pub free_list: Vec<u64>,
        // `modified_indices` is equivalent to the domain of `outstanding_items`
        // (this is part of the item table invariant). We maintain it as a separate 
        // vector to make it easier to iterate over the modified entries 
        pub modified_indices: Vec<u64>,
        pub outstanding_items: OutstandingItems<I>,
        pub state: Ghost<DurableItemTableView<I>>,
        pub _phantom: Ghost<Option<K>>,
    }

    impl<K, I> DurableItemTable<K, I>
        where
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
    {
        pub open spec fn view(self) -> DurableItemTableView<I>
        {
            self.state@
        }

        pub open spec fn free_list(self) -> Set<u64>
        {
            self.free_list@.to_set()
        }

        // this function returns the set of indices with valid items 
        // in the current durable state. the durable kv store should 
        // maintain as an invariant that this matches the main table's
        // durable valid item indices.
        pub open spec fn durable_valid_indices(self) -> Set<u64>
        {
            Set::new(|i: u64| {
                &&& 0 <= i < self@.durable_item_table.len()
                &&& self@.durable_item_table[i as int] is Some
            })
        }

        // same as durable_valid_indices, except it returns a set including
        // indices with outstanding Created items and excluding Deleted items
        pub open spec fn tentative_valid_indices(self) -> Set<u64>
        {
            Set::new(|i: u64| {
                &&& 0 <= i < self@.durable_item_table.len()
                &&& {
                    ||| {
                            &&& self.outstanding_items[i] matches Some(item)
                            &&& item is Created 
                        } 
                    ||| {
                            &&& self.outstanding_items[i] is None
                            &&& self@.durable_item_table[i as int] is Some
                        }
                }
            })
        }

        // The tentative view of an item table is its durable view with any outstanding entries
        // applied. We maintain as an invariant in kvimpl_v.rs that this is equivalent 
        // to the tentative view obtained by installing the current log and parsing the item table
        // based on the valid item indices from the tentative main table.
        pub open spec fn tentative_view(self) -> DurableItemTableView<I>
        {
            DurableItemTableView {
                durable_item_table: self@.durable_item_table.map(|i: int, e| {
                    if self.outstanding_items@.contains_key(i as u64) {
                        let outstanding_item = self.outstanding_items@[i as u64];
                        match outstanding_item {
                            OutstandingItem::Created(item) => Some(item),
                            OutstandingItem::Deleted | OutstandingItem::CreatedThenDeleted => None,
                        }
                    } else {
                        e
                    }
                })
            }
        }

        pub open spec fn outstanding_item_table_entry_matches_pm_view(
            self,
            pm: PersistentMemoryRegionView,
            i: u64
        ) -> bool
        {
            let entry_size = I::spec_size_of() + u64::spec_size_of();
            let start = index_to_offset(i as nat, entry_size as nat) as int;
            match self.outstanding_items[i] {
                None => no_outstanding_writes_in_range(pm, start, start + entry_size),
                Some(item) => {
                    match item {
                        OutstandingItem::Created(item) => {
                            &&& outstanding_bytes_match(pm, start, spec_crc_bytes(I::spec_to_bytes(item)))
                            &&& outstanding_bytes_match(pm, start + u64::spec_size_of(), I::spec_to_bytes(item))
                        },
                        // with CreatedThenDeleted, there are outstanding bytes, but we don't know (or really care)
                        // what they are anymore
                        OutstandingItem::CreatedThenDeleted => true, 
                        OutstandingItem::Deleted => no_outstanding_writes_in_range(pm, start, start + entry_size),
                    }
                },
            }
        }
                                                                      
        pub open spec fn opaquable_inv(self, overall_metadata: OverallMetadata, valid_indices: Set<u64>) -> bool
        {
            let entry_size = I::spec_size_of() + u64::spec_size_of();
            &&& self.item_size == overall_metadata.item_size
            &&& self.entry_size == entry_size
            &&& self.free_list@.no_duplicates()
            &&& self.modified_indices@.no_duplicates()
            &&& forall|idx: u64| self.free_list@.contains(idx) ==> 
                    0 <= idx < overall_metadata.num_keys
            &&& forall |idx: u64| self.modified_indices@.contains(idx) ==> 
                    0 <= idx < overall_metadata.num_keys

            &&& forall |idx: u64| self.outstanding_items@.contains_key(idx) <==> 
                    #[trigger] self.modified_indices@.contains(idx)
            &&& self.outstanding_items@.len() == self.modified_indices@.len()

            // free list and list of modified indices are always disjoint
            &&& forall |idx: u64| #[trigger] self.modified_indices@.contains(idx) ==>
                    !self.free_list@.contains(idx)
            &&& forall |idx: u64| self.free_list@.contains(idx) ==>
                    !(#[trigger] self.modified_indices@.contains(idx))

            // if an item is not free, it is valid or has an outstanding update
            &&& forall |idx: u64| 0 <= idx < self@.durable_item_table.len() && !self.free_list@.contains(idx) ==>
                    self@.durable_item_table[idx as int] is Some || #[trigger] self.modified_indices@.contains(idx)

            // if an entry is valid in the durable table, it is not free
            &&& forall |idx: u64| {
                &&& 0 <= idx < self@.durable_item_table.len() 
                &&& {
                    ||| self@.durable_item_table[idx as int] is Some
                    ||| self.outstanding_items[idx] is Some
                }
            } ==> !(#[trigger] self.free_list@.contains(idx))

            // if an idx has an outstanding create write, it is currently invalid
            // in the durable state
            &&& forall |idx: u64| {
                &&& #[trigger] self.outstanding_items@.contains_key(idx) 
                &&& (self.outstanding_items@[idx] is Created || self.outstanding_items@[idx] is CreatedThenDeleted)
            } ==> self@.durable_item_table[idx as int] is None

            // if an idx has an outstanding delete write, it is currently valid
            // in the durable state
            &&& forall |idx: u64| {
                &&& #[trigger] self.outstanding_items@.contains_key(idx) 
                &&& self.outstanding_items@[idx] is Deleted 
            } ==> self@.durable_item_table[idx as int] is Some

            &&& self.modified_indices@.len() <= self@.durable_item_table.len()
            &&& self.outstanding_items.inv()
        }

        pub open spec fn inv(
            self,
            pm_view: PersistentMemoryRegionView,
            overall_metadata: OverallMetadata,
        ) -> bool
        {
            let entry_size = I::spec_size_of() + u64::spec_size_of();
            &&& self.opaquable_inv(overall_metadata, self.tentative_valid_indices())
            &&& self@.len() == self.num_keys == overall_metadata.num_keys
            &&& pm_view.len() >= overall_metadata.item_table_size >= overall_metadata.num_keys * entry_size
            &&& parse_item_table::<I, K>(pm_view.durable_state, overall_metadata.num_keys as nat,
                                       self.durable_valid_indices()) == Some(self@)
            &&& parse_item_table::<I, K>(pm_view.read_state, overall_metadata.num_keys as nat,
                                       self.durable_valid_indices()) == Some(self@)
            &&& forall|idx: u64| self.durable_valid_indices().contains(idx) ==> {
                let entry_bytes = extract_bytes(pm_view.durable_state, index_to_offset(idx as nat, entry_size as nat),
                                                entry_size as nat);
                &&& idx < overall_metadata.num_keys
                &&& validate_item_table_entry::<I, K>(entry_bytes)
                &&& self@.durable_item_table[idx as int] is Some
                &&& self@.durable_item_table[idx as int] == parse_item_entry::<I, K>(entry_bytes)
            }
            &&& forall |idx: u64| idx < overall_metadata.num_keys ==>
                self.outstanding_item_table_entry_matches_pm_view(pm_view, idx)
            &&& no_outstanding_writes_in_range(pm_view, overall_metadata.num_keys * entry_size,
                                             overall_metadata.item_table_size as int)
        }

        pub open spec fn valid(
            self,
            pm_view: PersistentMemoryRegionView,
            overall_metadata: OverallMetadata,
            valid_indices: Set<u64>,
        ) -> bool
        {
            &&& self.inv(pm_view, overall_metadata)
        }

        proof fn lemma_establish_bytes_parseable_for_valid_item(
            self,
            pm: PersistentMemoryRegionView,
            overall_metadata: OverallMetadata,
            index: u64,
        )
            requires
                self.inv(pm, overall_metadata),
                0 <= index < overall_metadata.num_keys,
                self.durable_valid_indices().contains(index),
                self@.durable_item_table[index as int] is Some,
            ensures
                ({
                    let entry_size = I::spec_size_of() + u64::spec_size_of();
                    let crc_bytes = extract_bytes(
                        pm.durable_state,
                        (index * entry_size as u64) as nat,
                        u64::spec_size_of() as nat,
                    );
                    let item_bytes = extract_bytes(
                        pm.durable_state,
                        (index * entry_size as u64) as nat + u64::spec_size_of(),
                        I::spec_size_of() as nat,
                    );
                    &&& u64::bytes_parseable(crc_bytes)
                    &&& I::bytes_parseable(item_bytes)
                    &&& crc_bytes == spec_crc_bytes(item_bytes)
                }),
        {
            let entry_size = I::spec_size_of() + u64::spec_size_of();
            lemma_valid_entry_index(index as nat, overall_metadata.num_keys as nat, entry_size as nat);
            let entry_bytes = extract_bytes(pm.durable_state, (index * entry_size) as nat, entry_size as nat);
            assert(extract_bytes(entry_bytes, 0, u64::spec_size_of()) =~=
                   extract_bytes(pm.durable_state, (index * entry_size as u64) as nat, u64::spec_size_of()));
            assert(extract_bytes(entry_bytes, u64::spec_size_of(), I::spec_size_of()) =~=
                   extract_bytes(pm.durable_state,
                                 (index * entry_size as u64) as nat + u64::spec_size_of(),
                                 I::spec_size_of()));
            assert(validate_item_table_entry::<I, K>(entry_bytes));
        }

        pub open spec fn get_latest_item_at_index(self, index: u64) -> Option<I>
        {
            if self.outstanding_items@.contains_key(index) {
                match self.outstanding_items[index].unwrap() {
                    OutstandingItem::Created(item) => Some(item),
                    OutstandingItem::Deleted | OutstandingItem::CreatedThenDeleted => None
                }
            } else if self@.durable_item_table[index as int] is Some {
                self@.durable_item_table[index as int]
            } else {
                None
            }
        }

        // This function updates `outstanding_items and `modified_indices` to 
        // reflect a newly-created item
        exec fn outstanding_item_create(&mut self, index: u64, item: I, Ghost(overall_metadata): Ghost<OverallMetadata>) 
            requires 
                // since we've removed this index from the free list, opaquable_inv 
                // doesn't hold here. most preconditions are conjuncts from opaquable_inv
                // that do currently hold; we reestablish the rest in this function
                old(self).outstanding_items.inv(),
                old(self).outstanding_items[index] is None,
                old(self)@.durable_item_table[index as int] is None,
                forall |idx: u64| old(self).outstanding_items@.contains_key(idx) <==> 
                    #[trigger] old(self).modified_indices@.contains(idx),
                forall |idx: u64| old(self).modified_indices@.contains(idx) ==>
                    idx < overall_metadata.num_keys,
                forall |idx: u64| old(self).free_list@.contains(idx) ==>
                    idx < overall_metadata.num_keys,

                !old(self).free_list@.contains(index),
                forall |idx: u64| #[trigger] old(self).modified_indices@.contains(idx) ==>
                    !old(self).free_list@.contains(idx),
                forall |idx: u64| old(self).free_list@.contains(idx) ==>
                    !(#[trigger] old(self).modified_indices@.contains(idx)),
                forall |idx: u64| 0 <= idx < old(self)@.durable_item_table.len() && !old(self).free_list@.contains(idx) && idx != index ==>
                    old(self)@.durable_item_table[idx as int] is Some || #[trigger] old(self).modified_indices@.contains(idx),
                forall |idx: u64| {
                    &&& 0 <= idx < old(self)@.durable_item_table.len() 
                    &&& {
                        ||| old(self)@.durable_item_table[idx as int] is Some
                        ||| old(self).outstanding_items[idx] is Some
                    }
                } ==> !(#[trigger] old(self).free_list@.contains(idx)),
                forall |idx: u64| {
                    &&& #[trigger] old(self).outstanding_items@.contains_key(idx) 
                    &&& (old(self).outstanding_items@[idx] is Created || old(self).outstanding_items@[idx] is CreatedThenDeleted)
                } ==> old(self)@.durable_item_table[idx as int] is None,
                forall |idx: u64| {
                    &&& #[trigger] old(self).outstanding_items@.contains_key(idx) 
                    &&& old(self).outstanding_items@[idx] is Deleted 
                } ==> old(self)@.durable_item_table[idx as int] is Some,
                forall |idx: u64| #[trigger] old(self).outstanding_items@.contains_key(idx) ==> ({
                    ||| old(self).outstanding_items@[idx] is Created
                    ||| old(self).outstanding_items@[idx] is Deleted
                    ||| old(self).outstanding_items@[idx] is CreatedThenDeleted
                }),

                index < overall_metadata.num_keys,
                old(self).modified_indices@.len() <= old(self)@.durable_item_table.len(),
                old(self)@.durable_item_table.len() == overall_metadata.num_keys,

                old(self).item_size == overall_metadata.item_size,
                old(self).free_list@.no_duplicates(),
                old(self).modified_indices@.no_duplicates(),
                old(self).entry_size == I::spec_size_of() + u64::spec_size_of(),
                old(self).outstanding_items@.len() == old(self).modified_indices@.len(),
            ensures 
                self.opaquable_inv(overall_metadata, self.tentative_valid_indices()),
                self.outstanding_items.inv(),
                self@ == old(self)@,
                self.entry_size == old(self).entry_size,
                self.num_keys == old(self).num_keys,
                self.free_list@ == old(self).free_list@,
                forall |idx: u64| self.outstanding_items@.contains_key(idx) <==> 
                    #[trigger] self.modified_indices@.contains(idx),
                ({
                    let outstanding_item = OutstandingItem::Created(item);
                    self.outstanding_items@ == old(self).outstanding_items@.insert(index, outstanding_item)
                })
        {
            let outstanding_item = OutstandingItem::Created(item);
            self.outstanding_items.contents.insert(index, outstanding_item);

            self.modified_indices.push(index);

            proof {
                assert(!old(self).modified_indices@.contains(index));

                // trigger useful facts about the new modified_indices list
                assert forall |idx: u64| self.modified_indices@.contains(idx) implies
                    idx < overall_metadata.num_keys
                by {
                    if idx == index { assert(index < overall_metadata.num_keys); } 
                    else { assert(old(self).modified_indices@.contains(idx)); }
                }
                assert(self.modified_indices@.subrange(0, self.modified_indices@.len() - 1) == old(self).modified_indices@);
                assert(self.modified_indices@[self.modified_indices@.len() - 1] == index);

                broadcast use vstd::std_specs::hash::group_hash_axioms;

                // Prove that modified indices and outstanding items still match
                assert forall |idx: u64| self.outstanding_items@.contains_key(idx) implies 
                    #[trigger] self.modified_indices@.contains(idx) 
                by {
                    if idx == index {
                        assert(self.modified_indices@.contains(index));
                    } else {
                        assert(old(self).outstanding_items@.contains_key(idx));
                        assert(old(self).modified_indices@.contains(idx));
                    }
                }
                assert forall |idx: u64| #[trigger] self.modified_indices@.contains(idx) implies
                    self.outstanding_items@.contains_key(idx)
                by {
                    if idx == index {
                        assert(self.outstanding_items.contents@.contains_key(idx));
                    } else {
                        assert(old(self).modified_indices@.contains(idx));
                        assert(old(self).outstanding_items@.contains_key(idx));
                    }
                }

                // Prove that modified indices and the free list are still disjoint
                assert forall |idx: u64| #[trigger] self.modified_indices@.contains(idx) implies
                    !self.free_list@.contains(idx)
                by {
                    if idx != index {
                        assert(old(self).modified_indices@.contains(idx));
                        assert(!old(self).free_list@.contains(idx));
                    } // else trivial
                }

                assert forall |idx: u64| 0 <= idx < self@.durable_item_table.len() && !self.free_list@.contains(idx) implies
                    self@.durable_item_table[idx as int] is Some || #[trigger] self.modified_indices@.contains(idx)
                by {
                    if idx != index {
                        assert(old(self)@.durable_item_table[idx as int] is Some || old(self).modified_indices@.contains(idx));
                    } // else trivial
                }

                assert(self.modified_indices@.len() <= self@.durable_item_table.len()) by {
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
        }

        // This function updates `outstanding_items` and `modified_indices` to 
        // reflect a deleted item
        exec fn outstanding_item_delete(&mut self, index: u64, Ghost(overall_metadata): Ghost<OverallMetadata>)
            requires
                old(self).opaquable_inv(overall_metadata, old(self).tentative_valid_indices()),
                index < overall_metadata.num_keys,
                !old(self).free_list@.contains(index),
                old(self)@.durable_item_table.len() == overall_metadata.num_keys,
                ({
                    ||| old(self).outstanding_items[index] is None 
                    ||| ({
                        &&& old(self).outstanding_items[index] matches Some(entry)
                        &&& entry is Created
                    })
                }),
            ensures 
                self.opaquable_inv(overall_metadata, self.tentative_valid_indices()),
                self.outstanding_items.inv(),
                self@ == old(self)@,
                self.entry_size == old(self).entry_size,
                self.num_keys == old(self).num_keys,
                self.free_list@ == old(self).free_list@,
                forall |idx: u64| self.outstanding_items@.contains_key(idx) <==> 
                    #[trigger] self.modified_indices@.contains(idx),
                ({
                    let outstanding_item = if old(self).outstanding_items[index] is Some {
                        OutstandingItem::CreatedThenDeleted
                    } else {
                        OutstandingItem::Deleted
                    };
                    self.outstanding_items@ == old(self).outstanding_items@.insert(index, outstanding_item)
                })
        {
            if !self.outstanding_items.contents.contains_key(&index) {
                assert(!self.modified_indices@.contains(index)) by {
                    broadcast use vstd::std_specs::hash::group_hash_axioms;
                }
                self.modified_indices.push(index);
                assert(self.modified_indices@.subrange(0, self.modified_indices@.len() - 1) == old(self).modified_indices@);
                assert(self.modified_indices@[self.modified_indices@.len() - 1] == index);
            } else {
                assert(self.modified_indices@ == old(self).modified_indices@);
            }
            let outstanding_item = if self.outstanding_items.contents.contains_key(&index) {
                OutstandingItem::CreatedThenDeleted
            } else {
                OutstandingItem::Deleted
            };
            self.outstanding_items.contents.insert(index, outstanding_item);

            proof {
                // TODO: refactor this; some of it is identical to outstanding_item_create
                broadcast use vstd::std_specs::hash::group_hash_axioms;

                // trigger useful facts about the new modified_indices list
                assert forall |idx: u64| self.modified_indices@.contains(idx) implies
                    idx < overall_metadata.num_keys
                by {
                    if idx == index { assert(index < overall_metadata.num_keys); } 
                    else { assert(old(self).modified_indices@.contains(idx)); }
                }

                // Prove that modified indices and outstanding items still match
                assert forall |idx: u64| self.outstanding_items@.contains_key(idx) implies 
                    #[trigger] self.modified_indices@.contains(idx) 
                by {
                    if idx == index {
                        assert(self.modified_indices@.contains(index));
                    } else {
                        assert(old(self).outstanding_items@.contains_key(idx));
                        assert(old(self).modified_indices@.contains(idx));
                    }
                }
                assert forall |idx: u64| #[trigger] self.modified_indices@.contains(idx) implies
                    self.outstanding_items@.contains_key(idx)
                by {
                    if idx == index {
                        assert(self.outstanding_items.contents@.contains_key(idx));
                    } else {
                        assert(old(self).modified_indices@.contains(idx));
                        assert(old(self).outstanding_items@.contains_key(idx));
                    }
                }

                assert forall |idx: u64| 0 <= idx < self@.durable_item_table.len() && !self.free_list@.contains(idx) implies
                    self@.durable_item_table[idx as int] is Some || #[trigger] self.modified_indices@.contains(idx)
                by {
                    if idx != index {
                        assert(old(self)@.durable_item_table[idx as int] is Some || old(self).modified_indices@.contains(idx));
                    } // else trivial
                }

                assert(self.modified_indices@.len() <= self@.durable_item_table.len()) by {
                    // if we increased the length of the modified indices list, we have to prove
                    // that it still hasn't grown beyond the length of the table itself
                    if !old(self).modified_indices@.contains(index) {
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

                assert forall |idx: u64| {
                    &&& #[trigger] self.outstanding_items@.contains_key(idx) 
                    &&& (self.outstanding_items@[idx] is Created || self.outstanding_items@[idx] is CreatedThenDeleted)
                } implies self@.durable_item_table[idx as int] is None by {
                    if self.outstanding_items@[idx] is CreatedThenDeleted  {
                        assert(old(self)@.durable_item_table[idx as int] is None);
                    }
                }
            }
        }

        // Read an item from the item table given an index. Returns error if the index
        // does not contain a valid, uncorrupted item. 
        pub exec fn read_item<PM>(
            &self,
            subregion: &PersistentMemorySubregion,
            pm_region: &PM,
            item_table_index: u64,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        ) -> (result: Result<Box<I>, KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires
                subregion.inv(pm_region),
                self.inv(subregion.view(pm_region), overall_metadata),
                item_table_index < self.num_keys,
                self.tentative_valid_indices().contains(item_table_index),
                ({
                    ||| ({
                        &&& self.outstanding_items[item_table_index] matches Some(item)
                        &&& item is Created
                    })
                    ||| self@.durable_item_table[item_table_index as int] is Some
                }),
            ensures
                match result {
                    Ok(item) => Some(*item) == self.get_latest_item_at_index(item_table_index),
                    Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                    _ => false,
                },
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;

            let ghost pm_view = subregion.view(pm_region);
            let entry_size = self.entry_size;
            proof {
                lemma_valid_entry_index(item_table_index as nat, overall_metadata.num_keys as nat, entry_size as nat);
            }

            // if there is an outstanding version of this item, read it. if not, go to PM
            // TODO: discuss whether this is actually what we want to do. for internal metadata
            // We want to be sure to always read the most recent version, but I'm not sure about 
            // returning tentative items. 
            // However, right now, this is the only thing we CAN do because the model currently 
            // prevents us from reading outstanding bytes.
            
            if self.outstanding_items.contents.contains_key(&item_table_index) {
                match self.outstanding_items.contents.get(&item_table_index).unwrap() {
                    OutstandingItem::Created(item) => Ok(Box::new(*item)),
                    OutstandingItem::Deleted | OutstandingItem::CreatedThenDeleted => {
                        assert(false);
                        Err(KvError::InternalError)
                    },
                }
            } else {
                let crc_addr = item_table_index * (entry_size as u64);
                let item_addr = crc_addr + traits_t::size_of::<u64>() as u64;

                // Read the item and CRC at this slot
                let ghost mem = pm_view.read_state;
                let ghost entry_bytes = extract_bytes(mem, (item_table_index * entry_size) as nat, entry_size as nat);
                assert(self.outstanding_item_table_entry_matches_pm_view(pm_view, item_table_index));
                assert(entry_bytes =~= extract_bytes(pm_view.durable_state,
                                                     (item_table_index * entry_size) as nat, entry_size as nat));
                let ghost true_crc_bytes = extract_bytes(mem, crc_addr as nat, u64::spec_size_of());
                let ghost true_item_bytes = extract_bytes(mem, item_addr as nat, I::spec_size_of());
                let ghost true_item = I::spec_from_bytes(true_item_bytes);

                proof {
                    assert(self.durable_valid_indices().contains(item_table_index));
                    self.lemma_establish_bytes_parseable_for_valid_item(pm_view, overall_metadata, item_table_index);
                    assert(true_crc_bytes =~= extract_bytes(entry_bytes, 0, u64::spec_size_of()));
                    assert(true_item_bytes =~= extract_bytes(entry_bytes, u64::spec_size_of(), I::spec_size_of()));
                    assert(self@.durable_item_table[item_table_index as int] == parse_item_entry::<I, K>(entry_bytes));
                }

                assert(self.outstanding_item_table_entry_matches_pm_view(pm_view, item_table_index));
                let crc = match subregion.read_relative_aligned::<u64, PM>(pm_region, crc_addr) {
                    Ok(val) => val,
                    Err(e) => { assert(false); return Err(KvError::PmemErr { pmem_err: e }); }
                };
                let item = match subregion.read_relative_aligned::<I, PM>(pm_region, item_addr) {
                    Ok(val) => val,
                    Err(e) => { assert(false); return Err(KvError::PmemErr { pmem_err: e }); },
                };
                
                if !check_crc(item.as_slice(), crc.as_slice(), Ghost(true_item_bytes),
                              Ghost(pm_region.constants().impervious_to_corruption),
                              Ghost(item_addr + subregion.start()),
                              Ghost(crc_addr + subregion.start())) {
                    return Err(KvError::CRCMismatch);
                }

                let item = item.extract_init_val(Ghost(true_item));
                Ok(item)
            }
        }

        pub proof fn lemma_changing_unused_entry_doesnt_affect_parse_item_table(
            self: Self,
            v1: PersistentMemoryRegionView,
            v2: PersistentMemoryRegionView,
            overall_metadata: OverallMetadata,
            which_entry: u64,
        )
            requires
                v1.valid(),
                v2.valid(),
                self.inv(v1, overall_metadata),
                !self.durable_valid_indices().contains(which_entry),
                v1.len() == v2.len(),
                which_entry < overall_metadata.num_keys,
                forall|addr: int| {
                    let entry_size = I::spec_size_of() + u64::spec_size_of();
                    let start_addr = which_entry * entry_size;
                    let end_addr = start_addr + entry_size;
                    &&& 0 <= addr < v1.len()
                    &&& !(start_addr <= addr < end_addr)
                } ==> views_match_at_addr(v1, v2, addr),
            ensures
                parse_item_table::<I, K>(v2.durable_state, overall_metadata.num_keys as nat,
                                         self.durable_valid_indices()) == Some(self@),
                parse_item_table::<I, K>(v2.read_state, overall_metadata.num_keys as nat,
                                         self.durable_valid_indices()) == Some(self@),
        {
            let entry_size = I::spec_size_of() + u64::spec_size_of();
            let num_keys = overall_metadata.num_keys;
            let start_addr = which_entry * entry_size;
            let end_addr = start_addr + entry_size;
            let can_views_differ_at_addr = |addr: int| start_addr <= addr < end_addr;

            assert(parse_item_table::<I, K>(v1.durable_state, num_keys as nat, self.durable_valid_indices()) ==
                   Some(self@));
            lemma_valid_entry_index(which_entry as nat, num_keys as nat, entry_size as nat);
            let entry_bytes = extract_bytes(v1.durable_state, (which_entry * entry_size) as nat, entry_size as nat);
            assert forall|addr: int| {
                       &&& 0 <= addr < v2.durable_state.len()
                       &&& v1.durable_state[addr] != #[trigger] v2.durable_state[addr]
                   } implies
                   address_belongs_to_invalid_item_table_entry::<I>(addr, num_keys, self.durable_valid_indices())
            by {
                let entry_size = I::spec_size_of() + u64::spec_size_of();
                assert(!views_match_at_addr(v1, v2, addr));
                assert(can_views_differ_at_addr(addr));
                let addrs_entry = addr / entry_size as int;
                lemma_addr_in_entry_divided_by_entry_size(which_entry as nat, entry_size as nat, addr);
            }
            lemma_parse_item_table_doesnt_depend_on_fields_of_invalid_entries::<I, K>(
                v1.durable_state, v2.durable_state, num_keys, self.durable_valid_indices()
            );

            assert(parse_item_table::<I, K>(v1.read_state, num_keys as nat, self.durable_valid_indices()) ==
                   Some(self@));
            assert forall|addr: int| {
                       &&& 0 <= addr < v2.read_state.len()
                       &&& v1.read_state[addr] != #[trigger] v2.read_state[addr]
                   } implies
                   address_belongs_to_invalid_item_table_entry::<I>(addr, num_keys, self.durable_valid_indices())
            by {
                let entry_size = I::spec_size_of() + u64::spec_size_of();
                assert(!views_match_at_addr(v1, v2, addr));
                assert(can_views_differ_at_addr(addr));
                let addrs_entry = addr / entry_size as int;
                lemma_addr_in_entry_divided_by_entry_size(which_entry as nat, entry_size as nat, addr);
            }
            lemma_parse_item_table_doesnt_depend_on_fields_of_invalid_entries::<I, K>(
                v1.read_state, v2.read_state, num_keys, self.durable_valid_indices()
            );
        }

        // this function can be used to both create new items and do COW updates to existing items.
        // must always write to an invalid slot
        // this operation is NOT directly logged
        // returns the index of the slot that the item was written to
        pub exec fn tentatively_write_item<PM, Perm>(
            &mut self,
            subregion: &WriteRestrictedPersistentMemorySubregion,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
            item: &I,
            Tracked(perm): Tracked<&Perm>,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        ) -> (result: Result<u64, KvError<K>>)
            where
                PM: PersistentMemoryRegion,
                Perm: CheckPermission<Seq<u8>>,
            requires
                subregion.inv(old::<&mut _>(wrpm_region), perm),
                old(self).inv(subregion.view(old::<&mut _>(wrpm_region)), overall_metadata),
                subregion.len() >= overall_metadata.item_table_size,
                forall|addr: int| {
                    &&& 0 <= addr < subregion.view(old::<&mut _>(wrpm_region)).len()
                    &&& address_belongs_to_invalid_item_table_entry::<I>(
                        addr, overall_metadata.num_keys,
                        old(self).durable_valid_indices().union(old(self).tentative_valid_indices())
                    )
                } ==> #[trigger] subregion.is_writable_relative_addr(addr),
                old(self).free_list().disjoint(old(self).tentative_valid_indices()),
                // we have not yet made any modifications to the subregion
                subregion.initial_subregion_view() == subregion.view(old::<&mut _>(wrpm_region)),
                subregion.initial_region_view() == old::<&mut _>(wrpm_region)@,
            ensures
                subregion.inv(wrpm_region, perm),
                self.inv(subregion.view(wrpm_region), overall_metadata),
                match result {
                    Ok(index) => {
                        &&& index < overall_metadata.num_keys
                        &&& old(self).free_list().contains(index)
                        &&& self@.durable_item_table == old(self)@.durable_item_table
                        &&& self.free_list() == old(self).free_list().remove(index)
                        &&& self.durable_valid_indices() == old(self).durable_valid_indices()
                        &&& self.tentative_valid_indices() == old(self).tentative_valid_indices().insert(index)
                        &&& self.outstanding_items@ ==
                               old(self).outstanding_items@.insert(index, OutstandingItem::Created(*item))
                        &&& self.tentative_view() == old(self).tentative_view().update(index as int, *item)
                    },
                    Err(KvError::OutOfSpace) => {
                        &&& self@ == old(self)@
                        &&& self.free_list() == old(self).free_list()
                        &&& self.free_list().len() == 0
                        &&& wrpm_region == old(wrpm_region)
                        &&& self.tentative_view() == old(self).tentative_view()
                        &&& self.tentative_valid_indices() == old(self).tentative_valid_indices()
                    },
                    _ => false,
                }
        {
            let ghost old_pm_view = subregion.view(wrpm_region);
            
            let entry_size = self.entry_size;
            assert(self.inv(subregion.view(wrpm_region), overall_metadata));
            assert(entry_size == u64::spec_size_of() + I::spec_size_of());
            
            // pop a free index from the free list
            let free_index = match self.free_list.pop() {
                Some(index) => index,
                None => {
                    proof {
                        self.free_list@.unique_seq_to_set();
                        assert forall|idx: u64| 0 <= idx < overall_metadata.num_keys implies
                            self.outstanding_item_table_entry_matches_pm_view(subregion.view(wrpm_region), idx)
                        by {
                            lemma_valid_entry_index(idx as nat, self.num_keys as nat, entry_size as nat);
                            assert(old(self).outstanding_item_table_entry_matches_pm_view(old_pm_view, idx));
                        }
                    }
                    return Err(KvError::OutOfSpace);
                }
            };

            proof {
                // popping an index from the free list breaks some parts of the invariant, but since we haven't modified
                // PM or the outstanding item map, this part still holds
                assert(self.outstanding_item_table_entry_matches_pm_view(subregion.view(wrpm_region), free_index)) by {
                    assert(!self.modified_indices@.contains(free_index));
                    assert(old(self).outstanding_item_table_entry_matches_pm_view(subregion.view(old::<&mut _>(wrpm_region)), free_index));
                }

                assert(old(self).free_list().contains(free_index));
                assert(!self.durable_valid_indices().contains(free_index));
                assert(!self.tentative_valid_indices().contains(free_index));
                assert forall |idx: u64| self.free_list@.contains(idx) implies 
                    idx < overall_metadata.num_keys
                by {
                    assert(old(self).free_list@.contains(idx));
                }

                assert forall|addr: int| free_index * entry_size <= addr < free_index * entry_size + entry_size implies
                    subregion.is_writable_relative_addr(addr)
                by {
                    lemma_addr_in_entry_divided_by_entry_size(free_index as nat, entry_size as nat, addr);
                    lemma_valid_entry_index(free_index as nat, overall_metadata.num_keys as nat, entry_size as nat);
                }

                broadcast use pmcopy_axioms;
                lemma_valid_entry_index(free_index as nat, overall_metadata.num_keys as nat, entry_size as nat);
                assert(self.outstanding_items[free_index] is None);

                assert(old(self).free_list@.subrange(0, old(self).free_list@.len() - 1) == self.free_list@);
                assert(old(self).free_list@[old(self).free_list@.len() - 1] == free_index);
                assert(self.free_list@.len() == old(self).free_list@.len() - 1);
                assert(!self.free_list@.contains(free_index));

                // Prove that if the current free list does not contain an index, then it's 
                // either the one we just allocated or it was already in use.
                assert forall |idx: u64| {
                    &&& 0 <= idx < old(self)@.durable_item_table.len() 
                    &&& !self.free_list@.contains(idx) 
                } implies {
                    ||| idx == free_index 
                    ||| !old(self).free_list@.contains(idx)
                } by {
                    if idx != free_index {
                        // proof by contradiction -- suppose the old free list did contain idx.
                        // then, idx would have to equal free_index
                        if old(self).free_list@.contains(idx) {
                            assert(old(self).free_list@.subrange(0, old(self).free_list@.len() - 1) == self.free_list@);
                            assert(forall |i: int| 0 <= i < old(self).free_list@.len() - 1 ==> 
                                old(self).free_list@[i] == self.free_list@[i]);
                            assert(idx == old(self).free_list@[old(self).free_list@.len() - 1]);
                            assert(false);
                        }
                    }
                }

                // If an index is valid in the durable state or has an outstanding write,
                // then it's not free.
                assert forall |idx: u64| {
                    &&& 0 <= idx < self@.durable_item_table.len() 
                    &&& {
                        ||| self@.durable_item_table[idx as int] is Some
                        ||| self.outstanding_items[idx] is Some
                    }
                } implies !(#[trigger] self.free_list@.contains(idx)) by {
                    if self@.durable_item_table[idx as int] is Some {
                        assert(!old(self).free_list@.contains(idx));
                        assert(!self.free_list@.contains(idx));
                    } else {
                        assert(self.outstanding_items[idx] is Some);
                        assert(self.modified_indices@.contains(idx));
                    }
                }
            }

            let crc_addr = free_index * (entry_size as u64);
            let item_addr = crc_addr + traits_t::size_of::<u64>() as u64;

            // calculate and write the CRC of the provided item
            let crc: u64 = calculate_crc(item);

            assert(subregion.view(wrpm_region) == subregion.view(old::<&mut _>(wrpm_region)));
            subregion.serialize_and_write_relative::<u64, Perm, PM>(wrpm_region, crc_addr, &crc, Tracked(perm));
            
            let ghost cur_wrpm = *wrpm_region;

            // write the item itself
            subregion.serialize_and_write_relative::<I, Perm, PM>(wrpm_region, item_addr, item, Tracked(perm));

            // Add this item to the outstanding item map
            self.outstanding_item_create(free_index, *item, Ghost(overall_metadata));

            let ghost pm_view = subregion.view(wrpm_region);
            proof {
                lemma_auto_can_result_from_partial_write_effect();
            }

            assert forall|idx: u64| {
                &&& idx < overall_metadata.num_keys
                &&& #[trigger] self.outstanding_items[idx] is None
            } implies {
                let start = index_to_offset(idx as nat, entry_size as nat) as int;
                no_outstanding_writes_in_range(pm_view, start, start + entry_size) 
            } by {
                let start = index_to_offset(idx as nat, entry_size as nat) as int;
                lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, entry_size as nat);
                lemma_entries_dont_overlap_unless_same_index(idx as nat, free_index as nat, entry_size as nat);
                assert(old(self).outstanding_item_table_entry_matches_pm_view(subregion.view(old::<&mut _>(wrpm_region)),
                                                                            idx));
                assert(no_outstanding_writes_in_range(subregion.view(old::<&mut _>(wrpm_region)), start,
                                                      start + entry_size));
            }

            assert forall|idx: u64| self.durable_valid_indices().contains(idx) implies {
                let entry_bytes = extract_bytes(pm_view.durable_state, (idx * entry_size) as nat, entry_size as nat);
                &&& idx < overall_metadata.num_keys
                &&& validate_item_table_entry::<I, K>(entry_bytes)
                &&& self@.durable_item_table[idx as int] is Some
                &&& self@.durable_item_table[idx as int] == parse_item_entry::<I, K>(entry_bytes)
            } by {
                let entry_bytes = extract_bytes(pm_view.durable_state, (idx * entry_size) as nat, entry_size as nat);
                lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, entry_size as nat);
                lemma_entries_dont_overlap_unless_same_index(idx as nat, free_index as nat, entry_size as nat);
                assert(entry_bytes =~= extract_bytes(subregion.view(old::<&mut _>(wrpm_region)).durable_state,
                                                     (idx * entry_size) as nat, entry_size as nat));
            }

            assert forall |other_index: u64| self.free_list().contains(other_index) <==>
                     old(self).free_list().contains(other_index) && other_index != free_index by {
                if other_index != free_index {
                    if old(self).free_list().contains(other_index) {
                        let j = choose|j: int| 0 <= j < old(self).free_list@.len() && old(self).free_list@[j] == other_index;
                        assert(self.free_list@[j] == other_index);
                        assert(self.free_list().contains(other_index));
                    }
                }
            }

            assert(parse_item_table::<I, K>(pm_view.durable_state, overall_metadata.num_keys as nat,
                                            self.durable_valid_indices()) == Some(self@) &&
                   parse_item_table::<I, K>(pm_view.read_state, overall_metadata.num_keys as nat,
                                            self.durable_valid_indices()) == Some(self@)) by {
                old(self).lemma_changing_unused_entry_doesnt_affect_parse_item_table(
                    old_pm_view, pm_view, overall_metadata, free_index
                );
            }

            assert forall|idx: u64| 0 <= idx < overall_metadata.num_keys implies
                self.outstanding_item_table_entry_matches_pm_view(pm_view, idx) 
            by {
                lemma_valid_entry_index(idx as nat, self.num_keys as nat, entry_size as nat);
                lemma_entries_dont_overlap_unless_same_index(idx as nat, free_index as nat, entry_size as nat);
                assert(old(self).outstanding_item_table_entry_matches_pm_view(old_pm_view, idx));
            }

            assert(self.free_list() =~= old(self).free_list().remove(free_index));
            assert(self.tentative_valid_indices() =~= old(self).tentative_valid_indices().insert(free_index));
            assert(self.tentative_view() =~= old(self).tentative_view().update(free_index as int, *item));

            Ok(free_index)
        }

        pub proof fn lemma_table_is_empty_at_setup<PM, L>(
            subregion: &WritablePersistentMemorySubregion,
            pm_region: &PM,
            valid_indices: Set<u64>,
            num_keys: u64,
        )
            where 
                PM: PersistentMemoryRegion,
                L: PmCopy,
            requires 
                valid_indices == Set::<u64>::empty(),
                ({ 
                    let mem = subregion.view(pm_region).durable_state;
                    let item_entry_size = I::spec_size_of() + u64::spec_size_of();
                    num_keys * item_entry_size <= mem.len()
                }),
            ensures
                ({
                    let mem = subregion.view(pm_region).durable_state;
                    &&& parse_item_table::<I, K>(mem, num_keys as nat, valid_indices) matches Some(item_table_view)
                    &&& item_table_view == DurableItemTableView::<I>::init(num_keys as int)
                })
        {
            let mem = subregion.view(pm_region).durable_state;
            let item_entry_size = I::spec_size_of() + u64::spec_size_of();
            let item_table_view = parse_item_table::<I, K>(mem, num_keys as nat, valid_indices);
            assert(item_table_view is Some);

            let item_table_view = item_table_view.unwrap();
            
            assert(item_table_view == DurableItemTableView::<I>::init(num_keys as int));
        }

        pub exec fn start<PM, L>(
            subregion: &PersistentMemorySubregion,
            pm_region: &PM,
            key_index_info: &Vec<(Box<K>, u64, u64)>,
            overall_metadata: OverallMetadata,
            version_metadata: VersionMetadata,
        ) -> (result: Result<Self, KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
                L: PmCopy + std::fmt::Debug,
            requires
                subregion.inv(pm_region),
                pm_region@.flush_predicted(),
                overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr, overall_metadata.kvstore_id),
                subregion.len() == overall_metadata.item_table_size,
                subregion.view(pm_region).flush_predicted(),
                ({
                    let valid_indices_view = Seq::new(key_index_info@.len(), |i: int| key_index_info[i].2);
                    let table = parse_item_table::<I, K>(subregion.view(pm_region).durable_state, overall_metadata.num_keys as nat, valid_indices_view.to_set());
                    table is Some
                }),
                overall_metadata.item_size == I::spec_size_of(),
                forall |j: int| 0 <= j < key_index_info.len() ==> 
                    0 <= (#[trigger] key_index_info[j]).2 < overall_metadata.num_keys,
                overall_metadata.item_size + u64::spec_size_of() <= u64::MAX,
            ensures 
                match result {
                    Ok(item_table) => {
                        let valid_indices_view = Seq::new(key_index_info@.len(), |i: int| key_index_info[i].2);
                        let valid_indices = valid_indices_view.to_set();
                        let table = parse_item_table::<I, K>(subregion.view(pm_region).durable_state, overall_metadata.num_keys as nat, valid_indices_view.to_set()).unwrap();
                        &&& item_table.valid(subregion.view(pm_region), overall_metadata, valid_indices)
                        // table view is correct
                        &&& table == item_table@
                        &&& forall |i: int| 0 <= i < key_index_info.len() ==> {
                                let index = #[trigger] key_index_info[i].2;
                                // all indexes that are in use are not in the free list
                                !item_table.free_list().contains(index)
                            }
                        &&& {
                            let in_use_indices = Set::new(|i: u64| 0 <= i < overall_metadata.num_keys && key_index_info_contains_index(key_index_info@, i));
                            let all_possible_indices = Set::new(|i: u64| 0 <= i < overall_metadata.num_keys);
                            let free_indices = all_possible_indices - in_use_indices;
                            // all free indexes are in the free list
                            &&& forall |i: u64| free_indices.contains(i) ==> #[trigger] item_table.free_list().contains(i)
                            &&& in_use_indices == Seq::new(key_index_info@.len(), |i: int| key_index_info[i].2).to_set()

                            &&& item_table.durable_valid_indices() == in_use_indices
                            &&& item_table.tentative_valid_indices() == in_use_indices
                        }
                    }
                    Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                    Err(KvError::PmemErr{ pmem_err }) => true,
                    Err(_) => false
                }
        {
            // The main thing we need to do here is to use the key_index_info vector to construct the item table's
            // allocator. We don't need to read anything from the item table, but we should have its subregion so we can 
            // prove that the allocator is correct

            let num_keys = overall_metadata.num_keys;
            let ghost pm_view = subregion.view(pm_region);

            let ghost valid_indices_view = Seq::new(key_index_info@.len(), |i: int| key_index_info[i].2);
            let ghost table = parse_item_table::<I, K>(pm_view.durable_state, overall_metadata.num_keys as nat, valid_indices_view.to_set());

            // TODO: we could make this a bit more efficient by making the boolean vector a bitmap
            let mut free_vec: Vec<bool> = Vec::with_capacity(num_keys as usize);
            let mut i: usize = 0;
            // initialize the vec to all true; we'll set indexes that are in-use to false. 
            // verus doesn't support array literals right now, so we have to do this with a loop
            while i < num_keys as usize
                invariant 
                    0 <= i <= num_keys,
                    free_vec.len() == i,
                    forall |j: int| 0 <= j < i ==> free_vec[j],
            {
                free_vec.push(true);
                i += 1;    
            }

            i = 0;
            // now set all indexes that are in use to false
            let ghost old_free_vec_len = free_vec.len();
            while i < key_index_info.len()
                invariant 
                    0 <= i <= key_index_info.len(),
                    free_vec.len() == old_free_vec_len,
                    free_vec.len() == num_keys,
                    forall |j: int| 0 <= j < key_index_info.len() ==> 0 <= #[trigger] key_index_info[j].2 < num_keys,
                    forall |j: int| 0 <= j < i ==> {
                        let index = #[trigger] key_index_info[j].2;
                        !free_vec[index as int]
                    },
                    forall |j: int| 0 <= j < free_vec.len() ==> {
                        // either free_vec is true at j and there are no entries between 0 and i with this index
                        #[trigger] free_vec[j] <==> (forall |k: int| 0 <= k < i ==> #[trigger] key_index_info[k].2 != j)
                    },
            {
                let index = key_index_info[i].2;
                free_vec.set(index as usize, false);
                i += 1;
            }

            // next, build the allocator based on the values in the boolean array. indexes containing true 
            // are free, indexes containing false are not
            let mut item_table_allocator: Vec<u64> = Vec::with_capacity(num_keys as usize);
            i = 0;
            while i < num_keys as usize
                invariant
                    0 <= i <= num_keys,
                    item_table_allocator.len() <= i <= num_keys,
                    free_vec.len() == num_keys,
                    forall |j: u64| 0 <= j < i ==> free_vec[j as int] ==> item_table_allocator@.contains(j),
                    forall |j: int| 0 <= j < key_index_info.len() ==> !item_table_allocator@.contains(#[trigger] key_index_info[j].2),
                    forall |j: int| 0 <= j < free_vec.len() ==> 
                        (#[trigger] free_vec[j] <==>
                         forall |k: int| 0 <= k < key_index_info.len() ==> #[trigger] key_index_info[k].2 != j),
                    forall |j: int| 0 <= j < item_table_allocator.len() ==> item_table_allocator@[j] < i,
                    forall |j: int, k: int| 0 <= j < item_table_allocator.len() && 0 <= k < item_table_allocator.len() && j != k ==>
                        item_table_allocator@[j] != item_table_allocator@[k],
            {
                let ghost old_item_table_allocator = item_table_allocator;
                assert(forall |j: int| 0 <= j < key_index_info.len() ==> !item_table_allocator@.contains(#[trigger] key_index_info[j].2));
                if free_vec[i] {
                    item_table_allocator.push(i as u64);
                    assert(item_table_allocator@.subrange(0, item_table_allocator.len() - 1) == old_item_table_allocator@);
                    assert(item_table_allocator@[item_table_allocator.len() - 1] == i);
                    assert(forall |j: int| 0 <= j < key_index_info.len() ==> #[trigger] key_index_info[j].2 != i);
                }
                
                i += 1;
            }

            let ghost in_use_indices = Set::new(|i: u64| 0 <= i < overall_metadata.num_keys &&
                                                key_index_info_contains_index(key_index_info@, i));
            let item_table = Self {
                item_size: overall_metadata.item_size,
                entry_size: overall_metadata.item_size + traits_t::size_of::<u64>() as u64, // item + CRC
                num_keys: overall_metadata.num_keys,
                free_list: item_table_allocator,
                modified_indices: Vec::new(),
                outstanding_items: OutstandingItems::new(),
                state: Ghost(table.unwrap()),
                _phantom: Ghost(None)
            };
            assert(in_use_indices =~= Seq::new(key_index_info@.len(), |i: int| key_index_info[i].2).to_set()) by {
                assert forall|j: u64| in_use_indices.contains(j) implies
                    Seq::new(key_index_info@.len(), |i: int| key_index_info[i].2).to_set().contains(j) by {
                    let jj = choose|jj: int| 0 <= jj < key_index_info@.len() && (#[trigger] key_index_info@[jj]).2 == j;
                    assert(Seq::new(key_index_info@.len(), |i: int| key_index_info[i].2)[jj] == j);
                }
            }

            proof {
                assert(forall |i: int| 0 <= i < key_index_info.len() ==> {
                    let index = #[trigger] key_index_info[i].2;
                    !item_table.free_list().contains(index)
                });

                let all_possible_indices = Set::new(|i: u64| 0 <= i < overall_metadata.num_keys);
                let free_indices = all_possible_indices - in_use_indices;
                let entry_size = I::spec_size_of() + u64::spec_size_of();

                assert forall|idx: u64| #[trigger] in_use_indices.contains(idx) implies
                    !item_table.free_list@.contains(idx) && item_table.state@.durable_item_table[idx as int] is Some by {
                    let j: int = choose|j: int| 0 <= j < key_index_info.len() && (#[trigger] key_index_info[j]).2 == idx;
                    assert(valid_indices_view[j] == idx);
                    assert(valid_indices_view.to_set().contains(idx));
                    assert(idx * entry_size + entry_size <= overall_metadata.num_keys * entry_size) by {
                        lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, entry_size as nat);
                    }
                    assert(validate_item_table_entry::<I, K>(extract_bytes(pm_view.durable_state,
                        index_to_offset(idx as nat, entry_size as nat), entry_size as nat)));
                }

                assert forall|idx: u64| idx < num_keys &&
                           #[trigger] item_table.outstanding_items[idx] is None implies
                    no_outstanding_writes_in_range(pm_view, idx * entry_size, idx * entry_size + entry_size) by {
                        lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, entry_size as nat);
                }
            }

            proof {
                // Prove that the item table region only has one crash state, which recovers to the initial table's state
                let pm_view = subregion.view(pm_region);
//                lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(pm_view);
//                assert(forall |s| pm_view.can_crash_as(s) ==> s == pm_view.durable_state);
                assert(in_use_indices == item_table.durable_valid_indices());
                assert(parse_item_table::<I, K>(pm_view.durable_state, overall_metadata.num_keys as nat, in_use_indices) == Some(item_table@));

                assert(item_table.durable_valid_indices() == in_use_indices);
                assert(item_table.tentative_valid_indices() == in_use_indices);
            }

            Ok(item_table)
        }

        pub exec fn tentatively_deallocate_item(
            &mut self,
            Ghost(pm_subregion): Ghost<PersistentMemoryRegionView>,
            index: u64,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        )
            requires 
                old(self).inv(pm_subregion, overall_metadata),
                0 <= index < overall_metadata.num_keys,
                // the provided index is not currently free or pending (de)allocation
                !old(self).free_list().contains(index),
                ({
                    ||| old(self).outstanding_items[index] is None 
                    ||| ({
                        &&& old(self).outstanding_items[index] matches Some(entry)
                        &&& entry is Created
                    })
                }),
            ensures
                self.inv(pm_subregion, overall_metadata),
                old(self).free_list() == self.free_list(),
                old(self)@ == self@,
                ({
                    let outstanding_item = if old(self).outstanding_items[index] is Some {
                        OutstandingItem::CreatedThenDeleted
                    } else {
                        OutstandingItem::Deleted
                    };
                    self.outstanding_items@ == old(self).outstanding_items@.insert(index, outstanding_item)
                }),
                self.tentative_valid_indices() == old(self).tentative_valid_indices().remove(index),
                self.durable_valid_indices() == old(self).durable_valid_indices(),
        {
            self.outstanding_item_delete(index, Ghost(overall_metadata));

            proof {
                let entry_size = I::spec_size_of() + u64::spec_size_of();
                assert forall |idx: u64| idx < overall_metadata.num_keys implies
                    self.outstanding_item_table_entry_matches_pm_view(pm_subregion, idx)
                by { assert(old(self).outstanding_item_table_entry_matches_pm_view(pm_subregion, idx)); }
                assert(self.tentative_valid_indices() =~= old(self).tentative_valid_indices().remove(index));
            }
        }

        pub exec fn abort_transaction(
            &mut self,
            Ghost(pm): Ghost<PersistentMemoryRegionView>,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        )
            requires 
                pm.flush_predicted(),
                old(self).opaquable_inv(overall_metadata, old(self).tentative_valid_indices()),
                ({
                    let entry_size = I::spec_size_of() + u64::spec_size_of();
                    &&& pm.len() >= overall_metadata.item_table_size >= overall_metadata.num_keys * entry_size
                }),
                ({
                    let s = pm.durable_state;
                    &&& parse_item_table::<I, K>(s, overall_metadata.num_keys as nat, old(self).durable_valid_indices())
                            matches Some(table_view)
                    &&& table_view.durable_item_table == old(self)@.durable_item_table
                }),
                forall|idx: u64| old(self).durable_valid_indices().contains(idx) ==> {
                    let entry_size = I::spec_size_of() + u64::spec_size_of();
                    let entry_bytes = extract_bytes(pm.durable_state, (idx * entry_size) as nat, entry_size as nat);
                    &&& idx < overall_metadata.num_keys
                    &&& validate_item_table_entry::<I, K>(entry_bytes)
                    &&& old(self)@.durable_item_table[idx as int] is Some
                    &&& old(self)@.durable_item_table[idx as int] == parse_item_entry::<I, K>(entry_bytes)
                },
                old(self).num_keys == old(self)@.len() == overall_metadata.num_keys,
            ensures
                self.inv(pm, overall_metadata),
                self@ == old(self)@,
                self.outstanding_items@.len() == 0,
                self.tentative_view() == self@,
                self.tentative_valid_indices() == self.durable_valid_indices(),
        {
            self.clear_modified_indices_for_abort(Ghost(overall_metadata));

            assert forall |idx: u64| 0 <= idx < overall_metadata.num_keys implies
                self.outstanding_item_table_entry_matches_pm_view(pm, idx)
            by {
                let entry_size = I::spec_size_of() + u64::spec_size_of();
                let start = index_to_offset(idx as nat, entry_size as nat) as int;
                lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, entry_size as nat);
                assert(no_outstanding_writes_in_range(pm, start, start + entry_size));
            }
            
            assert(self.inv(pm, overall_metadata));
            assert(self.tentative_view() == self@);
            assert(self.tentative_valid_indices() == self.durable_valid_indices());
        }

        exec fn clear_modified_indices_for_abort(
            &mut self,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        )
            requires 
                old(self).opaquable_inv(overall_metadata, old(self).tentative_valid_indices()),
                old(self).outstanding_items.inv(),
            ensures 
                self.opaquable_inv(overall_metadata, self.tentative_valid_indices()),
                self.outstanding_items@.len() == 0,
                self.modified_indices@.len() == 0,
                self.num_keys == old(self).num_keys,
                self@ == old(self)@,
                forall |idx: u64| {
                    // the free list contains idx if 1) idx was already free, or 
                    // 2) the idx was allocated in this transaction
                    ||| old(self).free_list@.contains(idx)
                    ||| {
                        &&& old(self).modified_indices@.contains(idx)
                        &&& (old(self).outstanding_items@[idx] is Created || 
                                old(self).outstanding_items@[idx] is CreatedThenDeleted)
                    }
                } <==> #[trigger] self.free_list@.contains(idx),
        {
            // iterate over the modified indices and update the free list
            // with entries that were allocated in this transaction
            let mut index = 0;
            while index < self.modified_indices.len()
                invariant
                    self.modified_indices@.no_duplicates(),
                    self.free_list@.no_duplicates(),
                    self@ == old(self)@,
                    self.num_keys == old(self).num_keys,
                    self.item_size == old(self).item_size,
                    self.entry_size == old(self).entry_size,
                    forall |i: u64| index <= i < self.modified_indices.len() ==> { 
                        let j = #[trigger] self.modified_indices@[i as int];
                        &&& self.modified_indices@.contains(j) ==> !self.free_list@.contains(j)
                        &&& self.free_list@.contains(j) ==> !self.modified_indices@.contains(j)
                    },
                    forall |idx: u64| self.outstanding_items@.contains_key(idx) <==> 
                        #[trigger] self.modified_indices@.contains(idx),
                    self.outstanding_items@ == old(self).outstanding_items@,
                    self.modified_indices@ == old(self).modified_indices@,
                    self@.durable_item_table == old(self)@.durable_item_table,
                    forall |i: u64| {
                        let j = #[trigger] old(self).modified_indices[i as int];
                        &&& 0 <= i < index 
                        &&& old(self).outstanding_items@.contains_key(j) 
                        &&& (old(self).outstanding_items@[j] is Created || 
                                old(self).outstanding_items@[j] is CreatedThenDeleted)
                    } ==> self.free_list@.contains(old(self).modified_indices[i as int]),
                    forall |idx: u64| self.modified_indices@.contains(idx) ==> idx < overall_metadata.num_keys,
                    forall |idx: u64| self.free_list@.contains(idx) ==> idx < overall_metadata.num_keys,

                    forall |idx: u64| 0 <= idx < self@.durable_item_table.len() && !self.free_list@.contains(idx) ==>
                        self@.durable_item_table[idx as int] is Some || #[trigger] self.modified_indices@.contains(idx),

                    forall |idx: u64| old(self).free_list@.contains(idx) ==> self.free_list@.contains(idx),
                    forall |idx: u64| #![trigger self.free_list@.contains(idx)]
                                      #![trigger old(self).free_list@.contains(idx)] 
                                      #![trigger old(self).modified_indices@.contains(idx)]
                        self.free_list@.contains(idx) ==> {
                            ||| old(self).free_list@.contains(idx)
                            ||| ({
                                    &&& old(self).modified_indices@.contains(idx)
                                    &&& (old(self).outstanding_items@[idx] is Created || 
                                            old(self).outstanding_items@[idx] is CreatedThenDeleted)
                                })
                        },
            {
                broadcast use vstd::std_specs::hash::group_hash_axioms;

                let ghost free_list_at_top = self.free_list@;
                let current_index = self.modified_indices[index];
                assert(self.modified_indices@.contains(current_index)); // required for triggers

                let current_item = self.outstanding_items.contents.get(&current_index).unwrap();
                match current_item {
                    OutstandingItem::Created(_) | OutstandingItem::CreatedThenDeleted => {
                        self.free_list.push(current_index);
                        assert(self.free_list@.subrange(0, free_list_at_top.len() as int) == free_list_at_top);
                        assert(self.free_list@[free_list_at_top.len() as int] == current_index);
                        assert forall |idx: u64| self.free_list@.contains(idx) implies idx < overall_metadata.num_keys by {
                            if idx != current_index {
                                assert(free_list_at_top.contains(idx));
                            }
                        }
                    }
                    _ => {} // deleted indices remain valid when the transaction is aborted
                }

                index += 1;
            }

            self.modified_indices.clear();
            self.outstanding_items.clear();

            assert forall |idx: u64| 0 <= idx < self@.durable_item_table.len() && !self.free_list@.contains(idx) implies
                self@.durable_item_table[idx as int] is Some || #[trigger] self.modified_indices@.contains(idx)
            by {
                if !old(self).free_list@.contains(idx) {
                    // neither the old nor the new free list contain idx
                    if old(self)@.durable_item_table[idx as int] is Some {
                        assert(self@.durable_item_table[idx as int] is Some);
                    } else {
                        // idx is not free but also not valid -- this is impossible
                        assert(old(self).modified_indices@.contains(idx));
                        assert(!self.modified_indices@.contains(idx));
                        assert(false);                                              
                    }
                } // else, trivial
            }
        }

        exec fn finalize_outstanding_items(
            &mut self,
            Ghost(pm): Ghost<PersistentMemoryRegionView>,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        )
            requires 
                forall |idx: u64| old(self).outstanding_items@.contains_key(idx) ==> {
                    let entry = old(self).outstanding_items@[idx];
                    match entry {
                        OutstandingItem::Created(item) => old(self)@.durable_item_table[idx as int] is Some,
                        _ => old(self)@.durable_item_table[idx as int] is None
                    }
                },
                old(self).outstanding_items.inv(),
                old(self).modified_indices@.no_duplicates(),
                old(self).free_list@.no_duplicates(),
                forall |idx: u64| old(self).outstanding_items@.contains_key(idx) <==> 
                    #[trigger] old(self).modified_indices@.contains(idx),
                forall |idx: u64| old(self).modified_indices@.contains(idx) ==> 
                    0 <= idx < overall_metadata.num_keys,
                forall |idx: u64| old(self).free_list@.contains(idx) ==> 
                    0 <= idx < overall_metadata.num_keys,
                old(self).modified_indices@.len() <= old(self)@.durable_item_table.len(),
                forall |i: u64| 0 <= i < old(self).modified_indices.len() ==> { 
                    let j = #[trigger] old(self).modified_indices@[i as int];
                    &&& old(self).modified_indices@.contains(j) ==> !old(self).free_list@.contains(j)
                    &&& old(self).free_list@.contains(j) ==> !old(self).modified_indices@.contains(j)
                },
                old(self).item_size == overall_metadata.item_size,
                old(self).entry_size == I::spec_size_of() + u64::spec_size_of(),
                forall |idx: u64| 0 <= idx < old(self)@.durable_item_table.len() && !old(self).free_list@.contains(idx) ==>
                    old(self)@.durable_item_table[idx as int] is Some || #[trigger] old(self).modified_indices@.contains(idx),
                forall |idx: u64| {
                    &&& 0 <= idx < old(self)@.durable_item_table.len() 
                    &&& {
                        ||| old(self)@.durable_item_table[idx as int] is Some
                        ||| old(self).outstanding_items[idx] is Some
                    }
                } ==> !(#[trigger] old(self).free_list@.contains(idx)),
            ensures 
                self.opaquable_inv(overall_metadata, self.tentative_valid_indices()),
                self@ == old(self)@,
                self.num_keys == old(self).num_keys,
                self.entry_size == old(self).entry_size,
                self.outstanding_items@.len() == 0,
        {
            // iterate over the modified items and determine 
            // which should be added to the free list
            let mut index = 0;
            while index < self.modified_indices.len() 
                invariant 
                    self@ == old(self)@,
                    self.outstanding_items.inv(),
                    self.item_size == old(self).item_size,
                    self.num_keys == old(self).num_keys,
                    self.entry_size == old(self).entry_size,
                    self.outstanding_items@ == old(self).outstanding_items@,
                    self.modified_indices@ == old(self).modified_indices@,
                    self.modified_indices@.no_duplicates(),
                    self.free_list@.no_duplicates(),
                    forall |idx: u64| self.outstanding_items@.contains_key(idx) <==> 
                        #[trigger] self.modified_indices@.contains(idx),
                    forall |idx: u64| self.modified_indices@.contains(idx) ==> 
                        0 <= idx < overall_metadata.num_keys,
                    forall |idx: u64| self.free_list@.contains(idx) ==> 
                        0 <= idx < overall_metadata.num_keys,
                    forall |i: u64| index <= i < self.modified_indices.len() ==> { 
                        let j = #[trigger] self.modified_indices@[i as int];
                        &&& self.modified_indices@.contains(j) ==> !self.free_list@.contains(j)
                        &&& self.free_list@.contains(j) ==> !self.modified_indices@.contains(j)
                    },
                    self.modified_indices@.len() <= self@.durable_item_table.len(),
                    // no entries are removed from the free list
                    forall |idx: u64| old(self).free_list@.contains(idx) ==>
                        self.free_list@.contains(idx),
                    forall |idx: u64| 0 <= idx < self@.durable_item_table.len() && !self.free_list@.contains(idx) ==>
                        self@.durable_item_table[idx as int] is Some || #[trigger] self.modified_indices@.contains(idx),
                    // all new free list elements are associated with a deleted entry
                    forall |idx: u64| !old(self).free_list@.contains(idx) && self.free_list@.contains(idx) ==> {
                        &&& self.outstanding_items[idx] matches Some(entry)
                        &&& (entry is Deleted || entry is CreatedThenDeleted)
                    },
                    forall |i: int| {
                        let idx = #[trigger] self.modified_indices@[i];
                        &&& 0 <= i < index
                        &&& self.outstanding_items[idx] matches Some(entry)
                        &&& (entry is Deleted || entry is CreatedThenDeleted)
                    } ==> {
                        let idx = self.modified_indices@[i];
                        self.free_list@.contains(idx)
                    },
            {
                let ghost free_list_at_top = self.free_list@;
                let current_index = self.modified_indices[index];
                proof {
                    assert(self.modified_indices@.contains(current_index)); // required for triggers
                    assert(current_index < overall_metadata.num_keys);
                    broadcast use vstd::std_specs::hash::group_hash_axioms;
                }
                
                let current_item = self.outstanding_items.contents.get(&current_index).unwrap();
                match current_item {
                    OutstandingItem::Deleted | OutstandingItem::CreatedThenDeleted => {
                        self.free_list.push(current_index);
                        assert(self.free_list@.subrange(0, free_list_at_top.len() as int) == free_list_at_top);
                        assert(self.free_list@[free_list_at_top.len() as int] == current_index);
                        assert(self.free_list@.contains(current_index));
                        assert forall |idx: u64| self.free_list@.contains(idx) implies idx < overall_metadata.num_keys by {
                            if idx != current_index {
                                assert(free_list_at_top.contains(idx));
                            }
                        }
                    }
                    _ => {} // otherwise, do nothing
                }
                index += 1;
            }
            
            self.modified_indices.clear();
            self.outstanding_items.clear();

            assert forall |idx: u64| 0 <= idx < self@.durable_item_table.len() && !self.free_list@.contains(idx) implies
                self@.durable_item_table[idx as int] is Some || #[trigger] self.modified_indices@.contains(idx)
            by {
                if !old(self).free_list@.contains(idx) {
                    // neither the old nor new free list contain idx

                    // if the free list does not contain idx, then it is either
                    // currently valid or has an outstanding write
                    if old(self)@.durable_item_table[idx as int] is Some {
                        assert(self@.durable_item_table[idx as int] is Some);
                    } else {
                        assert(old(self).modified_indices@.contains(idx));
                        match old(self).outstanding_items@[idx] {
                            OutstandingItem::Created(item) => {
                                assert(self@.durable_item_table[idx as int] is Some);
                                assert(false);
                            }
                            OutstandingItem::Deleted | OutstandingItem::CreatedThenDeleted => {
                                assert(self.free_list@.contains(idx));
                                assert(false);
                            }
                        }                        
                    }
                } // else, trivial
            }
        }

        pub exec fn finalize_item_table(
            &mut self,
            Ghost(old_self): Ghost<Self>,
            Ghost(pm): Ghost<PersistentMemoryRegionView>,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        )
            requires
                pm.flush_predicted(),
                old(self).opaquable_inv(overall_metadata, old(self).durable_valid_indices()),
                ({
                    let subregion_view = get_subregion_view(pm, overall_metadata.item_table_addr as nat,
                        overall_metadata.item_table_size as nat);
                    let entry_size = I::spec_size_of() + u64::spec_size_of();
                    &&& parse_item_table::<I, K>(subregion_view.durable_state, overall_metadata.num_keys as nat, old(self).tentative_valid_indices()) == 
                            Some(old(self).tentative_view())
                    &&& subregion_view.len() >= overall_metadata.item_table_size >= overall_metadata.num_keys * entry_size
                }),
                pm.len() >= overall_metadata.item_table_addr + overall_metadata.item_table_size,
                old_self@.len() == old(self)@.len() == old(self).num_keys == overall_metadata.num_keys,
                old_self.free_list() == old(self).free_list(),
                old_self.num_keys == old(self).num_keys,
                old_self@.durable_item_table.len() == old(self)@.durable_item_table.len(),
            ensures 
                ({
                    let subregion_view = get_subregion_view(pm, overall_metadata.item_table_addr as nat,
                        overall_metadata.item_table_size as nat);
                    let entry_size = I::spec_size_of() + u64::spec_size_of();
                    &&& self.inv(subregion_view, overall_metadata)
                    &&& Some(self@) == parse_item_table::<I, K>(subregion_view.durable_state, overall_metadata.num_keys as nat, old(self).tentative_valid_indices())
                }),
                self@.len() == old(self)@.len(),
                self.num_keys == old(self).num_keys,
                self.outstanding_items@.len() == 0,
        {
            assert forall |idx: u64| self.outstanding_items@.contains_key(idx) implies {
                let entry = self.outstanding_items@[idx];
                match entry {
                    OutstandingItem::Created(item) => self.tentative_view().durable_item_table[idx as int] is Some,
                    _ => self.tentative_view().durable_item_table[idx as int] is None
                }
            } by {
                assert(self.modified_indices@.contains(idx));
                assert(idx < overall_metadata.num_keys);
            }

            let ghost subregion_view = get_subregion_view(pm, overall_metadata.item_table_addr as nat,
                overall_metadata.item_table_size as nat);
            self.state = Ghost(parse_item_table::<I, K>(subregion_view.durable_state, 
                overall_metadata.num_keys as nat, self.tentative_valid_indices()).unwrap());

            assert(self.durable_valid_indices() == self.tentative_valid_indices());
            assert(self.durable_valid_indices() == old(self).tentative_valid_indices());

            self.finalize_outstanding_items(Ghost(subregion_view), Ghost(overall_metadata));
            
            proof {
                assert(parse_item_table::<I, K>(subregion_view.durable_state, overall_metadata.num_keys as nat, self.durable_valid_indices()) == Some(self@));
//                lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(subregion_view);
                
                let subregion_view = get_subregion_view(pm, overall_metadata.item_table_addr as nat,
                    overall_metadata.item_table_size as nat);
                assert forall |idx: u64| idx < overall_metadata.num_keys implies
                    self.outstanding_item_table_entry_matches_pm_view(subregion_view, idx)
                by {
                    let entry_size = I::spec_size_of() + u64::spec_size_of();
                    lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, entry_size);
                }
            }
        }
    }
}
