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

        // pub closed spec fn spec_index(self, index: int) -> Option<DurableItemTableViewEntry<I>>
        // {
        //     if index < 0 || index >= self.len() 
        //     {
        //         self.item_table[index]
        //     } else {
        //         None
        //     }
        // }

        pub open spec fn len(self) -> nat 
        {
            self.durable_item_table.len()
        }

        pub open spec fn delete(self, index: int) -> Self {
            Self {
                durable_item_table: self.durable_item_table.update(index, None)
            }
        }

        pub open spec fn insert(self, index: int, item: I) -> Self {
            Self {
                durable_item_table: self.durable_item_table.update(index, Some(item))
            }
        }

        // // Inserting an entry and committing it are two separate operations. Inserted entries
        // // are invalid until they are explicitly committed. Attempting to insert at an index
        // // that already has a valid entry results in an error.
        // // TODO: update these operations for version without valid CDBs in the items
        // pub closed spec fn insert<K>(self, index: int, crc: u64, item: I) -> Result<Self, KvError<K>> 
        //     where 
        //         K: std::fmt::Debug
        // {
        //     if index < 0 || index >= self.len() {
        //         Err(KvError::IndexOutOfRange)
        //     } else if self[index] is Some {
        //         Err(KvError::EntryIsValid)
        //     } else {
        //         Ok(Self {
        //             item_table: self.item_table.update(
        //                     index,
        //                     Some(DurableItemTableViewEntry {
        //                         crc,
        //                         item,
        //                     })
        //                 ),

        //             }
        //         )
        //     } 
        // }

        // // pub closed spec fn commit_entry(self, index: int) -> Result<Self, KvError<K>> 
        // // {
        // //     if index < 0 || index >= self.len() {
        // //         Err(KvError::IndexOutOfRange)
        // //     } else if self[index] is Some {
        // //         Err(KvError::EntryIsValid)
        // //     } else {
        // //         let old_entry = self.item_table[index];
        // //         Ok(Self {
        // //             item_table: self.item_table.update(
        // //                 index,
        // //                 Some(DurableItemTableViewEntry {
        // //                     crc: old_entry.crc,
        // //                     item: old_entry.item
        // //                 })
        // //             ),
        // //             _phantom: None
        // //         })
        // //     }
        // // }

        // pub closed spec fn invalidate_entry<K>(self, index: int) -> Result<Self, KvError<K>>
        //     where 
        //         K: std::fmt::Debug
        // {
        //     if index < 0 || index >= self.len() {
        //         Err(KvError::IndexOutOfRange)
        //     } else if self[index] is None {
        //         Err(KvError::EntryIsNotValid)
        //     } else {
        //         let old_entry = self.item_table[index];
        //         Ok(Self {
        //             item_table: self.item_table.update(
        //                 index,
        //                 None
        //             ),
        //         })
        //     }
        // }
    }

    pub open spec fn key_index_info_contains_index<K>(key_index_info: Seq<(Box<K>, u64, u64)>, idx: u64) -> bool
    {
        exists|j: int| 0 <= j < key_index_info.len() && (#[trigger] key_index_info[j]).2 == idx
    }

    // pub struct DurableItemTableAllocatorView 
    // {
    //     pub free_list: Set<u64>,
    //     pub pending_allocations: Set<u64>,
    //     pub pending_deallocations: Set<u64>
    // }

    // impl DurableItemTableAllocatorView {
    //     // pub open spec fn spec_abort_alloc_transaction(self) -> Self 
    //     // {
    //     //     Self {
    //     //         free_list: self.free_list + self.pending_allocations,
    //     //         pending_allocations: Set::empty(),
    //     //         pending_deallocations: Set::empty(),
    //     //     }
    //     // }

    //     // pub open spec fn pending_alloc_check(
    //     //     self,
    //     //     idx: u64,
    //     //     current_valid_indices: Set<u64>,
    //     //     tentative_valid_indices: Set<u64>
    //     // ) -> bool 
    //     // {
    //     //     // If an index is in the current valid index set but not the tentative one, 
    //     //     // it is pending deallocation. We still consider this index valid because it
    //     //     // will be valid upon recovery if we were to crash right now.
    //     //     &&& {
    //     //         &&& current_valid_indices.contains(idx)
    //     //         &&& !tentative_valid_indices.contains(idx)
    //     //     } <==> self.pending_deallocations.contains(idx) 
    //     //     // If an index is not in the current valid index set but is in the tentative one,
    //     //     // it is pending allocation
    //     //     &&& {
    //     //         &&& !current_valid_indices.contains(idx)
    //     //         &&& tentative_valid_indices.contains(idx)
    //     //     } <==> self.pending_allocations.contains(idx)
    //     //     // If the index is in neither set, it is in the free list
    //     //     &&& {
    //     //         &&& !current_valid_indices.contains(idx)
    //     //         &&& !tentative_valid_indices.contains(idx)
    //     //     } <==> self.free_list.contains(idx)
    //     //     // If the index is in both sets, it's valid and not pending deallocation.
    //     //     &&& {
    //     //         &&& current_valid_indices.contains(idx)
    //     //         &&& tentative_valid_indices.contains(idx)
    //     //     } ==> !self.pending_deallocations.contains(idx)
    //     // }
    // }

    #[verifier::reject_recursive_types(I)]
    pub enum OutstandingItem<I> {
        Created(I),
        CreatedThenDeleted,
        Deleted,
    }

    // #[verifier::reject_recursive_types(I)]
    // pub struct OutstandingItem<I> {
    //     pub status: EntryStatus,
    //     pub item: I,
    // }

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
        pub modified_indices: Vec<u64>,
        pub outstanding_items: OutstandingItems<I>, // when we can read outstanding bytes, this doesn't need to store I
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
                None => pm.no_outstanding_writes_in_range(start, start + entry_size),
                Some(item) => {
                    match item {
                        OutstandingItem::Created(item) => {
                            &&& outstanding_bytes_match(pm, start, spec_crc_bytes(I::spec_to_bytes(item)))
                            &&& outstanding_bytes_match(pm, start + u64::spec_size_of(), I::spec_to_bytes(item))
                        },
                        // with CreatedThenDeleted, there are outstanding bytes, but we don't know (or really care)
                        // what they are anymore
                        OutstandingItem::CreatedThenDeleted => true, 
                        OutstandingItem::Deleted => pm.no_outstanding_writes_in_range(start, start + entry_size),
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

            // &&& forall|i: int| 0 <= i < self.pending_allocations@.len() ==> 
            //         self.pending_allocations@[i] < overall_metadata.num_keys
            // &&& forall |i: int| 0 <= i < self.pending_deallocations@.len() ==>
            //         self.pending_deallocations@[i] < overall_metadata.num_keys
            
            // &&& forall|i: int, j: int| 0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() && i != j ==>
            //         self.free_list@[i] != self.free_list@[j]
            
                    // &&& forall|i: int| 0 <= i < self.free_list@.len() ==>
            //         self.outstanding_item_table@[#[trigger] self.free_list@[i] as int] is None
            // &&& forall|idx: u64| valid_indices.contains(idx) ==>
            //     #[trigger] self.outstanding_item_table@[idx as int] is None
        }

        // TODO: this needs to say something about pending allocations
        pub open spec fn inv(
            self,
            pm_view: PersistentMemoryRegionView,
            overall_metadata: OverallMetadata,
            // valid_indices: Set<u64>,
        ) -> bool
        {
            let entry_size = I::spec_size_of() + u64::spec_size_of();
            &&& self.opaquable_inv(overall_metadata, self.tentative_valid_indices())
            &&& self@.len() == self.num_keys == overall_metadata.num_keys
            &&& pm_view.len() >= overall_metadata.item_table_size >= overall_metadata.num_keys * entry_size
            // &&& forall|idx: u64| #[trigger] valid_indices.contains(idx) ==> 
            //         !self.free_list().contains(idx) && !self.pending_allocations_view().contains(idx)
            // &&& self.pending_allocations_view().disjoint(self.pending_deallocations_view())
            // &&& self.free_list().disjoint(self.pending_deallocations_view())
            &&& forall |s| #[trigger] pm_view.can_crash_as(s) ==>
                   parse_item_table::<I, K>(s, overall_metadata.num_keys as nat, self.durable_valid_indices()) == Some(self@)
            &&& forall|idx: u64| self.durable_valid_indices().contains(idx) ==> {
                let entry_bytes = extract_bytes(pm_view.committed(), index_to_offset(idx as nat, entry_size as nat), entry_size as nat);
                &&& idx < overall_metadata.num_keys
                &&& validate_item_table_entry::<I, K>(entry_bytes)
                &&& self@.durable_item_table[idx as int] is Some
                &&& self@.durable_item_table[idx as int] == parse_item_entry::<I, K>(entry_bytes)
            }
            &&& forall |idx: u64| idx < overall_metadata.num_keys ==>
                self.outstanding_item_table_entry_matches_pm_view(pm_view, idx)
            &&& pm_view.no_outstanding_writes_in_range(overall_metadata.num_keys * entry_size,
                                                      overall_metadata.item_table_size as int)
            // &&& forall|idx: u64| self.pending_allocations@.contains(idx) ==>
            //     #[trigger] self.outstanding_item_table@[idx as int] is Some

            // &&& forall |idx: u64| 0 <= idx < self.num_keys ==> 
            //         self.allocator_view().spec_abort_alloc_transaction().pending_alloc_check(idx, valid_indices, valid_indices)
        }

        // pub open spec fn pending_alloc_inv(
        //     self,
        //     current_valid_indices: Set<u64>,
        //     tentative_valid_indices: Set<u64>
        // ) -> bool
        // {
        //     forall |idx: u64| 0 <= idx < self.num_keys ==> 
        //         self.allocator_view().pending_alloc_check(idx, current_valid_indices, tentative_valid_indices)
        // }

        // pub open spec fn pending_alloc_check(
        //     self,
        //     idx: u64,
        //     current_valid_indices: Set<u64>,
        //     durable_valid_indices: Set<u64>,
        //     tentative_valid_indices: Set<u64>
        // ) -> bool 
        // {
        //     // If an index is in the current valid index set but not the tentative one, 
        //     // it is pending deallocation. We still consider this index valid because it
        //     // will be valid upon recovery if we were to crash right now.
        //     &&& {
        //         &&& durable_valid_indices.contains(idx)
        //         &&& !tentative_valid_indices.contains(idx)
        //     } <==> {
        //         &&& self.pending_deallocations_view().contains(idx) 
        //         &&& current_valid_indices.contains(idx)
        //     }
        //     // If an index is not in the current valid index set but is in the tentative one,
        //     // it is pending allocation
        //     &&& {
        //         &&& !durable_valid_indices.contains(idx)
        //         &&& tentative_valid_indices.contains(idx)
        //     } <==> self.pending_allocations_view().contains(idx)
        //     // If the index is in neither set, it is in the free list
        //     &&& {
        //         &&& !durable_valid_indices.contains(idx)
        //         &&& !tentative_valid_indices.contains(idx)
        //     } <==> self.free_list().contains(idx)
        //     // If the index is in both sets, it's valid and not pending deallocation.
        //     &&& {
        //         &&& durable_valid_indices.contains(idx)
        //         &&& tentative_valid_indices.contains(idx)
        //     } <==> {
        //         &&& !self.pending_deallocations_view().contains(idx) 
        //         &&& current_valid_indices.contains(idx)
        //     }
        // }

        // // TODO @hayley look at the triggers here
        // pub proof fn lemma_valid_indices_disjoint_with_free_and_pending_alloc(
        //     self,
        //     current_valid_indices: Set<u64>,
        //     tentative_valid_indices: Set<u64>
        // )
        //     requires 
        //         self.pending_alloc_inv(current_valid_indices, tentative_valid_indices),
        //     ensures 
        //         forall |idx: u64| 0 <= idx < self.num_keys && !(#[trigger] current_valid_indices.contains(idx)) ==> {
        //             ||| self.pending_allocations_view().contains(idx)
        //             ||| self.free_list().contains(idx)
        //         },
        //         forall|idx: u64| 0 <= idx < self.num_keys && #[trigger] current_valid_indices.contains(idx) ==> 
        //             !self.free_list().contains(idx) && !self.pending_allocations_view().contains(idx),
        //         forall|idx: u64| #![trigger current_valid_indices.contains(idx)]
        //             0 <= idx < self.num_keys && self.free_list().contains(idx) ==>
        //             !current_valid_indices.contains(idx) && !tentative_valid_indices.contains(idx),
        // {
        //     // Annoyingly, we have to have the entire alloc check specified here, presumably 
        //     // to hit the proper triggers. 
        //     assert(forall |idx: u64| #![trigger current_valid_indices.contains(idx)]
        //             0 <= idx < self.num_keys &&
        //             self.allocator_view().pending_alloc_check(idx, current_valid_indices, tentative_valid_indices) ==> {
        //             &&& {
        //                     &&& current_valid_indices.contains(idx)
        //                     &&& !tentative_valid_indices.contains(idx)
        //                 } <==> self.pending_deallocations_view().contains(idx)
        //             &&& {
        //                     &&& !current_valid_indices.contains(idx)
        //                     &&& tentative_valid_indices.contains(idx)
        //                 } <==> self.pending_allocations_view().contains(idx)
        //             &&& {
        //                     &&& !current_valid_indices.contains(idx)
        //                     &&& !tentative_valid_indices.contains(idx)
        //                } <==> self.free_list().contains(idx)
        //             &&& {
        //                     &&& current_valid_indices.contains(idx)
        //                     &&& tentative_valid_indices.contains(idx)
        //                } ==> !self.pending_deallocations_view().contains(idx) 
        //         }
        //     );
        // }

        pub open spec fn valid(
            self,
            pm_view: PersistentMemoryRegionView,
            overall_metadata: OverallMetadata,
            valid_indices: Set<u64>,
        ) -> bool
        {
            &&& self.inv(pm_view, overall_metadata)
            // &&& forall|idx: u64| idx < overall_metadata.num_keys ==>
            //     #[trigger] self.outstanding_item_table@[idx as int] is None
        }

        // pub open spec fn pending_allocations_view(self) -> Set<u64>
        // {
        //     self.pending_allocations@.to_set()
        // }

        // pub open spec fn pending_deallocations_view(self) -> Set<u64>
        // {
        //     self.pending_deallocations@.to_set()
        // }

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
                        pm.committed(),
                        (index * entry_size as u64) as nat,
                        u64::spec_size_of() as nat,
                    );
                    let item_bytes = extract_bytes(
                        pm.committed(),
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
            let entry_bytes = extract_bytes(pm.committed(), (index * entry_size) as nat, entry_size as nat);
            assert(extract_bytes(entry_bytes, 0, u64::spec_size_of()) =~=
                   extract_bytes(pm.committed(), (index * entry_size as u64) as nat, u64::spec_size_of()));
            assert(extract_bytes(entry_bytes, u64::spec_size_of(), I::spec_size_of()) =~=
                   extract_bytes(pm.committed(),
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
                        // assert(old(self).outstanding_items@[idx] is Created);
                        assert(old(self)@.durable_item_table[idx as int] is None);
                    }
                }
            }
        }

        // Read an item from the item table given an index. Returns `None` if the index
        // does not contain a valid, uncorrupted item. 
        // TODO: should probably return result, not option
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
                        return Err(KvError::InternalError);
                    }
                }
            } else {
                let crc_addr = item_table_index * (entry_size as u64);
                let item_addr = crc_addr + traits_t::size_of::<u64>() as u64;

                // Read the item and CRC at this slot
                let ghost mem = pm_view.committed();
                let ghost entry_bytes = extract_bytes(mem, (item_table_index * entry_size) as nat, entry_size as nat);
                let ghost true_crc_bytes = extract_bytes(mem, crc_addr as nat, u64::spec_size_of());
                let ghost true_item_bytes = extract_bytes(mem, item_addr as nat, I::spec_size_of());

                let ghost true_crc = u64::spec_from_bytes(true_crc_bytes);
                let ghost true_item = I::spec_from_bytes(true_item_bytes);

                let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| crc_addr + subregion.start() + i);
                let ghost item_addrs = Seq::new(I::spec_size_of() as nat, |i: int| item_addr + subregion.start() + i);

                proof {
                    assert(self.durable_valid_indices().contains(item_table_index));
                    self.lemma_establish_bytes_parseable_for_valid_item(pm_view, overall_metadata, item_table_index);
                    assert(extract_bytes(pm_view.committed(), crc_addr as nat, u64::spec_size_of()) =~=
                        Seq::new(u64::spec_size_of() as nat, |i: int| pm_region@.committed()[crc_addrs[i]]));
                    assert(extract_bytes(pm_view.committed(), item_addr as nat, I::spec_size_of()) =~=
                        Seq::new(I::spec_size_of() as nat, |i: int| pm_region@.committed()[item_addrs[i]]));
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
                
                if !check_crc(item.as_slice(), crc.as_slice(), Ghost(pm_region@.committed()),
                            Ghost(pm_region.constants().impervious_to_corruption), Ghost(item_addrs), Ghost(crc_addrs)) {
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
            crash_state2: Seq<u8>,
            overall_metadata: OverallMetadata,
            which_entry: u64,
        )
            requires
                self.inv(v1, overall_metadata),
                !self.durable_valid_indices().contains(which_entry),
                v1.len() == v2.len(),
                v2.can_crash_as(crash_state2),
                which_entry < overall_metadata.num_keys,
                forall|addr: int| {
                    let entry_size = I::spec_size_of() + u64::spec_size_of();
                    let start_addr = which_entry * entry_size;
                    let end_addr = start_addr + entry_size;
                    &&& 0 <= addr < v1.len()
                    &&& !(start_addr <= addr < end_addr)
                } ==> v2.state[addr] == v1.state[addr],
            ensures
                parse_item_table::<I, K>(crash_state2, overall_metadata.num_keys as nat, self.durable_valid_indices()) == Some(self@),
        {
            let entry_size = I::spec_size_of() + u64::spec_size_of();
            let num_keys = overall_metadata.num_keys;
            let start_addr = which_entry * entry_size;
            let end_addr = start_addr + entry_size;
            let can_views_differ_at_addr = |addr: int| start_addr <= addr < end_addr;
            let crash_state1 = lemma_get_crash_state_given_one_for_other_view_differing_only_at_certain_addresses(
                v2, v1, crash_state2, can_views_differ_at_addr
            );
            assert(parse_item_table::<I, K>(crash_state1, num_keys as nat, self.durable_valid_indices()) == Some(self@));
            lemma_valid_entry_index(which_entry as nat, num_keys as nat, entry_size as nat);
            let entry_bytes = extract_bytes(crash_state1, (which_entry * entry_size) as nat, entry_size as nat);
            lemma_subrange_of_subrange_forall(crash_state1);
            assert forall|addr: int| {
                       &&& 0 <= addr < crash_state2.len()
                       &&& crash_state1[addr] != #[trigger] crash_state2[addr]
                   } implies
                   address_belongs_to_invalid_item_table_entry::<I>(addr, num_keys, self.durable_valid_indices())
            by {
                let entry_size = I::spec_size_of() + u64::spec_size_of();
                assert(can_views_differ_at_addr(addr));
                let addrs_entry = addr / entry_size as int;
                lemma_addr_in_entry_divided_by_entry_size(which_entry as nat, entry_size as nat, addr);
            }
            lemma_parse_item_table_doesnt_depend_on_fields_of_invalid_entries::<I, K>(
                crash_state1, crash_state2, num_keys, self.durable_valid_indices()
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
                subregion.view(wrpm_region).committed() == subregion.view(old::<&mut _>(wrpm_region)).committed(),
                match result {
                    Ok(index) => {
                        &&& index < overall_metadata.num_keys
                        &&& old(self).free_list().contains(index)
                        &&& self@.durable_item_table == old(self)@.durable_item_table
                        &&& self.free_list() == old(self).free_list().remove(index)
                        &&& self.durable_valid_indices() == old(self).durable_valid_indices()
                        &&& self.tentative_valid_indices() == old(self).tentative_valid_indices().insert(index)
                        // &&& !self.durable_valid_indices().contains(index)
                        // &&& self.tentative_valid_indices().contains(index)
                        // &&& forall |i: u64| 0 <= i < overall_metadata.num_keys && i != index ==>
                        //         #[trigger] self.outstanding_items[i] == old(self).outstanding_items[i]
                        // &&& ({
                        //     &&& self.outstanding_items[index] matches Some(outstanding_item)
                        //     &&& outstanding_item == OutstandingItem::Created(*item)
                        // })
                        &&& self.outstanding_items@ == old(self).outstanding_items@.insert(index, OutstandingItem::Created(*item))
                        &&& wrpm_region@.committed() == old(wrpm_region)@.committed()
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
            assert(parse_item_table::<I, K>(old_pm_view.committed(), overall_metadata.num_keys as nat,
                self.durable_valid_indices()) == Some(self@)) 
            by {
                lemma_persistent_memory_view_can_crash_as_committed(old_pm_view);
            }
            
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

            subregion.serialize_and_write_relative::<u64, Perm, PM>(wrpm_region, crc_addr, &crc, Tracked(perm));
            assert(wrpm_region@.committed() == old(wrpm_region)@.committed()) by {
                lemma_writing_does_not_change_committed_view(subregion.view(old::<&mut _>(wrpm_region)), crc_addr as int, crc.spec_to_bytes());
                subregion.lemma_if_committed_subview_unchanged_then_committed_view_unchanged(wrpm_region);
            }
            
            let ghost cur_wrpm = *wrpm_region;
            assert(subregion.view(&cur_wrpm).committed() == subregion.initial_subregion_view().committed());

            // write the item itself
            subregion.serialize_and_write_relative::<I, Perm, PM>(wrpm_region, item_addr, item, Tracked(perm));
            assert(wrpm_region@.committed() == cur_wrpm@.committed()) by {
                lemma_writing_does_not_change_committed_view(subregion.view(&cur_wrpm), item_addr as int, item.spec_to_bytes());
                subregion.lemma_if_committed_subview_unchanged_then_committed_view_unchanged(wrpm_region);
            }

            // Add this item to the outstanding item map
            self.outstanding_item_create(free_index, *item, Ghost(overall_metadata));

            let ghost pm_view = subregion.view(wrpm_region);
            assert(pm_view.committed() =~= old_pm_view.committed());

            assert forall|idx: u64| idx < overall_metadata.num_keys && #[trigger] self.outstanding_items[idx] is None implies {
                let start = index_to_offset(idx as nat, entry_size as nat) as int;
                pm_view.no_outstanding_writes_in_range(start, start + entry_size) 
            } by {
                let start = index_to_offset(idx as nat, entry_size as nat) as int;
                lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, entry_size as nat);
                lemma_entries_dont_overlap_unless_same_index(idx as nat, free_index as nat, entry_size as nat);
                assert(old(self).outstanding_item_table_entry_matches_pm_view(subregion.view(old::<&mut _>(wrpm_region)), idx));
                assert(subregion.view(old::<&mut _>(wrpm_region)).no_outstanding_writes_in_range(start, start + entry_size));
            }

            assert forall|idx: u64| self.durable_valid_indices().contains(idx) implies {
                let entry_bytes = extract_bytes(pm_view.committed(), (idx * entry_size) as nat, entry_size as nat);
                &&& idx < overall_metadata.num_keys
                &&& validate_item_table_entry::<I, K>(entry_bytes)
                &&& self@.durable_item_table[idx as int] is Some
                &&& self@.durable_item_table[idx as int] == parse_item_entry::<I, K>(entry_bytes)
            } by {
                let entry_bytes = extract_bytes(pm_view.committed(), (idx * entry_size) as nat, entry_size as nat);
                lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, entry_size as nat);
                lemma_entries_dont_overlap_unless_same_index(idx as nat, free_index as nat, entry_size as nat);
                assert(entry_bytes =~= extract_bytes(subregion.view(old::<&mut _>(wrpm_region)).committed(),
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

            assert forall |s| #[trigger] pm_view.can_crash_as(s) implies {
                parse_item_table::<I, K>(s, overall_metadata.num_keys as nat, self.durable_valid_indices()) == Some(self@)
            } by {
                old(self).lemma_changing_unused_entry_doesnt_affect_parse_item_table(
                    old_pm_view, pm_view, s, overall_metadata, free_index
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

            Ok(free_index)
        }

        // pub open spec fn recover<L>(
        //     mem: Seq<u8>,
        //     // op_log: Seq<OpLogEntryType<L>>,
        //     valid_indices: Set<int>,
        //     num_keys: u64,
        // ) -> Option<DurableItemTableView<I>>
        //     where 
        //         L: PmCopy,
        // {
        //     if mem.len() < ABSOLUTE_POS_OF_TABLE_AREA {
        //         // If the memory is not large enough to store the metadata header,
        //         // it is not valid
        //         None
        //     }
        //     else {
        //         // replay the log on `mem`, then parse it into (hopefully) a valid item table view
        //         // TODO: may not need to do any replay here?
        //         // let mem = Self::spec_replay_log_item_table(mem, op_log);
        //         parse_item_table::<I, K>(mem, num_keys as nat, valid_indices)
        //     }

        // }

        // // Recursively apply log operations to the item table bytes. Skips all log entries that 
        // // do not modify the item table.
        // // TODO: check length of `mem`?
        // pub open spec fn spec_replay_log_item_table<L>(mem: Seq<u8>, op_log: Seq<LogicalOpLogEntry<L>>) -> Seq<u8>
        //     where 
        //         L: PmCopy,
        //     decreases op_log.len(),
        // {
        //     if op_log.len() == 0 {
        //         mem
        //     } else {
        //         let current_op = op_log[0];
        //         let op_log = op_log.drop_first();
        //         let mem = Self::apply_log_op_to_item_table_mem(mem, current_op);
        //         Self::spec_replay_log_item_table(mem, op_log)
        //     }
        // }

        // // TODO: refactor -- logic in both cases is the same
        // pub open spec fn apply_log_op_to_item_table_mem<L>(mem: Seq<u8>, op: OpLogEntryType<L>) -> Seq<u8>
        //     where 
        //         L: PmCopy,
        // {
        //     mem
        //     // let item_entry_size = I::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of();
        //     // match op {
        //     //     OpLogEntryType::ItemTableEntryCommit { item_index } => {
        //     //         let entry_offset = ABSOLUTE_POS_OF_TABLE_AREA + item_index * item_entry_size;
        //     //         let addr = entry_offset + RELATIVE_POS_OF_VALID_CDB;
        //     //         let valid_cdb = spec_u64_to_le_bytes(CDB_TRUE);
        //     //         let mem = mem.map(|pos: int, pre_byte: u8| 
        //     //                                             if addr <= pos < addr + valid_cdb.len() { valid_cdb[pos - addr]}
        //     //                                             else { pre_byte }
        //     //                                         );
        //     //         mem
        //     //     }
        //     //     OpLogEntryType::ItemTableEntryInvalidate { item_index } => {
        //     //         let entry_offset = ABSOLUTE_POS_OF_TABLE_AREA + item_index * item_entry_size;
        //     //         let addr = entry_offset + RELATIVE_POS_OF_VALID_CDB;
        //     //         let invalid_cdb = spec_u64_to_le_bytes(CDB_FALSE);
        //     //         let mem = mem.map(|pos: int, pre_byte: u8| 
        //     //                                             if addr <= pos < addr + invalid_cdb.len() { invalid_cdb[pos - addr]}
        //     //                                             else { pre_byte }
        //     //                                         );
        //     //         mem
        //     //     }
        //     //     _ => mem
        //     // }
        // }

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
                    let mem = subregion.view(pm_region).committed();
                    let item_entry_size = I::spec_size_of() + u64::spec_size_of();
                    num_keys * item_entry_size <= mem.len()
                }),
            ensures
                ({
                    let mem = subregion.view(pm_region).committed();
                    &&& parse_item_table::<I, K>(mem, num_keys as nat, valid_indices) matches Some(item_table_view)
                    &&& item_table_view == DurableItemTableView::<I>::init(num_keys as int)
                })
        {
            let mem = subregion.view(pm_region).committed();
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
                pm_region@.no_outstanding_writes(),
                overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr, overall_metadata.kvstore_id),
                subregion.len() == overall_metadata.item_table_size,
                subregion.view(pm_region).no_outstanding_writes(),
                ({
                    let valid_indices_view = Seq::new(key_index_info@.len(), |i: int| key_index_info[i].2);
                    let table = parse_item_table::<I, K>(subregion.view(pm_region).committed(), overall_metadata.num_keys as nat, valid_indices_view.to_set());
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
                        let table = parse_item_table::<I, K>(subregion.view(pm_region).committed(), overall_metadata.num_keys as nat, valid_indices_view.to_set()).unwrap();
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
            let ghost table = parse_item_table::<I, K>(pm_view.committed(), overall_metadata.num_keys as nat, valid_indices_view.to_set());

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
                    assert(validate_item_table_entry::<I, K>(extract_bytes(pm_view.committed(),
                        index_to_offset(idx as nat, entry_size as nat), entry_size as nat)));
                }

                assert forall|idx: u64| idx < num_keys &&
                           #[trigger] item_table.outstanding_items[idx] is None implies
                    pm_view.no_outstanding_writes_in_range(idx * entry_size, idx * entry_size + entry_size) by {
                        lemma_valid_entry_index(idx as nat, overall_metadata.num_keys as nat, entry_size as nat);
                }
            }

            proof {
                // Prove that the item table region only has one crash state, which recovers to the initial table's state
                let pm_view = subregion.view(pm_region);
                lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(pm_view);
                assert(forall |s| pm_view.can_crash_as(s) ==> s == pm_view.committed());
                assert(in_use_indices == item_table.durable_valid_indices());
                assert(forall |s| #[trigger] pm_view.can_crash_as(s) ==> 
                    parse_item_table::<I, K>(s, overall_metadata.num_keys as nat, in_use_indices) == Some(item_table@));

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
                pm.no_outstanding_writes(),
                old(self).opaquable_inv(overall_metadata, old(self).tentative_valid_indices()),
                ({
                    let entry_size = I::spec_size_of() + u64::spec_size_of();
                    &&& pm.len() >= overall_metadata.item_table_size >= overall_metadata.num_keys * entry_size
                }),
                forall |s| #[trigger] pm.can_crash_as(s) ==> {
                    &&& parse_item_table::<I, K>(s, overall_metadata.num_keys as nat, old(self).durable_valid_indices())
                            matches Some(table_view)
                    &&& table_view.durable_item_table == old(self)@.durable_item_table
                },
                forall|idx: u64| old(self).durable_valid_indices().contains(idx) ==> {
                    let entry_size = I::spec_size_of() + u64::spec_size_of();
                    let entry_bytes = extract_bytes(pm.committed(), (idx * entry_size) as nat, entry_size as nat);
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
                assert(pm.no_outstanding_writes_in_range(start, start + entry_size));
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
            // Ghost(old_valid_indices): Ghost<Set<u64>>,
            // Ghost(valid_indices): Ghost<Set<u64>>,
        )
            requires 
                // old(self).opaquable_inv(overall_metadata, old_valid_indices),
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
                pm.no_outstanding_writes(),
                old(self).opaquable_inv(overall_metadata, old(self).durable_valid_indices()),
                ({
                    let subregion_view = get_subregion_view(pm, overall_metadata.item_table_addr as nat,
                        overall_metadata.item_table_size as nat);
                    let entry_size = I::spec_size_of() + u64::spec_size_of();
                    &&& parse_item_table::<I, K>(subregion_view.committed(), overall_metadata.num_keys as nat, old(self).tentative_valid_indices()) == 
                            Some(old(self).tentative_view())
                    &&& subregion_view.len() >= overall_metadata.item_table_size >= overall_metadata.num_keys * entry_size
                }),
                pm.len() >= overall_metadata.item_table_addr + overall_metadata.item_table_size,
                old_self@.len() == old(self)@.len() == old(self).num_keys == overall_metadata.num_keys,
                // forall |idx: u64| valid_indices.contains(idx) ==> idx < old(self).num_keys,
                // forall |idx: u64| old_valid_indices.contains(idx) ==> idx < old(self).num_keys,
                // old_self.pending_alloc_inv(old_valid_indices, valid_indices),

                // old_self.pending_allocations_view().disjoint(old_self.pending_deallocations_view()),
                // old_self.free_list().disjoint(old_self.pending_deallocations_view()),
                old_self.free_list() == old(self).free_list(),
                // old_self.pending_allocations_view() == old(self).pending_allocations_view(),
                // old_self.pending_deallocations_view() == old(self).pending_deallocations_view(),
                old_self.num_keys == old(self).num_keys,
                old_self@.durable_item_table.len() == old(self)@.durable_item_table.len(),

                // we have already committed the log when we finalize the item table,
                


                // forall |idx: u64| #[trigger] valid_indices.contains(idx) ==> old(self).outstanding_item_table@[idx as int] is None,
            ensures 
                ({
                    let subregion_view = get_subregion_view(pm, overall_metadata.item_table_addr as nat,
                        overall_metadata.item_table_size as nat);
                    let entry_size = I::spec_size_of() + u64::spec_size_of();
                    // &&& self.inv(subregion_view, overall_metadata, valid_indices)
                    &&& self.inv(subregion_view, overall_metadata)
                    &&& Some(self@) == parse_item_table::<I, K>(subregion_view.committed(), overall_metadata.num_keys as nat, old(self).tentative_valid_indices())
                    // &&& forall|idx: u64| idx < overall_metadata.num_keys && #[trigger] self.outstanding_item_table@[idx as int] is None ==>
                    //         subregion_view.no_outstanding_writes_in_range(idx * entry_size, idx * entry_size + entry_size)
                }),
                // self.pending_alloc_inv(valid_indices, valid_indices),
                // self.pending_allocations_view().is_empty(),
                // self.pending_deallocations_view().is_empty(),
                // forall|idx: u64| idx < overall_metadata.num_keys ==>
                //     #[trigger] self.outstanding_item_table@[idx as int] is None,
                self@.len() == old(self)@.len(),
                self.num_keys == old(self).num_keys,
                self.outstanding_items@.len() == 0,
                // self.outstanding_item_table@ == Seq::new(old(self).outstanding_item_table@.len(), |i: int| None::<I>),
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
            self.state = Ghost(parse_item_table::<I, K>(subregion_view.committed(), 
                overall_metadata.num_keys as nat, self.tentative_valid_indices()).unwrap());

            assert(self.durable_valid_indices() == self.tentative_valid_indices());
            assert(self.durable_valid_indices() == old(self).tentative_valid_indices());

            self.finalize_outstanding_items(Ghost(subregion_view), Ghost(overall_metadata));
            
            proof {
                assert(parse_item_table::<I, K>(subregion_view.committed(), overall_metadata.num_keys as nat, self.durable_valid_indices()) == Some(self@));
                lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(subregion_view);
                
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


        /* temporarily commented out for subregion development 

        pub exec fn play_item_log<PM, L>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedItemTablePermission, PM>,
            table_id: u128,
            log_entries: &Vec<OpLogEntryType<L>>,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
            Ghost(state): Ghost<DurableItemTableView<I>>
        ) -> (result: Result<(), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
                L: PmCopy,
            requires 
                // TODO
            ensures 
                // TODO 
        {
            Self::replay_log_item_table(wrpm_region, table_id, log_entries, self.item_slot_size, Tracked(perm), Ghost(state))?;
            // replay_log_item_table cannot add newly-invalidated metadata entries back into the allocator,
            // because it doesn't (and can't) take &mut self, so as a quick fix we'll just iterate over the log again.
            // TODO: refactor so this happens in the same pass as is used in replay_log_item_table

            for i in 0..log_entries.len() 
            {
                assume(false);
                let log_entry = &log_entries[i];

                if let OpLogEntryType::ItemTableEntryInvalidate { item_index } = log_entry {
                    self.free_list.push(*item_index);
                }
            }

            Ok(())
        }

        exec fn replay_log_item_table<PM, L>(
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedItemTablePermission, PM>,
            table_id: u128,
            log_entries: &Vec<OpLogEntryType<L>>,
            item_slot_size: u64,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
            Ghost(state): Ghost<DurableItemTableView<I>>
        ) -> (result: Result<(), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
                L: PmCopy,
            requires 
                // TODO
            ensures 
                // TODO 
        {
            // There are only two types of operation that need to be replayed onto the item table:
            // item commit and item invalidation. So we just need to determine the item index updated
            // by each log entry and what we need to set the CDB to.
            for i in 0..log_entries.len() 
                invariant 
                    // TODO
            {
                assume(false);
                let log_entry = &log_entries[i];

                let result = match log_entry {
                    OpLogEntryType::ItemTableEntryCommit { item_index } => Some((CDB_TRUE, item_index)),
                    OpLogEntryType::ItemTableEntryInvalidate { item_index } => Some((CDB_FALSE, item_index)),
                    _ => None  // the other operations do not modify the item table
                };

                if let Some((cdb_val, item_index)) = result {
                    // the slot offset is also the address of the CDB
                    let item_slot_offset = ABSOLUTE_POS_OF_TABLE_AREA + item_index * item_slot_size;
                    wrpm_region.serialize_and_write(item_slot_offset, &cdb_val, Tracked(perm));
                }
            }
            Ok(())
        }

        // this function can be used to both create new items and do COW updates to existing items.
        // must always write to an invalid slot
        // this operation is NOT directly logged
        // returns the index of the slot that the item was written to
        pub exec fn tentatively_write_item<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedItemTablePermission, PM>,
            Ghost(item_table_id): Ghost<u128>,
            item: &I,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
        ) -> (result: Result<u64, KvError<K>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(wrpm_region).inv(),
                forall |i: int|  0 <= i < old(self).free_list().len() ==>
                    0 <= #[trigger] old(self).free_list()[i] < old(self).num_keys,
                ({
                    let item_slot_size = old(self).spec_item_size() + u64::spec_size_of() + u64::spec_size_of();
                    let metadata_header_size = ItemTableMetadata::spec_size_of() + u64::spec_size_of();
                    &&& 0 <= item_slot_size < usize::MAX
                    &&& 0 <= item_slot_size * old(self).num_keys < usize::MAX
                    &&& 0 <= metadata_header_size + (item_slot_size * old(self).num_keys) < usize::MAX
                })
                // TODO
            ensures
                wrpm_region.inv()
                // TODO
        {
            // pop a free index from the free list
            assume(false);
            let free_index = match self.free_list.pop() {
                Some(index) => index,
                None => return Err(KvError::OutOfSpace)
            };
            assert(free_index < self.num_keys);
            let item_slot_size = (self.item_size as usize + traits_t::size_of::<u64>() + traits_t::size_of::<u64>()) as u64;
            let item_slot_offset = ABSOLUTE_POS_OF_TABLE_AREA + free_index * item_slot_size;
            let crc_addr = item_slot_offset + traits_t::size_of::<u64>() as u64;
            let item_addr = crc_addr + traits_t::size_of::<u64>() as u64;

            // calculate and write the CRC of the provided item
            let crc = calculate_crc(item);
            wrpm_region.serialize_and_write(crc_addr, &crc, Tracked(perm));
            // write the item itself
            wrpm_region.serialize_and_write(item_addr, item, Tracked(perm));

            Ok(free_index)
        }

        // makes a slot valid by setting its valid bit.
        // must log the operation before calling this function
        pub exec fn commit_item<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedItemTablePermission, PM>,
            item_table_id: u128,
            item_table_index: u64,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
        ) -> (result: Result<(), KvError<K>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(wrpm_region).inv(),
                ({
                    let item_slot_size = old(self).spec_item_size() + u64::spec_size_of() + u64::spec_size_of();
                    let metadata_header_size = ItemTableMetadata::spec_size_of() + u64::spec_size_of();
                    &&& 0 <= item_slot_size < usize::MAX
                    &&& 0 <= item_slot_size * old(self).num_keys < usize::MAX
                    &&& 0 <= metadata_header_size + (item_slot_size * old(self).num_keys) < usize::MAX
                })
                // TODO: item update must have been logged
            ensures
                wrpm_region.inv(),
                // TODO
        {
            assume(false);
            let item_slot_size = (self.item_size as usize + traits_t::size_of::<u64>() + traits_t::size_of::<u64>()) as u64;
            let item_slot_offset = ABSOLUTE_POS_OF_TABLE_AREA + item_table_index * item_slot_size;
            wrpm_region.serialize_and_write(item_slot_offset + RELATIVE_POS_OF_VALID_CDB, &CDB_TRUE, Tracked(perm));
            Ok(())
        }

        pub fn write_setup_metadata<PM>(pm_region: &mut PM, num_keys: u64)
        where
            PM: PersistentMemoryRegion,
        requires
            old(pm_region).inv(),
            old(pm_region)@.len() == 1,
            old(pm_region)@.no_outstanding_writes(),
            ({
                let item_size = I::spec_size_of() + u64::spec_size_of() + u64::spec_size_of();
                let metadata_header_size = ItemTableMetadata::spec_size_of() + u64::spec_size_of();
                old(pm_region)@.len() >= metadata_header_size + (item_size * num_keys)
            })
            // TODO: precondition that the region is large enough
        ensures
            pm_region.inv(),
            // TODO: postcondition that the table is set up correctly
    {
        // Initialize metadata header and compute its CRC
        let metadata_header = ItemTableMetadata {
            version_number: ITEM_TABLE_VERSION_NUMBER,
            item_size: I::size_of() as u64,
            num_keys,
            _padding: 0,
            program_guid: ITEM_TABLE_PROGRAM_GUID,
        };
        let metadata_crc = calculate_crc(&metadata_header);

        let metadata_header_addr = ABSOLUTE_POS_OF_METADATA_HEADER;
        let crc_addr = metadata_header_addr + traits_t::size_of::<ItemTableMetadata>() as u64;

        pm_region.serialize_and_write(metadata_header_addr, &metadata_header);
        pm_region.serialize_and_write(crc_addr, &metadata_crc);
    }

    pub fn read_table_metadata<PM>(pm_region: &PM, table_id: u128) -> (result: Result<Box<ItemTableMetadata>, KvError<K>>)
        where
            PM: PersistentMemoryRegion,
        requires
            pm_region.inv()
            // TODO: finish writing preconditions
        ensures
            match result {
                Ok(output_table) => {
                    let item_slot_size = I::spec_size_of() + u64::spec_size_of() + u64::spec_size_of();
                    let metadata_header_size = ItemTableMetadata::spec_size_of() + u64::spec_size_of();
                    let num_keys = output_table.num_keys;
                    &&& 0 <= item_slot_size < usize::MAX
                    &&& 0 <= item_slot_size * num_keys < usize::MAX
                    &&& 0 <= metadata_header_size + (item_slot_size * num_keys) < usize::MAX
                    &&& output_table.item_size == I::spec_size_of()

                }
                Err(_) => true
            }
            // TODO: finish writing postconditions
        {
            assume(false);

            let ghost mem = pm_region@.committed();

            // read in the metadata structure and its CRC, make sure it has not been corrupted

            let ghost true_main_table = ItemTableMetadata::spec_from_bytes(mem.subrange(ABSOLUTE_POS_OF_METADATA_HEADER as int, ABSOLUTE_POS_OF_METADATA_HEADER + ItemTableMetadata::spec_size_of()));
            let ghost true_crc = u64::spec_from_bytes(mem.subrange(ABSOLUTE_POS_OF_HEADER_CRC as int, ABSOLUTE_POS_OF_HEADER_CRC + u64::spec_size_of()));

            let metadata_header_addr = ABSOLUTE_POS_OF_METADATA_HEADER;
            let crc_addr = metadata_header_addr + traits_t::size_of::<ItemTableMetadata>() as u64;

            let table_metadata = pm_region.read_aligned::<ItemTableMetadata>(metadata_header_addr).map_err(|e| KvError::PmemErr { pmem_err: e })?;
            let table_crc = pm_region.read_aligned::<u64>(crc_addr).map_err(|e| KvError::PmemErr { pmem_err: e })?;

            let ghost header_addrs = Seq::new(ItemTableMetadata::spec_size_of() as nat, |i: int| ABSOLUTE_POS_OF_METADATA_HEADER + i);
            let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| ABSOLUTE_POS_OF_HEADER_CRC + i);

            let ghost true_header_bytes = Seq::new(ItemTableMetadata::spec_size_of() as nat, |i: int| mem[header_addrs[i]]);
            let ghost true_crc_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem[crc_addrs[i]]);

            if !check_crc(table_metadata.as_slice(), table_crc.as_slice(), Ghost(mem),
                    Ghost(pm_region.constants().impervious_to_corruption),
                    Ghost(header_addrs), 
                    Ghost(crc_addrs)) {
                return Err(KvError::CRCMismatch);
            }

            let table_metadata = table_metadata.extract_init_val(
                Ghost(true_main_table),
                Ghost(true_header_bytes),
                Ghost(pm_region.constants().impervious_to_corruption),
            );

            // Since we've already checked for corruption, this condition should never fail
            if {
                ||| table_metadata.program_guid != ITEM_TABLE_PROGRAM_GUID
                ||| table_metadata.version_number != ITEM_TABLE_VERSION_NUMBER
                ||| table_metadata.item_size != I::size_of() as u64
            } {
                return Err(KvError::InvalidItemTableHeader);
            }

            return Ok(table_metadata);
        }
        */
    }
}
