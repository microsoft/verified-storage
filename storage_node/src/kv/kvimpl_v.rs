//! This file contains the verified implementation of the KV store. The methods
//! defined here are meant to be called by methods in kvimpl_t.rs with `Perm`
//! arguments that have been audited along with the rest of that file.
//!
//! The UntrustedKvStoreImpl is split into two key components: a volatile index
//! and a durable store. Each of these may be further split into separate components,
//! but having a high-level split between volatile and durable should make the
//! distinction between updates that require crash-consistency proofs, and updates
//! that don't, clear. The view of an UntrustedKvStoreImpl is obtained using the contents
//! of its current volatile and durable components.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::seq::*;

use super::durable::durableimpl_v::*;
use super::durable::listlayout_v::*;
use super::durable::inv_v::*;
use super::durable::itemtablelayout_v::*;
use super::durable::maintablelayout_v::*;
use super::inv_v::*;
use super::kvspec_t::*;
use super::volatile::volatileimpl_v::*;
use super::volatile::volatilespec_v::*;
use crate::kv::kvimpl_t::*;
use crate::kv::layout_v::*;
use crate::kv::setup_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use crate::log2::logimpl_v::*;
use crate::util_v::*;

use std::hash::Hash;

verus! {

#[verifier::reject_recursive_types(K)]
pub struct UntrustedKvStoreImpl<Perm, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PM: PersistentMemoryRegion,
    K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
    I: PmCopy + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug + Copy,
    // V: VolatileKvIndex<K>,
{
    id: u128,
    durable_store: DurableKvStore<Perm, PM, K, I, L>,
    volatile_index: VolatileKvIndexImpl::<K>,
}

impl<Perm, PM, K, I, L> UntrustedKvStoreImpl<Perm, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PM: PersistentMemoryRegion,
    K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug + Copy,
    // V: VolatileKvIndex<K>,
{
    pub open spec fn recover(mem: Seq<u8>, kv_id: u128) -> Option<AbstractKvStoreState<K, I, L>>
    {
        AbstractKvStoreState::<K, I, L>::recover::<Perm, PM>(mem, kv_id)
    }

    pub closed spec fn constants(self) -> PersistentMemoryConstants
    {
        self.durable_store.constants()
    }

    pub closed spec fn view(&self) -> AbstractKvStoreState<K, I, L>
    {
        AbstractKvStoreState {
            id: self.id,
            // obtaining the view only from durable state (rather than using both durable and volatile) makes recovery states
            // easier to reason about.
            contents: AbstractKvStoreState::<K, I, L>::construct_view_from_durable_state(self.durable_store@),
        }
    }

    pub closed spec fn wrpm_view(self) -> PersistentMemoryRegionView
    {
        self.durable_store.wrpm_view()
    }

    pub closed spec fn valid(self) -> bool
    {
        &&& self.durable_store_matches_volatile_index()
        // &&& self.durable_store@.matches_volatile_index(self.volatile_index@)
        &&& self.durable_store.valid()
        &&& self.volatile_index.valid()
    }

    pub closed spec fn durable_store_matches_volatile_index(self) -> bool 
    {
        // all keys in the volatile index are stored at the indexed offset in the durable store
        &&& forall |k: K| #[trigger] self.volatile_index@.contains_key(k) ==> {
                let indexed_offset = self.volatile_index@[k].unwrap().header_addr;
                &&& self.durable_store@.contains_key(indexed_offset as int)
                &&& self.durable_store@[indexed_offset as int].unwrap().key == k
            }
        // all offsets in the durable store have a corresponding entry in the volatile index
        &&& forall |i: int| #[trigger] self.durable_store@.contains_key(i) ==> {
            &&& self.volatile_index@.contains_key(self.durable_store@[i].unwrap().key)
            &&& self.volatile_index@[self.durable_store@[i].unwrap().key].unwrap().header_addr == i
        }
    }

    pub exec fn untrusted_setup(
        pm_region: &mut PM,
        kvstore_id: u128,
        num_keys: u64, 
        num_list_entries_per_node: u32,
        num_list_nodes: u64,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(pm_region).inv(),
        ensures
            pm_region.inv(),
            match result {
                Ok(()) => {
                    &&& pm_region@.no_outstanding_writes()
                    &&& Self::recover(pm_region@.committed(), kvstore_id) matches Some(recovered_view)
                    &&& recovered_view == AbstractKvStoreState::<K, I, L>::init(kvstore_id)
                }
                Err(_) => true
            }
    {
        // 1. flush the pm to ensure there are no outstanding writes
        pm_region.flush();

        // 2. Write the version and overall metadata to PM
        let (version_metadata, overall_metadata) = setup::<PM, K, I, L>(pm_region, kvstore_id, num_keys, 
            num_list_entries_per_node, num_list_nodes)?;

        // 3. Set up the other durable regions
        DurableKvStore::<Perm, PM, K, I, L>::setup(pm_region, version_metadata, overall_metadata, overall_metadata.kvstore_id)?;
        
        // 4. Prove that the resulting recovery view is an empty store
        proof {
            Self::lemma_recovery_view_is_init_if_durable_recovery_view_is_init(pm_region@.committed(), version_metadata, overall_metadata);
        }
        
        Ok(())
    }

    proof fn lemma_recovery_view_is_init_if_durable_recovery_view_is_init(
        mem: Seq<u8>, 
        version_metadata: VersionMetadata,
        overall_metadata: OverallMetadata,
    )
        requires
            memory_correctly_set_up_on_region::<K, I, L>(mem, overall_metadata.kvstore_id),
            DurableKvStore::<Perm, PM, K, I, L>::physical_recover(mem, version_metadata, overall_metadata) == Some(DurableKvStoreView::<K, I, L>::init()),
            ({
                let read_version_metadata = deserialize_version_metadata(mem);
                let read_version_crc = deserialize_version_crc(mem);
                let read_overall_metadata = deserialize_overall_metadata(mem, version_metadata.overall_metadata_addr);
                let read_overall_crc = deserialize_overall_crc(mem, version_metadata.overall_metadata_addr);
                &&& read_version_metadata == version_metadata 
                &&& read_overall_metadata == overall_metadata
            }),
        ensures 
            Self::recover(mem, overall_metadata.kvstore_id) == Some(AbstractKvStoreState::<K, I, L>::init(overall_metadata.kvstore_id))
    {
        let read_version_metadata = deserialize_version_metadata(mem);
        let read_version_crc = deserialize_version_crc(mem);
        let read_overall_metadata = deserialize_overall_metadata(mem, version_metadata.overall_metadata_addr);
        let read_overall_crc = deserialize_overall_crc(mem, version_metadata.overall_metadata_addr);
        assert({
            &&& read_version_crc == version_metadata.spec_crc()
            &&& read_overall_crc == overall_metadata.spec_crc()
            &&& version_metadata_valid(read_version_metadata)
            &&& overall_metadata_valid::<K, I, L>(read_overall_metadata, read_version_metadata.overall_metadata_addr, read_overall_metadata.kvstore_id)
            &&& mem.len() >= VersionMetadata::spec_size_of() + u64::spec_size_of()
        });
        let recovered_durable_store = DurableKvStore::<Perm, PM, K, I, L>::physical_recover(mem, version_metadata, overall_metadata).unwrap();
        assert(recovered_durable_store.contents == Map::<int, DurableKvStoreViewEntry<K, I, L>>::empty());
        let recovered_view = AbstractKvStoreState::construct_view_from_durable_state(recovered_durable_store);
        assert(recovered_view == Map::<K, (I, Seq<L>)>::empty());
    }

    pub fn untrusted_start(
        mut wrpm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        kvstore_id: u128,
        Ghost(state): Ghost<AbstractKvStoreState<K, I, L>>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<Self, KvError<K>>)
        requires 
            wrpm_region.inv(),
            wrpm_region@.no_outstanding_writes(),
            Self::recover(wrpm_region@.committed(), kvstore_id) == Some(state),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::recover(s, kvstore_id) == Some(state),
            K::spec_size_of() > 0,
            I::spec_size_of() + u64::spec_size_of() <= u64::MAX,
            vstd::std_specs::hash::obeys_key_model::<K>(),
        ensures 
            match result {
                Ok(kv) => {
                    &&& kv.valid()
                    &&& kv.wrpm_view().no_outstanding_writes()
                    &&& Some(kv@) == Self::recover(kv.wrpm_view().committed(), kvstore_id)
                }
                Err(KvError::CRCMismatch) => !wrpm_region.constants().impervious_to_corruption,
                // TODO: proper handling of other error types
                Err(KvError::LogErr { log_err }) => true,
                Err(KvError::InternalError) => true, 
                Err(KvError::IndexOutOfRange) => true,
                Err(KvError::PmemErr{ pmem_err }) => true,
                Err(_) => false 
            }
    {        
        // 1. Read the version and overall metadata from PM.
        let pm = wrpm_region.get_pm_region_ref();
        let version_metadata = read_version_metadata::<PM, K, I, L>(pm, kvstore_id)?;
        let overall_metadata = read_overall_metadata::<PM, K, I, L>(pm, &version_metadata, kvstore_id)?;

        // 2. Call the durable KV store's start method
        let ghost durable_kvstore_state = DurableKvStore::<Perm, PM, K, I, L>::physical_recover(
            wrpm_region@.committed(), version_metadata, overall_metadata).unwrap();
        assert(state.contents == AbstractKvStoreState::<K, I, L>::construct_view_from_durable_state(durable_kvstore_state));

        proof {
            assert(DurableKvStore::<Perm, PM, K, I, L>::physical_recover(
                wrpm_region@.committed(), version_metadata, overall_metadata) is Some);
            assert(overall_metadata_valid::<K, I, L>(deserialize_overall_metadata(wrpm_region@.committed(), version_metadata.overall_metadata_addr), version_metadata.overall_metadata_addr, kvstore_id));
            assert forall |s| {
                &&& version_and_overall_metadata_match_deserialized(s, wrpm_region@.committed())
                &&& Some(durable_kvstore_state) == #[trigger] DurableKvStore::<Perm, PM, K, I, L>::physical_recover(s, version_metadata, overall_metadata)
            } implies Self::recover(s, kvstore_id) == Some(state) by {
                broadcast use pmcopy_axioms;
            }
            let base_log_state = UntrustedLogImpl::recover(wrpm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
            assert(base_log_state.log.len() == 0 || base_log_state.log.len() > u64::spec_size_of());

            if base_log_state.log.len() > u64::spec_size_of() {
                DurableKvStore::<Perm, PM, K, I, L>::lemma_log_size_does_not_overflow_u64(wrpm_region@, version_metadata, overall_metadata);
            } else {
                assert(base_log_state.log.len() == 0);
            }
        }
    
        let (kvstore, entry_list) = DurableKvStore::<Perm, PM, K, I, L>::start(wrpm_region, overall_metadata, 
            version_metadata, Tracked(perm), Ghost(durable_kvstore_state))?;

        let ghost entry_list_view = Seq::new(entry_list@.len(), |i: int| (*entry_list[i].0, entry_list[i].1, entry_list[i].2));
        assert(forall |i: int| 0 <= i < entry_list@.len() ==>
            #[trigger] entry_list_view[i] == (*entry_list@[i].0, entry_list@[i].1, entry_list@[i].2));
        assert(entry_list_view.to_set() == kvstore.key_index_list_view());

        assert forall |i: int| 0 <= i < entry_list_view.len() implies
            kvstore@.contains_key((#[trigger] entry_list_view[i].1) as int)
        by {
            assert(kvstore.key_index_list_view().contains(entry_list_view[i]));
        }

        // 3. Set up the volatile index based on the contents of the KV store
        // entry list contains keys, main table indexes, and item table indexes. We don't use the item indexes
        // when setting up the volatile side of things, but we use the list that contains them as it would be 
        // less efficient to create a copy of the list without the item indexes.
        let mut volatile_index = VolatileKvIndexImpl::<K>::new(kvstore_id, overall_metadata.num_keys as usize, 
            overall_metadata.num_list_entries_per_node as u64)?;

        let ghost old_kvstore = kvstore;
        let mut i = 0;
        while i < entry_list.len() 
            invariant 
                volatile_index.valid(),
                forall |k: int, l: int| {
                    &&& 0 <= k < entry_list.len()
                    &&& 0 <= l < entry_list.len()
                    &&& k != l
                } ==> *(#[trigger] entry_list[k]).0 != *(#[trigger] entry_list[l]).0,
                forall |index: int| i <= index < entry_list.len() ==> 
                    volatile_index@[*(#[trigger] entry_list@[index]).0] is None,
                forall |index: int| 0 <= index < i ==> {
                    &&& volatile_index@[*(#[trigger] entry_list@[index]).0] matches Some(volatile_entry)
                    &&& volatile_entry.header_addr == entry_list@[index].1
                    &&& kvstore@.contains_key(volatile_entry.header_addr as int)
                },
                forall |k| volatile_index@.contains_key(k) ==> {
                    &&& volatile_index@[k] matches Some(volatile_entry)
                    &&& exists |v| {
                        &&& #[trigger] entry_list_view.contains(v)
                        &&& v.0 == k
                        &&& v.1 == volatile_entry.header_addr
                    }
                },
                forall |j: int| 0 <= j < entry_list@.len() ==>
                    #[trigger] entry_list_view[j] == (*entry_list@[j].0, entry_list@[j].1, entry_list@[j].2),
                forall |j: int| 0 <= j < entry_list_view.len() ==>
                    kvstore@.contains_key((#[trigger] entry_list_view[j].1) as int),
                kvstore == old_kvstore,
                0 <= i <= entry_list_view.len(),
                entry_list_view.len() == entry_list@.len() == entry_list.len(),
        {
            if i < entry_list.len() {
                assert(kvstore@.contains_key(entry_list_view[i as int].1 as int));
            }
            let ghost old_volatile_index = volatile_index;
            let (key, index) = (*entry_list[i].0, entry_list[i].1);
            volatile_index.insert_key(&key, index)?;

            proof {
                assert forall |k| volatile_index@.contains_key(k) implies {
                    &&& volatile_index@[k] matches Some(volatile_entry)
                    &&& exists |v| {
                        &&& #[trigger] entry_list_view.contains(v)
                        &&& v.0 == k
                        &&& v.1 == volatile_entry.header_addr
                    }
                } by {
                    let volatile_entry = volatile_index@[k].unwrap();
                    if k == key {
                        let v = entry_list_view[i as int];
                        assert({
                            &&& #[trigger] entry_list_view.contains(v)
                            &&& v.0 == k
                            &&& v.1 == volatile_entry.header_addr
                        });
                    } else {
                        assert(old_volatile_index@.contains_key(k));
                    }
                }
            }

            i += 1;
        }

        let kvstore = Self {
            id: kvstore_id,
            durable_store: kvstore,
            volatile_index,
        };

        // 4. Prove postconditions
        proof {
            assert(kvstore.durable_store.key_index_list_view() == entry_list_view.to_set());

            // Each key in the volatile index maps to a main table entry containing that same key
            assert forall |k: K| #[trigger] kvstore.volatile_index@.contains_key(k) implies {
                let indexed_offset = (#[trigger] kvstore.volatile_index@[k]).unwrap().header_addr;
                &&& kvstore.durable_store@.contains_key(indexed_offset as int)
                &&& kvstore.durable_store@[indexed_offset as int].unwrap().key == k
            } by {
                let index = kvstore.volatile_index@[k].unwrap().header_addr;
                assert(exists |v| {
                    &&& #[trigger] entry_list_view.contains(v) 
                    &&& v.0 == k 
                    &&& v.1 == index
                });
                let witness = choose |v| {
                    &&& #[trigger] entry_list_view.contains(v) 
                    &&& v.0 == k 
                    &&& v.1 == index
                };
                assert(kvstore.durable_store.key_index_list_view().contains(witness));
            }

            assert(forall |i: int| 0 <= i < entry_list_view.len() ==> {
                let k = #[trigger] entry_list_view[i].0;
                let index = #[trigger] entry_list_view[i].1;
                &&& kvstore.volatile_index@.contains_key(k)
                &&& kvstore.durable_store@.contains_key(index as int)
            });
            // each key in the durable table corresponds to an entry in the volatile index
            assert forall |i: int| #[trigger] kvstore.durable_store@.contains_key(i) implies {
                &&& kvstore.volatile_index@.contains_key(kvstore.durable_store@[i].unwrap().key)
                &&& kvstore.volatile_index@[kvstore.durable_store@[i].unwrap().key].unwrap().header_addr == i
            } by {
                let k = kvstore.durable_store@[i].unwrap().key;
                assert(kvstore.volatile_index@.contains_key(k));
            }
        }

        Ok(kvstore)
    }

    pub exec fn read_item(
        &self,
        key: &K,
    ) -> (result: Result<Box<I>, KvError<K>>)
        requires 
            self.valid(),
        ensures 
            match result {
                Ok(item) => {
                    match self@[*key] {
                        Some(i) => i.0 == item,
                        None => false,
                    }
                }
                Err(KvError::CRCMismatch) => !self.constants().impervious_to_corruption,
                Err(KvError::KeyNotFound) => !self@.contains_key(*key),
                Err(_) => false,
            }
    {
        proof { self.durable_store.lemma_main_table_index_key(); }

        // 1. Look up the table entry in the volatile index.
        // If the key is not in the volatile index, return an error.
        let index = match self.volatile_index.get(key) {
            Some(index) => index,
            None => {
                assert(!self@.contains_key(*key));
                return Err(KvError::KeyNotFound);
            }
        };

        proof {
            assert(self.volatile_index@.contains_key(*key));
            assert(self.durable_store@.contains_key(index as int));
        }

        // 2. Read the item from the durable store using the index we just obtained
        let ret = self.durable_store.read_item(index);
        
        proof {
            match &ret {
                Ok(item) => {
                    // We have to prove that successful reads from the index and durable store
                    // imply that `key` is in self@
                    let index_to_key = Map::new(
                        |i: int| self.durable_store@.contents.dom().contains(i),
                        |i: int| self.durable_store@.contents[i].key
                    );
                    let key_to_index = index_to_key.invert();
                    assert(index_to_key.contains_key(index as int));
                    assert(key_to_index.contains_key(*key));
                }
                Err(e) => {
                    assert(e == KvError::<K>::CRCMismatch);
                }
            }
        }
        ret
    }

/*
    pub fn untrusted_create(
        &mut self,
        key: &K,
        item: &I,
        kvstore_id: u128,
        perm: Tracked<&TrustedKvPermission<PM>>
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == old(self)@.create(*key, *item).unwrap()
                }
                Err(KvError::KeyAlreadyExists) => {
                    &&& old(self)@.contents.contains_key(*key)
                    &&& old(self)@ == self@
                }
                Err(_) => false
            }
    {
        assume(false);
        // check whether the key already exists
        if self.volatile_index.get(key).is_some() {
            return Err(KvError::KeyAlreadyExists);
        }

        let ghost old_durable_state = self.durable_store@;
        let ghost old_volatile_state = self.volatile_index@;
        let ghost old_kv_state = self@;

        // `item` stores its own key, so we don't have to pass its key to the durable
        // store separately.
        let (key_offset, list_head) = self.durable_store.tentative_create(&key, &item, kvstore_id, perm)?;
        self.durable_store.commit(kvstore_id, perm)?;
        self.volatile_index.insert_key(key, key_offset)?;

        // proof {
        //     // the volatile index and durable store match after creating the new entry in both
        //     lemma_volatile_matches_durable_after_create(old_durable_state, old_volatile_state, offset as int, *key, *item);
        //     let new_kv_state = old_kv_state.create(*key, *item).unwrap();
        //     // the kv state reflects the new volatile and durable store states
        //     assert(new_kv_state.contents =~= AbstractKvStoreState::construct_view_contents(
        //             self.volatile_index@, self.durable_store@));
        // }

        Ok(())
    }

    pub fn untrusted_read_item(&self, key: &K) -> (result: Result<Box<I>, KvError<K>>)
        requires
            self.valid()
        ensures
        // ({
        //     let spec_result = self@.read_item_and_list(*key);
        //     match (result, spec_result) {
        //         (Some(output_item), Some((spec_item, pages))) => {
        //             &&& spec_item == output_item
        //         }
        //         (Some(output_item), None) => false,
        //         (None, Some((spec_item, pages))) => false,
        //         (None, None) => true,
        //     }
        // })
    {
        assume(false); // TODO

        // First, get the offset of the header in the durable store using the volatile index
        let offset = self.volatile_index.get(key);
        match offset {
            Some(offset) => self.durable_store.read_item(self.id, offset),
            None => Err(KvError::KeyNotFound) // TODO: get actual error from volatile?
        }
    }

    // // // TODO: return a Vec<&L> to save space/reduce copies
    // // pub fn untrusted_read_item_and_list(&self, key: &K) -> (result: Option<(&I, Vec<&L>)>)
    // //     requires
    // //         self.valid(),
    // //     ensures
    // //     ({
    // //         let spec_result = self@.read_item_and_list(*key);
    // //         match (result, spec_result) {
    // //             (Some((output_item, output_pages)), Some((spec_item, spec_pages))) => {
    // //                 &&& spec_item == output_item
    // //                 &&& spec_pages == output_pages@
    // //             }
    // //             (Some((output_item, output_pages)), None) => false,
    // //             (None, Some((spec_item, spec_pages))) => false,
    // //             (None, None) => true,
    // //         }
    // //     })
    // // {
    // //     assume(false);
    // //     // First, get the offset of the header in the durable store using the volatile index
    // //     let offset = self.volatile_index.get(key);
    // //     match offset {
    // //         Some(offset) => self.durable_store.read_item_and_list(offset),
    // //         None => None
    // //     }
    // // }

    // pub fn untrusted_read_list_entry_at_index(&self, key: &K, idx: u64) -> (result: Result<&L, KvError<K>>)
    //     requires
    //         self.valid()
    //     ensures
    //         ({
    //             let spec_result = self@.read_list_entry_at_index(*key, idx as int);
    //             match (result, spec_result) {
    //                 (Ok(output_entry), Ok(spec_entry)) => {
    //                     &&& output_entry == spec_entry
    //                 }
    //                 (Err(KvError::IndexOutOfRange), Err(KvError::IndexOutOfRange)) => {
    //                     &&& self@.contents.contains_key(*key)
    //                     &&& self@.contents[*key].1.len() <= idx
    //                 }
    //                 (Err(KvError::KeyNotFound), Err(KvError::KeyNotFound)) => {
    //                     &&& !self@.contents.contains_key(*key)
    //                 }
    //                 (_, _) => false
    //             }
    //         })
    // {
    //     assume(false);
    //     Err(KvError::NotImplemented)
    // }

    // // pub fn untrusted_read_list(&self, key: &K) -> (result: Option<&Vec<L>>)
    // //     requires
    // //         self.valid(),
    // //     ensures
    // //     ({
    // //         let spec_result = self@.read_item_and_list(*key);
    // //         match (result, spec_result) {
    // //             (Some(output_pages), Some((spec_item, spec_pages))) => {
    // //                 &&& spec_pages == output_pages@
    // //             }
    // //             (Some(output_pages), None) => false,
    // //             (None, Some((spec_item, spec_pages))) => false,
    // //             (None, None) => true,
    // //         }
    // //     })
    // // {
    // //     assume(false);
    // //     let offset = self.volatile_index.get(key);
    // //     match offset {
    // //         Some(offset) => self.durable_store.read_list(offset),
    // //         None => None
    // //     }
    // // }

    pub fn untrusted_update_item(
        &mut self,
        key: &K,
        new_item: &I,
        kvstore_id: u128,
        perm: Tracked<&TrustedKvPermission<PM>>
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == old(self)@.update_item(*key, *new_item).unwrap()
                }
                Err(KvError::KeyNotFound) => {
                    &&& !old(self)@.contents.contains_key(*key)
                    &&& old(self)@ == self@
                }
                Err(_) => false
            }
    {
        assume(false);
        let offset = self.volatile_index.get(key);
        match offset {
            Some(offset) => {
                self.durable_store.tentative_update_item(offset, kvstore_id, new_item)?;
                self.durable_store.commit(kvstore_id, perm)
            }
            None => Err(KvError::KeyNotFound)
        }
    }

    // pub fn untrusted_delete(
    //     &mut self,
    //     key: &K,
    //     kvstore_id: u128,
    //     perm: Tracked<&TrustedKvPermission<PM>>
    // ) -> (result: Result<(), KvError<K>>)
    //     requires
    //         old(self).valid()
    //     ensures
    //         self.valid(),
    //         match result {
    //             Ok(()) => {
    //                 &&& self@ == old(self)@.delete(*key).unwrap()
    //             }
    //             Err(KvError::KeyNotFound) => {
    //                 &&& !old(self)@.contents.contains_key(*key)
    //                 &&& old(self)@ == self@
    //             }
    //             Err(_) => false
    //         }
    // {
    //     assume(false);
    //     // Remove the entry from the volatile index, obtaining the physical offset as the return value
    //     let offset = self.volatile_index.remove(key)?;
    //     self.durable_store.delete(offset, kvstore_id, perm)
    // }

    // pub fn untrusted_append_to_list(
    //     &mut self,
    //     key: &K,
    //     new_list_entry: L,
    //     perm: Tracked<&TrustedKvPermission<PM>>
    // ) -> (result: Result<(), KvError<K>>)
    //     requires
    //         old(self).valid()
    //     ensures
    //         self.valid(),
    //         match result {
    //             Ok(()) => {
    //                 &&& self@ == old(self)@.append_to_list(*key, new_list_entry).unwrap()
    //             }
    //             Err(KvError::KeyNotFound) => {
    //                 &&& !old(self)@.contents.contains_key(*key)
    //                 &&& old(self)@ == self@
    //             }
    //             // TODO: case for if we run out of space to append to the list
    //             Err(_) => false
    //         }
    // {
    //     assume(false);
    //     return Err(KvError::InternalError);
    //     // let offset = self.volatile_index.get(key);
    //     // // append a page to the list rooted at this offset
    //     // let page_offset = match offset {
    //     //     Some(offset) => self.durable_store.append(offset, new_list_entry, perm)?,
    //     //     None => return Err(KvError::KeyNotFound)
    //     // };
    //     // // add the durable location of the page to the in-memory list
    //     // self.volatile_index.append_offset_to_list(key, page_offset)
    // }

    // pub fn untrusted_append_to_list_and_update_item(
    //     &mut self,
    //     key: &K,
    //     new_list_entry: L,
    //     new_item: I,
    //     perm: Tracked<&TrustedKvPermission<PM>>
    // ) -> (result: Result<(), KvError<K>>)
    //     requires
    //         old(self).valid()
    //     ensures
    //         self.valid(),
    //         match result {
    //             Ok(()) => {
    //                 &&& self@ == old(self)@.append_to_list_and_update_item(*key, new_list_entry, new_item).unwrap()
    //             }
    //             Err(KvError::KeyNotFound) => {
    //                 &&& !old(self)@.contents.contains_key(*key)
    //                 &&& old(self)@ == self@
    //             }
    //             // TODO: case for if we run out of space to append to the list
    //             Err(_) => false
    //         }
    // {
    //     assume(false);
    //     let offset = self.volatile_index.get(key);
    //     // update the header at this offset append a page to the list rooted there
    //     let page_offset = match offset {
    //         Some(offset) => self.durable_store.update_item_and_append(offset, new_list_entry, new_item, perm)?,
    //         None => return Err(KvError::KeyNotFound)
    //     };

    //     // TODO: use append_node_offset or append_to_list depending on whether you need to allocate or not?
    //     self.volatile_index.append_to_list(key)
    // }

    // pub fn untrusted_update_list_entry_at_index(
    //     &mut self,
    //     key: &K,
    //     idx: usize,
    //     new_list_entry: L,
    //     perm: Tracked<&TrustedKvPermission<PM>>
    // ) -> (result: Result<(), KvError<K>>)
    //     requires
    //         old(self).valid()
    //     ensures
    //         self.valid(),
    //         match result {
    //             Ok(()) => {
    //                 &&& self@ == old(self)@.update_list_entry_at_index(*key, idx, new_list_entry).unwrap()
    //             }
    //             Err(KvError::KeyNotFound) => {
    //                 &&& !old(self)@.contents.contains_key(*key)
    //                 &&& old(self)@ == self@
    //             }
    //             Err(_) => false
    //         }
    // {
    //     assume(false);
    //     match self.volatile_index.get_entry_location_by_index(key, idx) {
    //         Ok((list_node_addr, offset_within_list_node)) =>
    //             self.durable_store.update_list_entry_at_index(list_node_addr, offset_within_list_node, new_list_entry, perm),
    //         Err(e) => Err(e),
    //     }
    // }

    // pub fn untrusted_update_entry_at_index_and_item(
    //     &mut self,
    //     key: &K,
    //     idx: usize,
    //     new_list_entry: L,
    //     new_item: I,
    //     perm: Tracked<&TrustedKvPermission<PM>>
    // ) -> (result: Result<(), KvError<K>>)
    //     requires
    //         old(self).valid()
    //     ensures
    //         match result {
    //             Ok(()) => {
    //                 &&& self.valid()
    //                 &&& self@ == old(self)@.update_entry_at_index_and_item(*key, idx, new_list_entry, new_item).unwrap()
    //             }
    //             Err(KvError::KeyNotFound) => {
    //                 &&& !old(self)@.contents.contains_key(*key)
    //                 &&& old(self)@ == self@
    //             }
    //             Err(_) => false
    //         }
    // {
    //     assume(false);
    //     let header_offset = self.volatile_index.get(key);
    //     match self.volatile_index.get_entry_location_by_index(key, idx) {
    //         Ok((list_node_addr, offset_within_list_node)) =>
    //             self.durable_store.update_entry_at_index_and_item(list_node_addr, offset_within_list_node,
    //                                                               new_item, new_list_entry,  perm),
    //         Err(e) => Err(e),
    //     }
    // }

    // pub fn untrusted_trim_list(
    //     &mut self,
    //     key: &K,
    //     trim_length: usize,
    //     perm: Tracked<&TrustedKvPermission<PM>>
    // ) -> (result: Result<(), KvError<K>>)
    //     requires
    //         old(self).valid()
    //     ensures
    //         match result {
    //             Ok(()) => {
    //                 &&& self.valid()
    //                 &&& self@ == old(self)@.trim_list(*key, trim_length as int).unwrap()
    //             }
    //             Err(KvError::KeyNotFound) => {
    //                 &&& !old(self)@.contents.contains_key(*key)
    //                 &&& old(self)@ == self@
    //             }
    //             Err(_) => false
    //         }
    //     {
    //     // use the volatile index to figure out which physical offsets should be removed
    //     // from the list, then use that information to trim the list on the durable side
    //     // TODO: trim_length is in terms of list entries, not bytes, right? Check Jay's impl
    //     // note: we trim from the beginning of the list, not the end
    //     assume(false);
    //     let item_offset = match self.volatile_index.get(key) {
    //         Some(header_addr) => header_addr,
    //         None => return Err(KvError::KeyNotFound),
    //     };
    //     if trim_length == 0 {
    //         return Ok(());
    //     }
    //     let first_location_trimmed = self.volatile_index.get_entry_location_by_index(key, 0);
    //     let last_location_trimmed = self.volatile_index.get_entry_location_by_index(key, trim_length - 1);
    //     self.volatile_index.trim_list(key, trim_length)?;
    //     match (first_location_trimmed, last_location_trimmed) {
    //         (Ok((first_trimmed_list_node_addr, first_trimmed_offset_within_list_node)),
    //          Ok((last_trimmed_list_node_addr, last_trimmed_offset_within_list_node))) =>
    //             // TODO: The interface to `DurableKvStore::trim_list` might
    //             // need to change, to also take
    //             // `first_trimmed_offset_within_list_node` and
    //             // `last_trimmed_offset_within_list_node`.
    //             self.durable_store.trim_list(item_offset, first_trimmed_list_node_addr, last_trimmed_list_node_addr, trim_length, perm),
    //         (Err(e), _) => Err(e),
    //         (_, Err(e)) => Err(e),
    //     }
    // }

    // pub fn untrusted_trim_list_and_update_item(
    //     &mut self,
    //     key: &K,
    //     trim_length: usize,
    //     new_item: I,
    //     perm: Tracked<&TrustedKvPermission<PM>>
    // ) -> (result: Result<(), KvError<K>>)
    //     requires
    //         old(self).valid()
    //     ensures
    //         match result {
    //             Ok(()) => {
    //                 &&& self.valid()
    //                 &&& self@ == old(self)@.trim_list_and_update_item(*key, trim_length as int, new_item).unwrap()
    //             }
    //             Err(KvError::KeyNotFound) => {
    //                 &&& !old(self)@.contents.contains_key(*key)
    //                 &&& old(self)@ == self@
    //             }
    //             Err(_) => false
    //         }
    // {
    //     assume(false);
    //     let item_offset = match self.volatile_index.get(key) {
    //         Some(header_addr) => header_addr,
    //         None => return Err(KvError::KeyNotFound),
    //     };
    //     if trim_length == 0 {
    //         return Ok(());
    //     }
    //     let first_location_trimmed = self.volatile_index.get_entry_location_by_index(key, 0);
    //     let last_location_trimmed = self.volatile_index.get_entry_location_by_index(key, trim_length - 1);
    //     self.volatile_index.trim_list(key, trim_length)?;
    //     match (first_location_trimmed, last_location_trimmed) {
    //         (Ok((first_trimmed_list_node_addr, first_trimmed_offset_within_list_node)),
    //          Ok((last_trimmed_list_node_addr, last_trimmed_offset_within_list_node))) =>
    //             // TODO: The interface to `DurableKvStore::trim_list` might
    //             // need to change, to also take
    //             // `first_trimmed_offset_within_list_node` and
    //             // `last_trimmed_offset_within_list_node`.
    //             self.durable_store.trim_list_and_update_item(item_offset, first_trimmed_list_node_addr, last_trimmed_list_node_addr, trim_length, new_item, perm),
    //         (Err(e), _) => Err(e),
    //         (_, Err(e)) => Err(e),
    //     }
    // }

    // pub fn untrusted_get_keys(&self) -> (result: Vec<K>)
    //     requires
    //         self.valid()
    //     ensures
    //         result@.to_set() == self@.get_keys()
    // {
    //     assume(false);
    //     self.volatile_index.get_keys()
    // }

    */

    pub fn untrusted_contains_key(&self, key: &K) -> (result: bool)
        requires
            self.valid(),
        ensures
            match result {
                true => self@[*key] is Some,
                false => self@[*key] is None
            }
    {
        assume(false);
        self.volatile_index.get(key).is_some()
    }

}

}
