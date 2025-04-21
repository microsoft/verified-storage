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
use super::kvspec_t::*;
use super::volatile::volatileimpl_v::*;
use super::volatile::volatilespec_v::*;
use crate::kv::kvimpl_t::*;
use crate::kv::layout_v::*;
use crate::kv::setup_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use crate::pmem::pmemutil_v::*;
use crate::log2::logimpl_v::*;
use crate::common::util_v::*;

use std::hash::Hash;

verus! {

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
pub struct UntrustedKvStoreImpl<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + std::fmt::Debug,
    I: PmCopy + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug + Copy,
    // V: VolatileKvIndex<K>,
{
    id: u128,
    durable_store: DurableKvStore<TrustedKvPermission<PM>, PM, K, I, L>,
    volatile_index: VolatileKvIndexImpl::<K>,
}

impl<PM, K, I, L> UntrustedKvStoreImpl<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug + Copy,
    // V: VolatileKvIndex<K>,
{
    pub open spec fn recover(mem: Seq<u8>, kv_id: u128) -> Option<AbstractKvStoreState<K, I, L>>
    {
        AbstractKvStoreState::<K, I, L>::recover::<TrustedKvPermission<PM>, PM>(mem, kv_id)
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

    pub closed spec fn tentative_view(&self) -> AbstractKvStoreState<K, I, L>
    {
        AbstractKvStoreState {
            id: self.id,
            contents: AbstractKvStoreState::<K, I, L>::construct_view_from_durable_state(self.durable_store.tentative_view().unwrap()),
        }
    }

    pub closed spec fn powerpm_view(self) -> PersistentMemoryRegionView
    {
        self.durable_store.powerpm_view()
    }


    pub closed spec fn transaction_committed(self) -> bool 
    {
        self.durable_store.transaction_committed()
    }

    pub closed spec fn spec_num_log_entries_in_current_transaction(self) -> nat 
    {
        self.durable_store.spec_num_log_entries_in_current_transaction()
    }

    pub exec fn num_log_entries_in_current_transaction(&self) -> (out: usize) 
        requires 
            self.valid(),
        ensures 
            out == self.spec_num_log_entries_in_current_transaction()
    {
        self.durable_store.num_log_entries_in_current_transaction()
    }

    pub closed spec fn valid(self) -> bool
    {
        &&& self.durable_store_matches_volatile_index()
        &&& self.tentative_durable_store_matches_tentative_volatile_index()
        // &&& self.durable_store@.matches_volatile_index(self.volatile_index@)
        &&& self.durable_store.valid()
        &&& self.volatile_index.valid()

        &&& Self::recover(self.powerpm_view().durable_state, self.id) == Some(self@)
        &&& !self.durable_store.transaction_committed()
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

    pub closed spec fn tentative_durable_store_matches_tentative_volatile_index(self) -> bool 
    {
        let durable_tentative_view = self.durable_store.tentative_view().unwrap();
        // all keys in the volatile index are stored at the indexed offset in the durable store
        &&& forall |k: K| #[trigger] self.volatile_index.tentative_view().contains_key(k) ==> {
            let indexed_offset = self.volatile_index.tentative_view()[k].unwrap().header_addr;
            &&& durable_tentative_view.contains_key(indexed_offset as int)
            &&& durable_tentative_view[indexed_offset as int].unwrap().key == k
        }
        // all offsets in the durable store have a corresponding entry in the volatile index
        &&& forall |i: int| #[trigger] durable_tentative_view.contains_key(i) ==> {
            &&& self.volatile_index.tentative_view().contains_key(durable_tentative_view[i].unwrap().key)
            &&& self.volatile_index.tentative_view()[durable_tentative_view[i].unwrap().key].unwrap().header_addr == i
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
                    &&& pm_region@.flush_predicted()
                    &&& Self::recover(pm_region@.durable_state, kvstore_id) matches Some(recovered_view)
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
        DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::setup(pm_region, version_metadata, overall_metadata, overall_metadata.kvstore_id)?;
        
        // 4. Prove that the resulting recovery view is an empty store
        proof {
            Self::lemma_recovery_view_is_init_if_durable_recovery_view_is_init(pm_region@.durable_state, version_metadata, overall_metadata);
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
            DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::physical_recover(mem, version_metadata, overall_metadata) == Some(DurableKvStoreView::<K, I, L>::init()),
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
            &&& overall_metadata_valid::<K, I, L>(read_overall_metadata, read_version_metadata.overall_metadata_addr)
            &&& overall_metadata.kvstore_id == read_overall_metadata.kvstore_id
            &&& mem.len() >= VersionMetadata::spec_size_of() + u64::spec_size_of()
        });
        let recovered_durable_store = DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::physical_recover(mem, version_metadata, overall_metadata).unwrap();
        assert(recovered_durable_store.contents == Map::<int, DurableKvStoreViewEntry<K, I, L>>::empty());
        let recovered_view = AbstractKvStoreState::construct_view_from_durable_state(recovered_durable_store);
        assert(recovered_view == Map::<K, (I, Seq<L>)>::empty());
    }

    pub fn untrusted_start(
        mut powerpm_region: PoWERPersistentMemoryRegion<TrustedKvPermission<PM>, PM>,
        kvstore_id: u128,
        Ghost(state): Ghost<AbstractKvStoreState<K, I, L>>,
        Tracked(perm): Tracked<&TrustedKvPermission<PM>>,
    ) -> (result: Result<Self, KvError<K>>)
        requires 
            powerpm_region.inv(),
            powerpm_region@.flush_predicted(),
            Self::recover(powerpm_region@.durable_state, kvstore_id) == Some(state),
            forall |s| #[trigger] perm.permits(s) <==> Self::recover(s, kvstore_id) == Some(state),
            K::spec_size_of() > 0,
            I::spec_size_of() + u64::spec_size_of() <= u64::MAX,
            vstd::std_specs::hash::obeys_key_model::<K>(),
        ensures 
            match result {
                Ok(kv) => {
                    &&& kv.valid()
                    &&& kv.powerpm_view().flush_predicted()
                    &&& Some(kv@) == Self::recover(kv.powerpm_view().durable_state, kvstore_id)
                }
                Err(KvError::CRCMismatch) => !powerpm_region.constants().impervious_to_corruption(),
                Err(_) => false 
            }
    {        
        // 1. Read the version and overall metadata from PM.
        let pm = powerpm_region.get_pm_region_ref();
        let version_metadata = read_version_metadata::<PM, K, I, L>(pm, kvstore_id)?;
        let overall_metadata = read_overall_metadata::<PM, K, I, L>(pm, &version_metadata, kvstore_id)?;

        // 2. Call the durable KV store's start method
        let ghost durable_kvstore_state = DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::physical_recover(
            powerpm_region@.durable_state, version_metadata, overall_metadata).unwrap();
        assert(state.contents == AbstractKvStoreState::<K, I, L>::construct_view_from_durable_state(durable_kvstore_state));

        proof {
            assert(DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::physical_recover(
                powerpm_region@.durable_state, version_metadata, overall_metadata) is Some);
            assert(overall_metadata_valid::<K, I, L>(deserialize_overall_metadata(powerpm_region@.durable_state, version_metadata.overall_metadata_addr), version_metadata.overall_metadata_addr));
            assert forall |s| {
                &&& version_and_overall_metadata_match_deserialized(s, powerpm_region@.durable_state)
                &&& Some(durable_kvstore_state) == #[trigger] DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::physical_recover(s, version_metadata, overall_metadata)
            } implies Self::recover(s, kvstore_id) == Some(state) by {
                broadcast use pmcopy_axioms;
            }
            let base_log_state = UntrustedLogImpl::recover(powerpm_region@.durable_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
            assert(base_log_state.log.len() == 0 || base_log_state.log.len() > u64::spec_size_of());

            if base_log_state.log.len() > u64::spec_size_of() {
                DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::lemma_log_size_does_not_overflow_u64(powerpm_region@, version_metadata, overall_metadata);
            } else {
                assert(base_log_state.log.len() == 0);
            }
        }
    
        let (kvstore, entry_list) = DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::start(powerpm_region, overall_metadata, 
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
        assert(volatile_index@ == volatile_index.tentative_view()) by {
            assert(volatile_index@.contents == Map::<K, VolatileKvIndexEntry>::empty());
            assert(volatile_index.tentative_view().contents == Map::<K, VolatileKvIndexEntry>::empty());
        }
        proof {
            // volatile_index.lemma_if_tentative_view_matches_view_then_no_tentative_entries();
            assert(volatile_index.tentative@.is_empty());
            assert(volatile_index.tentative@.dom().finite());
        }

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
                volatile_index@ == volatile_index.tentative_view(),
                volatile_index.tentative_keys@.len() == 0,
                volatile_index@.contents.dom().finite(),
        {
            let ghost tentative_at_top = volatile_index.tentative@;
            if i < entry_list.len() {
                assert(kvstore@.contains_key(entry_list_view[i as int].1 as int));
            }
            let ghost old_volatile_index = volatile_index;
            let (key, index) = (*entry_list[i].0, entry_list[i].1);
            volatile_index.insert_key_during_startup(&key, index)?;

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
                    match self.tentative_view()[*key] {
                        Some(i) => i.0 == item,
                        None => false,
                    }
                }
                Err(KvError::CRCMismatch) => !self.constants().impervious_to_corruption(),
                Err(KvError::KeyNotFound) => !self.tentative_view().contains_key(*key),
                Err(_) => false,
            }
    {
        proof { 
            self.durable_store.lemma_valid_implies_inv();
            self.durable_store.lemma_main_table_index_key_durable(); 
            self.durable_store.lemma_main_table_index_key_tentative(); 
        }

        // 1. Look up the table entry in the volatile index.
        // If the key is not in the volatile index, return an error.
        let index = match self.volatile_index.get(key) {
            Some(index) => index,
            None => {
                assert(!self.tentative_view().contains_key(*key));
                return Err(KvError::KeyNotFound);
            }
        };

        proof {
            assert(self.volatile_index.tentative_view().contains_key(*key));
            assert(self.volatile_index.tentative_view()[*key].unwrap().header_addr == index);
            assert(self.durable_store.tentative_view().unwrap().contains_key(index as int));
        }

        // 2. Read the item from the durable store using the index we just obtained
        let ret = self.durable_store.read_item(index);
        
        proof {
            match &ret {
                Ok(item) => {
                    // We have to prove that successful reads from the index and durable store
                    // imply that `key` is in self@
                    let index_to_key = Map::new(
                        |i: int| self.durable_store.tentative_view().unwrap().contents.dom().contains(i),
                        |i: int| self.durable_store.tentative_view().unwrap().contents[i].key
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

    proof fn lemma_if_key_in_tentative_volatile_index_then_key_in_tentative_view(
        self, 
        key: K,
        index: u64,
        kvstore_id: u128,
    )
        requires
            self.valid(),
            self.volatile_index.tentative_view().contains_key(key),
            self.volatile_index.tentative_view()[key].unwrap().header_addr == index,
            Self::recover(self.powerpm_view().durable_state, kvstore_id) == Some(self@),
        ensures 
            self.tentative_view().contains_key(key),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        self.durable_store.lemma_valid_implies_inv();
        self.durable_store.lemma_main_table_index_key_durable(); 
        self.durable_store.lemma_main_table_index_key_tentative(); 

        assert(self.volatile_index.tentative_view().contains_key(key));
        assert(self.volatile_index.tentative_view()[key].unwrap().header_addr == index);
        assert(self.durable_store.tentative_view().unwrap().contains_key(index as int));
        self.durable_store.lemma_reveal_opaque_inv();

        // Prove that the presence of this key in the volatile index implies 
        // that it is in the current tentative view
        let durable_store_state = self.durable_store.tentative_view().unwrap();
        let index_to_key = Map::new(
            |i| durable_store_state.contents.dom().contains(i),
            |i| durable_store_state.contents[i].key
        );
        let indexed_offset = self.volatile_index.tentative_view()[key].unwrap().header_addr;
        assert(index_to_key.contains_value(key)) by {
            assert(index_to_key.dom().contains(indexed_offset as int));
        }
        assert(self.tentative_view().contains_key(key));
    }

    // This function performs a tentative update to the item of the specified key 
    // as part of an ongoing transaction.
    pub exec fn untrusted_update_item(
        &mut self,
        key: &K,
        new_item: &I,
        kvstore_id: u128,
        Tracked(perm): Tracked<&TrustedKvPermission<PM>>,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            old(self)@.id == kvstore_id,
            forall |s| #[trigger] perm.permits(s) <==> Self::recover(s, kvstore_id) == Some(old(self)@),
        ensures 
            self.valid(),
            old(self)@.id == self@.id,
            match result {
                Ok(()) => {
                    &&& Ok::<AbstractKvStoreState<K, I, L>, KvError<K>>(self.tentative_view()) == old(self).tentative_view().update_item(*key, *new_item)
                    &&& self@ == old(self)@
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@
                    &&& self.tentative_view() == self@
                    &&& !self.constants().impervious_to_corruption()
                }, 
                Err(KvError::KeyNotFound) => {
                    &&& self@ == old(self)@
                    &&& self.tentative_view() == old(self).tentative_view()
                    &&& !self.tentative_view().contains_key(*key)
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@
                    &&& self.tentative_view() == self@
                    // TODO
                }
                Err(_) => false,
            }
    {
        proof { 
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            self.durable_store.lemma_valid_implies_inv();
            self.durable_store.lemma_main_table_index_key_durable(); 
            self.durable_store.lemma_main_table_index_key_tentative(); 
            self.durable_store.lemma_reveal_opaque_inv();
        }

        // 1. Look up the key in the volatile index. If it does not exist,
        // return error.
        let index = match self.volatile_index.get(key) {
            Some(index) => index,
            None => {
                assert(!self.tentative_view().contains_key(*key));
                return Err(KvError::KeyNotFound);
            }
        };

        proof {
            self.lemma_if_key_in_tentative_volatile_index_then_key_in_tentative_view(*key, index, kvstore_id);
            self.durable_store.lemma_reveal_opaque_inv();

            let version_metadata = self.durable_store.spec_version_metadata();
            let overall_metadata = self.durable_store.spec_overall_metadata();
            let durable_kvstore_state = DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::physical_recover(
                    self.powerpm_view().durable_state, version_metadata, overall_metadata);

            assert forall |s| {
                &&& version_and_overall_metadata_match_deserialized(s, self.powerpm_view().durable_state)
                &&& durable_kvstore_state == DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::physical_recover(s, version_metadata, overall_metadata)
            } implies #[trigger] Self::recover(s, kvstore_id) == Some(self@) by {                
                assert(memory_correctly_set_up_on_region::<K, I, L>(s, kvstore_id)) by {
                    broadcast use pmcopy_axioms;
                }
            }
        }

        // 2. Tentatively update the item in the durable store
        let result = self.durable_store.tentative_update_item(index, new_item, kvstore_id, Tracked(perm));
        if let Err(e) = result {
            self.volatile_index.abort_transaction();
            proof {
                self.durable_store.lemma_valid_implies_inv();
                self.durable_store.lemma_reveal_opaque_inv();
                self.durable_store.lemma_overall_metadata_addr();
                assert(perm.permits(self.powerpm_view().durable_state));
            }
            return Err(e);
        }

        proof {
            let durable_tentative_view = self.durable_store.tentative_view().unwrap();
            let old_durable_tentative_view = old(self).durable_store.tentative_view().unwrap();

            // The durable store's domain hasn't changed, so it still matches the volatile index
            assert forall |i: int| #[trigger] durable_tentative_view.contains_key(i) implies {
                &&& self.volatile_index.tentative_view().contains_key(durable_tentative_view[i].unwrap().key)
                &&& self.volatile_index.tentative_view()[durable_tentative_view[i].unwrap().key].unwrap().header_addr == i
            } by {
                assert(old(self).durable_store.tentative_view().unwrap().contains_key(i));
            }

            // the tentative view reflects the new update
            assert(self.tentative_view() == old(self).tentative_view().update_item(*key, *new_item).unwrap()) by {
                // the tentative views are obtained via index->key mappings in the durable tentative view,
                // so we have to prove that these mappings have not changed. We already know that the item
                // associated with the current key has been updated.
                let index_to_key = Map::new(
                    |i| durable_tentative_view.contents.dom().contains(i),
                    |i| durable_tentative_view.contents[i].key
                );
                let old_index_to_key = Map::new(
                    |i| old_durable_tentative_view.contents.dom().contains(i),
                    |i| old_durable_tentative_view.contents[i].key
                );
                assert(index_to_key == old_index_to_key);
                assert(self.tentative_view().contents == old(self).tentative_view().update_item(*key, *new_item).unwrap().contents);
               
            }
        }

        Ok(())
    }

    pub exec fn untrusted_commit(
        &mut self, 
        kvstore_id: u128,
        Tracked(perm): Tracked<&TrustedKvPermission<PM>>
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            // !old(self).transaction_committed(),
            // Self::recover(old(self).powerpm_view().durable_state, kvstore_id) == Some(old(self)@),
            old(self)@.id == kvstore_id,
            forall |s| #[trigger] perm.permits(s) <==> {
                &&& {
                    ||| Self::recover(s, kvstore_id) == Some(old(self)@)
                    ||| Self::recover(s, kvstore_id) == Some(old(self).tentative_view())
                }
            },
            old(self).spec_num_log_entries_in_current_transaction() > 0,
        ensures 
            self.valid(),
            self@.id == old(self)@.id,
            match result {
                Ok(()) => {
                    &&& self@ == old(self).tentative_view()
                    &&& self@ == self.tentative_view()
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@
                    &&& self@ == self.tentative_view()
                    &&& !self.constants().impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@
                    &&& self@ == self.tentative_view()
                    // TODO
                }
                Err(KvError::LogErr { log_err }) => {
                    &&& self@ == old(self)@
                    &&& self@ == self.tentative_view()
                    // TODO
                }
                Err(_) => false,
            }
    { 
        proof {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            self.durable_store.lemma_valid_implies_inv();
            self.durable_store.lemma_reveal_opaque_inv();
            self.durable_store.lemma_main_table_index_key_durable(); 
            self.durable_store.lemma_main_table_index_key_tentative(); 
            self.durable_store.lemma_reveal_opaque_inv_mem();

            assert(perm.permits(self.powerpm_view().durable_state)) by {
                self.durable_store.lemma_overall_metadata_addr();
//                lemma_establish_extract_bytes_equivalence(s, self.powerpm_view().durable_state);
//                lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(self.powerpm_view());
            }

            assert forall |s| {
                &&& version_and_overall_metadata_match_deserialized(s, self.powerpm_view().durable_state)
                &&& {
                    ||| DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::physical_recover(s, self.durable_store.spec_version_metadata(), self.durable_store.spec_overall_metadata()) == Some(self.durable_store@)
                    ||| DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::physical_recover(s, self.durable_store.spec_version_metadata(), self.durable_store.spec_overall_metadata()) == self.durable_store.tentative_view()
                }
            } implies #[trigger] perm.permits(s) by {
                assert(forall |s| #[trigger] perm.permits(s) <==> {
                    ||| Self::recover(s, kvstore_id) == Some(old(self)@)
                    ||| Self::recover(s, kvstore_id) == Some(old(self).tentative_view())
                });

                assert(version_and_overall_metadata_match_deserialized(s, self.powerpm_view().durable_state));
                assert(memory_correctly_set_up_on_region::<K, I, L>(s, kvstore_id)) by {
                    broadcast use pmcopy_axioms;
                }

                if DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::physical_recover(s, 
                    self.durable_store.spec_version_metadata(), self.durable_store.spec_overall_metadata()) == 
                        Some(self.durable_store@) 
                {
                    assert(Self::recover(s, kvstore_id) =~= Some(self@));
                } else {
                    assert(DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::physical_recover(s, 
                        self.durable_store.spec_version_metadata(), self.durable_store.spec_overall_metadata()) == 
                            self.durable_store.tentative_view());
                }
            }
        }

        let result = self.durable_store.commit(Tracked(perm));
        if let Err(e) = result {
            self.volatile_index.abort_transaction();
            proof {
                self.durable_store.lemma_valid_implies_inv();
                self.durable_store.lemma_reveal_opaque_inv();
                self.durable_store.lemma_overall_metadata_addr();
                assert(perm.permits(self.powerpm_view().durable_state));
            }
            return Err(e);
        }
        assert(perm.permits(self.powerpm_view().durable_state));

        self.volatile_index.commit_transaction();

        assert(self.volatile_index@ == old(self).volatile_index.tentative_view());
        assert(Some(self.durable_store@) == old(self).durable_store.tentative_view());
        assert(self.volatile_index@ == self.volatile_index.tentative_view());
        assert(Some(self.durable_store@) == self.durable_store.tentative_view());
        assert(Self::recover(self.powerpm_view().durable_state, kvstore_id) == Some(self@)) by {
            self.durable_store.lemma_valid_implies_inv();
            self.durable_store.lemma_reveal_opaque_inv();
            self.durable_store.lemma_reveal_opaque_inv_mem();
        }

        Ok(())
    }

    pub exec fn untrusted_create(
        &mut self,
        key: &K,
        item: &I,
        kvstore_id: u128,
        Tracked(perm): Tracked<&TrustedKvPermission<PM>>,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            old(self)@.id == kvstore_id,
            forall |s| #[trigger] perm.permits(s) <==> Self::recover(s, kvstore_id) == Some(old(self)@),
        ensures 
            self.valid(),
            self@.id == old(self)@.id,
            match result {
                Ok(()) => {
                    &&& Ok::<AbstractKvStoreState<K, I, L>, KvError<K>>(self.tentative_view()) == 
                        old(self).tentative_view().create(*key, *item)
                    &&& self@ == old(self)@
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@
                    &&& self.tentative_view() == self@
                    &&& !self.constants().impervious_to_corruption()
                }, 
                Err(KvError::KeyAlreadyExists) => {
                    &&& self@ == old(self)@
                    &&& self.tentative_view() == old(self).tentative_view()
                    &&& old(self).tentative_view().contains_key(*key)
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@
                    &&& self.tentative_view() == self@
                    // TODO
                }
                Err(_) => false,
            }
    {
        proof { 
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            self.durable_store.lemma_valid_implies_inv();
            self.durable_store.lemma_main_table_index_key_durable(); 
            self.durable_store.lemma_main_table_index_key_tentative(); 
            self.durable_store.lemma_reveal_opaque_inv();
        }

        // 1. Look up the key in the volatile index. If it already exists,
        // return error.
        // TODO: should this abort the transaction?
        if let Some(index) = self.volatile_index.get(key) {
            proof {
                self.lemma_if_key_in_tentative_volatile_index_then_key_in_tentative_view(*key, index, kvstore_id);
            }
            return Err(KvError::KeyAlreadyExists);
        }

        proof {
            let version_metadata = self.durable_store.spec_version_metadata();
            let overall_metadata = self.durable_store.spec_overall_metadata();
            let durable_kvstore_state = DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::physical_recover(
                    self.powerpm_view().durable_state, version_metadata, overall_metadata);

            assert forall |s| {
                &&& version_and_overall_metadata_match_deserialized(s, self.powerpm_view().durable_state)
                &&& durable_kvstore_state == DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::physical_recover(s, version_metadata, overall_metadata)
            } implies #[trigger] Self::recover(s, kvstore_id) == Some(self@) by {                
                assert(memory_correctly_set_up_on_region::<K, I, L>(s, kvstore_id)) by {
                    broadcast use pmcopy_axioms;
                }
            }

            assert(!self.volatile_index.tentative_view().contains_key(*key));
            assert(self.tentative_durable_store_matches_tentative_volatile_index());

            let durable_tentative_view = self.durable_store.tentative_view().unwrap();
            assert forall|e| #[trigger] durable_tentative_view.contents.contains_value(e) implies 
                e.key != key
            by {
                let witness = choose |i| #[trigger] durable_tentative_view.contents.dom().contains(i) && durable_tentative_view[i] == Some(e);
                assert(durable_tentative_view.contains_key(witness));
                assert(self.volatile_index.tentative_view().contains_key(durable_tentative_view[witness].unwrap().key));
                assert(self.volatile_index.tentative_view().contains_key(e.key));
            }
        }

        // 2. Tentatively create the durable record
        let result = self.durable_store.tentative_create(key, item, kvstore_id, Tracked(perm));
        let (offset, _head_node) = match result {
            Ok((offset, _head_node)) => (offset, _head_node),
            Err(e) => {
                self.volatile_index.abort_transaction();
                proof {
                    self.durable_store.lemma_valid_implies_inv();
                    self.durable_store.lemma_reveal_opaque_inv();
                    self.durable_store.lemma_overall_metadata_addr();
                    assert(perm.permits(self.powerpm_view().durable_state));
                }
                return Err(e);
            } 
        };

        assert(perm.permits(self.powerpm_view().durable_state));

        // 3. Update the volatile index
        self.volatile_index.insert_key(key, offset)?; 

        proof {
            assert(old(self).tentative_view().create(*key, *item) is Ok);

            let new_durable_store_state = self.durable_store.tentative_view().unwrap();
            let new_index_to_key = Map::new(
                |i| new_durable_store_state.contents.dom().contains(i),
                |i| new_durable_store_state.contents[i].key
            );
            let new_key_to_index = new_index_to_key.invert();
    
            let old_durable_store_state = old(self).durable_store.tentative_view().unwrap();
            let old_index_to_key = Map::new(
                |i| old_durable_store_state.contents.dom().contains(i),
                |i| old_durable_store_state.contents[i].key
            );
            let old_key_to_index = old_index_to_key.invert();

            assert(self.durable_store.valid());
            self.durable_store.lemma_valid_implies_inv();
            self.durable_store.lemma_main_table_index_key_tentative();
            lemma_injective_map_inverse(new_index_to_key);
            lemma_injective_map_inverse(old_index_to_key);
    
            assert forall |k| self.tentative_view().contents.contains_key(k) implies {
                &&& #[trigger] old(self).tentative_view().create(*key, *item).unwrap().contents.contains_key(k)
                &&& old(self).tentative_view().create(*key, *item).unwrap().contents[k] == self.tentative_view().contents[k]
            } by {    
                if k == key {
                    assert(self.tentative_view().contents == Map::new(
                        |k| new_key_to_index.dom().contains(k),
                        |k| {
                            let index = new_key_to_index[k];
                            let entry = new_durable_store_state.contents[index];
                            (entry.item, entry.list.list)
                        }
                    ));
                    assert(new_durable_store_state.contents[offset as int].item == item);
                    assert(new_index_to_key[offset as int] == key);
                } else {
                    assert(k != key);
                    assert(forall |j| new_index_to_key.contains_key(j) && j != offset ==> {
                        &&& old_index_to_key.contains_key(j)
                        &&& #[trigger] new_index_to_key[j] == old_index_to_key[j]
                    });
                }
            }
            assert forall |k| old(self).tentative_view().create(*key, *item).unwrap().contents.contains_key(k) implies {
                &&& #[trigger] self.tentative_view().contents.contains_key(k)
                &&& old(self).tentative_view().create(*key, *item).unwrap().contents[k] == self.tentative_view().contents[k]
            } by {
                assert(forall |j| #[trigger] new_index_to_key.contains_key(j) ==>
                    new_key_to_index[new_index_to_key[j]] == j);
                assert(forall |j| #[trigger] old_index_to_key.contains_key(j) ==>
                    old_key_to_index[new_index_to_key[j]] == j);
    
                assert(self.durable_store.tentative_view() ==
                    Some(old(self).durable_store.tentative_view().unwrap().create(offset as int, *key, *item).unwrap()));
    
                assert(forall |j| old_index_to_key.contains_key(j) && j != offset ==> {
                    &&& new_index_to_key.contains_key(j)
                    &&& #[trigger] new_index_to_key[j] == old_index_to_key[j]
                });
    
                assert(self.tentative_view().contents.dom() == new_key_to_index.dom());
                if k == key {
                    assert(new_index_to_key.contains_key(offset as int));
                    assert(new_key_to_index.contains_key(k));
                } 
            }
            assert(self.tentative_view().contents == old(self).tentative_view().create(*key, *item).unwrap().contents);
            assert(self.tentative_durable_store_matches_tentative_volatile_index()) by {
                assert(old(self).tentative_durable_store_matches_tentative_volatile_index());
                let durable_tentative_view = self.durable_store.tentative_view().unwrap();

                assert forall |k: K| #[trigger] self.volatile_index.tentative_view().contains_key(k) implies {
                    let indexed_offset = self.volatile_index.tentative_view()[k].unwrap().header_addr;
                    &&& durable_tentative_view.contains_key(indexed_offset as int)
                    &&& durable_tentative_view[indexed_offset as int].unwrap().key == k
                } by {
                    if k != key {
                        assert(old(self).volatile_index.tentative_view().contains_key(k));
                    } // else, trivial
                }
                assert forall |i: int| #[trigger] durable_tentative_view.contains_key(i) implies {
                    &&& self.volatile_index.tentative_view().contains_key(durable_tentative_view[i].unwrap().key)
                    &&& self.volatile_index.tentative_view()[durable_tentative_view[i].unwrap().key].unwrap().header_addr == i
                } by {
                    if i != offset {
                        assert(old(self).durable_store.tentative_view().unwrap().contains_key(i));
                    } // else, trivial
                }
            }
            
            assert(self.valid());
        }
        Ok(())
    }

    pub exec fn untrusted_delete(
        &mut self,
        key: &K,
        kvstore_id: u128,
        Tracked(perm): Tracked<&TrustedKvPermission<PM>>,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            old(self)@.id == kvstore_id,
            forall |s| #[trigger] perm.permits(s) <==> {
                Self::recover(s, kvstore_id) == Some(old(self)@)
            },
        ensures 
            self.valid(),
            self@.id == old(self)@.id,
            match result {
                Ok(()) => {
                    &&& Ok::<AbstractKvStoreState<K, I, L>, KvError<K>>(self.tentative_view()) == 
                        old(self).tentative_view().delete(*key)
                    &&& self@ == old(self)@
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@
                    &&& self.tentative_view() == self@
                    &&& !self.constants().impervious_to_corruption()
                }, 
                Err(KvError::KeyNotFound) => {
                    &&& self@ == old(self)@
                    &&& self.tentative_view() == old(self).tentative_view()
                    &&& !old(self).tentative_view().contains_key(*key)
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@
                    &&& self.tentative_view() == self@
                    // TODO
                }
                Err(_) => false,
            }
    {
        proof { 
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            self.durable_store.lemma_valid_implies_inv();
            self.durable_store.lemma_main_table_index_key_durable(); 
            self.durable_store.lemma_main_table_index_key_tentative(); 
            self.durable_store.lemma_reveal_opaque_inv();
        }

        // 1. Look up the key in the volatile index. If it does not exist,
        // return error.
        let index = match self.volatile_index.get(key) {
            Some(index) => index,
            None => {
                assert(!self.tentative_view().contains_key(*key));
                return Err(KvError::KeyNotFound);
            }
        };

        proof {
            self.lemma_if_key_in_tentative_volatile_index_then_key_in_tentative_view(*key, index, kvstore_id);
            self.durable_store.lemma_reveal_opaque_inv();

            let version_metadata = self.durable_store.spec_version_metadata();
            let overall_metadata = self.durable_store.spec_overall_metadata();
            let durable_kvstore_state = DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::physical_recover(
                    self.powerpm_view().durable_state, version_metadata, overall_metadata);

            assert forall |s| {
                &&& version_and_overall_metadata_match_deserialized(s, self.powerpm_view().durable_state)
                &&& durable_kvstore_state == DurableKvStore::<TrustedKvPermission<PM>, PM, K, I, L>::physical_recover(s, version_metadata, overall_metadata)
            } implies #[trigger] Self::recover(s, kvstore_id) == Some(self@) by {                
                assert(memory_correctly_set_up_on_region::<K, I, L>(s, kvstore_id)) by {
                    broadcast use pmcopy_axioms;
                }
            }
        }

        // 2. Tentatively delete the item in the durable store
        let result = self.durable_store.tentative_delete(index, Tracked(perm));
        if let Err(e) = result {
            self.volatile_index.abort_transaction();
            proof {
                self.durable_store.lemma_valid_implies_inv();
                self.durable_store.lemma_reveal_opaque_inv();
                self.durable_store.lemma_overall_metadata_addr();
                assert(perm.permits(self.powerpm_view().durable_state));
            }
            return Err(e);
        }

        // 3. Update the volatile index to reflect the pending deletion
        self.volatile_index.remove(key)?;

        proof {
            assert(old(self).tentative_view().delete(*key) is Ok);
            assert(self.durable_store.tentative_view() is Some);
            assert(old(self).durable_store.tentative_view().unwrap().delete(index as int).unwrap() == 
                self.durable_store.tentative_view().unwrap());

            let new_durable_store_state = self.durable_store.tentative_view().unwrap();
            let new_index_to_key = Map::new(
                |i| new_durable_store_state.contents.dom().contains(i),
                |i| new_durable_store_state.contents[i].key
            );
            let new_key_to_index = new_index_to_key.invert();
    
            let old_durable_store_state = old(self).durable_store.tentative_view().unwrap();
            let old_index_to_key = Map::new(
                |i| old_durable_store_state.contents.dom().contains(i),
                |i| old_durable_store_state.contents[i].key
            );
            let old_key_to_index = old_index_to_key.invert();

            assert(self.durable_store.valid());
            self.durable_store.lemma_valid_implies_inv();
            self.durable_store.lemma_main_table_index_key_tentative();
            lemma_injective_map_inverse(new_index_to_key);
            lemma_injective_map_inverse(old_index_to_key);

            assert(old_key_to_index.contains_key(*key));
            assert(old_index_to_key.remove(index as int) == new_index_to_key);

            assert(self.tentative_view().contents =~= 
                old(self).tentative_view().delete(*key).unwrap().contents);
        
            assert(self.tentative_durable_store_matches_tentative_volatile_index()) by {
                assert(old(self).tentative_durable_store_matches_tentative_volatile_index());
                let durable_tentative_view = self.durable_store.tentative_view().unwrap();
                assert forall |k: K| #[trigger] self.volatile_index.tentative_view().contains_key(k) implies {
                    let indexed_offset = self.volatile_index.tentative_view()[k].unwrap().header_addr;
                    &&& durable_tentative_view.contains_key(indexed_offset as int)
                    &&& durable_tentative_view[indexed_offset as int].unwrap().key == k
                } by {
                    if k != key {
                        assert(old(self).volatile_index.tentative_view().contains_key(k));
                    } // else, trivial
                }
                assert forall |i: int| #[trigger] durable_tentative_view.contains_key(i) implies {
                    &&& self.volatile_index.tentative_view().contains_key(durable_tentative_view[i].unwrap().key)
                    &&& self.volatile_index.tentative_view()[durable_tentative_view[i].unwrap().key].unwrap().header_addr == i
                } by {
                    if i != index {
                        assert(old(self).durable_store.tentative_view().unwrap().contains_key(i));
                    } // else, trivial
                }
            }
            assert(perm.permits(self.powerpm_view().durable_state));
        }

        Ok(())
    }

/*
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

    // pub fn untrusted_contains_key(&self, key: &K) -> (result: bool)
    //     requires
    //         self.valid(),
    //     ensures
    //         match result {
    //             true => self@[*key] is Some,
    //             false => self@[*key] is None
    //         }
    // {
    //     assume(false);
    //     self.volatile_index.get(key).is_some()
    // }

}

}
