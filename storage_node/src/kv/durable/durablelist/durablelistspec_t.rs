use crate::kv::kvimpl_t::*;
use crate::pmem::wrpm_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::kv::durable::itemtable::itemtablespec_t::*;
use crate::kv::durable::metadata::layout_v::*;

verus! {
    pub struct TrustedListPermission
    {
        // TODO: how many regions will this use? Probably just one?
        ghost is_state_allowable: spec_fn(Seq<Seq<u8>>) -> bool
    }

    impl CheckPermission<Seq<Seq<u8>>> for TrustedListPermission
    {
        closed spec fn check_permission(&self, state: Seq<Seq<u8>>) -> bool
        {
            (self.is_state_allowable)(state)
        }
    }

    pub struct DurableListElementView<L>
    {
        crc: u64,
        list_element: L
    }

    impl<L> DurableListElementView<L>
    {
        pub closed spec fn new(crc: u64, list_element: L) -> Self 
        {
            Self { crc, list_element }
        }
    }

    // The `lists` field represents the current contents of the list. It abstracts away the physical 
    // nodes of the unrolled linked list that the list is actually stored in, but it may contain
    // tentatively-appended list elements that are not visible yet.
    #[verifier::reject_recursive_types(K)]
    pub struct DurableListView<K, L, E>
    {
        lists: Map<K, Seq<DurableListElementView<L>>>,
        _phantom: Option<E>
    }

    impl<K, L, E> DurableListView<K, L, E>
        where
            K: std::fmt::Debug,
            E: std::fmt::Debug
    {
        pub closed spec fn spec_index(self, key: K) -> Option<Seq<DurableListElementView<L>>>
        {
            if self.lists.contains_key(key) {
                Some(self.lists[key])
            } else {
                None
            }
        }

        pub closed spec fn init() -> Self 
        {
            Self {
                lists: Map::empty(),
                _phantom: None
            }
        }

        pub closed spec fn new(lists: Map<K, Seq<DurableListElementView<L>>>) -> Self 
        {
            Self {
                lists,
                _phantom: None
            }
        }

        pub closed spec fn insert_key(self, key: K) -> Result<Self, KvError<K, E>>
        {
            if self.lists.contains_key(key) {
                Err(KvError::KeyAlreadyExists)
            } else {
                Ok(Self {
                    lists: self.lists.insert(key, Seq::empty()),
                    _phantom: None
                })
            }
        }

        pub closed spec fn insert_list_element(
            self,
            key: K,
            crc: u64,
            list_element: L,
            index: int
        ) -> Result<Self, KvError<K, E>>
        {
            if !self.lists.contains_key(key) {
                Err(KvError::KeyNotFound)
            } else if index < 0 || index > self.lists[key].len() {
                Err(KvError::IndexOutOfRange)
            } else {
                let new_lists = self.lists[key].update(index, DurableListElementView { crc, list_element });
                Ok(Self {
                    lists: self.lists.insert(key, new_lists),
                    _phantom: None
                })
            }
        }

        pub closed spec fn append_list_element(
            self,
            key: K,
            crc: u64,
            list_element: L
        ) -> Result<Self, KvError<K, E>>
        {
            if !self.lists.contains_key(key) {
                Err(KvError::KeyNotFound)
            } else {
                let new_lists = self.lists[key].push(DurableListElementView { crc, list_element });
                Ok(Self {
                    lists: self.lists.insert(key, new_lists),

                    _phantom: None
                })
            }
        }

        pub closed spec fn remove_key(
            self,
            key: K
        ) -> Result<Self, KvError<K, E>>
        {
            if !self.lists.contains_key(key) {
                Err(KvError::KeyNotFound)
            } else {
                Ok(Self {
                    lists: self.lists.remove(key),
                    _phantom: None
                })
            }
        }

        pub closed spec fn trim_lists(
            self,
            key: K,
            trim_length: int
        ) -> Result<Self, KvError<K, E>>
        {
            if !self.lists.contains_key(key) {
                Err(KvError::KeyNotFound)
            } else {
                let new_lists = self.lists[key].subrange(trim_length, self.lists[key].len() as int);
                Ok(Self {
                    lists: self.lists.insert(key, new_lists),
                    _phantom: None
                })
            }
        }
    }
}
