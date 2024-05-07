use crate::kv::kvimpl_t::*;
use crate::pmem::wrpm_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

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

    // TODO: think about what this should actually be, might need a few layers
    #[verifier::reject_recursive_types(K)]
    pub struct DurableListView<K, L, E>
    {
        list: Map<K, Seq<DurableListElementView<L>>>,
        _phantom: Option<E>
    }

    impl<K, L, E> DurableListView<K, L, E>
        where
            K: std::fmt::Debug,
            E: std::fmt::Debug
    {
        pub closed spec fn spec_index(self, key: K) -> Option<Seq<DurableListElementView<L>>>
        {
            if self.list.contains_key(key) {
                Some(self.list[key])
            } else {
                None
            }
        }

        pub closed spec fn insert_key(self, key: K) -> Result<Self, KvError<K, E>>
        {
            if self.list.contains_key(key) {
                Err(KvError::KeyAlreadyExists)
            } else {
                Ok(Self {
                    list: self.list.insert(key, Seq::empty()),
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
            if !self.list.contains_key(key) {
                Err(KvError::KeyNotFound)
            } else if index < 0 || index > self.list[key].len() {
                Err(KvError::IndexOutOfRange)
            } else {
                let new_list = self.list[key].update(index, DurableListElementView { crc, list_element });
                Ok(Self {
                    list: self.list.insert(key, new_list),
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
            if !self.list.contains_key(key) {
                Err(KvError::KeyNotFound)
            } else {
                let new_list = self.list[key].push(DurableListElementView { crc, list_element });
                Ok(Self {
                    list: self.list.insert(key, new_list),
                    _phantom: None
                })
            }
        }

        pub closed spec fn remove_key(
            self,
            key: K
        ) -> Result<Self, KvError<K, E>>
        {
            if !self.list.contains_key(key) {
                Err(KvError::KeyNotFound)
            } else {
                Ok(Self {
                    list: self.list.remove(key),
                    _phantom: None
                })
            }
        }

        pub closed spec fn trim_list(
            self,
            key: K,
            trim_length: int
        ) -> Result<Self, KvError<K, E>>
        {
            if !self.list.contains_key(key) {
                Err(KvError::KeyNotFound)
            } else {
                let new_list = self.list[key].subrange(trim_length, self.list[key].len() as int);
                Ok(Self {
                    list: self.list.insert(key, new_list),
                    _phantom: None
                })
            }
        }
    }
}
