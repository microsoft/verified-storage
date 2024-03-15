#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::paged_kv::durable::durableimpl_v::*;
use crate::paged_kv::pagedkvimpl_t::*;
use crate::paged_kv::pagedkvimpl_v::*;
use crate::paged_kv::volatile::volatileimpl_v::*;
use crate::pmem::pmemspec_t::*;
use std::hash::Hash;

verus! {

    // Since the durable part of the PagedKV is a list of PM regions,
    // we use Seq<Seq<u8>> to determine whether states are crash-consistent.
    pub struct TrustedKvPermission<PM, K, H, P, D, V, E>
        where
            PM: PersistentMemoryRegions,
            K: Hash + Eq + Clone + Serializable<E> + std::fmt::Debug,
            H: Serializable<E> + std::fmt::Debug,
            P: Serializable<E> + LogicalRange + std::fmt::Debug,
            D: DurableKvStore<PM, K, H, P, E>,
            V: VolatileKvIndex<K, E>,
            E: std::fmt::Debug,
    {
        ghost is_state_allowable: spec_fn(Seq<Seq<u8>>) -> bool,
        _phantom:  Ghost<core::marker::PhantomData<(PM, K, H, P, D, V, E)>>
    }

    impl<PM, K, H, P, D, V, E> CheckPermission<Seq<Seq<u8>>> for TrustedKvPermission<PM, K, H, P, D, V, E>
        where
            PM: PersistentMemoryRegions,
            K: Hash + Eq + Clone + Serializable<E> + std::fmt::Debug,
            H: Serializable<E> + std::fmt::Debug,
            P: Serializable<E> + LogicalRange + std::fmt::Debug,
            D: DurableKvStore<PM, K, H, P, E>,
            V: VolatileKvIndex<K, E>,
            E: std::fmt::Debug,
    {
        closed spec fn check_permission(&self, state: Seq<Seq<u8>>) -> bool
        {
            (self.is_state_allowable)(state)
        }
    }

    impl<PM, K, H, P, D, V, E> TrustedKvPermission<PM, K, H, P, D, V, E>
        where
            PM: PersistentMemoryRegions,
            K: Hash + Eq + Clone + Serializable<E> + std::fmt::Debug,
            H: Serializable<E> + std::fmt::Debug,
            P: Serializable<E> + LogicalRange + std::fmt::Debug,
            D: DurableKvStore<PM, K, H, P, E>,
            V: VolatileKvIndex<K, E>,
            E: std::fmt::Debug,
    {
        // methods copied from multilogimpl_t and updated for PagedKV structures

        // This is one of two constructors for `TrustedKvPermission`.
        // It conveys permission to do any update as long as a
        // subsequent crash and recovery can only lead to given
        // abstract state `state`.
        pub proof fn new_one_possibility(kv_id: u128, state: AbstractKvStoreState<K, H, P>) -> (tracked perm: Self)
            ensures
                forall |s| #[trigger] perm.check_permission(s) <==>
                    UntrustedPagedKvImpl::<PM, K, H, P, D, V, E>::recover(s, kv_id) == Some(state)
        {
            Self {
                is_state_allowable: |s| UntrustedPagedKvImpl::<PM, K, H, P, D, V, E>::recover(s, kv_id) == Some(state),
                _phantom: Ghost(spec_phantom_data())
            }
        }

        // This is the second of two constructors for
        // `TrustedKvPermission`.  It conveys permission to do any
        // update as long as a subsequent crash and recovery can only
        // lead to one of two given abstract states `state1` and
        // `state2`.
        pub proof fn new_two_possibilities(
            kv_id: u128,
            state1: AbstractKvStoreState<K, H, P>,
            state2: AbstractKvStoreState<K, H, P>
        ) -> (tracked perm: Self)
            ensures
                forall |s| #[trigger] perm.check_permission(s) <==> {
                    ||| UntrustedPagedKvImpl::<PM, K, H, P, D, V, E>::recover(s, kv_id) == Some(state1)
                    ||| UntrustedPagedKvImpl::<PM, K, H, P, D, V, E>::recover(s, kv_id) == Some(state2)
                }
        {
            Self {
                is_state_allowable: |s| {
                    ||| UntrustedPagedKvImpl::<PM, K, H, P, D, V, E>::recover(s, kv_id) == Some(state1)
                    ||| UntrustedPagedKvImpl::<PM, K, H, P, D, V, E>::recover(s, kv_id) == Some(state2)
                },
                _phantom: Ghost(spec_phantom_data())
            }
        }
    }


    /// An `AbstractKvStoreState` is an abstraction of
    /// an entire `PagedKvStore`.
    /// TODO: Should this be generic over the key/header/page
    /// types used in the kv store, or over their views?
    ///
    /// TODO: what does this annotation mean? Required to verify but not sure why
    #[verifier::reject_recursive_types(K)]
    pub struct AbstractKvStoreState<K, H, P>
    where
        K: Hash + Eq,
        P: LogicalRange,
    {
        pub id: u128,
        pub contents: Map<K, (H, Seq<P>)>
    }

    impl<K, H, P> AbstractKvStoreState<K, H, P>
    where
        K: Hash + Eq,
        P: LogicalRange,
    {
        pub open spec fn create(self, key: K, header: H) -> Self
        {
            Self {
                id: self.id,
                contents: self.contents.insert(key, (header, Seq::empty()))
            }
        }

        pub open spec fn read_header_and_pages(self, key: K) -> Option<(H, Seq<P>)>
        {
            if self.contents.contains_key(key) {
                Some(self.contents[key])
            } else {
                None
            }
        }

        pub open spec fn update_header(self, key: K, new_header: H) -> Self
        {
            let val = self.read_header_and_pages(key);
            match val {
                Some((old_header, pages)) => {
                    Self {
                        id: self.id,
                        contents: self.contents.insert(key, (new_header, pages))
                    }
                }
                None => {
                    self
                }
            }
        }

        pub open spec fn delete(self, key: K) -> Self
        {
            Self {
                id: self.id,
                contents: self.contents.remove(key)
            }
        }

        pub open spec fn get_page_idx_with_start(pages: Seq<P>, start: int) -> Option<int>
            decreases pages.len()
        {
            if pages.len() <= 0 {
                None
            } else if pages[0].spec_start() == start {
                Some(0)
            } else {
                let result = Self::get_page_idx_with_start(pages.subrange(1, pages.len() as int), start);
                match result {
                    Some(val) => Some(1 + val),
                    None => None,
                }
            }
        }

        pub open spec fn get_page_idx_with_end(pages: Seq<P>, end: int) -> Option<int>
            decreases pages.len()
        {
            if pages.len() <= 0 {
                None
            } else if pages[0].spec_end() == end {
                Some(0)
            } else {
                let result = Self::get_page_idx_with_end(pages.subrange(1, pages.len() as int), end);
                match result {
                    Some(val) => Some(1 + val),
                    None => None,
                }
            }
        }

        pub open spec fn find_page_with_logical_range_start(self, key: K, start: int) -> Option<int>
        {
            let val = self.read_header_and_pages(key);
            match val {
                Some((header, pages)) => Self::get_page_idx_with_start(pages, start),
                None => None
            }
        }

        pub open spec fn find_pages_in_logical_range(self, key: K, start: int, end: int) -> Seq<P>
        {
            let val = self.read_header_and_pages(key);
            match val {
                Some((header, pages)) => {
                    let start_idx = Self::get_page_idx_with_start(pages, start);
                    let end_idx = Self::get_page_idx_with_end(pages, end);
                    match (start_idx, end_idx) {
                        (Some(start_idx), Some(end_idx)) => pages.subrange(start_idx, end_idx),
                        _ => Seq::empty()
                    }
                }
                None => Seq::empty()
            }
        }

        pub open spec fn append_page(self, key: K, new_page: P) -> Self {
            let result = self.read_header_and_pages(key);
            match result {
                Some((header, pages)) => {
                    Self {
                        id: self.id,
                        contents: self.contents.insert(key, (header, pages.push(new_page)))
                    }
                }
                None => self
            }
        }

        pub open spec fn append_page_and_update_header(self, key: K, new_page: P, new_header: H) -> Self
        {
            let result = self.read_header_and_pages(key);
            match result {
                Some((header, pages)) => {
                    Self {
                        id: self.id,
                        contents: self.contents.insert(key, (new_header, pages.push(new_page)))
                    }
                }
                None => self
            }
        }

        pub open spec fn update_page(self, key: K, idx: usize, new_page: P) -> Self
        {
            let result = self.read_header_and_pages(key);
            match result {
                Some((header, pages)) => {
                    let pages = pages.update(idx as int, new_page);
                    Self {
                        id: self.id,
                        contents: self.contents.insert(key, (header, pages))
                    }
                }
                None => self
            }
        }

        pub open spec fn update_page_and_header(self, key: K, idx: usize, new_page: P, new_header: H) -> Self
        {
            let result = self.read_header_and_pages(key);
            match result {
                Some((header, pages)) => {
                    let pages = pages.update(idx as int, new_page);
                    Self {
                        id: self.id,
                        contents: self.contents.insert(key, (new_header, pages))
                    }
                }
                None => self
            }
        }

        pub open spec fn trim_pages(self, key: K, trim_length: int) -> Self
        {
            let result = self.read_header_and_pages(key);
            match result {
                Some((header, pages)) => {
                    let pages = pages.subrange(trim_length, pages.len() as int);
                    Self {
                        id: self.id,
                        contents: self.contents.insert(key, (header, pages))
                    }
                }
                None => self
            }
        }

        pub open spec fn trim_pages_and_update_header(self, key: K, trim_length: int, new_header: H) -> Self
        {
            let result = self.read_header_and_pages(key);
            match result {
                Some((header, pages)) => {
                    let pages = pages.subrange(trim_length, pages.len() as int);
                    Self {
                        id: self.id,
                        contents: self.contents.insert(key, (new_header, pages))
                    }
                }
                None => self
            }
        }

        pub open spec fn get_keys(self) -> Set<K>
        {
            self.contents.dom()
        }

    }

}
