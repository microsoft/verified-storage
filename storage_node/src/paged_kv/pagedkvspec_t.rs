#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::paged_kv::interface_t::*;
use std::hash::Hash;

verus! {

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
        // TODO: spec function for restore, if it makes sense to have one...?
        pub open spec fn restore(self);

        pub open spec fn create(self, key: K, header: H) -> Self
        {
            Self {
                id: self.id,
                contents: self.contents.insert(key, (header, Seq::empty()))
            }
        }

        pub open spec fn read_header(self, key: K) -> Option<H>
        {
            if self.contents.contains_key(key) {
                let (header, pages) = self.contents[key];
                Some(header)
            } else {
                None
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

        pub open spec fn read_pages(self, key: K) -> Option<Seq<P>>
        {
            if self.contents.contains_key(key) {
                let (header, pages) = self.contents[key];
                Some(pages)
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
            let val = self.read_pages(key);
            match val {
                Some(pages) => Self::get_page_idx_with_start(pages, start),
                None => None
            }
        }

        pub open spec fn find_pages_in_logical_range(self, key: K, start: int, end: int) -> Seq<P>
        {
            let val = self.read_pages(key);
            match val {
                Some(pages) => {
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
