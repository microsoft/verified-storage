#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use core::hash::Hash;
use std::collections::HashMap;
use vstd::prelude::*;

verus! {

#[verifier::ext_equal]
#[verifier::reject_recursive_types(Key)]
#[verifier::reject_recursive_types(Value)]
#[verifier::external_body]
pub struct MyHashMap<Key, Value> where Key: Eq + Hash {
    m: HashMap<Key, Value>,
}

impl<Key, Value> View for MyHashMap<Key, Value> where Key: Eq + Hash {
    type V = Map<Key, Value>;

    closed spec fn view(&self) -> Self::V;
}

impl<Key, Value> MyHashMap<Key, Value> where Key: Eq + Hash {
    #[verifier::external_body]
    pub fn new() -> (result: Self)
        ensures
            result@ == Map::<Key, Value>::empty(),
    {
        Self { m: HashMap::new() }
    }

    #[verifier::external_body]
    pub fn with_capacity(capacity: usize) -> (result: Self)
        ensures
            result@ == Map::<Key, Value>::empty(),
    {
        Self { m: HashMap::with_capacity(capacity) }
    }

    #[verifier::external_body]
    pub fn reserve(&mut self, additional: usize)
        ensures
            self@ == old(self)@,
    {
        self.m.reserve(additional);
    }

    pub open spec fn spec_len(&self) -> usize;

    #[verifier::external_body]
    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (result: usize)
        ensures
            result == self@.len(),
    {
        self.m.len()
    }

    #[verifier::external_body]
    pub fn insert(&mut self, k: Key, v: Value)
        ensures
            self@ == old(self)@.insert(k, v),
    {
        self.m.insert(k, v);
    }

    #[verifier::external_body]
    pub fn remove(&mut self, k: &Key) -> (result: Option<Value>)
        ensures
            self@ == old(self)@.remove(*k),
            match result {
                Some(v) => old(self)@.contains_key(*k) && old(self)@[*k] == v,
                None => !old(self)@.contains_key(*k),
            },
    {
        self.m.remove(k)
    }

    #[verifier::external_body]
    pub fn contains_key(&self, k: &Key) -> (result: bool)
        ensures
            result == self@.contains_key(*k),
    {
        self.m.contains_key(k)
    }

    #[verifier::external_body]
    pub fn get<'a>(&'a self, k: &Key) -> (result: Option<&'a Value>)
        ensures
            match result {
                Some(v) => self@.contains_key(*k) && *v == self@[*k],
                None => !self@.contains_key(*k),
            },
    {
        self.m.get(k)
    }

    #[verifier::external_body]
    pub fn clear(&mut self)
        ensures
            self@ == Map::<Key, Value>::empty(),
    {
        self.m.clear()
    }

    #[verifier::external_body]
    pub fn keys(&self) -> (result: Vec<&Key>)
        ensures
            forall |k: &Key| #[trigger] result@.contains(k) ==> self@.dom().contains(*k),
            forall |k: Key| self@.dom().contains(k) ==> exists |kr: &Key| result@.contains(kr) && *kr == k,
    {
        self.m.keys().collect()
    }
            
}

pub broadcast proof fn axiom_hash_map_with_view_spec_len<Key, Value>(
    m: &MyHashMap<Key, Value>,
) where Key: View + Eq + Hash
    ensures
        #[trigger] m.spec_len() == m@.len(),
{
    admit();
}

} // verus!
