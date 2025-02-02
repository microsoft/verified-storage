#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use deps_hack::PmCopy;
use std::collections::HashMap;
use std::hash::Hash;
use super::*;
use super::spec_v::*;
use super::super::impl_t::*;
use super::super::spec_t::*;

verus! {

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub struct KeyRecoveryMapping<K>
    where
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
{
    pub row_info: Map<u64, Option<(K, KeyTableRowMetadata)>>,
    pub key_info: Map<K, u64>,
    pub item_info: Map<u64, u64>,
    pub list_info: Map<u64, u64>,
}

impl<K> KeyRecoveryMapping<K>
    where
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
{
    pub(super) open spec fn new(s: Seq<u8>, sm: KeyTableStaticMetadata) -> Option<Self>
    {
        if exists|mapping: Self| mapping.corresponds(s, sm) {
            Some(choose|mapping: KeyRecoveryMapping<K>| mapping.corresponds(s, sm))
        }
        else {
            None
        }
    }

    pub(super) open spec fn new_empty(tm: TableMetadata) -> Self
    {
        let row_info = Map::<u64, Option<(K, KeyTableRowMetadata)>>::new(
            |addr: u64| tm.validate_row_addr(addr),
            |addr: u64| None,
        );
        Self{
            row_info,
            key_info: Map::<K, u64>::empty(),
            item_info: Map::<u64, u64>::empty(),
            list_info: Map::<u64, u64>::empty(),
        }
    }
    
    pub(super) open spec fn row_info_corresponds(self, s: Seq<u8>, sm: KeyTableStaticMetadata) -> bool
    {
        &&& forall|row_addr: u64| sm.table.validate_row_addr(row_addr) ==> #[trigger] self.row_info.contains_key(row_addr)
        &&& forall|row_addr: u64| #[trigger] self.row_info.contains_key(row_addr) ==>
            {
                let cdb = recover_cdb(s, row_addr + sm.row_cdb_start);
                &&& sm.table.validate_row_addr(row_addr)
                &&& match self.row_info[row_addr] {
                    None => cdb == Some(false),
                    Some((k, rm)) => {
                        &&& cdb == Some(true)
                        &&& recover_object::<K>(s, row_addr + sm.row_key_start,
                                                row_addr + sm.row_key_crc_start as u64) == Some(k)
                        &&& recover_object::<KeyTableRowMetadata>(s, row_addr + sm.row_metadata_start,
                                                                 row_addr + sm.row_metadata_crc_start) == Some(rm)
                        &&& self.key_info.contains_key(k)
                        &&& self.key_info[k] == row_addr
                        &&& self.item_info.contains_key(rm.item_addr)
                        &&& self.item_info[rm.item_addr] == row_addr
                        &&& rm.list_addr != 0 ==> self.list_info.contains_key(rm.list_addr)
                        &&& rm.list_addr != 0 ==> self.list_info[rm.list_addr] == row_addr
                    },
                }
            }
    }

    pub(super) open spec fn key_info_corresponds(self) -> bool
    {
        forall|k: K| #![trigger self.row_info.contains_key(self.key_info[k])]
            self.key_info.contains_key(k) ==> {
                let row_addr = self.key_info[k];
                &&& self.row_info.contains_key(row_addr)
                &&& self.row_info[row_addr] matches Some((k2, _))
                &&& k2 == k
            }
    }

    pub(super) open spec fn item_info_corresponds(self) -> bool
    {
        forall|item_addr: u64| #![trigger self.row_info.contains_key(self.item_info[item_addr])]
            self.item_info.contains_key(item_addr) ==> {
                let row_addr = self.item_info[item_addr];
                &&& self.row_info.contains_key(row_addr)
                &&& self.row_info[row_addr] matches Some((_, rm))
                &&& rm.item_addr == item_addr
            }
    }

    pub(super) open spec fn list_info_corresponds(self) -> bool
    {
        &&& !self.list_info.contains_key(0)
        &&& forall|list_addr: u64| #![trigger self.row_info.contains_key(self.list_info[list_addr])]
               self.list_info.contains_key(list_addr) ==> {
                   let row_addr = self.list_info[list_addr];
                   &&& self.row_info.contains_key(row_addr)
                   &&& self.row_info[row_addr] matches Some((_, rm))
                   &&& rm.list_addr == list_addr
               }
    }

    pub(super) open spec fn corresponds(self, s: Seq<u8>, sm: KeyTableStaticMetadata) -> bool
    {
        &&& self.row_info_corresponds(s, sm)
        &&& self.key_info_corresponds()
        &&& self.item_info_corresponds()
        &&& self.list_info_corresponds()
    }

    pub(super) open spec fn as_snapshot(self: KeyRecoveryMapping<K>) -> KeyTableSnapshot<K>
    {
        KeyTableSnapshot::<K>{
            key_info: Map::<K, KeyTableRowMetadata>::new(
                |k: K| self.key_info.contains_key(k) && self.row_info.contains_key(self.key_info[k]),
                |k: K| self.row_info[self.key_info[k]].unwrap().1,
            ),
            item_info: Map::<u64, K>::new(
                |item_addr: u64| self.item_info.contains_key(item_addr)
                                 && self.row_info.contains_key(self.item_info[item_addr]),
                |item_addr: u64| self.row_info[self.item_info[item_addr]].unwrap().0,
            ),
            list_info: Map::<u64, K>::new(
                |list_addr: u64| self.list_info.contains_key(list_addr)
                                 && self.row_info.contains_key(self.list_info[list_addr]),
                |list_addr: u64| self.row_info[self.list_info[list_addr]].unwrap().0,
            ),
        }
    }
    
    pub(super) proof fn lemma_uniqueness(self, other: Self, s: Seq<u8>, sm: KeyTableStaticMetadata)
        requires
            self.corresponds(s, sm),
            other.corresponds(s, sm),
        ensures
            self.as_snapshot() == other.as_snapshot(),
    {
        let ss = self.as_snapshot();
        let os = other.as_snapshot();

        assert(ss.key_info =~= os.key_info) by {
            assert forall|k: K| #[trigger] ss.key_info.contains_key(k) implies
                       os.key_info.contains_key(k) && os.key_info[k] == ss.key_info[k] by {
                assert(self.row_info.contains_key(self.key_info[k]));
                assert(other.row_info.contains_key(self.key_info[k]));
            }
            assert forall|k: K| #[trigger] os.key_info.contains_key(k) implies
                           ss.key_info.contains_key(k) && ss.key_info[k] == os.key_info[k] by {
                assert(other.row_info.contains_key(other.key_info[k]));
                assert(self.row_info.contains_key(other.key_info[k]));
            }
        }

        assert(ss.item_info =~= os.item_info) by {
            assert forall|item_addr: u64| #[trigger] ss.item_info.contains_key(item_addr) implies
                       os.item_info.contains_key(item_addr) && os.item_info[item_addr] == ss.item_info[item_addr] by {
                assert(self.row_info.contains_key(self.item_info[item_addr]));
                assert(other.row_info.contains_key(self.item_info[item_addr]));
            }
            assert forall|item_addr: u64| #[trigger] os.item_info.contains_key(item_addr) implies
                       ss.item_info.contains_key(item_addr) && ss.item_info[item_addr] == os.item_info[item_addr] by {
                assert(other.row_info.contains_key(other.item_info[item_addr]));
                assert(self.row_info.contains_key(other.item_info[item_addr]));
            }
        }

        assert(ss.list_info =~= os.list_info) by {
            assert forall|list_addr: u64| #[trigger] ss.list_info.contains_key(list_addr) implies
                       os.list_info.contains_key(list_addr) && os.list_info[list_addr] == ss.list_info[list_addr] by {
                assert(self.row_info.contains_key(self.list_info[list_addr]));
                assert(other.row_info.contains_key(self.list_info[list_addr]));
            }
            assert forall|list_addr: u64| #[trigger] os.list_info.contains_key(list_addr) implies
                       ss.list_info.contains_key(list_addr) && ss.list_info[list_addr] == os.list_info[list_addr] by {
                assert(other.row_info.contains_key(other.list_info[list_addr]));
                assert(self.row_info.contains_key(other.list_info[list_addr]));
            }
        }

        assert(ss =~= os);
    }

    pub(super) proof fn lemma_corresponds_implies_equals_new(self, s: Seq<u8>, sm: KeyTableStaticMetadata)
        requires
            self.corresponds(s, sm),
        ensures
            Self::new(s, sm) matches Some(mapping) && mapping.as_snapshot() == self.as_snapshot(),
    {
        self.lemma_uniqueness(Self::new(s, sm).unwrap(), s, sm);
    }
}

impl<PM, K> KeyTable<PM, K>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub proof fn lemma_recover_depends_only_on_my_area(
        s1: Seq<u8>,
        s2: Seq<u8>,
        sm: KeyTableStaticMetadata,
    )
        requires
            sm.valid::<K>(),
            sm.end() <= s1.len(),
            seqs_match_in_range(s1, s2, sm.start() as int, sm.end() as int),
            Self::recover(s1, sm) is Some,
        ensures
            Self::recover(s1, sm) == Self::recover(s2, sm),
    {
        let mapping1 = KeyRecoveryMapping::<K>::new(s1, sm).unwrap();
        assert(mapping1.corresponds(s2, sm)) by {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            broadcast use group_validate_row_addr;
        }
        mapping1.lemma_corresponds_implies_equals_new(s2, sm);
    }
    
}

}
