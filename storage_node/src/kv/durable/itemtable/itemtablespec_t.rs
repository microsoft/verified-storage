use crate::pmem::wrpm_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::kv::kvimpl_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::kv::durable::oplog::oplogspec_t::*;
use crate::kv::durable::util_v::*;

verus! {
    pub struct TrustedItemTablePermission
    {
        // The durable item table uses only one PM region
        ghost is_state_allowable: spec_fn(Seq<u8>) -> bool
    }

    impl CheckPermission<Seq<u8>> for TrustedItemTablePermission
    {
        closed spec fn check_permission(&self, state: Seq<u8>) -> bool
        {
            (self.is_state_allowable)(state)
        }
    }

    #[verifier::ext_equal]
    pub struct DurableItemTableView<I>
    {
        pub durable_item_table: Seq<Option<I>>,
        pub outstanding_item_table: Seq<Option<I>>,
    }

    impl<I> DurableItemTableView<I>
    {
        pub open spec fn init(num_keys: int) -> Self
        {
            Self {
                durable_item_table: Seq::new(num_keys as nat, |i: int| None),
                outstanding_item_table: Seq::new(num_keys as nat, |i: int| None),
            }
        }

        pub open spec fn new(item_table: Seq<Option<I>>) -> Self
        {
            Self {
                durable_item_table: item_table,
                outstanding_item_table: Seq::new(item_table.len(), |i: int| None),
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
}
