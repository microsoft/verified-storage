use crate::pmem::wrpm_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::kv::kvimpl_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use crate::kv::durable::oplog::oplogspec_t::*;

verus! {
    pub struct TrustedItemTablePermission
    {
        // The durable item table uses only one PM region
        ghost is_state_allowable: spec_fn(Seq<Seq<u8>>) -> bool
    }

    impl CheckPermission<Seq<Seq<u8>>> for TrustedItemTablePermission
    {
        closed spec fn check_permission(&self, state: Seq<Seq<u8>>) -> bool
        {
            (self.is_state_allowable)(state)
        }
    }

    pub struct DurableItemTableViewEntry<I>
    {
        valid: bool,
        crc: u64, // TODO: do we need this?
        item: I,
    }

    impl<I> DurableItemTableViewEntry<I>
    {
        pub closed spec fn new(valid: u64, crc: u64, item: I) -> Self
        {
            Self {
                valid: valid == CDB_TRUE,
                crc,
                item,
            }
        }

        pub closed spec fn get_crc(self) -> u64
        {
            self.crc
        }

        pub closed spec fn get_item(self) -> I
        {
            self.item
        }

        pub closed spec fn valid(self) -> bool 
        {
            self.valid
        }
    }

    pub struct DurableItemTableView<I, K, E>
        where
            K: std::fmt::Debug + Serializable,
            E: std::fmt::Debug,
    {
        item_table: Seq<DurableItemTableViewEntry<I>>,
        _phantom: Option<(K, E)>
    }

    impl<I, K, E> DurableItemTableView<I, K, E>
        where
            K: std::fmt::Debug + Serializable,
            E: std::fmt::Debug,
    {
        pub closed spec fn init(num_keys: int) -> Self
        {
            Self {
                item_table: Seq::new(
                    num_keys as nat,
                    |i: int| DurableItemTableViewEntry {
                        valid: false,
                        crc: 0,
                        // it doesn't matter what item is because the 
                        // entry is invalid
                        item: arbitrary()
                    }
                ),
                _phantom: None
            }
        }

        pub closed spec fn new(item_table: Seq<DurableItemTableViewEntry<I>>) -> Self
        {
            Self {
                item_table,
                _phantom: None
            }
        }

        pub closed spec fn spec_index(self, index: int) -> Option<DurableItemTableViewEntry<I>>
        {
            if index < 0 || index >= self.len() 
            {
                Some(self.item_table[index])
            } else {
                None
            }
        }

        pub closed spec fn len(self) -> nat 
        {
            self.item_table.len()
        }

        // Inserting an entry and committing it are two separate operations. Inserted entries
        // are invalid until they are explicitly committed. Attempting to insert at an index
        // that already has a valid entry results in an error.
        pub closed spec fn insert(self, index: int, crc: u64, item: I) -> Result<Self, KvError<K, E>> 
        {
            if index < 0 || index >= self.len() {
                Err(KvError::IndexOutOfRange)
            } else if self[index].unwrap().valid() {
                Err(KvError::EntryIsValid)
            } else {
                Ok(Self {
                    item_table: self.item_table.update(
                            index,
                            DurableItemTableViewEntry {
                                valid: false,
                                crc,
                                item,
                            }
                        ),
                        _phantom: None
                    }
                )
            } 
        }

        pub closed spec fn commit_entry(self, index: int) -> Result<Self, KvError<K, E>> 
        {
            if index < 0 || index >= self.len() {
                Err(KvError::IndexOutOfRange)
            } else if self[index].unwrap().valid() {
                Err(KvError::EntryIsValid)
            } else {
                let old_entry = self.item_table[index];
                Ok(Self {
                    item_table: self.item_table.update(
                        index,
                        DurableItemTableViewEntry {
                            valid: true,
                            crc: old_entry.crc,
                            item: old_entry.item
                        }
                    ),
                    _phantom: None
                })
            }
        }

        pub closed spec fn invalidate_entry(self, index: int) -> Result<Self, KvError<K, E>>
        {
            if index < 0 || index >= self.len() {
                Err(KvError::IndexOutOfRange)
            } else if !self[index].unwrap().valid() {
                Err(KvError::EntryIsNotValid)
            } else {
                let old_entry = self.item_table[index];
                Ok(Self {
                    item_table: self.item_table.update(
                        index,
                        DurableItemTableViewEntry {
                            valid: false,
                            crc: old_entry.crc,
                            item: old_entry.item
                        }
                    ),
                    _phantom: None
                })
            }
        }
    }
}
