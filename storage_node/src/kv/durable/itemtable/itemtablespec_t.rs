use crate::pmem::wrpm_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::kv::kvimpl_t::*;
use crate::pmem::pmemspec_t::*;
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

    pub struct DurableItemTableViewEntry<I, K>
    {
        valid: bool,
        crc: u64, // TODO: do we need this?
        item: I,
        key: K,
    }

    impl<I, K> DurableItemTableViewEntry<I, K>
    {
        pub closed spec fn new(valid: u64, crc: u64, item: I, key: K) -> Self
        {
            Self {
                valid: valid == CDB_TRUE,
                crc,
                item,
                key
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

        pub closed spec fn get_key(self) -> K
        {
            self.key
        }

        pub closed spec fn valid(self) -> bool 
        {
            self.valid
        }
    }

    pub struct DurableItemTableView<I, K, E>
        where
            K: std::fmt::Debug,
            E: std::fmt::Debug,
    {
        item_table: Seq<DurableItemTableViewEntry<I, K>>,
        _phantom: Option<E>
    }

    impl<I, K, E> DurableItemTableView<I, K, E>
        where
            K: std::fmt::Debug,
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
                        // it doesn't matter what key and item are because the 
                        // entry is invalid
                        item: arbitrary(),
                        key: arbitrary()
                    }
                ),
                _phantom: None
            }
        }

        pub closed spec fn new(item_table: Seq<DurableItemTableViewEntry<I, K>>) -> Self
        {
            Self {
                item_table,
                _phantom: None
            }
        }

        pub closed spec fn spec_index(self, index: int) -> Option<DurableItemTableViewEntry<I, K>>
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
        pub closed spec fn insert(self, index: int, crc: u64, item: I, key: K) -> Result<Self, KvError<K, E>> 
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
                                key,
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
                            item: old_entry.item,
                            key: old_entry.key
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
                            item: old_entry.item,
                            key: old_entry.key
                        }
                    ),
                    _phantom: None
                })
            }
        }

        pub closed spec fn replay_log_item_table(
            self,
            op_log: Seq<OpLogEntryType>
        ) -> Option<Self>
            decreases op_log.len()
        {
            if op_log.len() == 0 {
                Some(self)
            } else {
                let current_op = op_log[0];
                let op_log = op_log.drop_first();
                let item_table_view = self.apply_log_op_to_item_table(current_op);
                if item_table_view is None {
                    None
                } else {
                    item_table_view.unwrap().replay_log_item_table(op_log)
                }
            }
        }

        pub closed spec fn apply_log_op_to_item_table(
            self,
            op: OpLogEntryType,
        ) -> Option<Self> 
        {
            match op {
                OpLogEntryType::ItemTableEntryCommit { table_index } => {
                    let res = self.commit_entry(table_index as int);
                    match res {
                        Ok(table_view) => Some(table_view),
                        Err(_)=> None
                    }
                }
                OpLogEntryType::ItemTableEntryInvalidate { table_index} => {
                    let res = self.invalidate_entry(table_index as int);
                    match res {
                        Ok(table_view) => Some(table_view),
                        Err(_)=> None
                    }
                }
                _ => Some(self) // other ops leave the item table unchanged
            }
        }
    }
}
