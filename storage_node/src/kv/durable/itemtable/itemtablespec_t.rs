use crate::pmem::wrpm_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

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
        crc: u64,
        item: I,
    }

    impl<I> DurableItemTableViewEntry<I>
    {
        pub closed spec fn new(crc: u64, item: I) -> Self
        {
            Self {
                crc,
                item
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
    }

    pub struct DurableItemTableView<I>
    {
        // Maps indexes to their entries. Invalid/empty indexes have no mapping
        item_table: Map<int, DurableItemTableViewEntry<I>>
    }

    impl<I> DurableItemTableView<I>
    {
        pub closed spec fn init() -> Self
        {
            Self {
                item_table: Map::empty()
            }
        }

        pub closed spec fn new(item_table: Map<int, DurableItemTableViewEntry<I>>) -> Self
        {
            Self {
                item_table
            }
        }

        pub closed spec fn spec_index(self, index: int) -> Option<DurableItemTableViewEntry<I>>
        {
            if self.item_table.contains_key(index)
            {
                Some(self.item_table[index])
            } else {
                None
            }
        }

        // In the spec, we allow inserts that overwrite an existing entry
        // TODO: should we change that? the exec impl doesn't do this
        pub closed spec fn insert(self, index: int, entry: DurableItemTableViewEntry<I>) -> Self
        {
           Self { item_table: self.item_table.insert(index, entry) }
        }

        // TODO: return error if the index is not present?
        pub closed spec fn remove(self, index: int) -> Self
        {
            Self { item_table: self.item_table.remove(index) }
        }
    }
}
