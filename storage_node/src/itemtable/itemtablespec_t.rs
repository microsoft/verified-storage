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

    pub struct DurableItemTableView<I>
    {
        // Maps indexes to their entries. Invalid/empty indexes have no mapping
        item_table: Map<int, DurableItemTableViewEntry<I>>
    }

    impl<I> DurableItemTableView<I>
    {

    }
}
