#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use std::hash::Hash;
use super::listrecover_v::*;
use crate::common::table_v::*;
use super::super::kvspec_t::*;

verus! {

#[verifier::ext_equal]
pub struct ListTableSnapshot<L>
{
    pub m: Map<u64, Seq<L>>, // always maps the null address (0) to the empty sequence
}

impl<L> ListTableSnapshot<L>
{
    pub open spec fn init() -> Self
    {
        Self{ m: Map::<u64, Seq<L>>::empty() }
    }
}

#[verifier::ext_equal]
pub struct ListTableView<L>
{
    pub durable: ListTableSnapshot<L>,
    pub tentative: ListTableSnapshot<L>,
}

#[verifier::ext_equal]
pub struct ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    m: Map<u64, Vec<L>>,
    phantom: Ghost<core::marker::PhantomData<PM>>,
}

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub closed spec fn recover(
        s: Seq<u8>,
        addrs: Set<u64>,
        sm: ListTableStaticMetadata,
    ) -> Option<ListTableSnapshot<L>>
    {
        recover_lists::<L>(s, addrs, sm)
    }

    pub closed spec fn spec_setup_end(ps: SetupParameters, min_start: nat) -> nat
    {
        arbitrary()
    }

    pub exec fn setup_end(ps: &SetupParameters, min_start: &OverflowingU64) -> (result: OverflowingU64)
        ensures
            result@ == Self::spec_setup_end(*ps, min_start@),
            min_start@ <= result@,
    {
        assume(false);
        OverflowingU64::new(0)
    }

    pub exec fn setup<K>(
        pm: &mut PM,
        ps: &SetupParameters,
        min_start: u64,
        max_end: u64,
    ) -> (result: Result<ListTableStaticMetadata, KvError<K>>)
        where
            K: std::fmt::Debug,
        requires
            old(pm).inv(),
            ps.valid(),
            min_start <= max_end <= old(pm)@.len(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            pm@.len() == old(pm)@.len(),
            match result {
                Ok(sm) => {
                    &&& Self::recover(pm@.read_state, Set::<u64>::empty(), sm) == Some(ListTableSnapshot::<L>::init())
                    &&& seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.table.start as int,
                                                 sm.table.end as int)
                    &&& sm.valid()
                    &&& sm.consistent_with_type::<L>()
                    &&& min_start <= sm.table.start
                    &&& sm.table.start <= sm.table.end
                    &&& sm.table.end <= max_end
                    &&& sm.table.end == Self::spec_setup_end(*ps, min_start as nat)
                    &&& sm.table.num_rows == ps.num_keys
                },
                Err(KvError::OutOfSpace) => max_end < Self::spec_setup_end(*ps, min_start as nat),
                _ => false,
            },
    {
        assume(false);
        Err(KvError::OutOfSpace)
    }

    pub proof fn lemma_recover_depends_only_on_my_area(
        s1: Seq<u8>,
        s2: Seq<u8>,
        addrs: Set<u64>,
        sm: ListTableStaticMetadata,
    )
        requires
            sm.valid(),
            sm.consistent_with_type::<L>(),
            sm.table.end <= s1.len(),
            seqs_match_in_range(s1, s2, sm.table.start as int, sm.table.end as int),
            Self::recover(s1, addrs, sm) is Some,
        ensures
            Self::recover(s1, addrs, sm) == Self::recover(s2, addrs, sm),
    {
        assume(false);
    }
}

}
