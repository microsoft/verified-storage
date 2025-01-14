#![allow(unused_imports)]

pub mod abort_v;
pub mod commit_v;
pub mod crud_v;
pub mod impl_t;
pub mod impl_v;
pub mod inv_v;
pub mod items;
pub mod keys;
pub mod lists;
pub mod recover_v;
pub mod setup_v;
pub mod spec_t;
pub mod start_v;
pub mod util_v;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::seq::*;

use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use std::hash::Hash;
use impl_t::*;
use impl_v::*;
use inv_v::*;
use items::*;
use keys::*;
use lists::*;
use recover_v::*;
use setup_v::*;
use spec_t::*;

verus! {

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
pub struct UntrustedKvStoreImpl<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + std::fmt::Debug,
    I: PmCopy + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    status: Ghost<KvStoreStatus>,
    id: u128,
    sm: Ghost<KvStaticMetadata>,
    journal: Journal<TrustedKvPermission, PM>,
    keys: KeyTable<PM, K>,
    items: ItemTable<PM, I>,
    lists: ListTable<PM, L>,
}

impl<PM, K, I, L> View for UntrustedKvStoreImpl<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type V = KvStoreView<K, I, L>;

    closed spec fn view(&self) -> KvStoreView<K, I, L>
    {
        KvStoreView {
            id: self.id,
            logical_range_gaps_policy: self.lists@.logical_range_gaps_policy,
            pm_constants: self.journal@.pm_constants,
            durable: combine_component_snapshots(
                self.id,
                self.lists@.logical_range_gaps_policy,
                self.keys@.durable,
                self.items@.durable,
                self.lists@.durable,
            ),
            tentative: combine_component_snapshots(
                self.id,
                self.lists@.logical_range_gaps_policy,
                self.keys@.tentative.unwrap(),
                self.items@.tentative.unwrap(),
                self.lists@.tentative.unwrap(),
            ),
        }
    }
}

impl<PM, K, I, L> UntrustedKvStoreImpl<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub closed spec fn pm_constants(self) -> PersistentMemoryConstants
    {
        self.journal@.pm_constants
    }

    pub closed spec fn untrusted_recover(bytes: Seq<u8>) -> Option<AtomicKvStore<K, I, L>>
    {
        recover_journal_then_kv::<PM, K, I, L>(bytes)
    }

    pub closed spec fn valid(self) -> bool
    {
        &&& self.status@ is Quiescent
        &&& self.inv()
    }

    pub closed spec fn spec_space_needed_for_journal_capacity(ps: SetupParameters) -> nat
        where
            PM: PersistentMemoryRegion,
            L: PmCopy,
    {
        let bytes_per_operation =
            Journal::<TrustedKvPermission, PM>::spec_journal_entry_overhead() * 4
            + L::spec_size_of()
            + u64::spec_size_of() * 8;
        (ps.max_operations_per_transaction * bytes_per_operation) as nat
    }
    
    pub closed spec fn spec_space_needed_for_setup(ps: SetupParameters) -> nat
        recommends
            ps.valid(),
    {
        let journal_capacity = Self::spec_space_needed_for_journal_capacity(ps);
        let journal_end = Journal::<TrustedKvPermission, PM>::spec_space_needed_for_setup(journal_capacity);
        let sm_start = round_up_to_alignment(journal_end as int, KvStaticMetadata::spec_align_of() as int);
        let sm_end = sm_start + KvStaticMetadata::spec_size_of();
        let sm_crc_end = sm_end + u64::spec_size_of();
        let key_table_end = sm_crc_end + KeyTable::<PM, K>::spec_space_needed_for_setup(ps, sm_crc_end as nat);
        let item_table_end = key_table_end + ItemTable::<PM, I>::spec_space_needed_for_setup(ps, key_table_end as nat);
        let list_table_end = item_table_end + ListTable::<PM, L>::spec_space_needed_for_setup(ps, item_table_end as nat);
        list_table_end as nat
    }

}

}
