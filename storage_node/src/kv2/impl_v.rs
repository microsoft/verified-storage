#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::align_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use super::items::*;
use super::keys::*;
use super::lists::*;
use super::recover_v::*;
use super::spec_t::*;
use std::hash::Hash;

verus! {

pub(super) enum KvStoreStatus
{
    Quiescent,
    MustAbort,
    ComponentsDontCorrespond,
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
pub(super) struct UntrustedKvStoreImpl<Perm, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + std::fmt::Debug,
    I: PmCopy + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub(super) status: Ghost<KvStoreStatus>,
    pub(super) sm: Ghost<KvStaticMetadata>,
    pub(super) used_key_slots: Ghost<int>,
    pub(super) used_list_element_slots: Ghost<int>,
    pub(super) used_transaction_operation_slots: Ghost<int>,
    pub(super) journal: Journal<Perm, PM>,
    pub(super) keys: KeyTable<Perm, PM, K>,
    pub(super) items: ItemTable<Perm, PM, I>,
    pub(super) lists: ListTable<Perm, PM, L>,
}

impl<Perm, PM, K, I, L> View for UntrustedKvStoreImpl<Perm, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type V = KvStoreView<K, I, L>;

    open(super) spec fn view(&self) -> KvStoreView<K, I, L>
    {
        KvStoreView {
            ps: self.sm@.setup_parameters().unwrap(),
            used_key_slots: self.used_key_slots@,
            used_list_element_slots: self.used_list_element_slots@,
            used_transaction_operation_slots: self.used_transaction_operation_slots@,
            pm_constants: self.journal@.pm_constants,
            durable: combine_component_snapshots(
                self.lists@.logical_range_gaps_policy,
                self.keys@.durable,
                self.items@.durable,
                self.lists@.durable,
            ),
            tentative: combine_component_snapshots(
                self.lists@.logical_range_gaps_policy,
                self.keys@.tentative.unwrap(),
                self.items@.tentative.unwrap(),
                self.lists@.tentative.unwrap(),
            ),
        }
    }
}

impl<Perm, PM, K, I, L> UntrustedKvStoreImpl<Perm, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub open(super) spec fn pm_constants(self) -> PersistentMemoryConstants
    {
        self.journal@.pm_constants
    }

    pub open(super) spec fn recover(bytes: Seq<u8>) -> Option<RecoveredKvStore<K, I, L>>
    {
        recover_journal_then_kv::<Perm, PM, K, I, L>(bytes)
    }

    pub open(super) spec fn valid(self) -> bool
    {
        &&& self.status@ is Quiescent
        &&& self.inv()
    }

    pub open(super) spec fn spec_space_needed_for_transaction_operation() -> nat
    {
          Journal::<Perm, PM>::spec_journal_entry_overhead()
        + Journal::<Perm, PM>::spec_journal_entry_overhead()
        + Journal::<Perm, PM>::spec_journal_entry_overhead()
        + KeyTableRowMetadata::spec_size_of()
        + u64::spec_size_of()
        + u64::spec_size_of()
        + u64::spec_size_of()
    }

    pub open(super) spec fn spec_space_needed_for_setup(ps: SetupParameters) -> nat
        recommends
            ps.valid(),
    {
        let journal_capacity =
            (ps.max_operations_per_transaction * Self::spec_space_needed_for_transaction_operation()) as nat;
        let journal_end = Journal::<Perm, PM>::spec_space_needed_for_setup(journal_capacity);
        let sm_start = round_up_to_alignment(journal_end as int, KvStaticMetadata::spec_align_of() as int);
        let sm_end = sm_start + KvStaticMetadata::spec_size_of();
        let sm_crc_end = sm_end + u64::spec_size_of();
        let key_table_end = sm_crc_end + KeyTable::<Perm, PM, K>::spec_space_needed_for_setup(ps, sm_crc_end as nat);
        let item_table_end = key_table_end +
                             ItemTable::<Perm, PM, I>::spec_space_needed_for_setup(ps, key_table_end as nat);
        let list_table_end = item_table_end +
                             ListTable::<Perm, PM, L>::spec_space_needed_for_setup(ps, item_table_end as nat);
        list_table_end as nat
    }

    pub exec fn get_keys(&self) -> (result: Result<Vec<K>, KvError>)
        requires
            self.valid(),
        ensures
            match result {
                Ok(keys) => {
                    &&& keys@.to_set() == self@.tentative.get_keys()
                    &&& keys@.no_duplicates()
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(_) => false,
            },
    {
        assert(self@.tentative.get_keys() =~= self.keys@.tentative.unwrap().key_info.dom());
        Ok(self.keys.get_keys(&self.journal))
    }

}

}
