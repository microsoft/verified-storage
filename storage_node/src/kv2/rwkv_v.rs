#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use std::hash::Hash;
use super::concurrentspec_t::*;
use super::impl_v::*;
use super::spec_t::*;
use vstd::pcm::*;
use vstd::rwlock::{RwLock, RwLockPredicate};

verus! {

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
struct ConcurrentKvStoreInternal<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    invariant_resource: Tracked<Resource<OwnershipSplitter<K, I, L>>>,
    kv: UntrustedKvStoreImpl<PM, K, I, L>,
}

struct ConcurrentKvStorePredicate
{
    loc: Loc,
    powerpm_id: int,
}

impl<PM, K, I, L> RwLockPredicate<ConcurrentKvStoreInternal<PM, K, I, L>> for ConcurrentKvStorePredicate
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    closed spec fn inv(self, v: ConcurrentKvStoreInternal<PM, K, I, L>) -> bool
    {
        &&& v.kv.valid()
        &&& v.kv@.ps.valid()
        &&& v.kv@.used_key_slots == v.kv@.durable.num_keys()
        &&& v.kv@.used_list_element_slots == v.kv@.durable.num_list_elements()
        &&& v.kv@.used_transaction_operation_slots == 0
        &&& v.kv@.durable == v.kv@.tentative
        &&& v.kv@.ps.logical_range_gaps_policy == v.kv@.durable.logical_range_gaps_policy
        &&& self.loc == v.invariant_resource@.loc()
        &&& self.powerpm_id == v.kv@.powerpm_id
        &&& v.invariant_resource@.value() ==
               OwnershipSplitter::Invariant{ ckv: ConcurrentKvStoreView::from_kvstore_view(v.kv@) }
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
pub struct ConcurrentKvStore<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    loc: Ghost<Loc>,
    lock: RwLock<ConcurrentKvStoreInternal<PM, K, I, L>, ConcurrentKvStorePredicate>,
}

impl<PM, K, I, L> CanRecover<K, I, L> for ConcurrentKvStore<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    closed spec fn recover(s: Seq<u8>) -> Option<RecoveredKvStore<K, I, L>> {
        UntrustedKvStoreImpl::<PM, K, I, L>::recover(s)
    }
}

impl<PM, K, I, L> ConcurrentKvStore<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub closed spec fn valid(self) -> bool
    {
        &&& self.loc@ == self.lock.pred().loc
    }

    pub closed spec fn loc(self) -> Loc
    {
        self.loc@
    }

    pub closed spec fn powerpm_id(self) -> int
    {
        self.lock.pred().powerpm_id
    }

    pub closed spec fn spec_space_needed_for_setup(ps: SetupParameters) -> nat
    {
        UntrustedKvStoreImpl::<PM, K, I, L>::spec_space_needed_for_setup(ps)
    }

    pub closed spec fn spec_space_needed_for_transaction_operation() -> nat
    {
        UntrustedKvStoreImpl::<PM, K, I, L>::spec_space_needed_for_transaction_operation()
    }

    pub exec fn space_needed_for_setup(ps: &SetupParameters) -> (result: Result<u64, KvError>)
        ensures
            match result {
                Ok(v) => v == Self::spec_space_needed_for_setup(*ps),
                Err(KvError::InvalidParameter) => !ps.valid(),
                Err(KvError::OutOfSpace) => Self::spec_space_needed_for_setup(*ps) > u64::MAX,
                Err(_) => false,
            },
    {
        UntrustedKvStoreImpl::<PM, K, I, L>::space_needed_for_setup(ps)
    }

    pub exec fn setup(pm: &mut PM, ps: &SetupParameters) -> (result: Result<(), KvError>)
        requires
            old(pm).inv(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            match result {
                Ok(()) => {
                    &&& pm@.flush_predicted()
                    &&& Self::recover(pm@.durable_state) == Some(RecoveredKvStore::<K, I, L>::init(*ps))
                }
                Err(KvError::InvalidParameter) => !ps.valid(),
                Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
                Err(KvError::OutOfSpace) => pm@.len() < Self::spec_space_needed_for_setup(*ps),
                Err(_) => false,
            }
    {
        UntrustedKvStoreImpl::<PM, K, I, L>::setup(pm, ps)
    }

    pub exec fn start<Perm>(
        powerpm: PoWERPersistentMemoryRegion<PM>,
        kvstore_id: u128,
        Ghost(state): Ghost<RecoveredKvStore<K, I, L>>,
        Tracked(perm): Tracked<&Perm>
    ) -> (result: Result<(Self, Tracked<Resource<OwnershipSplitter::<K, I, L>>>), KvError>)
        where
            Perm: CheckPermission<Seq<u8>>,
        requires 
            powerpm.inv(),
            Self::recover(powerpm@.durable_state) == Some(state),
            vstd::std_specs::hash::obeys_key_model::<K>(),
            perm.id() == powerpm.id(),
            forall |s| #[trigger] perm.check_permission(s) <== Self::recover(s) == Some(state),
        ensures
        ({
            match result {
                Ok((kv, r)) => {
                    &&& kv.valid()
                    &&& kv.loc() == r@.loc()
                    &&& kv.powerpm_id() == powerpm.id()
                    &&& match r@.value() {
                           OwnershipSplitter::Application{ ckv } => {
                               &&& ckv.valid()
                               &&& ckv.ps == state.ps
                               &&& ckv.pm_constants == powerpm.constants()
                               &&& ckv.kv == state.kv
                           },
                           _ => false,
                    }
                },
                Err(KvError::CRCMismatch) => !powerpm.constants().impervious_to_corruption(),
                Err(KvError::WrongKvStoreId{ requested_id, actual_id }) => {
                   &&& requested_id == kvstore_id
                   &&& actual_id == state.ps.kvstore_id
                },
                Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
                Err(_) => false,
            }
        }),
    {
        let kv = match UntrustedKvStoreImpl::<PM, K, I, L>::start::<Perm>(powerpm, kvstore_id, Ghost(state), Tracked(perm)) {
            Ok(kv) => kv,
            Err(e) => { return Err(e); },
        };
        let ghost ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv@);
        let tracked both = Resource::<OwnershipSplitter<K, I, L>>::alloc(OwnershipSplitter::<K, I, L>::Both{ ckv });
        let ghost loc = both.loc();
        let ghost pred = ConcurrentKvStorePredicate{
            loc: loc,
            powerpm_id: kv@.powerpm_id,
        };
        let ghost application_value = OwnershipSplitter::<K, I, L>::Application{ ckv };
        let ghost invariant_value = OwnershipSplitter::<K, I, L>::Invariant{ ckv };
        let tracked split_resources = both.split(application_value, invariant_value);
        let tracked application_resource = split_resources.0;
        let tracked invariant_resource = split_resources.1;
        let kv_internal = ConcurrentKvStoreInternal::<PM, K, I, L>{
            invariant_resource: Tracked(invariant_resource),
            kv
        };
        assert(pred.inv(kv_internal));
        let lock = RwLock::<ConcurrentKvStoreInternal<PM, K, I, L>, ConcurrentKvStorePredicate>::new(
            kv_internal, Ghost(pred)
        );
        let selfish = Self{ loc: Ghost(loc), lock };
        Ok((selfish, Tracked(application_resource)))
    }

    pub exec fn read_item<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<I, KvError>, Tracked<CB::Completion>))
        where
            CB: ReadLinearizer<K, I, L, ReadItemOp<K>>,
        requires 
            self.valid(),
            cb.pre(self.loc(), ReadItemOp{ key: *key }),
        ensures
            self.valid(),
            cb.post(result.1@, self.loc(), ReadItemOp{ key: *key }, result.0),
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = ReadItemOp{ key: *key };
        let kv_internal = read_handle.borrow();
        let result = kv_internal.kv.read_item(key);
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        let tracked mut completion;
        proof {
            completion = cb.apply(op, result, invariant_resource);
        }
        read_handle.release_read();
        (result, Tracked(completion))
    }

    pub exec fn get_keys<CB: ReadLinearizer<K, I, L, GetKeysOp>>(
        &self,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<Vec<K>, KvError>, Tracked<CB::Completion>))
        requires 
            self.valid(),
            cb.pre(self.loc(), GetKeysOp{ }),
        ensures
            self.valid(),
            cb.post(result.1@, self.loc(), GetKeysOp{ }, result.0),
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = GetKeysOp{ };
        let kv_internal = read_handle.borrow();
        let result = kv_internal.kv.get_keys();
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        let tracked mut completion;
        proof {
            completion = cb.apply(op, result, invariant_resource);
        }
        read_handle.release_read();
        (result, Tracked(completion))
    }

    pub exec fn read_item_and_list<CB: ReadLinearizer<K, I, L, ReadItemAndListOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<(I, Vec<L>), KvError>, Tracked<CB::Completion>))
        requires 
            self.valid(),
            cb.pre(self.loc(), ReadItemAndListOp{ key: *key }),
        ensures
            self.valid(),
            cb.post(result.1@, self.loc(), ReadItemAndListOp{ key: *key }, result.0),
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = ReadItemAndListOp{ key: *key };
        let kv_internal = read_handle.borrow();
        let result = kv_internal.kv.read_item_and_list(key);
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        let tracked mut completion;
        proof {
            completion = cb.apply(op, result, invariant_resource);
        }
        read_handle.release_read();
        (result, Tracked(completion))
    }

    pub exec fn read_list<CB: ReadLinearizer<K, I, L, ReadListOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<Vec<L>, KvError>, Tracked<CB::Completion>))
        requires 
            self.valid(),
            cb.pre(self.loc(), ReadListOp{ key: *key }),
        ensures
            self.valid(),
            cb.post(result.1@, self.loc(), ReadListOp{ key: *key }, result.0),
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = ReadListOp{ key: *key };
        let kv_internal = read_handle.borrow();
        let result = kv_internal.kv.read_list(key);
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        let tracked mut completion;
        proof {
            completion = cb.apply(op, result, invariant_resource);
        }
        read_handle.release_read();
        (result, Tracked(completion))
    }

    pub exec fn get_list_length<CB: ReadLinearizer<K, I, L, GetListLengthOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (result: (Result<usize, KvError>, Tracked<CB::Completion>))
        requires 
            self.valid(),
            cb.pre(self.loc(), GetListLengthOp{ key: *key }),
        ensures
            self.valid(),
            cb.post(result.1@, self.loc(), GetListLengthOp{ key: *key }, result.0),
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = GetListLengthOp{ key: *key };
        let kv_internal = read_handle.borrow();
        let result = kv_internal.kv.get_list_length(key);
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        let tracked mut completion;
        proof {
            completion = cb.apply(op, result, invariant_resource);
        }
        read_handle.release_read();
        (result, Tracked(completion))
    }

    pub exec fn create<Perm, CB>(
        &self,
        key: &K,
        item: &I,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            Perm: CheckPermission<Seq<u8>>,
            CB: MutatingLinearizer<Perm, K, I, L, CreateOp<K, I>, Self>,
        requires
            self.valid(),
            old(cb).powerpm_id() == self.powerpm_id(),
            old(cb).pre(self.loc(), CreateOp{ key: *key, item: *item }),
        ensures 
            cb.post(*old(cb), self.loc(), CreateOp{ key: *key, item: *item }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = CreateOp::<K, I>{ key: *key, item: *item };
        let tracked perm = cb.grant_permission(op, kv_internal.invariant_resource.borrow());
        let result = match kv_internal.kv.tentatively_create::<Perm>(key, item, Tracked(perm)) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_ckv = ConcurrentKvStoreView::from_kvstore_view(kv_internal.kv@);
                let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>{ kv: kv_internal.kv@.tentative, ..old_ckv };
                assert(op.result_valid(old_ckv, new_ckv, Ok(())));
                kv_internal.kv.commit::<Perm>(Tracked(perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn update_item<Perm, CB>(
        &self,
        key: &K,
        item: &I,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            Perm: CheckPermission<Seq<u8>>,
            CB: MutatingLinearizer<Perm, K, I, L, UpdateItemOp<K, I>, Self>,
        requires
            self.valid(),
            old(cb).powerpm_id() == self.powerpm_id(),
            old(cb).pre(self.loc(), UpdateItemOp{ key: *key, item: *item }),
        ensures 
            cb.post(*old(cb), self.loc(), UpdateItemOp{ key: *key, item: *item }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = UpdateItemOp::<K, I>{ key: *key, item: *item };
        let tracked perm = cb.grant_permission(op, kv_internal.invariant_resource.borrow());
        let result = match kv_internal.kv.tentatively_update_item::<Perm>(key, item, Tracked(perm)) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_ckv = ConcurrentKvStoreView::from_kvstore_view(kv_internal.kv@);
                let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>{ kv: kv_internal.kv@.tentative, ..old_ckv };
                assert(op.result_valid(old_ckv, new_ckv, Ok(())));
                kv_internal.kv.commit::<Perm>(Tracked(perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn delete<Perm, CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            Perm: CheckPermission<Seq<u8>>,
            CB: MutatingLinearizer<Perm, K, I, L, DeleteOp<K>, Self>,
        requires
            self.valid(),
            old(cb).powerpm_id() == self.powerpm_id(),
            old(cb).pre(self.loc(), DeleteOp{ key: *key }),
        ensures 
            cb.post(*old(cb), self.loc(), DeleteOp{ key: *key }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = DeleteOp::<K>{ key: *key };
        let tracked perm = cb.grant_permission(op, kv_internal.invariant_resource.borrow());
        let result = match kv_internal.kv.tentatively_delete::<Perm>(key, Tracked(perm)) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_ckv = ConcurrentKvStoreView::from_kvstore_view(kv_internal.kv@);
                let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>{ kv: kv_internal.kv@.tentative, ..old_ckv };
                assert(op.result_valid(old_ckv, new_ckv, Ok(())));
                kv_internal.kv.commit::<Perm>(Tracked(perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn append_to_list<Perm, CB>(
        &self,
        key: &K,
        new_list_element: L,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            Perm: CheckPermission<Seq<u8>>,
            CB: MutatingLinearizer<Perm, K, I, L, AppendToListOp<K, L>, Self>,
        requires
            self.valid(),
            old(cb).powerpm_id() == self.powerpm_id(),
            old(cb).pre(self.loc(), AppendToListOp{ key: *key, new_list_element }),
        ensures 
            cb.post(*old(cb), self.loc(), AppendToListOp{ key: *key, new_list_element }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = AppendToListOp::<K, L>{ key: *key, new_list_element };
        let tracked perm = cb.grant_permission(op, kv_internal.invariant_resource.borrow());
        let result = match kv_internal.kv.tentatively_append_to_list::<Perm>(key, new_list_element, Tracked(perm)) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_ckv = ConcurrentKvStoreView::from_kvstore_view(kv_internal.kv@);
                let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>{ kv: kv_internal.kv@.tentative, ..old_ckv };
                assert(op.result_valid(old_ckv, new_ckv, Ok(())));
                kv_internal.kv.commit::<Perm>(Tracked(perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn append_to_list_and_update_item<Perm, CB>(
        &self,
        key: &K,
        new_list_element: L,
        new_item: &I,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            Perm: CheckPermission<Seq<u8>>,
            CB: MutatingLinearizer<Perm, K, I, L, AppendToListAndUpdateItemOp<K, I, L>, Self>,
        requires
            self.valid(),
            old(cb).powerpm_id() == self.powerpm_id(),
            old(cb).pre(self.loc(), AppendToListAndUpdateItemOp{ key: *key, new_list_element, new_item: *new_item }),
        ensures 
            cb.post(*old(cb), self.loc(), AppendToListAndUpdateItemOp{ key: *key, new_list_element, new_item: *new_item }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = AppendToListAndUpdateItemOp::<K, I, L>{ key: *key, new_list_element, new_item: *new_item };
        let tracked perm = cb.grant_permission(op, kv_internal.invariant_resource.borrow());
        let result = match kv_internal.kv.tentatively_append_to_list_and_update_item::<Perm>(key, new_list_element, new_item, Tracked(perm)) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_ckv = ConcurrentKvStoreView::from_kvstore_view(kv_internal.kv@);
                let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>{ kv: kv_internal.kv@.tentative, ..old_ckv };
                assert(op.result_valid(old_ckv, new_ckv, Ok(())));
                kv_internal.kv.commit::<Perm>(Tracked(perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn update_list_element_at_index<Perm, CB>(
        &self,
        key: &K,
        idx: usize,
        new_list_element: L,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            Perm: CheckPermission<Seq<u8>>,
            CB: MutatingLinearizer<Perm, K, I, L, UpdateListElementAtIndexOp<K, L>, Self>,
        requires
            self.valid(),
            old(cb).powerpm_id() == self.powerpm_id(),
            old(cb).pre(self.loc(), UpdateListElementAtIndexOp{ key: *key, idx, new_list_element }),
        ensures 
            cb.post(*old(cb), self.loc(), UpdateListElementAtIndexOp{ key: *key, idx, new_list_element }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = UpdateListElementAtIndexOp::<K, L>{ key: *key, idx, new_list_element };
        let tracked perm = cb.grant_permission(op, kv_internal.invariant_resource.borrow());
        let result = match kv_internal.kv.tentatively_update_list_element_at_index::<Perm>(key, idx, new_list_element, Tracked(perm)) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_ckv = ConcurrentKvStoreView::from_kvstore_view(kv_internal.kv@);
                let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>{ kv: kv_internal.kv@.tentative, ..old_ckv };
                assert(op.result_valid(old_ckv, new_ckv, Ok(())));
                kv_internal.kv.commit::<Perm>(Tracked(perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn update_list_element_at_index_and_item
        <Perm, CB>(
        &self,
        key: &K,
        idx: usize,
        new_list_element: L,
        new_item: &I,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            Perm: CheckPermission<Seq<u8>>,
            CB: MutatingLinearizer<Perm, K, I, L, UpdateListElementAtIndexAndItemOp<K, I, L>, Self>,
        requires
            self.valid(),
            old(cb).powerpm_id() == self.powerpm_id(),
            old(cb).pre(self.loc(), UpdateListElementAtIndexAndItemOp{ key: *key, idx, new_list_element, new_item: *new_item }),
        ensures 
            cb.post(*old(cb), self.loc(), UpdateListElementAtIndexAndItemOp{ key: *key, idx, new_list_element, new_item: *new_item }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = UpdateListElementAtIndexAndItemOp::<K, I, L>{ key: *key, idx, new_list_element,
                                                                     new_item: *new_item };
        let tracked perm = cb.grant_permission(op, kv_internal.invariant_resource.borrow());
        let result = match kv_internal.kv.tentatively_update_list_element_at_index_and_item::<Perm>(
            key, idx, new_list_element, new_item, Tracked(perm)
        ) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_ckv = ConcurrentKvStoreView::from_kvstore_view(kv_internal.kv@);
                let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>{ kv: kv_internal.kv@.tentative, ..old_ckv };
                assert(op.result_valid(old_ckv, new_ckv, Ok(())));
                kv_internal.kv.commit::<Perm>(Tracked(perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn trim_list<Perm, CB>(
        &self,
        key: &K,
        trim_length: usize,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            Perm: CheckPermission<Seq<u8>>,
            CB: MutatingLinearizer<Perm, K, I, L, TrimListOp<K>, Self>,
        requires
            self.valid(),
            old(cb).powerpm_id() == self.powerpm_id(),
            old(cb).pre(self.loc(), TrimListOp{ key : *key, trim_length }),
        ensures 
            cb.post(*old(cb), self.loc(), TrimListOp{ key: *key, trim_length }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = TrimListOp::<K>{ key: *key, trim_length };
        let tracked perm = cb.grant_permission(op, kv_internal.invariant_resource.borrow());
        let result = match kv_internal.kv.tentatively_trim_list::<Perm>(key, trim_length, Tracked(perm)) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_ckv = ConcurrentKvStoreView::from_kvstore_view(kv_internal.kv@);
                let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>{ kv: kv_internal.kv@.tentative, ..old_ckv };
                assert(op.result_valid(old_ckv, new_ckv, Ok(())));
                kv_internal.kv.commit::<Perm>(Tracked(perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn trim_list_and_update_item<Perm, CB>(
        &self,
        key: &K,
        trim_length: usize,
        new_item: &I,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            Perm: CheckPermission<Seq<u8>>,
            CB: MutatingLinearizer<Perm, K, I, L, TrimListAndUpdateItemOp<K, I>, Self>,
        requires
            self.valid(),
            old(cb).powerpm_id() == self.powerpm_id(),
            old(cb).pre(self.loc(), TrimListAndUpdateItemOp{ key : *key, trim_length, new_item: *new_item }),
        ensures 
            cb.post(*old(cb), self.loc(), TrimListAndUpdateItemOp{ key: *key, trim_length, new_item: *new_item }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = TrimListAndUpdateItemOp::<K, I>{ key: *key, trim_length, new_item: *new_item };
        let tracked perm = cb.grant_permission(op, kv_internal.invariant_resource.borrow());
        let result = match kv_internal.kv.tentatively_trim_list_and_update_item::<Perm>(key, trim_length, new_item, Tracked(perm)) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_ckv = ConcurrentKvStoreView::from_kvstore_view(kv_internal.kv@);
                let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>{ kv: kv_internal.kv@.tentative, ..old_ckv };
                assert(op.result_valid(old_ckv, new_ckv, Ok(())));
                kv_internal.kv.commit::<Perm>(Tracked(perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }
}

}
