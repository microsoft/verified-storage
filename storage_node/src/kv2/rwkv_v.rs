#![allow(unused_imports)]
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
use std::io::Read;
use super::*;
use super::concurrentspec_t::*;
use super::impl_v::*;
use super::recover_v::*;
use super::spec_t::*;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::pcm::*;
use vstd::rwlock::{RwLock, RwLockPredicate};

verus! {

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
struct ConcurrentKvStoreInternal<Perm, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    invariant_resource: Tracked<Resource<OwnershipSplitter<K, I, L>>>,
    kv: UntrustedKvStoreImpl<Perm, PM, K, I, L>,
}

struct ConcurrentKvStorePredicate
{
    loc: Loc,
}

impl<Perm, PM, K, I, L> RwLockPredicate<ConcurrentKvStoreInternal<Perm, PM, K, I, L>> for ConcurrentKvStorePredicate
where
    Perm: CheckPermission<Seq<u8>>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    closed spec fn inv(self, v: ConcurrentKvStoreInternal<Perm, PM, K, I, L>) -> bool
    {
        &&& v.kv.valid()
        &&& v.kv@.ps.valid()
        &&& v.kv@.used_key_slots == v.kv@.durable.num_keys()
        &&& v.kv@.used_list_element_slots == v.kv@.durable.num_list_elements()
        &&& v.kv@.used_transaction_operation_slots == 0
        &&& v.kv@.durable == v.kv@.tentative
        &&& v.kv@.ps.logical_range_gaps_policy == v.kv@.durable.logical_range_gaps_policy
        &&& self.loc == v.invariant_resource@.loc()
        &&& v.invariant_resource@.value() ==
               OwnershipSplitter::Invariant{ ckv: ConcurrentKvStoreView::from_kvstore_view(v.kv@) }
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(L)]
pub struct ConcurrentKvStore<Perm, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    loc: Ghost<Loc>,
    lock: RwLock<ConcurrentKvStoreInternal<Perm, PM, K, I, L>, ConcurrentKvStorePredicate>,
}

impl<Perm, PM, K, I, L> CanRecover<K, I, L> for ConcurrentKvStore<Perm, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    closed spec fn recover(s: Seq<u8>) -> Option<RecoveredKvStore<K, I, L>> {
        UntrustedKvStoreImpl::<Perm, PM, K, I, L>::recover(s)
    }
}

impl<Perm, PM, K, I, L> ConcurrentKvStore<Perm, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
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

    pub closed spec fn spec_space_needed_for_setup(ps: SetupParameters) -> nat
    {
        UntrustedKvStoreImpl::<Perm, PM, K, I, L>::spec_space_needed_for_setup(ps)
    }

    pub closed spec fn spec_space_needed_for_transaction_operation() -> nat
    {
        UntrustedKvStoreImpl::<Perm, PM, K, I, L>::spec_space_needed_for_transaction_operation()
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
        UntrustedKvStoreImpl::<Perm, PM, K, I, L>::space_needed_for_setup(ps)
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
        UntrustedKvStoreImpl::<Perm, PM, K, I, L>::setup(pm, ps)
    }

    pub exec fn start(
        wrpm: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        kvstore_id: u128,
        Ghost(state): Ghost<RecoveredKvStore<K, I, L>>,
        Tracked(perm): Tracked<&Perm>
    ) -> (result: Result<(Self, Tracked<Resource<OwnershipSplitter::<K, I, L>>>), KvError>)
        requires 
            wrpm.inv(),
            Self::recover(wrpm@.durable_state) == Some(state),
            vstd::std_specs::hash::obeys_key_model::<K>(),
            forall |s| #[trigger] perm.check_permission(s) <== Self::recover(s) == Some(state),
        ensures
        ({
            match result {
                Ok((kv, r)) => {
                    &&& kv.valid()
                    &&& kv.loc() == r@.loc()
                    &&& match r@.value() {
                           OwnershipSplitter::Application{ ckv } => {
                               &&& ckv.valid()
                               &&& ckv.ps == state.ps
                               &&& ckv.pm_constants == wrpm.constants()
                               &&& ckv.kv == state.kv
                           },
                           _ => false,
                    }
                },
                Err(KvError::CRCMismatch) => !wrpm.constants().impervious_to_corruption(),
                Err(KvError::WrongKvStoreId{ requested_id, actual_id }) => {
                   &&& requested_id == kvstore_id
                   &&& actual_id == state.ps.kvstore_id
                },
                Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
                Err(_) => false,
            }
        }),
    {
        let kv = match UntrustedKvStoreImpl::<Perm, PM, K, I, L>::start(wrpm, kvstore_id, Ghost(state), Tracked(perm)) {
            Ok(kv) => kv,
            Err(e) => { return Err(e); },
        };
        let ghost ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv@);
        let tracked both = Resource::<OwnershipSplitter<K, I, L>>::alloc(OwnershipSplitter::<K, I, L>::Both{ ckv });
        let ghost loc = both.loc();
        let ghost pred = ConcurrentKvStorePredicate{ loc };
        let ghost application_value = OwnershipSplitter::<K, I, L>::Application{ ckv };
        let ghost invariant_value = OwnershipSplitter::<K, I, L>::Invariant{ ckv };
        let tracked split_resources = both.split(application_value, invariant_value);
        let tracked application_resource = split_resources.0;
        let tracked invariant_resource = split_resources.1;
        let kv_internal = ConcurrentKvStoreInternal::<Perm, PM, K, I, L>{
            invariant_resource: Tracked(invariant_resource),
            kv
        };
        assert(pred.inv(kv_internal));
        let lock = RwLock::<ConcurrentKvStoreInternal<Perm, PM, K, I, L>, ConcurrentKvStorePredicate>::new(
            kv_internal, Ghost(pred)
        );
        let selfish = Self{ loc: Ghost(loc), lock };
        Ok((selfish, Tracked(application_resource)))
    }

    pub exec fn read_item<CB>(
        &self,
        key: &K,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<I, KvError>)
        where
            CB: ReadLinearizer<K, I, L, ReadItemOp<K>>,
        requires 
            self.valid(),
            old(cb).pre(self.loc(), ReadItemOp{ key: *key }),
        ensures
            self.valid(),
            cb.post(*old(cb), self.loc(), ReadItemOp{ key: *key }, result),
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = ReadItemOp{ key: *key };
        let kv_internal = read_handle.borrow();
        let result = kv_internal.kv.read_item(key);
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        let tracked apply_result = cb.apply(op, result, invariant_resource);
        read_handle.release_read();
        result
    }

    pub exec fn create<CB>(
        &mut self,
        key: &K,
        item: &I,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            CB: MutatingLinearizer<Perm, K, I, L, CreateOp<K, I>, Self>,
        requires
            old(self).valid(),
            old(cb).pre(old(self).loc(), CreateOp{ key: *key, item: *item }),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            cb.post(*old(cb), self.loc(), CreateOp{ key: *key, item: *item }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = CreateOp::<K, I>{ key: *key, item: *item };
        let tracked perm = cb.grant_permission(op, kv_internal.invariant_resource.borrow());
        let result = match kv_internal.kv.tentatively_create(key, item, Tracked(&perm)) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_ckv = ConcurrentKvStoreView::from_kvstore_view(kv_internal.kv@);
                let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>{ kv: kv_internal.kv@.tentative, ..old_ckv };
                assert(op.result_valid(old_ckv, new_ckv, Ok(())));
                kv_internal.kv.commit(Tracked(&perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn update_item<CB>(
        &mut self,
        key: &K,
        item: &I,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            CB: MutatingLinearizer<Perm, K, I, L, UpdateItemOp<K, I>, Self>,
        requires
            old(self).valid(),
            old(cb).pre(old(self).loc(), UpdateItemOp{ key: *key, item: *item }),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            cb.post(*old(cb), self.loc(), UpdateItemOp{ key: *key, item: *item }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = UpdateItemOp::<K, I>{ key: *key, item: *item };
        let tracked perm = cb.grant_permission(op, kv_internal.invariant_resource.borrow());
        let result = match kv_internal.kv.tentatively_update_item(key, item, Tracked(&perm)) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_ckv = ConcurrentKvStoreView::from_kvstore_view(kv_internal.kv@);
                let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>{ kv: kv_internal.kv@.tentative, ..old_ckv };
                assert(op.result_valid(old_ckv, new_ckv, Ok(())));
                kv_internal.kv.commit(Tracked(&perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }

    /*
    pub exec fn delete<CB: MutatingLinearizer<K, I, L, DeleteOp<K>>>(
        &mut self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (results: (Result<(), KvError>, Tracked<CB::ApplyResult>))
        requires
            old(self).valid(),
            cb.id() == old(self).loc(),
            cb.pre(DeleteOp{ key: *key }),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            ({
                let (exec_result, apply_result) = results;
                let op = DeleteOp{ key: *key };
                cb.post(op, exec_result, apply_result@)
            }),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = DeleteOp::<K>{ key: *key };
        let exec_result = match kv_internal.kv.tentatively_delete(key) {
            Err(e) => Err(e),
            Ok(()) => kv_internal.kv.commit(),
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        let tracked apply_result = cb.apply(op, new_ckv, exec_result, kv_internal.invariant_resource.borrow_mut());
        write_handle.release_write(kv_internal);
        (exec_result, Tracked(apply_result))
    }

    pub exec fn get_keys<CB: ReadLinearizer<K, I, L, GetKeysOp>>(
        &self,
        Tracked(cb): Tracked<CB>,
    ) -> (results: (Result<Vec<K>, KvError>, Tracked<CB::ApplyResult>))
        requires 
            self.valid(),
            cb.id() == self.loc(),
            cb.pre(GetKeysOp{ }),
        ensures
            self.valid(),
            ({
                let (exec_result, apply_result) = results;
                let op = GetKeysOp{ };
                cb.post(op, exec_result, apply_result@)
            })
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = GetKeysOp{ };
        let kv_internal = read_handle.borrow();
        let exec_result = kv_internal.kv.get_keys();
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        let tracked apply_result = cb.apply(op, exec_result, invariant_resource);
        read_handle.release_read();
        (exec_result, Tracked(apply_result))
    }

    pub exec fn read_item_and_list<CB: ReadLinearizer<K, I, L, ReadItemAndListOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (results: (Result<(I, Vec<L>), KvError>, Tracked<CB::ApplyResult>))
        requires 
            self.valid(),
            cb.id() == self.loc(),
            cb.pre(ReadItemAndListOp{ key: *key }),
        ensures
            self.valid(),
            ({
                let (exec_result, apply_result) = results;
                let op = ReadItemAndListOp{ key: *key };
                cb.post(op, exec_result, apply_result@)
            })
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = ReadItemAndListOp{ key: *key };
        let kv_internal = read_handle.borrow();
        let exec_result = kv_internal.kv.read_item_and_list(key);
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        let tracked apply_result = cb.apply(op, exec_result, invariant_resource);
        read_handle.release_read();
        (exec_result, Tracked(apply_result))
    }

    pub exec fn read_list<CB: ReadLinearizer<K, I, L, ReadListOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (results: (Result<Vec<L>, KvError>, Tracked<CB::ApplyResult>))
        requires 
            self.valid(),
            cb.id() == self.loc(),
            cb.pre(ReadListOp{ key: *key }),
        ensures
            self.valid(),
            ({
                let (exec_result, apply_result) = results;
                let op = ReadListOp{ key: *key };
                cb.post(op, exec_result, apply_result@)
            })
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = ReadListOp{ key: *key };
        let kv_internal = read_handle.borrow();
        let exec_result = kv_internal.kv.read_list(key);
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        let tracked apply_result = cb.apply(op, exec_result, invariant_resource);
        read_handle.release_read();
        (exec_result, Tracked(apply_result))
    }

    pub exec fn get_list_length<CB: ReadLinearizer<K, I, L, GetListLengthOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (results: (Result<usize, KvError>, Tracked<CB::ApplyResult>))
        requires 
            self.valid(),
            cb.id() == self.loc(),
            cb.pre(GetListLengthOp{ key: *key }),
        ensures
            self.valid(),
            ({
                let (exec_result, apply_result) = results;
                let op = GetListLengthOp{ key: *key };
                cb.post(op, exec_result, apply_result@)
            })
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = GetListLengthOp{ key: *key };
        let kv_internal = read_handle.borrow();
        let exec_result = kv_internal.kv.get_list_length(key);
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        let tracked apply_result = cb.apply(op, exec_result, invariant_resource);
        read_handle.release_read();
        (exec_result, Tracked(apply_result))
    }

    pub exec fn append_to_list<CB: MutatingLinearizer<K, I, L, AppendToListOp<K, L>>>(
        &mut self,
        key: &K,
        new_list_element: L,
        Tracked(cb): Tracked<CB>,
    ) -> (results: (Result<(), KvError>, Tracked<CB::ApplyResult>))
        requires
            old(self).valid(),
            cb.id() == old(self).loc(),
            cb.pre(AppendToListOp{ key: *key, new_list_element }),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            ({
                let (exec_result, apply_result) = results;
                let op = AppendToListOp{ key: *key, new_list_element };
                cb.post(op, exec_result, apply_result@)
            }),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = AppendToListOp::<K, L>{ key: *key, new_list_element };
        let exec_result = match kv_internal.kv.tentatively_append_to_list(key, new_list_element) {
            Err(e) => Err(e),
            Ok(()) => kv_internal.kv.commit(),
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        let tracked apply_result = cb.apply(op, new_ckv, exec_result, kv_internal.invariant_resource.borrow_mut());
        write_handle.release_write(kv_internal);
        (exec_result, Tracked(apply_result))
    }

    pub exec fn append_to_list_and_update_item<CB: MutatingLinearizer<K, I, L, AppendToListAndUpdateItemOp<K, I, L>>>(
        &mut self,
        key: &K,
        new_list_element: L,
        new_item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (results: (Result<(), KvError>, Tracked<CB::ApplyResult>))
        requires
            old(self).valid(),
            cb.id() == old(self).loc(),
            cb.pre(AppendToListAndUpdateItemOp{ key: *key, new_list_element, new_item: *new_item }),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            ({
                let (exec_result, apply_result) = results;
                let op = AppendToListAndUpdateItemOp{ key: *key, new_list_element, new_item: *new_item };
                cb.post(op, exec_result, apply_result@)
            }),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = AppendToListAndUpdateItemOp::<K, I, L>{ key: *key, new_list_element, new_item: *new_item };
        let exec_result =
            match kv_internal.kv.tentatively_append_to_list_and_update_item(key, new_list_element, new_item) {
            Err(e) => Err(e),
            Ok(()) => kv_internal.kv.commit(),
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        let tracked apply_result = cb.apply(op, new_ckv, exec_result, kv_internal.invariant_resource.borrow_mut());
        write_handle.release_write(kv_internal);
        (exec_result, Tracked(apply_result))
    }

    pub exec fn update_list_element_at_index<CB: MutatingLinearizer<K, I, L, UpdateListElementAtIndexOp<K, L>>>(
        &mut self,
        key: &K,
        idx: usize,
        new_list_element: L,
        Tracked(cb): Tracked<CB>,
    ) -> (results: (Result<(), KvError>, Tracked<CB::ApplyResult>))
        requires
            old(self).valid(),
            cb.id() == old(self).loc(),
            cb.pre(UpdateListElementAtIndexOp{ key: *key, idx, new_list_element }),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            ({
                let (exec_result, apply_result) = results;
                let op = UpdateListElementAtIndexOp{ key: *key, idx, new_list_element };
                cb.post(op, exec_result, apply_result@)
            }),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = UpdateListElementAtIndexOp::<K, L>{ key: *key, idx, new_list_element };
        let exec_result = match kv_internal.kv.tentatively_update_list_element_at_index(key, idx, new_list_element) {
            Err(e) => Err(e),
            Ok(()) => kv_internal.kv.commit(),
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        let tracked apply_result = cb.apply(op, new_ckv, exec_result, kv_internal.invariant_resource.borrow_mut());
        write_handle.release_write(kv_internal);
        (exec_result, Tracked(apply_result))
    }

    pub exec fn update_list_element_at_index_and_item
        <CB: MutatingLinearizer<K, I, L, UpdateListElementAtIndexAndItemOp<K, I, L>>>(
        &mut self,
        key: &K,
        idx: usize,
        new_list_element: L,
        new_item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (results: (Result<(), KvError>, Tracked<CB::ApplyResult>))
        requires
            old(self).valid(),
            cb.id() == old(self).loc(),
            cb.pre(UpdateListElementAtIndexAndItemOp{ key: *key, idx, new_list_element, new_item: *new_item }),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            ({
                let (exec_result, apply_result) = results;
                let op = UpdateListElementAtIndexAndItemOp{ key: *key, idx, new_list_element, new_item: *new_item };
                cb.post(op, exec_result, apply_result@)
            }),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = UpdateListElementAtIndexAndItemOp::<K, I, L>{ key: *key, idx, new_list_element,
                                                                     new_item: *new_item };
        let exec_result = match kv_internal.kv.tentatively_update_list_element_at_index_and_item(
            key, idx, new_list_element, new_item
        ) {
            Err(e) => Err(e),
            Ok(()) => kv_internal.kv.commit(),
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        let tracked apply_result = cb.apply(op, new_ckv, exec_result, kv_internal.invariant_resource.borrow_mut());
        write_handle.release_write(kv_internal);
        (exec_result, Tracked(apply_result))
    }

    pub exec fn trim_list<CB: MutatingLinearizer<K, I, L, TrimListOp<K>>>(
        &mut self,
        key: &K,
        trim_length: usize,
        Tracked(cb): Tracked<CB>,
    ) -> (results: (Result<(), KvError>, Tracked<CB::ApplyResult>))
        requires
            old(self).valid(),
            cb.id() == old(self).loc(),
            cb.pre(TrimListOp{ key : *key, trim_length }),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            ({
                let (exec_result, apply_result) = results;
                let op = TrimListOp{ key: *key, trim_length };
                cb.post(op, exec_result, apply_result@)
            }),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = TrimListOp::<K>{ key: *key, trim_length };
        let exec_result = match kv_internal.kv.tentatively_trim_list(key, trim_length) {
            Err(e) => Err(e),
            Ok(()) => kv_internal.kv.commit(),
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        let tracked apply_result = cb.apply(op, new_ckv, exec_result, kv_internal.invariant_resource.borrow_mut());
        write_handle.release_write(kv_internal);
        (exec_result, Tracked(apply_result))
    }

    pub exec fn trim_list_and_update_item<CB: MutatingLinearizer<K, I, L, TrimListAndUpdateItemOp<K, I>>>(
        &mut self,
        key: &K,
        trim_length: usize,
        new_item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (results: (Result<(), KvError>, Tracked<CB::ApplyResult>))
        requires
            old(self).valid(),
            cb.id() == old(self).loc(),
            cb.pre(TrimListAndUpdateItemOp{ key : *key, trim_length, new_item: *new_item }),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            ({
                let (exec_result, apply_result) = results;
                let op = TrimListAndUpdateItemOp{ key: *key, trim_length, new_item: *new_item };
                cb.post(op, exec_result, apply_result@)
            }),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = TrimListAndUpdateItemOp::<K, I>{ key: *key, trim_length, new_item: *new_item };
        let exec_result = match kv_internal.kv.tentatively_trim_list_and_update_item(key, trim_length, new_item) {
            Err(e) => Err(e),
            Ok(()) => kv_internal.kv.commit(),
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        let tracked apply_result = cb.apply(op, new_ckv, exec_result, kv_internal.invariant_resource.borrow_mut());
        write_handle.release_write(kv_internal);
        (exec_result, Tracked(apply_result))
    }

    */
}

}
