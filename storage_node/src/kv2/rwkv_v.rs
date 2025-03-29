#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
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
struct ConcurrentKvStoreInternal<Perm, PermFactory, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PermFactory: PermissionFactory<Seq<u8>, Perm>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    invariant_resource: Tracked<Resource<OwnershipSplitter<K, I, L>>>,
    kv: UntrustedKvStoreImpl<Perm, PermFactory, PM, K, I, L>,
}

struct ConcurrentKvStorePredicate
{
    loc: Loc,
}

impl<Perm, PermFactory, PM, K, I, L> RwLockPredicate<ConcurrentKvStoreInternal<Perm, PermFactory, PM, K, I, L>> for ConcurrentKvStorePredicate
where
    Perm: CheckPermission<Seq<u8>>,
    PermFactory: PermissionFactory<Seq<u8>, Perm>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    closed spec fn inv(self, v: ConcurrentKvStoreInternal<Perm, PermFactory, PM, K, I, L>) -> bool
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
pub struct ConcurrentKvStore<Perm, PermFactory, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PermFactory: PermissionFactory<Seq<u8>, Perm>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pm_constants: Ghost<PersistentMemoryConstants>,
    loc: Ghost<Loc>,
    lock: RwLock<ConcurrentKvStoreInternal<Perm, PermFactory, PM, K, I, L>, ConcurrentKvStorePredicate>,
}

impl<Perm, PermFactory, PM, K, I, L> CanRecover<K, I, L> for ConcurrentKvStore<Perm, PermFactory, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PermFactory: PermissionFactory<Seq<u8>, Perm>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    closed spec fn recover(s: Seq<u8>) -> Option<RecoveredKvStore<K, I, L>> {
        UntrustedKvStoreImpl::<Perm, PermFactory, PM, K, I, L>::recover(s)
    }
}

impl<Perm, PermFactory, PM, K, I, L> ConcurrentKvStore<Perm, PermFactory, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PermFactory: PermissionFactory<Seq<u8>, Perm>,
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

    pub closed spec fn pm_constants(self) -> PersistentMemoryConstants
    {
        self.pm_constants@
    }

    pub closed spec fn spec_space_needed_for_setup(ps: SetupParameters) -> nat
    {
        UntrustedKvStoreImpl::<Perm, PermFactory, PM, K, I, L>::spec_space_needed_for_setup(ps)
    }

    pub closed spec fn spec_space_needed_for_transaction_operation() -> nat
    {
        UntrustedKvStoreImpl::<Perm, PermFactory, PM, K, I, L>::spec_space_needed_for_transaction_operation()
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
        UntrustedKvStoreImpl::<Perm, PermFactory, PM, K, I, L>::space_needed_for_setup(ps)
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
        UntrustedKvStoreImpl::<Perm, PermFactory, PM, K, I, L>::setup(pm, ps)
    }

    pub exec fn start(
        wrpm: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        kvstore_id: u128,
        Ghost(state): Ghost<RecoveredKvStore<K, I, L>>,
        Tracked(perm_factory): Tracked<PermFactory>
    ) -> (result: Result<(Self, Tracked<Resource<OwnershipSplitter::<K, I, L>>>), KvError>)
        requires 
            wrpm.inv(),
            Self::recover(wrpm@.durable_state) == Some(state),
            vstd::std_specs::hash::obeys_key_model::<K>(),
            forall|s1: Seq<u8>, s2: Seq<u8>| Self::recover(s1) == Self::recover(s2) ==>
                #[trigger] perm_factory.check_permission(s1, s2),
        ensures
        ({
            match result {
                Ok((kv, r)) => {
                    &&& kv.valid()
                    &&& kv.loc() == r@.loc()
                    &&& kv.pm_constants() == wrpm.constants()
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
        let kv = match UntrustedKvStoreImpl::<Perm, PermFactory, PM, K, I, L>::start(wrpm, kvstore_id, Ghost(state), Tracked(perm_factory)) {
            Ok(kv) => kv,
            Err(e) => { return Err(e); },
        };
        let ghost ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv@);
        let tracked both = Resource::<OwnershipSplitter<K, I, L>>::alloc(OwnershipSplitter::<K, I, L>::Both{ ckv });
        let ghost pm_constants = wrpm.constants();
        let ghost loc = both.loc();
        let ghost pred = ConcurrentKvStorePredicate{ loc };
        let ghost application_value = OwnershipSplitter::<K, I, L>::Application{ ckv };
        let ghost invariant_value = OwnershipSplitter::<K, I, L>::Invariant{ ckv };
        let tracked split_resources = both.split(application_value, invariant_value);
        let tracked application_resource = split_resources.0;
        let tracked invariant_resource = split_resources.1;
        let kv_internal = ConcurrentKvStoreInternal::<Perm, PermFactory, PM, K, I, L>{
            invariant_resource: Tracked(invariant_resource),
            kv
        };
        assert(pred.inv(kv_internal));
        let lock = RwLock::<ConcurrentKvStoreInternal<Perm, PermFactory, PM, K, I, L>, ConcurrentKvStorePredicate>::new(
            kv_internal, Ghost(pred)
        );
        let selfish = Self{ pm_constants: Ghost(pm_constants), loc: Ghost(loc), lock };
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
        proof {
            cb.apply(op, result, invariant_resource);
        }
        read_handle.release_read();
        result
    }

    pub exec fn get_keys<CB: ReadLinearizer<K, I, L, GetKeysOp>>(
        &self,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<Vec<K>, KvError>)
        requires 
            self.valid(),
            old(cb).pre(self.loc(), GetKeysOp{ }),
        ensures
            self.valid(),
            cb.post(*old(cb), self.loc(), GetKeysOp{ }, result),
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = GetKeysOp{ };
        let kv_internal = read_handle.borrow();
        let result = kv_internal.kv.get_keys();
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        proof {
            cb.apply(op, result, invariant_resource);
        }
        read_handle.release_read();
        result
    }

    pub exec fn read_item_and_list<CB: ReadLinearizer<K, I, L, ReadItemAndListOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(I, Vec<L>), KvError>)
        requires 
            self.valid(),
            old(cb).pre(self.loc(), ReadItemAndListOp{ key: *key }),
        ensures
            self.valid(),
            cb.post(*old(cb), self.loc(), ReadItemAndListOp{ key: *key }, result),
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = ReadItemAndListOp{ key: *key };
        let kv_internal = read_handle.borrow();
        let result = kv_internal.kv.read_item_and_list(key);
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        proof {
            cb.apply(op, result, invariant_resource);
        }
        read_handle.release_read();
        result
    }

    pub exec fn read_list<CB: ReadLinearizer<K, I, L, ReadListOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<Vec<L>, KvError>)
        requires 
            self.valid(),
            old(cb).pre(self.loc(), ReadListOp{ key: *key }),
        ensures
            self.valid(),
            cb.post(*old(cb), self.loc(), ReadListOp{ key: *key }, result),
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = ReadListOp{ key: *key };
        let kv_internal = read_handle.borrow();
        let result = kv_internal.kv.read_list(key);
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        proof {
            cb.apply(op, result, invariant_resource);
        }
        read_handle.release_read();
        result
    }

    pub exec fn get_list_length<CB: ReadLinearizer<K, I, L, GetListLengthOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<usize, KvError>)
        requires 
            self.valid(),
            old(cb).pre(self.loc(), GetListLengthOp{ key: *key }),
        ensures
            self.valid(),
            cb.post(*old(cb), self.loc(), GetListLengthOp{ key: *key }, result),
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = GetListLengthOp{ key: *key };
        let kv_internal = read_handle.borrow();
        let result = kv_internal.kv.get_list_length(key);
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        proof {
            cb.apply(op, result, invariant_resource);
        }
        read_handle.release_read();
        result
    }

    pub exec fn create<CB>(
        &mut self,
        key: &K,
        item: &I,
        Tracked(perm): Tracked<Perm>,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            CB: MutatingLinearizer<K, I, L, CreateOp<K, I>, Self>,
        requires
            old(self).valid(),
            old(cb).pre(old(self).loc(), CreateOp{ key: *key, item: *item }),
            grants_permission_to_mutate::<Perm, K, I, L, CreateOp<K, I>, Self>(
                perm, CreateOp{ key: *key, item: *item }, old(self).pm_constants()
            ),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            self.pm_constants() == old(self).pm_constants(),
            cb.post(*old(cb), self.loc(), CreateOp{ key: *key, item: *item }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = CreateOp::<K, I>{ key: *key, item: *item };
        let result = match kv_internal.kv.tentatively_create(key, item) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.durable };
                let ghost new_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.tentative };
                let ghost pm_constants = self.pm_constants@;
                assert(op.result_valid(
                   ConcurrentKvStoreView::<K, I, L>{ ps: old_rkv.ps, pm_constants, kv: old_rkv.kv },
                   ConcurrentKvStoreView::<K, I, L>{ ps: new_rkv.ps, pm_constants, kv: new_rkv.kv },
                   Ok(())
                ));
                kv_internal.kv.commit(Tracked(perm))
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
        Tracked(perm): Tracked<Perm>,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            CB: MutatingLinearizer<K, I, L, UpdateItemOp<K, I>, Self>,
        requires
            old(self).valid(),
            old(cb).pre(old(self).loc(), UpdateItemOp{ key: *key, item: *item }),
            grants_permission_to_mutate::<Perm, K, I, L, UpdateItemOp<K, I>, Self>(
                perm, UpdateItemOp{ key: *key, item: *item }, old(self).pm_constants()
            ),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            self.pm_constants() == old(self).pm_constants(),
            cb.post(*old(cb), self.loc(), UpdateItemOp{ key: *key, item: *item }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = UpdateItemOp::<K, I>{ key: *key, item: *item };
        let result = match kv_internal.kv.tentatively_update_item(key, item) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.durable };
                let ghost new_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.tentative };
                let ghost pm_constants = self.pm_constants@;
                assert(op.result_valid(
                   ConcurrentKvStoreView::<K, I, L>{ ps: old_rkv.ps, pm_constants, kv: old_rkv.kv },
                   ConcurrentKvStoreView::<K, I, L>{ ps: new_rkv.ps, pm_constants, kv: new_rkv.kv },
                   Ok(())
                ));
                kv_internal.kv.commit(Tracked(perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn delete<CB>(
        &mut self,
        key: &K,
        Tracked(perm): Tracked<Perm>,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            CB: MutatingLinearizer<K, I, L, DeleteOp<K>, Self>,
        requires
            old(self).valid(),
            old(cb).pre(old(self).loc(), DeleteOp{ key: *key }),
            grants_permission_to_mutate::<Perm, K, I, L, DeleteOp<K>, Self>(
                perm, DeleteOp{ key: *key }, old(self).pm_constants()
            ),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            self.pm_constants() == old(self).pm_constants(),
            cb.post(*old(cb), self.loc(), DeleteOp{ key: *key }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = DeleteOp::<K>{ key: *key };
        let result = match kv_internal.kv.tentatively_delete(key) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.durable };
                let ghost new_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.tentative };
                let ghost pm_constants = self.pm_constants@;
                assert(op.result_valid(
                   ConcurrentKvStoreView::<K, I, L>{ ps: old_rkv.ps, pm_constants, kv: old_rkv.kv },
                   ConcurrentKvStoreView::<K, I, L>{ ps: new_rkv.ps, pm_constants, kv: new_rkv.kv },
                   Ok(())
                ));
                kv_internal.kv.commit(Tracked(perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn append_to_list<CB>(
        &mut self,
        key: &K,
        new_list_element: L,
        Tracked(perm): Tracked<Perm>,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            CB: MutatingLinearizer<K, I, L, AppendToListOp<K, L>, Self>,
        requires
            old(self).valid(),
            old(cb).pre(old(self).loc(), AppendToListOp{ key: *key, new_list_element }),
            grants_permission_to_mutate::<Perm, K, I, L, AppendToListOp<K, L>, Self>(
                perm, AppendToListOp{ key: *key, new_list_element }, old(self).pm_constants()
            ),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            self.pm_constants() == old(self).pm_constants(),
            cb.post(*old(cb), self.loc(), AppendToListOp{ key: *key, new_list_element }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = AppendToListOp::<K, L>{ key: *key, new_list_element };
        let result = match kv_internal.kv.tentatively_append_to_list(key, new_list_element) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.durable };
                let ghost new_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.tentative };
                let ghost pm_constants = self.pm_constants@;
                assert(op.result_valid(
                   ConcurrentKvStoreView::<K, I, L>{ ps: old_rkv.ps, pm_constants, kv: old_rkv.kv },
                   ConcurrentKvStoreView::<K, I, L>{ ps: new_rkv.ps, pm_constants, kv: new_rkv.kv },
                   Ok(())
                ));
                kv_internal.kv.commit(Tracked(perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn append_to_list_and_update_item<CB>(
        &mut self,
        key: &K,
        new_list_element: L,
        new_item: &I,
        Tracked(perm): Tracked<Perm>,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            CB: MutatingLinearizer<K, I, L, AppendToListAndUpdateItemOp<K, I, L>, Self>,
        requires
            old(self).valid(),
            old(cb).pre(old(self).loc(), AppendToListAndUpdateItemOp{ key: *key, new_list_element, new_item: *new_item }),
            grants_permission_to_mutate::<Perm, K, I, L, AppendToListAndUpdateItemOp<K, I, L>, Self>(
                perm, AppendToListAndUpdateItemOp{ key: *key, new_list_element, new_item: *new_item }, old(self).pm_constants()
            ),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            self.pm_constants() == old(self).pm_constants(),
            cb.post(*old(cb), self.loc(), AppendToListAndUpdateItemOp{ key: *key, new_list_element, new_item: *new_item }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = AppendToListAndUpdateItemOp::<K, I, L>{ key: *key, new_list_element, new_item: *new_item };
        let result = match kv_internal.kv.tentatively_append_to_list_and_update_item(key, new_list_element, new_item) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.durable };
                let ghost new_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.tentative };
                let ghost pm_constants = self.pm_constants@;
                assert(op.result_valid(
                   ConcurrentKvStoreView::<K, I, L>{ ps: old_rkv.ps, pm_constants, kv: old_rkv.kv },
                   ConcurrentKvStoreView::<K, I, L>{ ps: new_rkv.ps, pm_constants, kv: new_rkv.kv },
                   Ok(())
                ));
                kv_internal.kv.commit(Tracked(perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn update_list_element_at_index<CB>(
        &mut self,
        key: &K,
        idx: usize,
        new_list_element: L,
        Tracked(perm): Tracked<Perm>,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            CB: MutatingLinearizer<K, I, L, UpdateListElementAtIndexOp<K, L>, Self>,
        requires
            old(self).valid(),
            old(cb).pre(old(self).loc(), UpdateListElementAtIndexOp{ key: *key, idx, new_list_element }),
            grants_permission_to_mutate::<Perm, K, I, L, UpdateListElementAtIndexOp<K, L>, Self>(
                perm, UpdateListElementAtIndexOp{ key: *key, idx, new_list_element }, old(self).pm_constants()
            ),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            self.pm_constants() == old(self).pm_constants(),
            cb.post(*old(cb), self.loc(), UpdateListElementAtIndexOp{ key: *key, idx, new_list_element }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = UpdateListElementAtIndexOp::<K, L>{ key: *key, idx, new_list_element };
        let result = match kv_internal.kv.tentatively_update_list_element_at_index(key, idx, new_list_element) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.durable };
                let ghost new_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.tentative };
                let ghost pm_constants = self.pm_constants@;
                assert(op.result_valid(
                   ConcurrentKvStoreView::<K, I, L>{ ps: old_rkv.ps, pm_constants, kv: old_rkv.kv },
                   ConcurrentKvStoreView::<K, I, L>{ ps: new_rkv.ps, pm_constants, kv: new_rkv.kv },
                   Ok(())
                ));
                kv_internal.kv.commit(Tracked(perm))
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
        <CB>(
        &mut self,
        key: &K,
        idx: usize,
        new_list_element: L,
        new_item: &I,
        Tracked(perm): Tracked<Perm>,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            CB: MutatingLinearizer<K, I, L, UpdateListElementAtIndexAndItemOp<K, I, L>, Self>,
        requires
            old(self).valid(),
            old(cb).pre(old(self).loc(), UpdateListElementAtIndexAndItemOp{ key: *key, idx, new_list_element, new_item: *new_item }),
            grants_permission_to_mutate::<Perm, K, I, L, UpdateListElementAtIndexAndItemOp<K, I, L>, Self>(
                perm, UpdateListElementAtIndexAndItemOp{ key: *key, idx, new_list_element, new_item: *new_item }, old(self).pm_constants()
            ),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            self.pm_constants() == old(self).pm_constants(),
            cb.post(*old(cb), self.loc(), UpdateListElementAtIndexAndItemOp{ key: *key, idx, new_list_element, new_item: *new_item }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = UpdateListElementAtIndexAndItemOp::<K, I, L>{ key: *key, idx, new_list_element,
                                                                     new_item: *new_item };
        let result = match kv_internal.kv.tentatively_update_list_element_at_index_and_item(
            key, idx, new_list_element, new_item
        ) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.durable };
                let ghost new_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.tentative };
                let ghost pm_constants = self.pm_constants@;
                assert(op.result_valid(
                   ConcurrentKvStoreView::<K, I, L>{ ps: old_rkv.ps, pm_constants, kv: old_rkv.kv },
                   ConcurrentKvStoreView::<K, I, L>{ ps: new_rkv.ps, pm_constants, kv: new_rkv.kv },
                   Ok(())
                ));
                kv_internal.kv.commit(Tracked(perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn trim_list<CB>(
        &mut self,
        key: &K,
        trim_length: usize,
        Tracked(perm): Tracked<Perm>,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            CB: MutatingLinearizer<K, I, L, TrimListOp<K>, Self>,
        requires
            old(self).valid(),
            old(cb).pre(old(self).loc(), TrimListOp{ key : *key, trim_length }),
            grants_permission_to_mutate::<Perm, K, I, L, TrimListOp<K>, Self>(
                perm, TrimListOp{ key : *key, trim_length }, old(self).pm_constants()
            ),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            self.pm_constants() == old(self).pm_constants(),
            cb.post(*old(cb), self.loc(), TrimListOp{ key: *key, trim_length }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = TrimListOp::<K>{ key: *key, trim_length };
        let result = match kv_internal.kv.tentatively_trim_list(key, trim_length) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.durable };
                let ghost new_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.tentative };
                let ghost pm_constants = self.pm_constants@;
                assert(op.result_valid(
                   ConcurrentKvStoreView::<K, I, L>{ ps: old_rkv.ps, pm_constants, kv: old_rkv.kv },
                   ConcurrentKvStoreView::<K, I, L>{ ps: new_rkv.ps, pm_constants, kv: new_rkv.kv },
                   Ok(())
                ));
                kv_internal.kv.commit(Tracked(perm))
            },
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        proof {
            cb.apply(*old(cb), op, new_ckv, result, kv_internal.invariant_resource.borrow_mut());
        }
        write_handle.release_write(kv_internal);
        result
    }

    pub exec fn trim_list_and_update_item<CB>(
        &mut self,
        key: &K,
        trim_length: usize,
        new_item: &I,
        Tracked(perm): Tracked<Perm>,
        Tracked(cb): Tracked<&mut CB>,
    ) -> (result: Result<(), KvError>)
        where
            CB: MutatingLinearizer<K, I, L, TrimListAndUpdateItemOp<K, I>, Self>,
        requires
            old(self).valid(),
            old(cb).pre(old(self).loc(), TrimListAndUpdateItemOp{ key : *key, trim_length, new_item: *new_item }),
            grants_permission_to_mutate::<Perm, K, I, L, TrimListAndUpdateItemOp<K, I>, Self>(
                perm, TrimListAndUpdateItemOp{ key : *key, trim_length, new_item: *new_item }, old(self).pm_constants()
            ),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            self.pm_constants() == old(self).pm_constants(),
            cb.post(*old(cb), self.loc(), TrimListAndUpdateItemOp{ key: *key, trim_length, new_item: *new_item }, result),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = TrimListAndUpdateItemOp::<K, I>{ key: *key, trim_length, new_item: *new_item };
        let result = match kv_internal.kv.tentatively_trim_list_and_update_item(key, trim_length, new_item) {
            Err(e) => Err(e),
            Ok(()) => {
                let ghost old_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.durable };
                let ghost new_rkv =
                    RecoveredKvStore::<K, I, L>{ ps: kv_internal.kv@.ps, kv: kv_internal.kv@.tentative };
                let ghost pm_constants = self.pm_constants@;
                assert(op.result_valid(
                   ConcurrentKvStoreView::<K, I, L>{ ps: old_rkv.ps, pm_constants, kv: old_rkv.kv },
                   ConcurrentKvStoreView::<K, I, L>{ ps: new_rkv.ps, pm_constants, kv: new_rkv.kv },
                   Ok(())
                ));
                kv_internal.kv.commit(Tracked(perm))
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
