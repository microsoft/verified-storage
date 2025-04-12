#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::power_t::*;
use std::hash::Hash;
use super::spec_t::*;
use vstd::pcm::frac::*;

verus! {

#[verifier::reject_recursive_types(K)]
pub struct ConcurrentKvStoreView<K, I, L>
{
    pub ps: SetupParameters,
    pub pm_constants: PersistentMemoryConstants,
    pub kv: AtomicKvStore<K, I, L>,
}

impl<K, I, L> ConcurrentKvStoreView<K, I, L>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub open spec fn valid(self) -> bool
    {
        self.ps.logical_range_gaps_policy == self.kv.logical_range_gaps_policy
    }

    pub open spec fn from_kvstore_view(v: KvStoreView<K, I, L>) -> Self
    {
        Self{
            ps: v.ps,
            pm_constants: v.pm_constants,
            kv: v.durable
        }
    }
}

pub trait ReadOnlyOperation<K, I, L>: Sized
{
    type KvResult;

    spec fn result_valid(self, ckv: ConcurrentKvStoreView<K, I, L>, result: Result<Self::KvResult, KvError>) -> bool;
}

pub trait SingleKeyReadOnlyOperation<K, I, L>: ReadOnlyOperation<K, I, L>
    where
        K: std::fmt::Debug,
        L: LogicalRange,
{
    spec fn key(self) -> K;
    proof fn only_key_matters(self, ckv1: ConcurrentKvStoreView<K, I, L>, ckv2: ConcurrentKvStoreView<K, I, L>, result: Result<Self::KvResult, KvError>)
        requires
            self.result_valid(ckv1, result),
            ckv1.kv[self.key()] == ckv2.kv[self.key()],
            ckv1.ps == ckv2.ps,
            ckv1.pm_constants == ckv2.pm_constants,
            ckv1.kv.logical_range_gaps_policy == ckv2.kv.logical_range_gaps_policy,
        ensures
            self.result_valid(ckv2, result);
}

pub trait ReadLinearizer<K, I, L, Op: ReadOnlyOperation<K, I, L>> : Sized
{
    type Completion;

    spec fn namespaces(self) -> Set<int>;

    spec fn pre(self, id: int, op: Op) -> bool;

    spec fn post(self, apply: Self::Completion, id: int, op: Op, result: Result<Op::KvResult, KvError>) -> bool;

    proof fn apply(
        tracked self,
        op: Op,
        result: Result<Op::KvResult, KvError>,
        tracked r: &GhostVarAuth<ConcurrentKvStoreView<K, I, L>>,
    ) -> (tracked complete: Self::Completion)
        requires
            self.pre(r.id(), op),
            op.result_valid(r@, result),
        ensures
            self.post(complete, r.id(), op, result),
        opens_invariants self.namespaces()
    ;
}

pub trait MutatingOperation<K, I, L>: Sized
{
    type KvResult;

    spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>,
    ) -> bool;
}

pub open spec fn map_optset<K, V>(m: Map<K, V>, k: K, v: Option<V>) -> Map<K, V> {
    match v {
        Some(v) => m.insert(k, v),
        None => m.remove(k),
    }
}

pub trait SingleKeyMutatingOperation<K, I, L>: MutatingOperation<K, I, L>
    where
        K: std::fmt::Debug,
        L: LogicalRange,
{
    spec fn key(self) -> K;
    proof fn only_key_matters(self, old1: ConcurrentKvStoreView<K, I, L>, old2: ConcurrentKvStoreView<K, I, L>, new1: ConcurrentKvStoreView<K, I, L>, new2: ConcurrentKvStoreView<K, I, L>, result: Result<Self::KvResult, KvError>)
        requires
            self.result_valid(old1, new1, result),
            old1.kv[self.key()] == old2.kv[self.key()],
            new2.kv.m == map_optset(old2.kv.m, self.key(), new1.kv[self.key()]),
            old1.ps == old2.ps,
            old1.pm_constants == old2.pm_constants,
            old1.kv.logical_range_gaps_policy == old2.kv.logical_range_gaps_policy,
            new1.ps == new2.ps,
            new1.pm_constants == new2.pm_constants,
            new1.kv.logical_range_gaps_policy == new2.kv.logical_range_gaps_policy,
        ensures
            self.result_valid(old2, new2, result);
}

pub trait CanRecover<K, I, L>
{
    spec fn recover(s: Seq<u8>) -> Option<RecoveredKvStore<K, I, L>>;
}

pub open spec fn grants_permission_to_mutate<Perm, K, I, L, Op, Kv>(
    perm: Perm,
    op: Op,
    pm_constants: PersistentMemoryConstants,
) -> bool
where
    Perm: CheckPermission<Seq<u8>>,
    Op: MutatingOperation<K, I, L>,
    Kv: CanRecover<K, I, L>,
{
    forall|s1: Seq<u8>, s2: Seq<u8>|
    {
        &&& Kv::recover(s1) matches Some(old_rkv)
        &&& Kv::recover(s2) matches Some(new_rkv)
        &&& {
            ||| exists|result| {
                    #[trigger] op.result_valid(
                        ConcurrentKvStoreView::<K, I, L>{ ps: old_rkv.ps, pm_constants, kv: old_rkv.kv },
                        ConcurrentKvStoreView::<K, I, L>{ ps: new_rkv.ps, pm_constants, kv: new_rkv.kv },
                        result
                    )
                }
            ||| old_rkv == new_rkv
        }
    } ==> #[trigger] perm.check_permission(s1, s2)
}

pub trait MutatingLinearizer<K, I, L, Op: MutatingOperation<K, I, L>> : Sized
{
    type Completion;

    spec fn namespaces(self) -> Set<int>;

    spec fn pre(self, id: int, op: Op) -> bool;

    spec fn post(self, complete: Self::Completion, id: int, op: Op, exec_result: Result<Op::KvResult, KvError>) -> bool;

    proof fn apply(
        tracked self,
        op: Op,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        exec_result: Result<Op::KvResult, KvError>,
        tracked r: &mut GhostVarAuth<ConcurrentKvStoreView<K, I, L>>,
    ) -> (tracked complete: Self::Completion)
        requires
            self.pre(old(r).id(), op),
            op.result_valid(old(r)@, new_ckv, exec_result),
        ensures
            r.id() == old(r).id(),
            r@ == new_ckv,
            self.post(complete, r.id(), op, exec_result),
        opens_invariants self.namespaces()
    ;
}

pub struct ReadItemOp<K>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub key: K,
}

impl<K, I, L> ReadOnlyOperation<K, I, L> for ReadItemOp<K>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type KvResult = I;

    open spec fn result_valid(self, ckv: ConcurrentKvStoreView<K, I, L>, result: Result<Self::KvResult, KvError>) -> bool
    {
        match result {
            Ok(item) => {
                &&& ckv.kv.read_item(self.key) matches Ok(i)
                &&& item == i
            },
            Err(KvError::CRCMismatch) => !ckv.pm_constants.impervious_to_corruption(),
            Err(e) => {
                &&& ckv.kv.read_item(self.key) matches Err(e_spec)
                &&& e == e_spec
            },
        }
    }
}

impl<K, I, L> SingleKeyReadOnlyOperation<K, I, L> for ReadItemOp<K>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    open spec fn key(self) -> K { self.key }
    proof fn only_key_matters(self, ckv1: ConcurrentKvStoreView<K, I, L>, ckv2: ConcurrentKvStoreView<K, I, L>, result: Result<Self::KvResult, KvError>) {}
}

pub struct CreateOp<K, I, const STRICT_SPACE: bool>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
{
    pub key: K,
    pub item: I,
}

impl<K, I, L, const STRICT_SPACE: bool> MutatingOperation<K, I, L> for CreateOp<K, I, STRICT_SPACE>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type KvResult = ();

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>
    ) -> bool
    {
        match result {
            Ok(()) => {
                &&& new_ckv == ConcurrentKvStoreView{ kv: new_ckv.kv, ..old_ckv }
                &&& old_ckv.kv.create(self.key, self.item) matches Ok(kv)
                &&& kv == new_ckv.kv
            }
            Err(KvError::CRCMismatch) => {
                &&& new_ckv == old_ckv
                &&& !old_ckv.pm_constants.impervious_to_corruption()
            }, 
            Err(KvError::OutOfSpace) => {
                &&& new_ckv == old_ckv
                &&& STRICT_SPACE ==> old_ckv.kv.num_keys() >= old_ckv.ps.max_keys
            },
            Err(e) => {
                &&& new_ckv == old_ckv
                &&& old_ckv.kv.create(self.key, self.item) matches Err(e_spec)
                &&& e == e_spec
            },
        }
    }
}

impl<K, I, L> SingleKeyMutatingOperation<K, I, L> for CreateOp<K, I, false>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    open spec fn key(self) -> K { self.key }
    proof fn only_key_matters(
        self,
        old1: ConcurrentKvStoreView<K, I, L>,
        old2: ConcurrentKvStoreView<K, I, L>,
        new1: ConcurrentKvStoreView<K, I, L>,
        new2: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>,
    ) {
        if result is Err {
            assert(old2.kv.m == new2.kv.m);
        }
    }
}

pub struct UpdateItemOp<K, I, const STRICT_SPACE: bool>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
{
    pub key: K,
    pub item: I,
}

impl<K, I, L, const STRICT_SPACE: bool> MutatingOperation<K, I, L> for UpdateItemOp<K, I, STRICT_SPACE>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type KvResult = ();

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>
    ) -> bool
    {
        match result {
            Ok(()) => {
                &&& new_ckv == ConcurrentKvStoreView{ kv: new_ckv.kv, ..old_ckv }
                &&& old_ckv.kv.update_item(self.key, self.item) matches Ok(kv)
                &&& kv == new_ckv.kv
            }
            Err(KvError::CRCMismatch) => {
                &&& new_ckv == old_ckv
                &&& !old_ckv.pm_constants.impervious_to_corruption()
            }, 
            Err(KvError::OutOfSpace) => {
                &&& new_ckv == old_ckv
                &&& STRICT_SPACE ==> old_ckv.kv.num_keys() >= old_ckv.ps.max_keys
            },
            Err(e) => {
                &&& new_ckv == old_ckv
                &&& old_ckv.kv.update_item(self.key, self.item) matches Err(e_spec)
                &&& e == e_spec
            },
        }
    }
}

impl<K, I, L> SingleKeyMutatingOperation<K, I, L> for UpdateItemOp<K, I, false>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    open spec fn key(self) -> K { self.key }
    proof fn only_key_matters(
        self,
        old1: ConcurrentKvStoreView<K, I, L>,
        old2: ConcurrentKvStoreView<K, I, L>,
        new1: ConcurrentKvStoreView<K, I, L>,
        new2: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>,
    ) {
        if result is Err {
            assert(old2.kv.m == new2.kv.m);
        }
    }
}

pub struct DeleteOp<K>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub key: K,
}

impl<K, I, L> MutatingOperation<K, I, L> for DeleteOp<K>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type KvResult = ();

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>
    ) -> bool
    {
        match result {
            Ok(()) => {
                &&& new_ckv == ConcurrentKvStoreView{ kv: new_ckv.kv, ..old_ckv }
                &&& old_ckv.kv.delete(self.key) matches Ok(kv)
                &&& kv == new_ckv.kv
            }
            Err(KvError::CRCMismatch) => {
                &&& new_ckv == old_ckv
                &&& !old_ckv.pm_constants.impervious_to_corruption()
            }, 
            Err(e) => {
                &&& new_ckv == old_ckv
                &&& old_ckv.kv.delete(self.key) matches Err(e_spec)
                &&& e == e_spec
            },
        }
    }
}

impl<K, I, L> SingleKeyMutatingOperation<K, I, L> for DeleteOp<K>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    open spec fn key(self) -> K { self.key }
    proof fn only_key_matters(
        self,
        old1: ConcurrentKvStoreView<K, I, L>,
        old2: ConcurrentKvStoreView<K, I, L>,
        new1: ConcurrentKvStoreView<K, I, L>,
        new2: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>,
    ) {
        if result is Err {
            assert(old2.kv.m == new2.kv.m);
        }
    }
}

pub struct GetKeysOp
{
}

impl<K, I, L> ReadOnlyOperation<K, I, L> for GetKeysOp
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type KvResult = Vec<K>;

    open spec fn result_valid(self, ckv: ConcurrentKvStoreView<K, I, L>, result: Result<Self::KvResult, KvError>) -> bool
    {
        match result {
            Ok(keys) => {
                &&& keys@.to_set() == ckv.kv.get_keys()
                &&& keys@.no_duplicates()
            },
            Err(KvError::CRCMismatch) => !ckv.pm_constants.impervious_to_corruption(),
            Err(_) => false,
        }
    }
}

pub struct ReadItemAndListOp<K>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub key: K,
}

impl<K, I, L> ReadOnlyOperation<K, I, L> for ReadItemAndListOp<K>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type KvResult = (I, Vec<L>);

    open spec fn result_valid(self, ckv: ConcurrentKvStoreView<K, I, L>, result: Result<Self::KvResult, KvError>) -> bool
    {
        match result {
            Ok((item, lst)) => {
                &&& ckv.kv.read_item_and_list(self.key) matches Ok((i, l))
                &&& item == i
                &&& lst@ == l
            },
            Err(KvError::CRCMismatch) => !ckv.pm_constants.impervious_to_corruption(),
            Err(e) => {
                &&& ckv.kv.read_item_and_list(self.key) matches Err(e_spec)
                &&& e == e_spec
            },
        }
    }
}

impl<K, I, L> SingleKeyReadOnlyOperation<K, I, L> for ReadItemAndListOp<K>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    open spec fn key(self) -> K { self.key }
    proof fn only_key_matters(self, ckv1: ConcurrentKvStoreView<K, I, L>, ckv2: ConcurrentKvStoreView<K, I, L>, result: Result<Self::KvResult, KvError>) {}
}

pub struct ReadListOp<K>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub key: K,
}

impl<K, I, L> ReadOnlyOperation<K, I, L> for ReadListOp<K>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type KvResult = Vec<L>;

    open spec fn result_valid(self, ckv: ConcurrentKvStoreView<K, I, L>, result: Result<Self::KvResult, KvError>) -> bool
    {
        match result {
            Ok(lst) => {
                &&& ckv.kv.read_item_and_list(self.key) matches Ok((i, l))
                &&& lst@ == l
            },
            Err(KvError::CRCMismatch) => !ckv.pm_constants.impervious_to_corruption(),
            Err(e) => {
                &&& ckv.kv.read_item_and_list(self.key) matches Err(e_spec)
                &&& e == e_spec
            },
        }
    }
}

impl<K, I, L> SingleKeyReadOnlyOperation<K, I, L> for ReadListOp<K>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    open spec fn key(self) -> K { self.key }
    proof fn only_key_matters(self, ckv1: ConcurrentKvStoreView<K, I, L>, ckv2: ConcurrentKvStoreView<K, I, L>, result: Result<Self::KvResult, KvError>) {}
}

pub struct GetListLengthOp<K>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub key: K,
}

impl<K, I, L> ReadOnlyOperation<K, I, L> for GetListLengthOp<K>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type KvResult = usize;

    open spec fn result_valid(self, ckv: ConcurrentKvStoreView<K, I, L>, result: Result<Self::KvResult, KvError>) -> bool
    {
        match result {
            Ok(num_elements) => {
                &&& ckv.kv.get_list_length(self.key) matches Ok(n)
                &&& num_elements == n
            },
            Err(KvError::CRCMismatch) => !ckv.pm_constants.impervious_to_corruption(),
            Err(e) => {
                &&& ckv.kv.get_list_length(self.key) matches Err(e_spec)
                &&& e == e_spec
            },
        }
    }
}

impl<K, I, L> SingleKeyReadOnlyOperation<K, I, L> for GetListLengthOp<K>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    open spec fn key(self) -> K { self.key }
    proof fn only_key_matters(self, ckv1: ConcurrentKvStoreView<K, I, L>, ckv2: ConcurrentKvStoreView<K, I, L>, result: Result<Self::KvResult, KvError>) {}
}

pub struct AppendToListOp<K, L, const STRICT_SPACE: bool>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub key: K,
    pub new_list_element: L,
}

impl<K, I, L, const STRICT_SPACE: bool> MutatingOperation<K, I, L> for AppendToListOp<K, L, STRICT_SPACE>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type KvResult = ();

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>
    ) -> bool
    {
        match result {
            Ok(()) => {
                &&& new_ckv == ConcurrentKvStoreView{ kv: new_ckv.kv, ..old_ckv }
                &&& old_ckv.kv.append_to_list(self.key, self.new_list_element) matches Ok(kv)
                &&& kv == new_ckv.kv
            }
            Err(KvError::CRCMismatch) => {
                &&& new_ckv == old_ckv
                &&& !old_ckv.pm_constants.impervious_to_corruption()
            }, 
            Err(KvError::OutOfSpace) => {
                &&& new_ckv == old_ckv
                &&& STRICT_SPACE ==> {
                       ||| old_ckv.kv.num_keys() >= old_ckv.ps.max_keys
                       ||| old_ckv.kv.num_list_elements() >= old_ckv.ps.max_list_elements
                    }
            },
            Err(e) => {
                &&& new_ckv == old_ckv
                &&& old_ckv.kv.append_to_list(self.key, self.new_list_element) matches Err(e_spec)
                &&& e == e_spec
            },
        }
    }
}

impl<K, I, L> SingleKeyMutatingOperation<K, I, L> for AppendToListOp<K, L, false>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    open spec fn key(self) -> K { self.key }
    proof fn only_key_matters(
        self,
        old1: ConcurrentKvStoreView<K, I, L>,
        old2: ConcurrentKvStoreView<K, I, L>,
        new1: ConcurrentKvStoreView<K, I, L>,
        new2: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>,
    ) {
        if result is Err {
            assert(old2.kv.m == new2.kv.m);
        }
    }
}

pub struct AppendToListAndUpdateItemOp<K, I, L, const STRICT_SPACE: bool>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub key: K,
    pub new_list_element: L,
    pub new_item: I,
}

impl<K, I, L, const STRICT_SPACE: bool> MutatingOperation<K, I, L> for AppendToListAndUpdateItemOp<K, I, L, STRICT_SPACE>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type KvResult = ();

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>
    ) -> bool
    {
        match result {
            Ok(()) => {
                &&& new_ckv == ConcurrentKvStoreView{ kv: new_ckv.kv, ..old_ckv }
                &&& old_ckv.kv.append_to_list_and_update_item(self.key, self.new_list_element, self.new_item)
                    matches Ok(kv)
                &&& kv == new_ckv.kv
            }
            Err(KvError::CRCMismatch) => {
                &&& new_ckv == old_ckv
                &&& !old_ckv.pm_constants.impervious_to_corruption()
            }, 
            Err(KvError::OutOfSpace) => {
                &&& new_ckv == old_ckv
                &&& STRICT_SPACE ==> {
                       ||| old_ckv.kv.num_keys() >= old_ckv.ps.max_keys
                       ||| old_ckv.kv.num_list_elements() >= old_ckv.ps.max_list_elements
                    }
            },
            Err(e) => {
                &&& new_ckv == old_ckv
                &&& old_ckv.kv.append_to_list_and_update_item(self.key, self.new_list_element, self.new_item)
                    matches Err(e_spec)
                &&& e == e_spec
            },
        }
    }
}

impl<K, I, L> SingleKeyMutatingOperation<K, I, L> for AppendToListAndUpdateItemOp<K, I, L, false>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    open spec fn key(self) -> K { self.key }
    proof fn only_key_matters(
        self,
        old1: ConcurrentKvStoreView<K, I, L>,
        old2: ConcurrentKvStoreView<K, I, L>,
        new1: ConcurrentKvStoreView<K, I, L>,
        new2: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>,
    ) {
        if result is Err {
            assert(old2.kv.m == new2.kv.m);
        }
    }
}

pub struct UpdateListElementAtIndexOp<K, L, const STRICT_SPACE: bool>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub key: K,
    pub idx: usize,
    pub new_list_element: L,
}

impl<K, I, L, const STRICT_SPACE: bool> MutatingOperation<K, I, L> for UpdateListElementAtIndexOp<K, L, STRICT_SPACE>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type KvResult = ();

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>
    ) -> bool
    {
        match result {
            Ok(()) => {
                &&& new_ckv == ConcurrentKvStoreView{ kv: new_ckv.kv, ..old_ckv }
                &&& old_ckv.kv.update_list_element_at_index(self.key, self.idx as nat, self.new_list_element)
                    matches Ok(kv)
                &&& kv == new_ckv.kv
            }
            Err(KvError::CRCMismatch) => {
                &&& new_ckv == old_ckv
                &&& !old_ckv.pm_constants.impervious_to_corruption()
            }, 
            Err(KvError::OutOfSpace) => {
                &&& new_ckv == old_ckv
                &&& STRICT_SPACE ==> {
                       ||| old_ckv.kv.num_keys() >= old_ckv.ps.max_keys
                       ||| old_ckv.kv.num_list_elements() >= old_ckv.ps.max_list_elements
                    }
            },
            Err(e) => {
                &&& new_ckv == old_ckv
                &&& old_ckv.kv.update_list_element_at_index(self.key, self.idx as nat, self.new_list_element)
                    matches Err(e_spec)
                &&& e == e_spec
            },
        }
    }
}

impl<K, I, L> SingleKeyMutatingOperation<K, I, L> for UpdateListElementAtIndexOp<K, L, false>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    open spec fn key(self) -> K { self.key }
    proof fn only_key_matters(
        self,
        old1: ConcurrentKvStoreView<K, I, L>,
        old2: ConcurrentKvStoreView<K, I, L>,
        new1: ConcurrentKvStoreView<K, I, L>,
        new2: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>,
    ) {
        if result is Err {
            assert(old2.kv.m == new2.kv.m);
        }
    }
}

pub struct UpdateListElementAtIndexAndItemOp<K, I, L, const STRICT_SPACE: bool>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub key: K,
    pub idx: usize,
    pub new_list_element: L,
    pub new_item: I,
}

impl<K, I, L, const STRICT_SPACE: bool> MutatingOperation<K, I, L> for UpdateListElementAtIndexAndItemOp<K, I, L, STRICT_SPACE>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type KvResult = ();

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>
    ) -> bool
    {
        match result {
            Ok(()) => {
                &&& new_ckv == ConcurrentKvStoreView{ kv: new_ckv.kv, ..old_ckv }
                &&& old_ckv.kv.update_list_element_at_index_and_item(self.key, self.idx as nat, self.new_list_element,
                                                                    self.new_item) matches Ok(kv)
                &&& kv == new_ckv.kv
            }
            Err(KvError::CRCMismatch) => {
                &&& new_ckv == old_ckv
                &&& !old_ckv.pm_constants.impervious_to_corruption()
            }, 
            Err(KvError::OutOfSpace) => {
                &&& new_ckv == old_ckv
                &&& STRICT_SPACE ==> {
                       ||| old_ckv.kv.num_keys() >= old_ckv.ps.max_keys
                       ||| old_ckv.kv.num_list_elements() >= old_ckv.ps.max_list_elements
                    }
            },
            Err(e) => {
                &&& new_ckv == old_ckv
                &&& old_ckv.kv.update_list_element_at_index_and_item(self.key, self.idx as nat, self.new_list_element,
                                                                   self.new_item) matches Err(e_spec)
                &&& e == e_spec
            },
        }
    }
}

impl<K, I, L> SingleKeyMutatingOperation<K, I, L> for UpdateListElementAtIndexAndItemOp<K, I, L, false>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    open spec fn key(self) -> K { self.key }
    proof fn only_key_matters(
        self,
        old1: ConcurrentKvStoreView<K, I, L>,
        old2: ConcurrentKvStoreView<K, I, L>,
        new1: ConcurrentKvStoreView<K, I, L>,
        new2: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>,
    ) {
        if result is Err {
            assert(old2.kv.m == new2.kv.m);
        }
    }
}

pub struct TrimListOp<K, const STRICT_SPACE: bool>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub key: K,
    pub trim_length: usize,
}

impl<K, I, L, const STRICT_SPACE: bool> MutatingOperation<K, I, L> for TrimListOp<K, STRICT_SPACE>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type KvResult = ();

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>
    ) -> bool
    {
        match result {
            Ok(()) => {
                &&& new_ckv == ConcurrentKvStoreView{ kv: new_ckv.kv, ..old_ckv }
                &&& old_ckv.kv.trim_list(self.key, self.trim_length as nat) matches Ok(kv)
                &&& kv == new_ckv.kv
            }
            Err(KvError::CRCMismatch) => {
                &&& new_ckv == old_ckv
                &&& !old_ckv.pm_constants.impervious_to_corruption()
            }, 
            Err(KvError::OutOfSpace) => {
                &&& new_ckv == old_ckv
                &&& STRICT_SPACE ==> old_ckv.kv.num_keys() >= old_ckv.ps.max_keys
            },
            Err(e) => {
                &&& new_ckv == old_ckv
                &&& old_ckv.kv.trim_list(self.key, self.trim_length as nat) matches Err(e_spec)
                &&& e == e_spec
            },
        }
    }
}

impl<K, I, L> SingleKeyMutatingOperation<K, I, L> for TrimListOp<K, false>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    open spec fn key(self) -> K { self.key }
    proof fn only_key_matters(
        self,
        old1: ConcurrentKvStoreView<K, I, L>,
        old2: ConcurrentKvStoreView<K, I, L>,
        new1: ConcurrentKvStoreView<K, I, L>,
        new2: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>,
    ) {
        if result is Err {
            assert(old2.kv.m == new2.kv.m);
        }
    }
}

pub struct TrimListAndUpdateItemOp<K, I, const STRICT_SPACE: bool>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
{
    pub key: K,
    pub trim_length: usize,
    pub new_item: I,
}

impl<K, I, L, const STRICT_SPACE: bool> MutatingOperation<K, I, L> for TrimListAndUpdateItemOp<K, I, STRICT_SPACE>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type KvResult = ();

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>
    ) -> bool
    {
        match result {
            Ok(()) => {
                &&& new_ckv == ConcurrentKvStoreView{ kv: new_ckv.kv, ..old_ckv }
                &&& old_ckv.kv.trim_list_and_update_item(self.key, self.trim_length as nat, self.new_item) matches Ok(kv)
                &&& kv == new_ckv.kv
            }
            Err(KvError::CRCMismatch) => {
                &&& new_ckv == old_ckv
                &&& !old_ckv.pm_constants.impervious_to_corruption()
            }, 
            Err(KvError::OutOfSpace) => {
                &&& new_ckv == old_ckv
                &&& STRICT_SPACE ==> old_ckv.kv.num_keys() >= old_ckv.ps.max_keys
            },
            Err(e) => {
                &&& new_ckv == old_ckv
                &&& old_ckv.kv.trim_list_and_update_item(self.key, self.trim_length as nat, self.new_item)
                    matches Err(e_spec)
                &&& e == e_spec
            },
        }
    }
}

impl<K, I, L> SingleKeyMutatingOperation<K, I, L> for TrimListAndUpdateItemOp<K, I, false>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    open spec fn key(self) -> K { self.key }
    proof fn only_key_matters(
        self,
        old1: ConcurrentKvStoreView<K, I, L>,
        old2: ConcurrentKvStoreView<K, I, L>,
        new1: ConcurrentKvStoreView<K, I, L>,
        new2: ConcurrentKvStoreView<K, I, L>,
        result: Result<Self::KvResult, KvError>,
    ) {
        if result is Err {
            assert(old2.kv.m == new2.kv.m);
        }
    }
}

}
