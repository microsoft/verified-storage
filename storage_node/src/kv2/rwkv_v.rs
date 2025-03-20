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
use super::impl_t::*;
use super::recover_v::*;
use super::spec_t::*;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::pcm::*;
use vstd::rwlock::{RwLock, RwLockPredicate};

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

#[verifier::reject_recursive_types(K)]
pub enum OwnershipSplitter<K, I, L>
{
    Neither,
    Application{ ckv: ConcurrentKvStoreView<K, I, L> },
    Invariant{ ckv: ConcurrentKvStoreView<K, I, L> },
    Both{ ckv: ConcurrentKvStoreView<K, I, L> },
    Invalid,
}

impl<K, I, L> PCM for OwnershipSplitter<K, I, L>
{
    open spec fn unit() -> Self
    {
        Self::Neither
    }

    open spec fn valid(self) -> bool
    {
        !(self is Invalid)
    }

    open spec fn op(self, other: Self) -> Self
    {
        match (self, other) {
            (Self::Invalid, _) => Self::Invalid,
            (_, Self::Invalid) => Self::Invalid,
            (Self::Neither, _) => other,
            (_, Self::Neither) => self,
            (Self::Application{ ckv: ckv1 }, Self::Invariant{ ckv: ckv2 }) =>
                if ckv1 == ckv2 { Self::Both{ ckv: ckv1 } } else { Self::Invalid },
            (Self::Invariant{ ckv: ckv1 }, Self::Application{ ckv: ckv2 }) =>
                if ckv1 == ckv2 { Self::Both{ ckv: ckv1 } } else { Self::Invalid },
            (_, _) => Self::Invalid,
        }
    }

    proof fn closed_under_incl(a: Self, b: Self)
    {
    }

    proof fn commutative(a: Self, b: Self)
    {
    }

    proof fn associative(a: Self, b: Self, c: Self)
    {
    }

    proof fn op_unit(a: Self)
    {
    }

    proof fn unit_valid()
    {
    }
}

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
    kv: KvStore<PM, K, I, L>,
}

struct ConcurrentKvStorePredicate
{
    loc: Loc,
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
        &&& v.invariant_resource@.value() ==
               OwnershipSplitter::Invariant{ ckv: ConcurrentKvStoreView::from_kvstore_view(v.kv@) }
    }
}

pub trait ReadOnlyOperation<K, I, L>: Sized
{
    type ExecResult;

    spec fn result_valid(self, ckv: ConcurrentKvStoreView<K, I, L>, result: Self::ExecResult) -> bool;
}

pub trait ReadLinearizer<K, I, L, Op: ReadOnlyOperation<K, I, L>> : Sized
{
    type ApplyResult;

    spec fn id(self) -> Loc;

    spec fn namespaces(self) -> Set<int>;

    spec fn pre(self, op: Op) -> bool;

    spec fn post(self, op: Op, result: Op::ExecResult, ar: Self::ApplyResult) -> bool;

    proof fn apply(
        tracked self,
        op: Op,
        result: Op::ExecResult,
        tracked r: &Resource<OwnershipSplitter<K, I, L>>
    ) -> (tracked out: Self::ApplyResult)
        requires
            self.pre(op),
            r.loc() == self.id(),
            r.value() is Invariant,
            op.result_valid(r.value()->Invariant_ckv, result),
        ensures
            self.post(op, result, out),
    ;
}

pub trait MutatingOperation<K, I, L>: Sized
{
    type ExecResult;

    spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Self::ExecResult
    ) -> bool;
}

pub trait MutatingLinearizer<K, I, L, Op: MutatingOperation<K, I, L>> : Sized
{
    type ApplyResult;

    spec fn id(self) -> Loc;

    spec fn namespaces(self) -> Set<int>;

    spec fn pre(self, op: Op) -> bool;

    spec fn post(
        self,
        op: Op,
        exec_result: Op::ExecResult,
        apply_result: Self::ApplyResult
    ) -> bool;

    proof fn apply(
        tracked self,
        op: Op,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        exec_result: Op::ExecResult,
        tracked r: &mut Resource<OwnershipSplitter<K, I, L>>
    ) -> (tracked apply_result: Self::ApplyResult)
        requires
            self.pre(op),
            old(r).loc() == self.id(),
            old(r).value() is Invariant,
            op.result_valid(old(r).value()->Invariant_ckv, new_ckv, exec_result),
        ensures
            r.loc() == old(r).loc(),
            r.value() == (OwnershipSplitter::Invariant{ ckv: new_ckv }),
            self.post(op, exec_result, apply_result),
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
    type ExecResult = Result<I, KvError>;

    open spec fn result_valid(self, ckv: ConcurrentKvStoreView<K, I, L>, result: Self::ExecResult) -> bool
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

pub struct CreateOp<K, I>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
{
    pub key: K,
    pub item: I,
}

impl<K, I, L> MutatingOperation<K, I, L> for CreateOp<K, I>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type ExecResult = Result<(), KvError>;

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Self::ExecResult
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
                &&& old_ckv.kv.num_keys() >= old_ckv.ps.max_keys
            },
            Err(e) => {
                &&& new_ckv == old_ckv
                &&& old_ckv.kv.create(self.key, self.item) matches Err(e_spec)
                &&& e == e_spec
            },
        }
    }
}

pub struct UpdateItemOp<K, I>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
{
    pub key: K,
    pub item: I,
}

impl<K, I, L> MutatingOperation<K, I, L> for UpdateItemOp<K, I>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type ExecResult = Result<(), KvError>;

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Self::ExecResult
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
                &&& old_ckv.kv.num_keys() >= old_ckv.ps.max_keys
            },
            Err(e) => {
                &&& new_ckv == old_ckv
                &&& old_ckv.kv.update_item(self.key, self.item) matches Err(e_spec)
                &&& e == e_spec
            },
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
    type ExecResult = Result<(), KvError>;

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Self::ExecResult
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

pub struct GetKeysOp
{
}

impl<K, I, L> ReadOnlyOperation<K, I, L> for GetKeysOp
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type ExecResult = Result<Vec<K>, KvError>;

    open spec fn result_valid(self, ckv: ConcurrentKvStoreView<K, I, L>, result: Self::ExecResult) -> bool
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
    type ExecResult = Result<(I, Vec<L>), KvError>;

    open spec fn result_valid(self, ckv: ConcurrentKvStoreView<K, I, L>, result: Self::ExecResult) -> bool
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
    type ExecResult = Result<Vec<L>, KvError>;

    open spec fn result_valid(self, ckv: ConcurrentKvStoreView<K, I, L>, result: Self::ExecResult) -> bool
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
    type ExecResult = Result<usize, KvError>;

    open spec fn result_valid(self, ckv: ConcurrentKvStoreView<K, I, L>, result: Self::ExecResult) -> bool
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

pub struct AppendToListOp<K, L>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub key: K,
    pub new_list_element: L,
}

impl<K, I, L> MutatingOperation<K, I, L> for AppendToListOp<K, L>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type ExecResult = Result<(), KvError>;

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Self::ExecResult
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
                &&& {
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

pub struct AppendToListAndUpdateItemOp<K, I, L>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub key: K,
    pub new_list_element: L,
    pub new_item: I,
}

impl<K, I, L> MutatingOperation<K, I, L> for AppendToListAndUpdateItemOp<K, I, L>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type ExecResult = Result<(), KvError>;

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Self::ExecResult
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
                &&& {
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

pub struct UpdateListElementAtIndexOp<K, L>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub key: K,
    pub idx: usize,
    pub new_list_element: L,
}

impl<K, I, L> MutatingOperation<K, I, L> for UpdateListElementAtIndexOp<K, L>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type ExecResult = Result<(), KvError>;

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Self::ExecResult
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
                &&& {
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

pub struct UpdateListElementAtIndexAndItemOp<K, I, L>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub key: K,
    pub idx: usize,
    pub new_list_element: L,
    pub new_item: I,
}

impl<K, I, L> MutatingOperation<K, I, L> for UpdateListElementAtIndexAndItemOp<K, I, L>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type ExecResult = Result<(), KvError>;

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Self::ExecResult
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
                &&& {
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

pub struct TrimListOp<K>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub key: K,
    pub trim_length: usize,
}

impl<K, I, L> MutatingOperation<K, I, L> for TrimListOp<K>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type ExecResult = Result<(), KvError>;

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Self::ExecResult
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
                &&& old_ckv.kv.num_keys() >= old_ckv.ps.max_keys
            },
            Err(e) => {
                &&& new_ckv == old_ckv
                &&& old_ckv.kv.trim_list(self.key, self.trim_length as nat) matches Err(e_spec)
                &&& e == e_spec
            },
        }
    }
}

pub struct TrimListAndUpdateItemOp<K, I>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
{
    pub key: K,
    pub trim_length: usize,
    pub new_item: I,
}

impl<K, I, L> MutatingOperation<K, I, L> for TrimListAndUpdateItemOp<K, I>
where
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type ExecResult = Result<(), KvError>;

    open spec fn result_valid(
        self,
        old_ckv: ConcurrentKvStoreView<K, I, L>,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        result: Self::ExecResult
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
                &&& old_ckv.kv.num_keys() >= old_ckv.ps.max_keys
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

    pub closed spec fn recover(s: Seq<u8>) -> Option<RecoveredKvStore<K, I, L>>
    {
        KvStore::<PM, K, I, L>::recover(s)
    }

    pub closed spec fn spec_space_needed_for_setup(ps: SetupParameters) -> nat
    {
        KvStore::<PM, K, I, L>::spec_space_needed_for_setup(ps)
    }

    pub closed spec fn spec_space_needed_for_transaction_operation() -> nat
    {
        KvStore::<PM, K, I, L>::spec_space_needed_for_transaction_operation()
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
        KvStore::<PM, K, I, L>::space_needed_for_setup(ps)
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
        KvStore::<PM, K, I, L>::setup(pm, ps)
    }

    pub exec fn start(pm: PM, kvstore_id: u128) ->
        (result: Result<(Self, Tracked<Resource<OwnershipSplitter::<K, I, L>>>), KvError>)
        requires 
            pm.inv(),
            Self::recover(pm@.read_state) is Some,
            vstd::std_specs::hash::obeys_key_model::<K>(),
        ensures
        ({
            let state = Self::recover(pm@.read_state).unwrap();
            match result {
                Ok((kv, r)) => {
                    &&& kv.valid()
                    &&& kv.loc() == r@.loc()
                    &&& match r@.value() {
                           OwnershipSplitter::Application{ ckv } => {
                               &&& ckv.valid()
                               &&& ckv.ps == state.ps
                               &&& ckv.pm_constants == pm.constants()
                               &&& ckv.kv == state.kv
                           },
                           _ => false,
                    }
                },
                Err(KvError::CRCMismatch) => !pm.constants().impervious_to_corruption(),
                Err(KvError::WrongKvStoreId{ requested_id, actual_id }) => {
                   &&& requested_id == kvstore_id
                   &&& actual_id == state.ps.kvstore_id
                },
                Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
                Err(_) => false,
            }
        }),
    {
        let kv = match KvStore::<PM, K, I, L>::start(pm, kvstore_id) {
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

    pub exec fn read_item<CB: ReadLinearizer<K, I, L, ReadItemOp<K>>>(
        &self,
        key: &K,
        Tracked(cb): Tracked<CB>,
    ) -> (results: (Result<I, KvError>, Tracked<CB::ApplyResult>))
        requires 
            self.valid(),
            cb.id() == self.loc(),
            cb.pre(ReadItemOp{ key: *key }),
        ensures
            self.valid(),
            ({
                let (exec_result, apply_result) = results;
                let op = ReadItemOp{ key: *key };
                cb.post(op, exec_result, apply_result@)
            })
    {
        let read_handle = self.lock.acquire_read();
        let ghost op = ReadItemOp{ key: *key };
        let kv_internal = read_handle.borrow();
        let exec_result = kv_internal.kv.read_item(key);
        let tracked invariant_resource = kv_internal.invariant_resource.borrow();
        let tracked apply_result = cb.apply(op, exec_result, invariant_resource);
        read_handle.release_read();
        (exec_result, Tracked(apply_result))
    }

    pub exec fn create<CB: MutatingLinearizer<K, I, L, CreateOp<K, I>>>(
        &mut self,
        key: &K,
        item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (results: (Result<(), KvError>, Tracked<CB::ApplyResult>))
        requires
            old(self).valid(),
            cb.id() == old(self).loc(),
            cb.pre(CreateOp{ key: *key, item: *item }),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            ({
                let (exec_result, apply_result) = results;
                let op = CreateOp{ key: *key, item: *item };
                cb.post(op, exec_result, apply_result@)
            }),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = CreateOp::<K, I>{ key: *key, item: *item };
        let exec_result = match kv_internal.kv.tentatively_create(key, item) {
            Err(e) => Err(e),
            Ok(()) => kv_internal.kv.commit(),
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        let tracked apply_result = cb.apply(op, new_ckv, exec_result, kv_internal.invariant_resource.borrow_mut());
        write_handle.release_write(kv_internal);
        (exec_result, Tracked(apply_result))
    }

    pub exec fn update_item<CB: MutatingLinearizer<K, I, L, UpdateItemOp<K, I>>>(
        &mut self,
        key: &K,
        item: &I,
        Tracked(cb): Tracked<CB>,
    ) -> (results: (Result<(), KvError>, Tracked<CB::ApplyResult>))
        requires
            old(self).valid(),
            cb.id() == old(self).loc(),
            cb.pre(UpdateItemOp{ key: *key, item: *item }),
        ensures 
            self.valid(),
            self.loc() == old(self).loc(),
            ({
                let (exec_result, apply_result) = results;
                let op = UpdateItemOp{ key: *key, item: *item };
                cb.post(op, exec_result, apply_result@)
            }),
    {
        let (mut kv_internal, write_handle) = self.lock.acquire_write();
        let ghost op = UpdateItemOp::<K, I>{ key: *key, item: *item };
        let exec_result = match kv_internal.kv.tentatively_update_item(key, item) {
            Err(e) => Err(e),
            Ok(()) => kv_internal.kv.commit(),
        };
        let ghost new_ckv = ConcurrentKvStoreView::<K, I, L>::from_kvstore_view(kv_internal.kv@);
        let tracked apply_result = cb.apply(op, new_ckv, exec_result, kv_internal.invariant_resource.borrow_mut());
        write_handle.release_write(kv_internal);
        (exec_result, Tracked(apply_result))
    }

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
}

}
