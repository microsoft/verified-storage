#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use std::hash::Hash;
use super::spec_t::*;
use vstd::pcm::*;

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

pub trait ReadOnlyOperation<K, I, L>: Sized
{
    type ExecResult;

    spec fn result_valid(self, ckv: ConcurrentKvStoreView<K, I, L>, result: Self::ExecResult) -> bool;
}

pub trait ReadLinearizer<K, I, L, Op: ReadOnlyOperation<K, I, L>> : Sized
{
    spec fn namespaces(self) -> Set<int>;

    spec fn pre(self, loc: Loc, op: Op) -> bool;

    spec fn post(self, orig_self: Self, loc: Loc, op: Op, result: Op::ExecResult) -> bool;

    proof fn apply(
        tracked &mut self,
        op: Op,
        result: Op::ExecResult,
        tracked r: &Resource<OwnershipSplitter<K, I, L>>,
    )
        requires
            old(self).pre(r.loc(), op),
            r.value() is Invariant,
            op.result_valid(r.value()->Invariant_ckv, result),
        ensures
            self.post(*old(self), r.loc(), op, result),
        opens_invariants old(self).namespaces()
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
        &&& exists|result| {
               let old_ckv = ConcurrentKvStoreView::<K, I, L>{ ps: old_rkv.ps, pm_constants, kv: old_rkv.kv };
               let new_ckv = ConcurrentKvStoreView::<K, I, L>{ ps: new_rkv.ps, pm_constants, kv: new_rkv.kv };
               #[trigger] op.result_valid(old_ckv, new_ckv, result)
           }
    } ==> #[trigger] perm.check_permission(s1, s2)
}

pub trait MutatingLinearizer<K, I, L, Op: MutatingOperation<K, I, L>, Kv: CanRecover<K, I, L>> : Sized
{
    spec fn namespaces(self) -> Set<int>;

    spec fn pre(self, loc: Loc, op: Op) -> bool;

    spec fn post(self, orig_self: Self, old_ckv: ConcurrentKvStoreView<K, I, L>, loc: Loc, op: Op,
                 exec_result: Op::ExecResult) -> bool;

    proof fn apply(
        tracked &mut self,
        orig_self: Self,
        op: Op,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        exec_result: Op::ExecResult,
        tracked r: &mut Resource<OwnershipSplitter<K, I, L>>
    )
        requires
            old(r).value() is Invariant,
            old(self).pre(old(r).loc(), op),
            op.result_valid(old(r).value()->Invariant_ckv, new_ckv, exec_result),
        ensures
            r.loc() == old(r).loc(),
            r.value() == (OwnershipSplitter::Invariant{ ckv: new_ckv }),
            self.post(*old(self), old(r).value()->Invariant_ckv, r.loc(), op, exec_result),
        opens_invariants old(self).namespaces()
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

}
