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
use super::*;
use super::impl_t::*;
use super::recover_v::*;
use super::spec_t::*;
use vstd::atomic::*;
use vstd::rwlock::*;
use vstd::invariant::*;
use vstd::pcm::*;

verus! {

#[verifier::reject_recursive_types(K)]
pub enum OwnershipSplitter<K, I, L>
{
    Neither,
    Application{ kv: KvStoreView<K, I, L> },
    Invariant{ kv: KvStoreView<K, I, L> },
    Both{ kv: KvStoreView<K, I, L> },
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
            (Self::Application{ kv: kv1 }, Self::Invariant{ kv: kv2 }) =>
                if kv1 == kv2 { Self::Both{ kv: kv1 } } else { Self::Invalid },
            (Self::Invariant{ kv: kv1 }, Self::Application{ kv: kv2 }) =>
                if kv1 == kv2 { Self::Both{ kv: kv1 } } else { Self::Invalid },
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
        &&& self.loc == v.invariant_resource@.loc()
        &&& v.invariant_resource@.value() == OwnershipSplitter::Invariant{ kv: v.kv@ }
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
                        OwnershipSplitter::Application{ kv: v } => {
                            &&& v.valid()
                            &&& v.ps == state.ps
                            &&& v.used_key_slots == state.kv.m.dom().len()
                            &&& v.used_list_element_slots == state.kv.num_list_elements()
                            &&& v.used_transaction_operation_slots == 0
                            &&& v.pm_constants == pm.constants()
                            &&& v.durable == state.kv
                            &&& v.tentative == state.kv
                        },
                        _ => false
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
        let tracked both = Resource::<OwnershipSplitter<K, I, L>>::alloc(OwnershipSplitter::<K, I, L>::Both{ kv: kv@ });
        let ghost loc = both.loc();
        let ghost pred = ConcurrentKvStorePredicate{ loc };
        let ghost application_value = OwnershipSplitter::<K, I, L>::Application{ kv: kv@ };
        let ghost invariant_value = OwnershipSplitter::<K, I, L>::Invariant{ kv: kv@ };
        let tracked split_resources = both.split(application_value, invariant_value);
        let tracked application_resource = split_resources.0;
        let tracked invariant_resource = split_resources.1;
        let kv_internal = ConcurrentKvStoreInternal::<PM, K, I, L>{
            invariant_resource: Tracked(invariant_resource),
            kv
        };
        let lock = RwLock::<ConcurrentKvStoreInternal<PM, K, I, L>, ConcurrentKvStorePredicate>::new(
            kv_internal, Ghost(pred)
        );
        let selfish = Self{ loc: Ghost(loc), lock };
        Ok((selfish, Tracked(application_resource)))
    }
}

}
