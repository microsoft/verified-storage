#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use std::borrow::{Borrow, BorrowMut};
use std::sync::{LockResult, PoisonError, RwLock, RwLockReadGuard};
use vstd::invariant::*;

verus! {

pub trait RwLockPredicate<V>: Sized {
    spec fn inv(self, v: V) -> bool;
}

impl<V> RwLockPredicate<V> for spec_fn(V) -> bool {
    open spec fn inv(self, v: V) -> bool {
        self(v)
    }
}

pub trait RwLockWriter<V, Completion, Pred: RwLockPredicate<V>>: Sized {
    spec fn pred(self) -> Pred;

    spec fn pre(self) -> bool;
    spec fn post(self, completion: Completion) -> bool;

    exec fn write(self, v: &mut V) -> (completion: Completion)
        requires
            self.pre(),
            self.pred().inv(*old(v)),
        ensures
            self.pred().inv(*v),
            self.post(completion),
    ;
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExRwLock<T: ?Sized>(RwLock<T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExRwLockReadGuard<'a, T: ?Sized>(RwLockReadGuard<'a, T>);

#[verifier::reject_recursive_types(V)]
pub struct RwLockReadGuardWithPredicate<'a, V>
{
    guard: RwLockReadGuard<'a, V>
}

impl<'a, V> RwLockReadGuardWithPredicate<'a, V>
{
    pub uninterp spec fn view(&self) -> V;

    #[verifier::external_body]
    pub exec fn borrow(&self) -> (result: &V)
        ensures
            *result == self@,
    {
        self.guard.borrow()
    }
}

#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(Pred)]
pub struct RwLockWithPredicate<V, Pred: RwLockPredicate<V>> {
    lock: RwLock<V>,
    pred: Ghost<Pred>,
}

impl<V, Pred> RwLockWithPredicate<V, Pred>
    where
        Pred: RwLockPredicate<V>,
{
    #[verifier::external_body]
    pub fn new(val: V, Ghost(pred): Ghost<Pred>) -> (s: Self)
        requires
            pred.inv(val),
        ensures
            s.pred() == pred,
    {
        Self{
            lock: RwLock::new(val),
            pred: Ghost(pred),
        }
    }

    /// Predicate configured for this lock instance.
    #[verifier::external_body]
    pub closed spec fn pred(&self) -> Pred {
        self.pred@
    }

    /// Indicates if the value `v` can be stored in the lock. Per the definition,
    /// it depends on `[self.pred()]`, which is configured upon lock construction
    /// ([`RwLockWithPredicate::new`]).
    pub open spec fn inv(&self, val: V) -> bool {
        self.pred().inv(val)
    }

    #[verifier::external_body]
    pub exec fn read<'a>(&'a self) -> (result: RwLockReadGuardWithPredicate<'a, V>)
        ensures
            self.inv(result@),
    {
        RwLockReadGuardWithPredicate::<'a, V>{
            guard: self.lock.read().unwrap()
        }
    }

    #[verifier::external_body]
    pub exec fn write<Writer, Completion>(&self, writer: Writer) -> (completion: Completion)
        where
            Writer: RwLockWriter<V, Completion, Pred>,
        requires
            self.pred() == writer.pred(),
            writer.pre(),
        ensures
            writer.post(completion)
    {
        let mut lock_result = self.lock.write().unwrap();
        let v: &mut V = lock_result.borrow_mut();
        writer.write(v)
    }
}

}
