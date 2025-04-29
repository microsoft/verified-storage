#![allow(unused_imports)]
#![cfg_attr(verus_keep_ghost, verus::trusted)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

/// This file wraps the standard-library `std::sync::RwLock` to
/// provide a `RwLockWithPredicate`. Like `std::sync::RwLock`,
/// `RwLockWithPredicate` allows, at any given time, either multiple
/// concurrent readers or one concurrent writer to the underlying
/// object of some arbitrary type `V`.
///
/// The interface to `RwLockWithPredicate` differs from that to
/// `std::sync::RwLock` in two main ways:
///
/// First, as indicated by the type name, it associates a predicate
/// with the lock that's guaranteed to always hold on the value when
/// it is being read. This is enforced by requiring writers to ensure
/// the predicate holds after they're done writing it and are about to
/// release the lock.
///
/// Second, because Verus doesn't allow returning `&mut` references,
/// its write interface differs. Instead of returning a guard that can
/// be borrowed to get a `&mut` reference, instead `write` (1)
/// acquires the write lock, (2) invokes a writer object by passing it
/// an `&mut V`, (3) releases the write lock, then (4) returns the
/// result returned by the writer. That writer must satisfy the
/// `RwLockWriter` trait, the most important property of which is that
/// its `write` method must ensure it maintains the predicate.

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

/// A `RwLockWriter` is an object representing a write operation that
/// should be done on an object while a writer lock is held.
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
    /// Create a new read-write lock with a predicate that must hold on every update.
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

    /// Acquire a read lock. This returns a guard that one can borrow a reference
    /// to the `V` from. When that guard is dropped, the read lock is released.
    #[verifier::external_body]
    pub exec fn read<'a>(&'a self) -> (result: RwLockReadGuardWithPredicate<'a, V>)
        ensures
            self.inv(result@),
    {
        RwLockReadGuardWithPredicate::<'a, V>{
            guard: self.lock.read().unwrap()
        }
    }

    /// Acquire a write lock, run the given writer on the resulting
    /// `V` (mutating it in the process), and release the lock. Then
    /// return the completion returned by the writer.
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
