use vstd::prelude::*;
use vstd::invariant::*;

use std::sync::Arc;

verus! {
    // hold_until_crash() represents the notion that an atomic invariant
    // will keep holding until the system crashes.
    //
    // Effectively, keep_until_crash() simulates holding a reference on
    // the Arc<>.  This ensures that the invariant cannot be destroyed,
    // using inv.into_inner(), and therefore it will be sound after crash
    // to assume InvariantRecoverer::held_before_crash() and thereby
    // recover the invariant.
    #[verifier::external_body]
    pub proof fn hold_until_crash<Pred, State>(
        tracked inv: Arc<AtomicInvariant<Pred, State, Pred>>
    )
        where
            Pred: InvariantPredicate<Pred, State>
    {
        unimplemented!()
    }

    pub struct InvariantRecoverer<Pred, State>
        where
            Pred: InvariantPredicate<Pred, State>
    {
        ghost pred: Pred,
        ghost namespace: int,
        ghost _state: core::marker::PhantomData<State>,
    }

    impl<Pred, State> InvariantRecoverer<Pred, State>
        where
            Pred: InvariantPredicate<Pred, State>
    {
        pub uninterp spec fn held_before_crash(self) -> bool;

        pub closed spec fn pred(self) -> Pred { self.pred }
        pub closed spec fn namespace(self) -> int { self.namespace }

        pub proof fn new(pred: Pred, namespace: int) -> (tracked result: Self)
            ensures
                result.pred() == pred,
                result.namespace() == namespace,
        {
            Self{
                pred: pred,
                namespace: namespace,
                _state: core::marker::PhantomData,
            }
        }

        // This axiom is used in formalizing the assumption that some atomic
        // invariant held before a crash (described by the invariant predicate
        // and the invariant namespace), and can be assumed to still hold after
        // the system has restarted after a crash.
        //
        // This axiom requires self.held_before_crash() as a precondition, to
        // ensure it doesn't get used accidentally, since it's not sound in
        // general.  However, a caller that wants to make this assumption can
        // allocate a tracked InvariantRecoverer using ::new, then assume()
        // the held_before_crash() predicate, and finally call ::recover().
        //
        // The InvariantRecoverer is tracked to precisely capture that the
        // caller gets to recover one invariant for every assume() of
        // held_before_crash().
        #[verifier::external_body]
        pub proof fn get(tracked self) -> (tracked result: AtomicInvariant::<Pred, State, Pred>)
            requires
                self.held_before_crash(),
            ensures
                result.constant() == self.pred(),
                result.namespace() == self.namespace(),
        {
            unimplemented!()
        }
    }
}
