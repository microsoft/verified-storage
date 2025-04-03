// #![verus::trusted]
use crate::pmem::pmemspec_t::*;
use crate::pmem::frac_v::*;
use crate::pmem::power_t::*;
use vstd::prelude::*;
use vstd::invariant::*;
use std::sync::Arc;

verus! {

// This file formalizes the soundness argument for PoWER.
//
// The overall plan is to show that:
//
//   For any application that uses the PersistentMemoryRegionAtomic
//   interface provided in `power_t` (and in particular, the PoWER
//   library in `power_v` that is verifiably implemented on top of
//   that interface to provide the PoWER API), the developer can
//   be sure that the durable state of the PersistentMemoryRegion
//   always satisfies the application's crash invariant.
//
// In order to mechanize this argument, we define a model of what we
// expect an application built on top of the PoWER interface to look like:

trait PoWERApplication<PM> : Sized
    where
        PM: PersistentMemoryRegion,
{
    // valid() captures the set of valid crash states that the application
    // may want to enforce using PoWER.  In this model of PoWER, we assume
    // that the application state is static, and there's a fixed predicate
    // over crash states that doesn't change over time.
    spec fn valid(self, state: Seq<u8>) -> bool;

    // setup() is the executable function that implements the application's
    // initialization logic, setting up the contents of the persistent memory
    // region at first boot, and returning with the region satisfying valid().
    exec fn setup(&self, pm: &mut PM)
        requires
            old(pm).inv(),
        ensures
            pm.inv(),
            self.valid(pm@.durable_state);

    // run() is the executable function that implements the application's
    // logic to recover after a crash, taking a PersistentMemoryRegionAtomic
    // that already satisfies valid(), and continuing to run until the next
    // crash.
    //
    // The application receives a permission `perm` that allows all crash
    // states specified by the application's valid() predicate.
    exec fn run<Perm, PermFactory>(&self, pm: PersistentMemoryRegionAtomic<PM>, Tracked(perm_factory): Tracked<PermFactory>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PermFactory: PermissionFactory<Seq<u8>, Perm>,
        requires
            pm.inv(),
            pm@.durable_state == pm@.read_state,
            perm_factory.valid(pm.id()),
            forall |s1, s2| self.valid(s2) ==> #[trigger] perm_factory.check_permission(s1, s2),
            self.valid(pm@.durable_state);
}

// An example toy application modeled as PoWERApplication, to validate that
// it's possible to construct this trait.  The application enforces that
// location `addr` in persistent memory is always either `val0` or `val1`.

struct ExampleApp {
    addr: u64,
    val0: u8,
    val1: u8,
}

impl<PM> PoWERApplication<PM> for ExampleApp
    where
        PM: PersistentMemoryRegion,
{
    spec fn valid(self, state: Seq<u8>) -> bool {
        &&& self.addr < state.len()
        &&& {
            ||| state[self.addr as int] == self.val0
            ||| state[self.addr as int] == self.val1
        }
    }

    exec fn setup(&self, pm: &mut PM) {
        let len = pm.get_region_size();
        if self.addr >= len {
            loop {}
        }

        pm.write(self.addr, vec![self.val0].as_slice());
        pm.flush();
    }

    exec fn run<Perm, PermFactory>(&self, pm: PersistentMemoryRegionAtomic<PM>, Tracked(perm_factory): Tracked<PermFactory>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PermFactory: PermissionFactory<Seq<u8>, Perm>,
    {
        let mut power_pm: PoWERPersistentMemoryRegion<Perm, PM> = PoWERPersistentMemoryRegion::new_atomic(pm);

        loop
            invariant
                power_pm.inv(),
                perm_factory.valid(power_pm.id()),
                self.addr < power_pm@.len(),
                <Self as PoWERApplication<PM>>::valid(*self, power_pm@.durable_state),
                forall |s1, s2| <Self as PoWERApplication<PM>>::valid(*self, s2) ==> #[trigger] perm_factory.check_permission(s1, s2),
        {
            assert forall |s| can_result_from_partial_write(s, power_pm@.durable_state, self.addr as int, seq![self.val0]) implies #[trigger] perm_factory.check_permission(power_pm@.durable_state, s) by {
                crate::pmem::pmemutil_v::lemma_can_result_from_partial_write_effect(s, power_pm@.durable_state, self.addr as int, seq![self.val0]);
            }

            power_pm.write(self.addr, vec![self.val0].as_slice(), Tracked(perm_factory.grant_permission()));
            power_pm.write(self.addr, vec![self.val1].as_slice(), Tracked(perm_factory.grant_permission()));
            power_pm.flush();

            power_pm.write(self.addr, vec![self.val1].as_slice(), Tracked(perm_factory.grant_permission()));
            power_pm.write(self.addr, vec![self.val0].as_slice(), Tracked(perm_factory.grant_permission()));
            power_pm.flush();
        }
    }
}

// Now we mechanize the soundness argument for a particular application,
// by constructing an AtomicInvariant that holds the durable_state resource
// from PersistentMemoryRegionAtomic, and enforces PoWERApplication::valid()
// on it.
//
// The soundness argument critically depends on two assumptions:
//
// - That PersistentMemoryRegionAtomic<PM> correctly models the crash
//   semantics of the PersistentMemoryRegion, and in particular, it ensures
//   that at every point in the execution, the state of the fractional
//   resource exposed by PersistentMemoryRegionAtomic has the durable_state
//   of the PersistentMemoryRegion.
//
// - `invariant_recovery_axiom()`, stated below, is a sound axiom about
//   re-constructing an AtomicInvariant that existed before the computer
//   crashed and rebooted, and that the trusted code (`main_after_crash()`,
//   defined below) is only executed after a crash when the invariant held
//   before the crash.

struct DurableResource {
    r: Frac<Seq<u8>>,
}

struct DurablePredicate<PM, A>
    where
        PM: PersistentMemoryRegion,
        A: PoWERApplication<PM>,
{
    id: int,
    app: A,
    _pm: core::marker::PhantomData<PM>,
}

impl<PM, A> InvariantPredicate<DurablePredicate<PM, A>, DurableResource> for DurablePredicate<PM, A>
    where
        PM: PersistentMemoryRegion,
        A: PoWERApplication<PM>,
{
    closed spec fn inv(pred: DurablePredicate<PM, A>, inner: DurableResource) -> bool {
        &&& inner.r.valid(pred.id, 1)
        &&& pred.app.valid(inner.r@)
    }
}

struct SoundPermission<PM, A>
    where
        PM: PersistentMemoryRegion,
        A: PoWERApplication<PM>,
{
    inv: Arc<AtomicInvariant::<DurablePredicate<PM, A>, DurableResource, DurablePredicate<PM, A>>>,
}

impl<PM, A> CheckPermission<Seq<u8>> for SoundPermission<PM, A>
    where
        PM: PersistentMemoryRegion,
        A: PoWERApplication<PM>,
{
    closed spec fn check_permission(&self, s1: Seq<u8>, s2: Seq<u8>) -> bool {
        self.inv.constant().app.valid(s2)
    }

    closed spec fn valid(&self, id: int) -> bool {
        self.inv.constant().id == id
    }

    proof fn combine(tracked self, tracked other: Self) -> (tracked combined: Self) {
        self
    }

    proof fn apply(tracked self, tracked credit: OpenInvariantCredit, tracked r: &mut Frac<Seq<u8>>, new_state: Seq<u8>) {
        open_atomic_invariant_in_proof!(credit => &self.inv => inner => {
            r.update_with(&mut inner.r, new_state);
        });
    }
}

impl<PM, A> PermissionFactory<Seq<u8>, SoundPermission<PM, A>> for SoundPermission<PM, A>
    where
        PM: PersistentMemoryRegion,
        A: PoWERApplication<PM>,
{
    closed spec fn check_permission(&self, s1: Seq<u8>, s2: Seq<u8>) -> bool {
        CheckPermission::check_permission(self, s1, s2)
    }

    closed spec fn valid(&self, id: int) -> bool {
        CheckPermission::valid(self, id)
    }

    proof fn grant_permission(tracked &self) -> (tracked perm: SoundPermission<PM, A>) {
        Self{
            inv: self.inv.clone(),
        }
    }

    proof fn clone(tracked &self) -> (tracked other: Self) {
        Self{
            inv: self.inv.clone(),
        }
    }
}

// The main_first_time() function models what happens the first time
// persistent memory is initialized by the application: the application
// predicate is only established once the application finishes setup,
// and keeps being true at all points after that.
exec fn main_first_time<PM, A>(mut pm: PM, app: A)
    where
        PM: PersistentMemoryRegion,
        A: PoWERApplication<PM>,
    requires
        pm.inv(),
{
    // Initialize the contents of the persistent memory.
    app.setup(&mut pm);

    // Set up the atomic invariant to keep track of the durable state.
    let (mut pm_atomic, Tracked(r)) = PersistentMemoryRegionAtomic::new(pm);

    let ghost pred = DurablePredicate{
        id: r.id(),
        app: app,
        _pm: core::marker::PhantomData,
    };

    let tracked inv_res = DurableResource{
        r: r
    };

    let tracked inv = AtomicInvariant::<_, _, DurablePredicate<PM, A>>::new(pred, inv_res, 0);

    // Establish that the read state matches the durable state.
    pm_atomic.flush();

    // Construct a permission that captures the application predicate.
    let tracked perm_factory = SoundPermission{
        inv: Arc::new(inv),
    };

    // Allow the application to run until the next crash.
    app.run::<_, SoundPermission::<PM, A>>(pm_atomic, Tracked(perm_factory))

    // Note that the atomic invariant continues to exist, and therefore
    // enforces that the durable state will still satisfy the application
    // predicate, at all points during the application's execution in
    // app.run().
}

// The main_after_crash() function models what happens on recovery from
// crash once the system has already been successfully initialized by
// main_first_time(), with zero or more additional crashes and recoveries
// after that.
exec fn main_after_crash<PM, A>(pm: PM, app: A)
    where
        PM: PersistentMemoryRegion,
        A: PoWERApplication<PM>,
    requires
        pm.inv(),
{
    // Construct an atomic wrapper around pm, to get a resource for durable_state.
    let (mut pm_atomic, Tracked(r)) = PersistentMemoryRegionAtomic::new(pm);

    // Restore the atomic invariant, which we assume was true before the
    // system crashed (i.e., it must have been that the previous execution
    // started with main_first_time() and got all the way to running
    // app.run(), or the previous execution started with main_after_crash().
    let ghost pred = DurablePredicate{
        id: r.id(),
        app: app,
        _pm: core::marker::PhantomData,
    };

    let tracked inv = invariant_recovery_axiom(pred);

    // Open the invariant to observe that the current state satisfies valid(),
    // because the resource in the invariant agrees with `pm_atomic`.
    open_atomic_invariant!(&inv => inner => {
        proof {
            inner.r.agree(pm_atomic.res.borrow());
        }
    });

    // Establish that the read state matches the durable state, since this
    // is technically not required by the precondition of main_after_crash().
    pm_atomic.flush();

    // Construct a permission that captures the application predicate.
    let tracked perm_factory = SoundPermission{
        inv: Arc::new(inv),
    };

    // Allow the application to run until the next crash.
    app.run::<_, SoundPermission::<PM, A>>(pm_atomic, Tracked(perm_factory))

    // Note that the atomic invariant continues to exist, and therefore
    // enforces that the durable state will still satisfy the application
    // predicate, at all points during the application's execution in
    // app.run().
}

// The invariant_recovery_axiom() states a key assumption for the
// soundness argument: that an AtomicInvariant on the logically atomic
// contents of the disk still holds after recovery.  The assumption is
// that this axiom will be invoked only in situations where we know the
// AtomicInvariant held before the crash.  This models the use of atomic
// invariants that persist across crashes in Perennial.
#[verifier::external_body]
proof fn invariant_recovery_axiom<PM, A>(pred: DurablePredicate<PM, A>) -> (tracked result: AtomicInvariant::<DurablePredicate<PM, A>, DurableResource, DurablePredicate<PM, A>>)
    where
        PM: PersistentMemoryRegion,
        A: PoWERApplication<PM>,
    ensures
        result.constant() == pred,
{
    unimplemented!()
}

}
