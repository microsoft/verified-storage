# PoWER soundness proofs

This file describes the three formalized arguments of soundness for the
PoWER specification approach.

## Soundness of the PoWER API by correspondence to atomic invariants in Verus

We formalize the notion that a PoWER specification implies an atomic invariant
about the durable state of the storage device at any instant where a crash might
occur, where the atomic invariant maintains the same predicate about the durable
state that is implied by `perm.permits()` in the PoWER specification.

The formalization can be found in
[`capybaraKV/capybarakv/src/pmem/power_sound_t.rs`](../capybaraKV/capybarakv/src/pmem/power_sound_t.rs).
The
formal argument builds on a model of persistent storage that exposes a ghost
resource representing the state of the durable storage at any given time, based
on Perennial's model of reasoning about crash safety; this model is formalized
in
[`capybaraKV/capybarakv/src/pmem/power_t.rs`](../capybaraKV/capybarakv/src/pmem/power_t.rs).
The comments in
[`power_sound_t.rs`](../capybaraKV/capybarakv/src/pmem/power_sound_t.rs)
describe the soundness argument in more detail.

The proofs in this formalization are checked as part of building and
verifying all of the proofs in the `capybarakv` crate using Verus
(e.g., by running `verify-ae.sh`).

## Soundness of the PoWER API by correspondence to CHL

We formalize a correspondence between the preconditions enforced by the PoWER
specification and a crash condition established in Crash Hoare Logic, using the
Perennial framework to model a simple representation of an arbitrary program
that follows PoWER's precondition requirements, and using that to demonstrate
that the resulting program also maintains a corresponding CHL crash invariant.

This formalization can be found in the Perennial repo, at [https://github.com/mit-pdos/perennial/blob/master/src/program_proof/verus/wrs.v](https://github.com/mit-pdos/perennial/blob/master/src/program_proof/verus/wrs.v).

The proofs in this formalization can be checked by building
Perennial, following the instructions in the [Perennial
repo](https://github.com/mit-pdos/perennial).  Building Perennial 
can take up to 2 hours. Alternatively, this
proof is built and checked as part of the Perennial CI setup, so you can
check whether the latest CI checks in Perennial completed successfully,
as represented by a green or red CI badge at the top of the [Perennial
Github page](https://github.com/mit-pdos/perennial).

## Soundness of the PoWER API's prophecy model of durable state

We formalize a correspondence between PoWER's prophecy model of durable
state and a more explicit model that explicitly tracks outstanding
writes and models the fact that some subset of these writes are applied
to durable state on crash, at the granularity of each chunk in persistent
memory.

The explicit model of asynchronous persistent memory can be found in
[`capybaraKV/capybarakv/src/pmem/pmem_async_spec_t.rs`](../capybaraKV/capybarakv/src/pmem/pmem_async_spec_t.rs),
and the correspondence to the prophecy model can be found in
[`capybaraKV/capybarakv/src/pmem/pmem_async_equiv_t.rs`](../capybaraKV/capybarakv/src/pmem/pmem_async_equiv_t.rs);
the latter file describes the correspondence in more detail.

The proofs in this formalization are checked as part of building and
verifying all of the proofs in the `capybarakv` crate using Verus
(e.g., by running `verify-ae.sh`).
