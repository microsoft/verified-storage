#![allow(unused_imports)]
// #![verus::trusted]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;

verus! {

// This enumeration represents the various errors that can be
// returned from log operations. They're self-explanatory.
#[derive(Debug)]
pub enum MultilogErr {
    CantSetupWithFewerThanOneRegion,
    CantSetupWithMoreThanMaxRegions { max_num_regions: u64 },
    CapacityMustBePositive { which_log: u64 },
    SpaceNeededForSetupExceedsMax,
    InsufficientSpaceForSetup { required_space: u64 },
    StartFailedDueToMultilogIDMismatch { multilog_id_expected: u128, multilog_id_read: u128 },
    CRCMismatch,
    InvalidLogIndex,
    InsufficientSpaceForAppend { available_space: u64 },
    CantReadBeforeHead { head: u128 },
    CantReadPastTail { tail: u128 },
    CantAdvanceHeadPositionBeforeHead { head: u128 },
    CantAdvanceHeadPositionBeyondTail { tail: u128 },
    PmemErr { err: PmemError },
    NotYetImplemented,
}

// An `AbstractLogState` is an abstraction of a single log, of
// which an abstract multilog is composed. Its fields are:
//
// `head` -- the logical position of the first accessible byte
// in the log
//
// `log` -- the accessible bytes in the log, logically starting
// at position `head`
#[verifier::ext_equal]
pub struct AtomicLogState {
    pub head: int,
    pub log: Seq<u8>,
}

impl AtomicLogState {
    // This is the specification for the initial state of an
    // abstract log.
    pub open spec fn initialize() -> Self {
        Self { head: 0int, log: Seq::<u8>::empty() }
    }

    // This is the specification for what it means to append to a log.
    // It appends the given bytes to the `pending` field.
    pub open spec fn append(self, bytes: Seq<u8>) -> Self {
        Self { log: self.log + bytes, ..self }
    }

    // This is the specification for what it means to advance the
    // head to a given new value `new_value`.
    pub open spec fn advance_head(self, new_head: int) -> Self {
        let new_log = self.log.subrange(new_head - self.head, self.log.len() as int);
        Self { head: new_head, log: new_log, ..self }
    }

    // This is the specification for what it means to read `len`
    // bytes from a certain virtual position `pos` in the abstract
    // log.
    pub open spec fn read(self, pos: int, len: int) -> Seq<u8> {
        self.log.subrange(pos - self.head, pos - self.head + len)
    }

    pub open spec fn tail(self) -> int {
        self.head + self.log.len()
    }
}

#[verifier::ext_equal]
pub struct MultilogConstants {
    pub id: u128,
    pub capacities: Seq<u64>,
}

// An `AbstractMultiLogState` is an abstraction of a collection of
// logs that can be atomically collectively appended to. It
// consists of a sequence of logs of type `AtomicLogState`.
#[verifier::ext_equal]
pub struct AtomicMultilogState {
    pub logs: Seq<AtomicLogState>,
}

#[verifier::ext_equal]
impl AtomicMultilogState {
    // This is the specification for the number of logs in a
    // multilog.
    pub open spec fn num_logs(self) -> nat {
        self.logs.len()
    }

    // This is the specification for indexing into the sequence of
    // logs and getting the one at the given index `which_log`. Naming
    // it `spec_index` means it will be used whenever a term `s[w]` is
    // used in a specification where `s` is an `AtomicMultilogState`.
    pub open spec fn spec_index(self, which_log: int) -> AtomicLogState {
        self.logs[which_log]
    }

    // This is the specification for the initial state of an
    // abstract multilog.
    pub open spec fn initialize(num_logs: nat) -> Self {
        Self { logs: Seq::<AtomicLogState>::new(num_logs, |i| AtomicLogState::initialize()) }
    }

    // This is the specification for the operation of appending to an
    // abstract multilog.
    pub open spec fn append(self, which_log: int, bytes_to_append: Seq<u8>) -> Self {
        Self { logs: self.logs.update(which_log, self.logs[which_log].append(bytes_to_append)) }
    }

    // This is the specification for the operation of advancing
    // the head of one of the logs in a multilog.
    pub open spec fn advance_head(self, which_log: int, new_head: int) -> Self {
        Self { logs: self.logs.update(which_log, self.logs[which_log].advance_head(new_head)) }
    }

    // This is the specification for what it means to read `len`
    // bytes from a certain virtual position `pos` in the log
    // with a certain index `which_log`:
    pub open spec fn read(self, which_log: int, pos: int, len: int) -> Seq<u8> {
        self.logs[which_log].read(pos, len)
    }

    pub open spec fn compatible_with_constants(self, c: MultilogConstants) -> bool {
        self.num_logs() == c.capacities.len()
    }
}

#[verifier::ext_equal]
pub struct RecoveredMultilogState {
    pub c: MultilogConstants,
    pub state: AtomicMultilogState,
}

impl RecoveredMultilogState {
    pub open spec fn valid(self) -> bool {
        &&& self.state.compatible_with_constants(self.c)
        &&& self.state.num_logs() == self.c.capacities.len()
    }

    pub open spec fn initialize(id: u128, capacities: Seq<u64>) -> Self {
        Self {
            c: MultilogConstants { id, capacities },
            state: AtomicMultilogState::initialize(capacities.len()),
        }
    }
}

#[verifier::ext_equal]
pub struct MultilogView {
    pub c: MultilogConstants,
    pub durable: AtomicMultilogState,
    pub tentative: AtomicMultilogState,
}

impl MultilogView {
    pub open spec fn valid(self) -> bool {
        &&& self.durable.compatible_with_constants(self.c)
        &&& self.tentative.compatible_with_constants(self.c)
    }

    pub open spec fn abort(self) -> Self {
        Self { tentative: self.durable, ..self }
    }

    pub open spec fn commit(self) -> Self {
        Self { durable: self.tentative, ..self }
    }

    pub open spec fn recover(self) -> RecoveredMultilogState {
        RecoveredMultilogState { c: self.c, state: self.durable }
    }
}

// This is the specification that `LogImpl` provides for data
// bytes it reads. It says that those bytes are correct unless
// there was corruption on the persistent memory between the last
// write and this read.
pub open spec fn read_correct_modulo_corruption(
    bytes: Seq<u8>,
    true_bytes: Seq<u8>,
    pmc: PersistentMemoryConstants,
) -> bool {
    // There must exist a sequence of distinct
    // addresses `addrs` such that the nth byte of `bytes` is
    // a possibly corrupted version of the nth byte of
    // `true_bytes` read from the nth address in `addrs`.  We
    // don't require the sequence of addresses to be
    // contiguous because the data might not be contiguous on
    // disk (e.g., if it wrapped around the log area).
    exists|addrs: Seq<int>|
        {
            &&& addrs.no_duplicates()
            &&& #[trigger] pmc.maybe_corrupted(bytes, true_bytes, addrs)
        }
}

} // verus!
