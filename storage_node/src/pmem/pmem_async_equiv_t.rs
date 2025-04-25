// This file demonstrates a correspondence between the prophecy-based
// specification of PersistentMemoryRegion and the more explicit
// asynchronous specification of PersistentMemoryRegionAsync.
// 
// The correspondence is demonstrated by a verified transformation
// from an arbitrary PersistentMemoryRegionAsync (i.e., some PM region
// with explicit asynchronous behavior) to a PersistentMemoryRegion
// (i.e., a PM region with a prophecy-based specification), implemented
// by PMRegionProph::new().

use super::pmcopy_t::*;
use super::pmemspec_t::*;
use super::pmem_async_spec_t::*;
use super::pmem_async_equiv_v::*;

use std::collections::VecDeque;

use vstd::bytes::*;
use vstd::prelude::*;
use vstd::proph::*;

verus! {

// PMRegionProph implements the correspondence between PersistentMemoryRegion
// and PersistentMemoryRegionAsync.  In particular, PMRegionProph keeps the
// PersistentMemoryRegionAsync (PMRegion) internally, and provides an API that
// satisfies PersistentMemoryRegion.

pub struct PMRegionProph<PMRegion>
    where PMRegion: PersistentMemoryRegionAsync
{
    pub pm: PMRegion,
    pub len: usize,

    // `flush` predicts that any pending writes will be successfully flushed
    // before the next system crash.  This prophecy variable is re-allocated
    // at each successful flush, to refer to the next set of pending writes,
    // before the next flush.
    pub flush: Prophecy<bool>,

    // `durability` predicts, for each write since the last flush,
    // whether that write's changes to each chunk are made durable
    // or not.
    pub durability: VecDeque<ProphecyVec<bool>>,
}

impl<PMRegion> PMRegionProph<PMRegion>
    where PMRegion: PersistentMemoryRegionAsync
{
    pub fn new(pm: PMRegion) -> (result: PMRegionProph<PMRegion>)
        requires
            pm.inv(),
            pm@.no_outstanding_writes(),
        ensures
            result.inv(),
            result@.read_state == pm@.flush().committed(),
            result@.durable_state == pm@.committed(),
    {
        let len = pm.get_region_size() as usize;
        let result = PMRegionProph::<PMRegion>{
            pm: pm,
            len: len,
            flush: Prophecy::<bool>::new(),
            durability: VecDeque::new(),
        };
        result
    }

    // This function models what happens on crash, and demonstrates that for
    // any set of events that happen on crash (resolved prophecy variables),
    // the resulting durable_state propecized by PersistentMemoryRegion
    // matches the durable state of the explicit PersistentMemoryRegionAsync.
    #[cfg(verus_keep_ghost)]
    pub fn crash(self)
        requires
            self.inv()
    {
        broadcast use vstd::std_specs::vecdeque::group_vec_dequeue_axioms;

        let mut mself = self;

        // First, resolve the prophecy that we flush all pending writes
        // before crashing: this is false because we just crashed.
        mself.flush.resolve(&false);

        // Now, pick any state that PersistentMemoryRegionAsync says we
        // can crash into.  We must first prove to Verus that any such
        // state exists at all.
        proof {
            can_crash_as_committed(mself.pm@);
        }

        let ghost (crash_state, write_chunk_durability) = choose |bytes: Seq<u8>, write_chunk_durability: Seq<Seq<bool>>| mself.pm@.can_crash_as(bytes, write_chunk_durability);

        // This axiom is used to convert a ghost predictions into an
        // exec-mode Vec<Vec<bool>> representing the same values.
        // This is not strictly allowed by vstd::proph, but logically
        // the choices were part of the execution, in the sense of the
        // argument from the "Future is ours" paper.
        let predictions_vec = seq_to_vec(Ghost(write_chunk_durability));

        // Now that we know what durability choices were made, resolve
        // our prophecies to the same values.
        let mut durability = mself.durability;
        let dlen = durability.len();
        assert(durability@ == mself.durability@.subrange(0, dlen as int));
        assert forall |j| 0 <= j < dlen implies #[trigger] predictions_vec[j].len() == size_to_chunks(mself.pm@.len() as int) by {
            assert(write_chunk_durability[j].len() == size_to_chunks(mself.pm@.len() as int));
        }
        for i in 0..dlen
            invariant
                mself.durability@.len() == dlen,
                predictions_vec.len() == dlen,
                crash_state == mself.pm@.flush_selective(predictions_vec.deep_view()),
                durability@ == mself.durability@.subrange(i as int, dlen as int),
                forall |j| 0 <= j < dlen
                    ==> #[trigger] predictions_vec[j].len() == size_to_chunks(mself.pm@.len() as int),
                forall |j| 0 <= j < dlen
                    ==> #[trigger] mself.durability@[j]@.len() == size_to_chunks(mself.pm@.len() as int),
                forall |j| 0 <= j < i
                    ==> #[trigger] mself.durability@[j]@ == predictions_vec@[j]@
        {
            let p = durability.pop_front().unwrap();
            assert(durability@ == mself.durability@.subrange(i as int + 1, dlen as int));
            assert(predictions_vec[i as int].len() == size_to_chunks(mself.pm@.len() as int));
            assert(mself.durability@[i as int]@.len() == size_to_chunks(mself.pm@.len() as int));
            p.resolve(&predictions_vec[i]);
        }

        assert forall |i| 0 <= i < dlen implies #[trigger] mself.durability.deep_view()[i] == predictions_vec.deep_view()[i] by {
            assert(mself.durability.deep_view()[i] == mself.durability@[i]@);
            assert(predictions_vec.deep_view()[i] == predictions_vec@[i]@);
        }
        assert(mself.durability.deep_view() =~= predictions_vec.deep_view());

        // With the propecies resolved, prove that our prophecy-based
        // durable_state is the same as the arbitrary crash state that
        // we picked above from PersistentMemoryRegionAsync.
        assert(mself@.durable_state == crash_state);
    }
}

#[verifier::external_body]
#[cfg(verus_keep_ghost)]
exec fn seq_to_vec(Ghost(s): Ghost<Seq<Seq<bool>>>) -> (result: Vec<Vec<bool>>)
    ensures
        result.deep_view() == s
{
    arbitrary()
}

}
