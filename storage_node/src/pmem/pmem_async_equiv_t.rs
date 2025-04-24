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

use std::collections::VecDeque;

use vstd::bytes::*;
use vstd::prelude::*;
use vstd::proph::*;

verus! {

// ProphecyVec implements a sequence of prophecy variables, each of type T.
// ProphecyVec can be viewed in spec mode as a Seq<T>, and can be resolved
// in exec mode using a Vec<T>.
pub struct ProphecyVec<T: Structural> {
    pub v: Vec<Prophecy<T>>,
}

impl<T: Structural> ProphecyVec<T> {
    pub closed spec fn view(self) -> Seq<T> {
        Seq::new(self.v@.len(), |i| self.v@[i]@)
    }

    pub fn new(len: usize) -> (res: Self)
        ensures
            res@.len() == len,
    {
        let mut vec: Vec<Prophecy<T>> = Vec::with_capacity(len);
        while vec.len() != len {
            vec.push(Prophecy::<T>::new());
        }
        Self{
            v: vec,
        }
    }

    pub fn resolve(self, v: &Vec<T>)
        requires
            self@.len() == v@.len(),
        ensures
            self@ =~= v@
    {
        broadcast use vstd::std_specs::vec::group_vec_axioms;

        let mut pv = self.v;
        let len = v.len();

        assert(self.v@.subrange(0, len as int) == pv@);

        for i in 0..len
            invariant
                self.v@.subrange(i as int, len as int) == pv@,
                self.v@.len() == len,
                v@.len() == len,
                forall |j| 0 <= j < i ==> self.v@[j]@ == #[trigger] v@[j],
        {
            let iproph = pv.remove(0);
            iproph.resolve(&v[i]);
            assert(self.v@.subrange(i+1 as int, len as int) == pv@);
        }
    }
}

impl<T: Structural> DeepView for ProphecyVec<T> {
    type V = Seq<T>;

    open spec fn deep_view(&self) -> Seq<T> {
        self.view()
    }
}

// PMRegionProph implements the correspondence between PersistentMemoryRegion
// and PersistentMemoryRegionAsync.  In particular, PMRegionProph keeps the
// PersistentMemoryRegionAsync (PMRegion) internally, and provides an API that
// satisfies PersistentMemoryRegion.

pub struct PMRegionProph<PMRegion>
    where PMRegion: PersistentMemoryRegionAsync
{
    pm: PMRegion,
    len: usize,

    // `flush` predicts that any pending writes will be successfully flushed
    // before the next system crash.  This prophecy variable is re-allocated
    // at each successful flush, to refer to the next set of pending writes,
    // before the next flush.
    flush: Prophecy<bool>,

    // `durability` predicts, for each write since the last flush,
    // whether that write's changes to each chunk are made durable
    // or not.
    durability: VecDeque<ProphecyVec<bool>>,
}

proof fn flush_selective_committed(v: PersistentMemoryRegionAsyncView)
    ensures
        v.committed() == v.flush_selective(Seq::new(v.outstanding_writes.len(), |i| Seq::new(size_to_chunks(v.len() as int) as nat, |j| false)))
    decreases
        v.outstanding_writes.len()
{
    let ghost write_chunk_durability = Seq::new(v.outstanding_writes.len(), |i| Seq::new(size_to_chunks(v.len() as int) as nat, |j| false));
    if v.outstanding_writes.len() > 0 {
        let w0 = v.outstanding_writes.first();
        let d0 = write_chunk_durability.first();
        let v_new = PersistentMemoryRegionAsyncView{
            state_at_last_flush: apply_write_selective(v.state_at_last_flush, w0, d0),
            outstanding_writes: v.outstanding_writes.skip(1),
        };
        assert(v_new.committed() == v.committed());
        flush_selective_committed(v_new);
        let ghost write_chunk_durability1 = Seq::new(v_new.outstanding_writes.len(), |i| Seq::new(size_to_chunks(v.len() as int) as nat, |j| false));
        assert(write_chunk_durability1 == write_chunk_durability.skip(1));
    }
}

proof fn can_crash_as_committed(v: PersistentMemoryRegionAsyncView)
    ensures
        v.can_crash_as(v.committed(), Seq::new(v.outstanding_writes.len(), |i| Seq::new(size_to_chunks(v.len() as int) as nat, |j| false)))
{
    flush_selective_committed(v);
}

proof fn flush_preserves_len(v: PersistentMemoryRegionAsyncView)
    requires
        v.valid()
    ensures
        v.flush().committed().len() == v.committed().len(),
    decreases
        v.outstanding_writes.len()
{
    if v.outstanding_writes.len() > 0 {
        let w = v.outstanding_writes[0];
        flush_preserves_len(PersistentMemoryRegionAsyncView{
            state_at_last_flush: apply_write(v.state_at_last_flush, w),
            outstanding_writes: v.outstanding_writes.skip(1),
        });
    }
}

proof fn flush_selective_preserves_len(v: PersistentMemoryRegionAsyncView, ds: Seq<Seq<bool>>)
    requires
        v.valid()
    ensures
        v.flush_selective(ds).len() == v.committed().len(),
    decreases
        v.outstanding_writes.len()
{
    if v.outstanding_writes.len() > 0 {
        let w0 = v.outstanding_writes[0];
        let d0 = ds[0];

        let v_new = PersistentMemoryRegionAsyncView{
            state_at_last_flush: apply_write_selective(v.state_at_last_flush, w0, d0),
            outstanding_writes: v.outstanding_writes.skip(1),
        };

        flush_selective_preserves_len(v_new, ds.skip(1));
    }
}

proof fn flush_no_outstanding_writes(v: PersistentMemoryRegionAsyncView)
    ensures
        v.flush().no_outstanding_writes()
    decreases
        v.outstanding_writes.len()
{
    if v.outstanding_writes.len() > 0 {
        let w = v.outstanding_writes[0];
        flush_no_outstanding_writes(PersistentMemoryRegionAsyncView{
            state_at_last_flush: apply_write(v.state_at_last_flush, w),
            outstanding_writes: v.outstanding_writes.skip(1),
        });
    }
}

exec fn size_to_chunks_exec(sz: usize) -> (res: usize)
    ensures
        res == size_to_chunks(sz as int)
{
    let whole_chunks = sz / persistence_chunk_size();
    let overflowed_chunk = (sz - whole_chunks * persistence_chunk_size() + persistence_chunk_size() - 1) / persistence_chunk_size();
    whole_chunks + overflowed_chunk
}

proof fn flush_push(v: PersistentMemoryRegionAsyncView, w: Write)
    ensures
        v.write(w.addr, w.data).flush().state_at_last_flush == apply_write(v.flush().state_at_last_flush, w)
    decreases
        v.outstanding_writes.len()
{
    reveal_with_fuel(PersistentMemoryRegionAsyncView::flush, 2);
    if v.outstanding_writes.len() > 0 {
        let w0 = v.outstanding_writes[0];
        let flushed_one = PersistentMemoryRegionAsyncView{
            state_at_last_flush: apply_write(v.state_at_last_flush, w0),
            outstanding_writes: v.outstanding_writes.skip(1),
        };
        assert(v.write(w.addr, w.data).outstanding_writes.skip(1) ==
               flushed_one.write(w.addr, w.data).outstanding_writes);
        flush_push(flushed_one, w);
    }
}

proof fn flush_selective_push(v: PersistentMemoryRegionAsyncView, durability: Seq<Seq<bool>>, w: Write, d: Seq<bool>)
    requires
        v.outstanding_writes.len() == durability.len(),
    ensures
        v.write(w.addr, w.data).flush_selective(durability.push(d)) == apply_write_selective(v.flush_selective(durability), w, d)
    decreases
        v.outstanding_writes.len()
{
    reveal_with_fuel(PersistentMemoryRegionAsyncView::flush, 2);

    let w0 = v.write(w.addr, w.data).outstanding_writes.first();
    let d0 = durability.push(d).first();
    let v0 = PersistentMemoryRegionAsyncView{
        state_at_last_flush: apply_write_selective(v.write(w.addr, w.data).state_at_last_flush, w0, d0),
        outstanding_writes: v.write(w.addr, w.data).outstanding_writes.skip(1),
    };

    assert(v.write(w.addr, w.data).flush_selective(durability.push(d)) == v0.flush_selective(durability.push(d).skip(1)));

    if v.outstanding_writes.len() == 0 {
        assert(v0.flush_selective(durability.push(d).skip(1)) == v0.state_at_last_flush);
    } else {
        let w1 = v.outstanding_writes.first();
        let d1 = durability.first();
        let v1 = PersistentMemoryRegionAsyncView{
            state_at_last_flush: apply_write_selective(v.state_at_last_flush, w1, d1),
            outstanding_writes: v.outstanding_writes.skip(1),
        };

        assert(v.flush_selective(durability) == v1.flush_selective(durability.skip(1)));
        assert(v0 == v1.write(w.addr, w.data));
        assert(durability.skip(1).push(d) == durability.push(d).skip(1));

        flush_selective_push(v1, durability.skip(1), w, d);

        assert(v1.write(w.addr, w.data).flush_selective(durability.skip(1).push(d)) == apply_write_selective(v1.flush_selective(durability.skip(1)), w, d));
    } 
}

proof fn flush_selective_can_result_from_partial_write(v: PersistentMemoryRegionAsyncView, durability: Seq<Seq<bool>>, w: Write, d: Seq<bool>)
    requires
        v.outstanding_writes.len() == durability.len(),
    ensures
        can_result_from_partial_write(v.write(w.addr, w.data).flush_selective(durability.push(d)),
                                      v.flush_selective(durability),
                                      w.addr, w.data)
{
    flush_selective_push(v, durability, w, d);
}

proof fn can_crash_as_flush_selective(v: PersistentMemoryRegionAsyncView, crash_state: Seq<u8>, write_chunk_durability: Seq<Seq<bool>>)
    requires
        v.can_crash_as(crash_state, write_chunk_durability)
    ensures
        write_chunk_durability.len() == v.outstanding_writes.len(),
        crash_state == v.flush_selective(write_chunk_durability),
        forall |j| 0 <= j < write_chunk_durability.len()
                ==> #[trigger] write_chunk_durability[j].len() == size_to_chunks(v.len() as int),
    decreases
        v.outstanding_writes.len()
{
}

impl<PMRegion> PersistentMemoryRegion for PMRegionProph<PMRegion>
    where PMRegion: PersistentMemoryRegionAsync
{
    closed spec fn view(&self) -> PersistentMemoryRegionView {
        PersistentMemoryRegionView{
            read_state: self.pm@.flush().committed(),
            durable_state: if self.flush@ {
                self.pm@.flush().committed()
            } else {
                self.pm@.flush_selective(self.durability.deep_view())
            },
        }
    }

    closed spec fn inv(&self) -> bool {
        &&& self.pm.inv()
        &&& self.pm@.len() == self.len
        &&& self.durability@.len() == self.pm@.outstanding_writes.len()
        &&& forall |i| 0 <= i < self.durability@.len()
                ==> #[trigger] self.durability@[i]@.len() == size_to_chunks(self.len as int)
    }

    closed spec fn constants(&self) -> PersistentMemoryConstants {
        self.pm.constants()
    }

    proof fn lemma_inv_implies_view_valid(&self) {
        self.pm.lemma_inv_implies_view_valid();
        flush_preserves_len(self.pm@);
        flush_selective_preserves_len(self.pm@, self.durability.deep_view());
    }

    fn get_region_size(&self) -> u64 {
        proof {
            self.pm.lemma_inv_implies_view_valid();
            flush_preserves_len(self.pm@);
        }
        self.pm.get_region_size()
    }

    fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
        where S: PmCopy + Sized
    {
        proof {
            self.pm.lemma_inv_implies_view_valid();
            flush_preserves_len(self.pm@);
        }
        self.pm.read_aligned::<S>(addr)
    }

    fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>)
    {
        proof {
            self.pm.lemma_inv_implies_view_valid();
            flush_preserves_len(self.pm@);
        }
        self.pm.read_unaligned(addr, num_bytes)
    }

    fn write(&mut self, addr: u64, bytes: &[u8])
    {
        let write_durable_chunks = ProphecyVec::<bool>::new(size_to_chunks_exec(self.len));

        proof {
            let ghost w = Write{ addr: addr as int, data: bytes@ };
            self.pm.lemma_inv_implies_view_valid();
            flush_preserves_len(self.pm@);
            flush_selective_preserves_len(self.pm@, self.durability.deep_view());
            flush_push(self.pm@, w);
            flush_selective_can_result_from_partial_write(self.pm@, self.durability.deep_view(), w, write_durable_chunks@);
        }

        self.pm.write(addr, bytes);
        self.durability.push_back(write_durable_chunks);

        proof {
            assert(self.durability.deep_view() == old(self).durability.deep_view().push(write_durable_chunks@));
        }
    }

    fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S)
        where S: PmCopy + Sized
    {
        let write_durable_chunks = ProphecyVec::<bool>::new(size_to_chunks_exec(self.len));

        proof {
            let ghost w = Write{ addr: addr as int, data: to_write.spec_to_bytes() };
            self.pm.lemma_inv_implies_view_valid();
            flush_preserves_len(self.pm@);
            flush_selective_preserves_len(self.pm@, self.durability.deep_view());
            flush_push(self.pm@, w);
            flush_selective_can_result_from_partial_write(self.pm@, self.durability.deep_view(), w, write_durable_chunks@);
        }

        self.pm.serialize_and_write(addr, to_write);
        self.durability.push_back(write_durable_chunks);

        proof {
            assert(self.durability.deep_view() == old(self).durability.deep_view().push(write_durable_chunks@));
        }
    }

    fn flush(&mut self)
    {
        let mut flushproph = Prophecy::<bool>::new();
        std::mem::swap(&mut self.flush, &mut flushproph);
        flushproph.resolve(&true);

        proof {
            self.pm.lemma_inv_implies_view_valid();
            flush_no_outstanding_writes(self.pm@);
            flush_preserves_len(self.pm@);
        }

        self.pm.flush();
        self.durability = VecDeque::new();
    }
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
exec fn seq_to_vec(Ghost(s): Ghost<Seq<Seq<bool>>>) -> (result: Vec<Vec<bool>>)
    ensures
        result.deep_view() == s
{
    arbitrary()
}

}
