use super::pmcopy_t::*;
use super::pmemspec_t::*;
use super::pmem_async_spec_t::*;
use super::pmem_async_equiv_t::*;

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
        while vec.len() != len
            invariant
                vec.len() <= len,
            decreases
                len - vec.len(),
        {
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

pub proof fn flush_selective_committed(v: PersistentMemoryRegionAsyncView)
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

pub proof fn can_crash_as_committed(v: PersistentMemoryRegionAsyncView)
    ensures
        v.can_crash_as(v.committed(), Seq::new(v.outstanding_writes.len(), |i| Seq::new(size_to_chunks(v.len() as int) as nat, |j| false)))
{
    flush_selective_committed(v);
}

pub proof fn flush_preserves_len(v: PersistentMemoryRegionAsyncView)
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

pub proof fn flush_selective_preserves_len(v: PersistentMemoryRegionAsyncView, ds: Seq<Seq<bool>>)
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

pub proof fn flush_no_outstanding_writes(v: PersistentMemoryRegionAsyncView)
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

pub exec fn size_to_chunks_exec(sz: usize) -> (res: usize)
    ensures
        res == size_to_chunks(sz as int)
{
    let whole_chunks = sz / persistence_chunk_size();
    let overflowed_chunk = (sz - whole_chunks * persistence_chunk_size() + persistence_chunk_size() - 1) / persistence_chunk_size();
    whole_chunks + overflowed_chunk
}

pub proof fn flush_push(v: PersistentMemoryRegionAsyncView, w: Write)
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

pub proof fn flush_selective_push(v: PersistentMemoryRegionAsyncView, durability: Seq<Seq<bool>>, w: Write, d: Seq<bool>)
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

pub proof fn flush_selective_can_result_from_partial_write(v: PersistentMemoryRegionAsyncView, durability: Seq<Seq<bool>>, w: Write, d: Seq<bool>)
    requires
        v.outstanding_writes.len() == durability.len(),
    ensures
        can_result_from_partial_write(v.write(w.addr, w.data).flush_selective(durability.push(d)),
                                      v.flush_selective(durability),
                                      w.addr, w.data)
{
    flush_selective_push(v, durability, w, d);
}

pub proof fn can_crash_as_flush_selective(v: PersistentMemoryRegionAsyncView, crash_state: Seq<u8>, write_chunk_durability: Seq<Seq<bool>>)
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
    open(super) spec fn view(&self) -> PersistentMemoryRegionView {
        PersistentMemoryRegionView{
            read_state: self.pm@.flush().committed(),
            durable_state: if self.flush@ {
                self.pm@.flush().committed()
            } else {
                self.pm@.flush_selective(deep_view(self.durability))
            },
        }
    }

    open(super) spec fn inv(&self) -> bool {
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
        flush_selective_preserves_len(self.pm@, deep_view(self.durability));
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
            flush_selective_preserves_len(self.pm@, deep_view(self.durability));
            flush_push(self.pm@, w);
            flush_selective_can_result_from_partial_write(self.pm@, deep_view(self.durability), w, write_durable_chunks@);
        }

        self.pm.write(addr, bytes);
        self.durability.push_back(write_durable_chunks);

        proof {
            assert(deep_view(self.durability) == deep_view(old(self).durability).push(write_durable_chunks@));
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
            flush_selective_preserves_len(self.pm@, deep_view(self.durability));
            flush_push(self.pm@, w);
            flush_selective_can_result_from_partial_write(self.pm@, deep_view(self.durability), w, write_durable_chunks@);
        }

        self.pm.serialize_and_write(addr, to_write);
        self.durability.push_back(write_durable_chunks);

        proof {
            assert(deep_view(self.durability) == deep_view(old(self).durability).push(write_durable_chunks@));
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

}
