/*

  This file specifies, with the `PersistentMemory` type, the behavior
  of a persistent memory region. One of the things it models is what
  can happen to the persistent memory region if the system crashes in
  the middle of a write.

*/

use crate::main_t::can_only_crash_as_state;
use crate::multilog_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::bytes::*;
use vstd::set::*;
use vstd::slice::*;
use crate::sccf::CheckPermission;

verus! {

    pub open spec fn maybe_corrupted(bytes: Seq<u8>, true_bytes: Seq<u8>, addrs: Seq<int>) -> bool {
        &&& bytes.len() == true_bytes.len() == addrs.len()
        &&& forall |i: int| #![auto] 0 <= i < bytes.len() ==> maybe_corrupted_byte(bytes[i], true_bytes[i], addrs[i])
    }

    pub open spec fn maybe_corrupted_u64(val: u64, true_val: u64, addrs: Seq<int>) -> bool 
    {
        maybe_corrupted(spec_u64_to_le_bytes(val), spec_u64_to_le_bytes(true_val), addrs)
    }

    pub open spec fn maybe_corrupted_u64_from_le_bytes(val: u64, true_bytes: Seq<u8>, addrs: Seq<int>) -> bool 
    {
        maybe_corrupted(spec_u64_to_le_bytes(val), true_bytes, addrs)
    }

    pub closed spec fn maybe_corrupted_byte(byte: u8, true_byte: u8, addr: int) -> bool;

    pub open spec fn all_elements_unique(seq: Seq<int>) -> bool {
        forall |i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] != seq[j]
    }

    // We mark this as `external_body` so that the verifier can't see
    // that there's nothing important in it and thereby shortcut some
    // checks.

    #[verifier(external_body)]
    pub struct PersistentMemory {
        /// Models a persistent memory region.
        handle: usize
    }

    impl PersistentMemory {
        #[verifier(external_body)]
        pub exec fn create(capacity: u64) -> (result: Result<Self, ()>)
            ensures
                match result {
                    Ok(pm) => pm@.state.len() == capacity && pm@.no_outstanding_writes(),
                    Err(_) => true
                }
        {
            unimplemented!()
        }

        #[verifier(external_body)]
        pub closed spec fn impervious_to_corruption(self) -> bool
        {
            unimplemented!()
        }
    }

    /// We model the persistent memory as getting flushed in chunks,
    /// where each chunk has `persistence_chunk_size` bytes. We refer
    /// to chunk number `id` as the set of addresses `addr` such that
    /// `addr / persistence_chunk_size == id`.
    pub spec const persistence_chunk_size: int = 8;

    /// We model the state of each byte of persistent memory as
    /// follows.  `state_at_last_flush` contains the contents
    /// immediately after the most recent flush. `outstanding_write`
    /// contains `None` if there's no outstanding write, or `Some(b)`
    /// if there's an outstanding write of `b`. We don't model the
    /// possibility of there being multiple outstanding writes because
    /// we restrict reads and writes to not be allowed at locations
    /// with currently outstanding writes.

    #[verifier::ext_equal]
    pub struct PersistentMemoryByte {
        pub state_at_last_flush: u8,
        pub outstanding_write: Option<u8>,
    }

    impl PersistentMemoryByte {
        pub open spec fn write(self, byte: u8) -> Self
        {
            // Self { outstanding_write: Some(byte), ..self }
            Self {
                state_at_last_flush: self.state_at_last_flush,
                outstanding_write: Some(byte)
            }
        }

        pub open spec fn flush_byte(self) -> u8
        {
            match self.outstanding_write {
                None => self.state_at_last_flush,
                Some(b) => b
            }
        }

        pub open spec fn flush(self) -> Self
        {
            Self { state_at_last_flush: self.flush_byte(), outstanding_write: None }
        }
    }

    #[verifier::ext_equal]
    pub struct PersistentMemoryView
    {
        pub state: Seq<PersistentMemoryByte>
    }

    impl PersistentMemoryView
    {
        pub open spec fn len(self) -> nat
        {
            self.state.len()
        }

        pub open spec fn write(self, addr: int, bytes: Seq<u8>) -> Self
        {
            Self { state: self.state.map(|pos: int, pre_byte: PersistentMemoryByte|
                                         if addr <= pos < addr + bytes.len() { pre_byte.write(bytes[pos - addr]) }
                                         else { pre_byte }) }
        }

        pub open spec fn flush(self) -> Self
        {
            Self { state: self.state.map(|_addr, b: PersistentMemoryByte| b.flush()) }
        }

        pub open spec fn no_outstanding_writes_in_range(self, i: int, j: int) -> bool
        {
            forall |k| #![trigger(self.state[k].outstanding_write)] i <= k < j ==> self.state[k].outstanding_write.is_none()
        }

        pub open spec fn no_outstanding_writes(self) -> bool
        {
            Self::no_outstanding_writes_in_range(self, 0, self.state.len() as int)
        }

        pub open spec fn committed(self) -> Seq<u8>
        {
            self.state.map(|_addr, b: PersistentMemoryByte| b.state_at_last_flush)
        }

        pub open spec fn flush_committed(self) -> Seq<u8>
        {
            self.flush().committed()
        }

        pub open spec fn in_flight(self) -> Seq<Option<u8>>
        {
            self.state.map(|_addr, b: PersistentMemoryByte| b.outstanding_write)
        }

        pub open spec fn chunk_corresponds_at_last_flush(self, chunk: int, bytes: Seq<u8>) -> bool
        {
            forall |addr: int| {
                &&& 0 <= addr < self.len()
                &&& addr / persistence_chunk_size == chunk
            } ==> #[trigger] bytes[addr] == self.state[addr].state_at_last_flush
        }

        pub open spec fn chunk_corresponds_after_flush(self, chunk: int, bytes: Seq<u8>) -> bool
        {
            forall |addr: int| {
                &&& 0 <= addr < self.len()
                &&& addr / persistence_chunk_size == chunk
            } ==> #[trigger] bytes[addr] == self.state[addr].flush_byte()
        }

        pub open spec fn can_crash_as(self, bytes: Seq<u8>) -> bool
        {
            &&& bytes.len() == self.len()
            &&& forall |chunk| {
                  ||| self.chunk_corresponds_at_last_flush(chunk, bytes)
                  ||| self.chunk_corresponds_after_flush(chunk, bytes)
              }
        }
    }

    impl PersistentMemory {
        pub open spec fn view(self) -> PersistentMemoryView;

        /// This is the model of some external routine that queries
        /// how many bytes are in the persistent memory region.
        #[verifier(external_body)]
        pub exec fn get_capacity(&self) -> (result: u64)
            ensures result == self@.len()
        {
            unimplemented!()
        }

        /// This is the model of some external routine that reads
        /// the `num_bytes` bytes at address `addr`.
        #[verifier(external_body)]
        pub exec fn read(&self, addr: u64, num_bytes: u64) -> (out: (Vec<u8>, Ghost<Seq<int>>))
            requires
                addr + num_bytes <= self@.state.len(),
                self@.no_outstanding_writes_in_range(addr as int, addr + num_bytes)
            ensures
                ({ 
                    let (bytes, addrs) = out;
                    let pm_bytes = self@.committed().subrange(addr as int, addr + num_bytes);
                    &&& addrs =~= Ghost(Seq::<int>::new(num_bytes as nat, |i: int| i + addr))
                    &&& maybe_corrupted(bytes@, pm_bytes, addrs@)
                    &&& all_elements_unique(addrs@)
                    &&& self.impervious_to_corruption() ==> bytes@ == pm_bytes
                })
        {
            unimplemented!()
        }

        /// This is the model of some external routine that writes
        /// `bytes` starting at address `addr`.
        #[verifier(external_body)]
        pub exec fn write(&mut self, addr: u64, bytes: &[u8])
            requires
                addr + bytes@.len() <= (old(self))@.len(),
                old(self)@.no_outstanding_writes_in_range(addr as int, addr + bytes@.len())
            ensures
                self@ == old(self)@.write(addr as int, bytes@),
                self.impervious_to_corruption() == old(self).impervious_to_corruption()
        {
            unimplemented!()
        }

        /// This is the model of a flush routine that writes all outstanding
        /// bytes durably.
        #[verifier(external_body)]
        pub exec fn flush(&mut self)
            ensures
                self@ == old(self)@.flush(),
                self.impervious_to_corruption() == old(self).impervious_to_corruption()
        {
            unimplemented!()
        }
    }

    /// A `WriteRestrictedPersistentMemory<P>` object wraps a
    /// `PersistentMemory` object to restrict how it's written.
    /// Untrusted code passed one of these can only write to the
    /// encapsulated persistent memory by providing a permission of
    /// type `P`. That permission must allow all possible states `s`
    /// such that crashing in the middle of the write might leave the
    /// persistent memory in state `s`.
    pub struct WriteRestrictedPersistentMemory<P>
        where
            P: CheckPermission<Seq<u8>>
    {
        pm: PersistentMemory,
        ghost perm: Option<P> // unused, but Rust demands some reference to P
    }

    impl <P> WriteRestrictedPersistentMemory<P>
        where
            P: CheckPermission<Seq<u8>>
    {
        pub closed spec fn view(self) -> PersistentMemoryView {
            self.pm@
        }

        pub closed spec fn impervious_to_corruption(self) -> bool {
            self.pm.impervious_to_corruption()
        }

        pub exec fn new(pm: PersistentMemory) -> (wrpm: Self)
            ensures
                wrpm@ == pm@,
                wrpm.impervious_to_corruption() == pm.impervious_to_corruption()
        {
            Self { pm: pm, perm: None }
        }

        pub exec fn get_pm_ref(&self) -> (pm: &PersistentMemory)
            ensures
                pm@ == self@,
                pm.impervious_to_corruption() == self.impervious_to_corruption()
        {
            &self.pm
        }

        /// This `write` function can only be called if a crash in the
        /// middle of the requested write will leave the persistent
        /// memory in a state allowed by `perm`. The state must be
        /// allowed no matter what subset of the persistence chunks
        /// have been flushed.
        pub exec fn write(&mut self, addr: u64, bytes: &[u8], perm: Tracked<&P>)
            requires
                addr + bytes@.len() <= old(self)@.len(),
                old(self)@.no_outstanding_writes_in_range(addr as int, addr + bytes@.len()),
                forall |s| old(self)@.write(addr as int, bytes@).can_crash_as(s) ==> #[trigger] perm@.check_permission(s)
            ensures
                self@ == old(self)@.write(addr as int, bytes@),
                self.impervious_to_corruption() == old(self).impervious_to_corruption()
        {
            self.pm.write(addr, bytes)
        }

        /// The `flush` function can always be called if you have a mutable
        /// reference to `self`. After all, on every write we check that any
        /// crash state, including the one resulting from a full flush, is
        /// allowed.
        pub exec fn flush(&mut self)
            ensures
                self@ == old(self)@.flush(),
                self.impervious_to_corruption() == old(self).impervious_to_corruption()
        {
            self.pm.flush()
        }
    }

    /// A `MultiLogPersistentMemory` represents an ordered list of one 
    /// or more persistent memory regions grouped into a multilog.
    /// The main log is required and stores the IB
    pub struct MultiLogPersistentMemory {
        pub regions: Vec<PersistentMemory>
    }

    impl MultiLogPersistentMemory {
        pub closed spec fn view(self) -> MultiLogPersistentMemoryView
        {
            MultiLogPersistentMemoryView {
                regions: Seq::<PersistentMemoryView>::new(self.regions@.len(), |i| self.regions[i]@)
            }
        }

        pub open spec fn no_outstanding_writes(self) -> bool 
        {
            forall |i: int| #[trigger] self.regions[i]@.no_outstanding_writes()
        }

        pub open spec fn no_outstanding_writes_in_range(self, index: int, i: int, j: int) -> bool 
        {
            forall |k| #![trigger(self.regions[index]@.state[k].outstanding_write)] i <= k < j ==> 
                self.regions[index]@.state[k].outstanding_write.is_none()
        }

        pub closed spec fn impervious_to_corruption(self) -> bool;

        #[verifier::external_body]
        pub exec fn read(&self, index: usize, addr: u64, num_bytes: u64) -> (out: (Vec<u8>, Ghost<Seq<int>>))
            requires 
                1 <= index < self@.len(),
                addr + num_bytes <= self@[index as int].len()
            ensures 
                ({
                    let (bytes, addrs) = out;
                    &&& addrs =~= Ghost(Seq::<int>::new(num_bytes as nat, |i: int| i + addr))
                    &&& maybe_corrupted(bytes@, self@[index as int].committed().subrange(addr as int, addr + num_bytes), addrs@)
                    &&& all_elements_unique(addrs@)
                    &&& self.impervious_to_corruption() ==> bytes@ == self@[index as int].committed().subrange(addr as int, addr + num_bytes)
                })
        {
            self.regions[index].read(addr, num_bytes)
        }

    }

    pub struct MultiLogWriteRestrictedPersistentMemory<P> 
        where 
            P: CheckPermission<Seq<Seq<u8>>>
    {
        pms: MultiLogPersistentMemory,
        ghost perm: Option<P>,
    }

    impl<P> MultiLogWriteRestrictedPersistentMemory<P> 
        where 
            P: CheckPermission<Seq<Seq<u8>>>
    {
        pub closed spec fn view(self) -> MultiLogPersistentMemoryView
        {
            MultiLogPersistentMemoryView {
                regions: Seq::<PersistentMemoryView>::new(self.pms@.len(), |i| self.pms.regions[i]@)
            }
        }

        pub closed spec fn impervious_to_corruption(self) -> bool {
            self.pms.impervious_to_corruption()
        }

        pub closed spec fn no_outstanding_writes(self) -> bool 
        {
            self.pms.no_outstanding_writes()
        }

        pub exec fn new(regions: MultiLogPersistentMemory) -> (wrpms: Self)
            ensures 
                wrpms@ == regions@,
                ({
                    let (r_ib, r_headers) = multilog_to_views(regions@.committed()[0]);
                    let (w_ib, w_headers) = multilog_to_views(wrpms@.committed()[0]);
                    &&& r_ib == w_ib 
                    &&& r_headers =~= w_headers
                    &&& r_headers.log_num_bytes =~= w_headers.log_num_bytes
                }),
                wrpms.impervious_to_corruption() == regions.impervious_to_corruption(),
                wrpms.no_outstanding_writes() == regions.no_outstanding_writes(),
        {
            Self {
                pms: regions,
                perm: None
            }
        }

        pub closed spec fn spec_get_pms(&self) -> MultiLogPersistentMemory
        {
            self.pms
        }

        pub exec fn get_pms_ref(&self) -> (pms: &MultiLogPersistentMemory)
            ensures 
                pms@ == self@,
                pms.impervious_to_corruption() == self.impervious_to_corruption(),
                pms == self.spec_get_pms()
        {
            &self.pms
        }

        // TODO: implement based on WriteRestrictedPersistentMemory or make unimplemented with external_body
        pub exec fn write(&mut self, index: usize, addr: u64, bytes: &[u8], perm: Tracked<&P>) 
            requires 
                addr + bytes@.len() <= old(self)@[index as int].len(),
                forall |s| old(self)@.write(index as int, addr as int, bytes@).can_crash_as(s) ==> #[trigger] perm@.check_permission(s),
                old(self)@[index as int].no_outstanding_writes_in_range(addr as int, addr + bytes@.len()),
            ensures 
                self@ == old(self)@.write(index as int, addr as int, bytes@),
                self.impervious_to_corruption() == old(self).impervious_to_corruption(),
        {
            assume(false);
        }

        #[verifier::external_body]
        pub exec fn flush(&mut self)
            ensures 
                self@.len() == old(self)@.len(),
                self@ == old(self)@.flush(),
                self.impervious_to_corruption() == old(self).impervious_to_corruption(),
        {
            unimplemented!()
        }
    }

    #[verifier::ext_equal]
    pub struct MultiLogPersistentMemoryView {
        pub regions: Seq<PersistentMemoryView>
    }

    impl MultiLogPersistentMemoryView {
        pub open spec fn committed(self) -> Seq<Seq<u8>>
        {
            Seq::<Seq<u8>>::new(self.len(), |i: int| self[i].committed())
        }

        pub open spec fn flush_committed(self) -> Seq<Seq<u8>>
        {
            Seq::<Seq<u8>>::new(self.len(), |i: int| self[i].flush_committed())
        }

        pub open spec fn in_flight(self) -> Seq<Seq<Option<u8>>>
        {
            Seq::<Seq<Option<u8>>>::new(self.len(), |i: int| self[i].in_flight())
        }

        pub open spec fn len(self) -> nat 
        {
            self.regions.len()
        }

        pub open spec fn write(self, index: int, addr: int, bytes: Seq<u8>) -> Self 
        {
            Self {
                regions: self.regions.map(|pos: int, pre_view: PersistentMemoryView| 
                    if pos == index {
                        pre_view.write(addr, bytes)
                    } else {
                        pre_view
                    }
                )
            }
        }

        pub open spec fn flush(self) -> Self 
        {
            Self { regions: self.regions.map(|pos, pm: PersistentMemoryView| pm.flush()) }
        }

        pub open spec fn spec_index(self, i: int) -> PersistentMemoryView 
        {
            self.regions[i]
        }

        pub open spec fn can_crash_as(self, crash_bytes: Seq<Seq<u8>>) -> bool 
        {
            &&& crash_bytes.len() == self.len()
            &&& forall |i: int| #![auto] 0 <= i < self.len() ==> {
                    &&& crash_bytes[i].len() == self[i].len()
                    &&& forall |chunk| #![auto] {
                        ||| self[i].chunk_corresponds_at_last_flush(chunk, crash_bytes[i])
                        ||| self[i].chunk_corresponds_after_flush(chunk, crash_bytes[i])
                    }
                }
        }

        pub open spec fn no_outstanding_writes(self) -> bool {
            forall |i: int| #![auto] 0 <= i < self.len() ==> self[i].no_outstanding_writes()
        }

        // takes a view of the to_write argument to write so that we can use this spec function directly
        pub open spec fn no_outstanding_writes_in_range(self, index: int, start: int, end: int) -> bool
        {
            self[index].no_outstanding_writes_in_range(start, end)
        }
    }
}
