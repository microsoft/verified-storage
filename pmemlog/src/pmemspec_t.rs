/*

  This file specifies, with the `PersistentMemory` type, the behavior
  of a persistent memory region. One of the things it models is what
  can happen to the persistent memory region if the system crashes in
  the middle of a write.

*/

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::bytes::*;
use vstd::set::*;
use vstd::slice::*;
use crate::sccf::CheckPermission;

verus! {

    pub open spec fn maybe_corrupted(bytes: Seq<u8>, true_bytes: Seq<u8>, addrs: Seq<int>) -> bool {
        if bytes.len() != true_bytes.len() || bytes.len() != addrs.len() {
            false
        } else {
            forall |i: int| #![auto] 0 <= i < bytes.len() ==> maybe_corrupted_byte(bytes[i], true_bytes[i], addrs[i])
        }
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
                    Ok(pm) => pm@.len() == capacity,
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

    impl PersistentMemory {
        pub open spec fn view(self) -> Seq<u8>;

        /// Return the byte at address `addr` after writing
        /// `write_bytes` to address `write_addr`, if the byte at
        /// `addr` before the write was `prewrite_byte`.
        pub open spec fn update_byte_to_reflect_write(addr: int, prewrite_byte: u8, write_addr: int,
                                                      write_bytes: Seq<u8>) -> u8
        {
            if write_addr <= addr && addr < write_addr + write_bytes.len() {
                write_bytes[addr - write_addr]
            }
            else {
                prewrite_byte
            }
        }

        /// Return the contents of persistent memory after writing
        /// `write_bytes` to address `write_addr`, if the contents
        /// before the write was `prewrite_contents`.
        pub open spec(checked) fn update_contents_to_reflect_write(prewrite_contents: Seq<u8>, write_addr: int,
                                                                   write_bytes: Seq<u8>) -> Seq<u8>
            recommends
                0 <= write_addr,
                write_addr + write_bytes.len() <= prewrite_contents.len(),
        {
            Seq::<u8>::new(prewrite_contents.len(),
                           |addr| Self::update_byte_to_reflect_write(addr, prewrite_contents[addr],
                                                                     write_addr, write_bytes))
        }

        /// Return the byte at address `addr` after initiating (but
        /// not necessarily completing) a write of `write_bytes` to
        /// address `write_addr`, given that the byte at `addr` before
        /// the write was `prewrite_byte` and given that the set of
        /// chunk IDs that have been flushed since the initiation of
        /// the write is `chunks_flushed`.
        pub open spec fn update_byte_to_reflect_partially_flushed_write(addr: int, prewrite_byte: u8, write_addr: int,
                                                                        write_bytes: Seq<u8>,
                                                                        chunks_flushed: Set<int>) -> u8
        {
            if chunks_flushed.contains(addr / persistence_chunk_size) {
                Self::update_byte_to_reflect_write(addr, prewrite_byte, write_addr, write_bytes)
            }
            else {
                prewrite_byte
            }
        }

        /// Return the contents of persistent memory after initiating
        /// (but not necessarily completing) a write of `write_bytes`
        /// to address `write_addr`, given that the contents before
        /// the write were `prewrite_contents` and given that the set of
        /// chunk IDs that have been flushed since the initiation of
        /// the write is `chunks_flushed`.
        pub open spec(checked) fn update_contents_to_reflect_partially_flushed_write(contents: Seq<u8>, write_addr: int,
                                                                                     write_bytes: Seq<u8>,
                                                                                     chunks_flushed: Set<int>) -> Seq<u8>
            recommends
                0 <= write_addr,
                write_addr + write_bytes.len() <= contents.len(),
        {
            Seq::<u8>::new(contents.len(),
                           |addr| Self::update_byte_to_reflect_partially_flushed_write(addr, contents[addr], write_addr,
                                                                                       write_bytes, chunks_flushed))
        }

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
                addr + num_bytes <= self@.len(),
            ensures
                ({ 
                    let (bytes, addrs) = out;
                    &&& addrs =~= Ghost(Seq::<int>::new(num_bytes as nat, |i: int| i + addr))
                    &&& maybe_corrupted(bytes@, self@.subrange(addr as int, addr + num_bytes), addrs@)
                    &&& all_elements_unique(addrs@)
                    &&& self.impervious_to_corruption() ==> bytes@ == self@.subrange(addr as int, addr + num_bytes)
                })
        {
            unimplemented!()
        }

        /// This is the model of some external routine that writes
        /// `bytes` starting at address `addr`.
        #[verifier(external_body)]
        pub exec fn write(&mut self, addr: u64, bytes: &[u8])
            requires
                addr + bytes@.len() <= (old(self))@.len()
            ensures
                self@ == Self::update_contents_to_reflect_write(old(self)@, addr as int, bytes@),
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
        pub closed spec fn view(self) -> Seq<u8> {
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
                forall |chunks_flushed| {
                    let new_contents: Seq<u8> =
                        #[trigger] PersistentMemory::update_contents_to_reflect_partially_flushed_write(
                            old(self)@, addr as int, bytes@, chunks_flushed
                        );
                    perm@.check_permission(new_contents)
                },
            ensures
                self@ == PersistentMemory::update_contents_to_reflect_write(old(self)@, addr as int, bytes@),
                self.impervious_to_corruption() == old(self).impervious_to_corruption()
        {
            self.pm.write(addr, bytes)
        }
    }

}
