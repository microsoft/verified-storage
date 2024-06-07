use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use crate::pmem::wrpm_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;

verus! {

pub open spec fn get_subregion_view(
    region: PersistentMemoryRegionView,
    start: int,
    len: int,
) -> PersistentMemoryRegionView
    recommends
        0 <= start,
        0 <= len,
        start + len <= region.len(),
{
    PersistentMemoryRegionView{ state: region.state.subrange(start as int, start + len) }
}

pub open spec fn views_differ_only_where_subregion_allows(
    v1: PersistentMemoryRegionView,
    v2: PersistentMemoryRegionView,
    start: int,
    len: int,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool
) -> bool
    recommends
        0 <= start,
        0 <= len,
{
    forall |addr: int| {
       ||| 0 <= addr < start
       ||| start + len <= addr < v1.len()
       ||| start <= addr < start + len && !is_writable_absolute_addr_fn(addr)
    } ==> v1.state[addr] == #[trigger] v2.state[addr]
}

pub struct WriteRestrictedPersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<int>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_writable_absolute_addr_fn_: Ghost<spec_fn(int) -> bool>,
}

impl WriteRestrictedPersistentMemorySubregion
{
    pub exec fn new<Perm, PMRegion>(
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        Tracked(perm): Tracked<&Perm>,
        start: u64,
        Ghost(len): Ghost<int>,
        Ghost(is_writable_absolute_addr_fn): Ghost<spec_fn(int) -> bool>,
    ) -> (result: Self)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            wrpm.inv(),
            0 <= len,
            start + len <= wrpm@.len() <= u64::MAX,
            forall |alt_region_view: PersistentMemoryRegionView, crash_state: Seq<u8>| {
                &&& #[trigger] alt_region_view.can_crash_as(crash_state)
                &&& wrpm@.len() == alt_region_view.len()
                &&& views_differ_only_where_subregion_allows(wrpm@, alt_region_view, start as int, len,
                                                           is_writable_absolute_addr_fn)
            } ==> perm.check_permission(crash_state),
        ensures
            result.inv(wrpm, perm),
            result.constants() == wrpm.constants(),
            result.start() == start,
            result.len() == len,
            result.initial_region_view() == wrpm@,
            result.is_writable_absolute_addr_fn() == is_writable_absolute_addr_fn,
            result.view(wrpm) == result.initial_subregion_view(),
            result.view(wrpm) == get_subregion_view(wrpm@, start as int, len),
    {
        let result = Self{
            start_: start,
            len_: Ghost(len),
            constants_: Ghost(wrpm.constants()),
            initial_region_view_: Ghost(wrpm@),
            is_writable_absolute_addr_fn_: Ghost(is_writable_absolute_addr_fn),
        };
        result
    }

    pub closed spec fn constants(self) -> PersistentMemoryConstants
    {
        self.constants_@
    }

    pub closed spec fn start(self) -> int
    {
        self.start_ as int
    }

    pub closed spec fn len(self) -> int
    {
        self.len_@
    }

    pub open spec fn end(self) -> int
    {
        self.start() + self.len()
    }

    pub closed spec fn initial_region_view(self) -> PersistentMemoryRegionView
    {
        self.initial_region_view_@
    }

    pub closed spec fn is_writable_absolute_addr_fn(self) -> spec_fn(int) -> bool
    {
        self.is_writable_absolute_addr_fn_@
    }

    pub open spec fn is_writable_relative_addr(self, addr: int) -> bool
    {
        self.is_writable_absolute_addr_fn()(addr + self.start())
    }

    pub closed spec fn initial_subregion_view(self) -> PersistentMemoryRegionView
    {
        get_subregion_view(self.initial_region_view(), self.start(), self.len())
    }

    pub closed spec fn view<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>
    ) -> PersistentMemoryRegionView
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
    {
        get_subregion_view(wrpm@, self.start(), self.len())
    }

    pub closed spec fn opaque_inv<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: &Perm
    ) -> bool
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
    {
        &&& wrpm.inv()
        &&& wrpm.constants() == self.constants()
        &&& wrpm@.len() == self.initial_region_view().len()
        &&& self.initial_region_view().len() <= u64::MAX
        &&& self.start() + self.len() <= wrpm@.len()
        &&& self.view(wrpm).len() == self.len()
        &&& views_differ_only_where_subregion_allows(self.initial_region_view(), wrpm@, self.start(),
                                                   self.len(), self.is_writable_absolute_addr_fn())
        &&& forall |alt_region_view: PersistentMemoryRegionView, crash_state: Seq<u8>| {
              &&& #[trigger] alt_region_view.can_crash_as(crash_state)
              &&& self.initial_region_view().len() == alt_region_view.len()
              &&& views_differ_only_where_subregion_allows(self.initial_region_view(), alt_region_view,
                                                         self.start(), self.len(),
                                                         self.is_writable_absolute_addr_fn())
           } ==> perm.check_permission(crash_state)
    }

    pub open spec fn inv<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: &Perm
    ) -> bool
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
    {
        &&& self.view(wrpm).len() == self.len()
        &&& self.opaque_inv(wrpm, perm)
    }

    pub exec fn read_relative<Perm, PMRegion>(
        self: &Self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        relative_addr: u64,
        num_bytes: u64,
        Tracked(perm): Tracked<&Perm>,
    ) -> (bytes: Vec<u8>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(wrpm, perm),
            relative_addr + num_bytes <= self.len(),
            self.view(wrpm).no_outstanding_writes_in_range(relative_addr as int, relative_addr + num_bytes),
        ensures
            ({
                let true_bytes = self.view(wrpm).committed().subrange(relative_addr as int, relative_addr + num_bytes);
                // If the persistent memory region is impervious
                // to corruption, read returns the last bytes
                // written. Otherwise, it returns a
                // possibly-corrupted version of those bytes.
                if wrpm.constants().impervious_to_corruption {
                    bytes@ == true_bytes
                }
                else {
                    // The addresses in `maybe_corrupted` reflect the fact
                    // that we're reading from a subregion at a certain
                    // start.
                    let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| relative_addr + self.start() + i);
                    maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                }
            })
    {
        let ghost true_bytes1 = self.view(wrpm).committed().subrange(relative_addr as int, relative_addr + num_bytes);
        let ghost true_bytes2 = wrpm@.committed().subrange(self.start() + relative_addr,
                                                           self.start() + relative_addr + num_bytes);
        assert(true_bytes1 =~= true_bytes2);
        assert forall |i| #![trigger wrpm@.state[i]]
                   relative_addr + self.start_ <= i < relative_addr + self.start_ + num_bytes implies
                   wrpm@.state[i].outstanding_write.is_none() by {
            assert(wrpm@.state[i] == self.view(wrpm).state[i - self.start()]);
        }
        wrpm.get_pm_region_ref().read(relative_addr + self.start_, num_bytes)
    }

    pub exec fn read_absolute<Perm, PMRegion>(
        self: &Self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        absolute_addr: u64,
        num_bytes: u64,
        Tracked(perm): Tracked<&Perm>,
    ) -> (bytes: Vec<u8>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(wrpm, perm),
            self.start() <= absolute_addr,
            absolute_addr + num_bytes <= self.end(),
            self.view(wrpm).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + num_bytes - self.start(),
            ),
        ensures
            ({
                let true_bytes = self.view(wrpm).committed().subrange(
                    absolute_addr - self.start(),
                    absolute_addr + num_bytes - self.start()
                );
                // If the persistent memory region is impervious
                // to corruption, read returns the last bytes
                // written. Otherwise, it returns a
                // possibly-corrupted version of those bytes.
                if wrpm.constants().impervious_to_corruption {
                    bytes@ == true_bytes
                }
                else {
                    // The addresses in `maybe_corrupted` reflect the fact
                    // that we're reading from a subregion at a certain
                    // start.
                    let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| absolute_addr + i);
                    maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                }
            })
    {
        let ghost true_bytes1 = self.view(wrpm).committed().subrange(
            absolute_addr - self.start(),
            absolute_addr + num_bytes - self.start(),
        );
        let ghost true_bytes2 = wrpm@.committed().subrange(
            absolute_addr as int,
            absolute_addr + num_bytes
        );
        assert(true_bytes1 =~= true_bytes2);
        assert forall |i| #![trigger wrpm@.state[i]]
                   absolute_addr <= i < absolute_addr + num_bytes implies
                   wrpm@.state[i].outstanding_write.is_none() by {
            assert(wrpm@.state[i] == self.view(wrpm).state[i - self.start()]);
        }
        wrpm.get_pm_region_ref().read(absolute_addr, num_bytes)
    }
 
    pub exec fn read_and_deserialize_relative<'a, S, Perm, PMRegion>(
        self: &Self,
        wrpm: &'a WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        relative_addr: u64,
        Tracked(perm): Tracked<&Perm>,
    ) -> (output: &'a S)
        where
            S: Serializable + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(wrpm, perm),
            relative_addr + S::spec_serialized_len() <= self.len(),
            self.view(wrpm).no_outstanding_writes_in_range(
                relative_addr as int,
                relative_addr + S::spec_serialized_len(),
            ),
        ensures
        ({
            let true_bytes = self.view(wrpm).committed().subrange(
                relative_addr as int,
                relative_addr + S::spec_serialized_len(),
            );
            let true_val = S::spec_deserialize(true_bytes);
            if self.constants().impervious_to_corruption {
                output == true_val
            } else {
                maybe_corrupted_serialized(*output, true_val, relative_addr + self.start())
            }
        })
    {
        let absolute_addr = relative_addr + self.start_;
        let ghost num_bytes = S::spec_serialized_len();
        let ghost true_bytes1 = self.view(wrpm).committed().subrange(
            relative_addr as int,
            relative_addr + num_bytes,
        );
        let ghost true_bytes2 = wrpm@.committed().subrange(
            absolute_addr as int,
            absolute_addr + num_bytes
        );
        assert(true_bytes1 =~= true_bytes2);
        assert forall |i| #![trigger wrpm@.state[i]]
                   absolute_addr <= i < absolute_addr + num_bytes implies
                   wrpm@.state[i].outstanding_write.is_none() by {
            assert(wrpm@.state[i] == self.view(wrpm).state[i - self.start()]);
        }
        wrpm.get_pm_region_ref().read_and_deserialize::<S>(absolute_addr)
    }
 
    pub exec fn read_and_deserialize_absolute<'a, S, Perm, PMRegion>(
        self: &Self,
        wrpm: &'a WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        absolute_addr: u64,
        Tracked(perm): Tracked<&Perm>,
    ) -> (output: &'a S)
        where
            S: Serializable + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(wrpm, perm),
            self.start() <= absolute_addr,
            absolute_addr + S::spec_serialized_len() <= self.end(),
            self.view(wrpm).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + S::spec_serialized_len() - self.start(),
            ),
        ensures
        ({
            let true_bytes = self.view(wrpm).committed().subrange(
                absolute_addr - self.start(),
                absolute_addr + S::spec_serialized_len() - self.start()
            );
            let true_val = S::spec_deserialize(true_bytes);
            if self.constants().impervious_to_corruption {
                output == true_val
            } else {
                maybe_corrupted_serialized(*output, true_val, absolute_addr as int)
            }
        })
    {
        let ghost num_bytes = S::spec_serialized_len();
        let ghost true_bytes1 = self.view(wrpm).committed().subrange(
            absolute_addr - self.start(),
            absolute_addr + num_bytes - self.start(),
        );
        let ghost true_bytes2 = wrpm@.committed().subrange(
            absolute_addr as int,
            absolute_addr + num_bytes
        );
        assert(true_bytes1 =~= true_bytes2);
        assert forall |i| #![trigger wrpm@.state[i]]
                   absolute_addr <= i < absolute_addr + num_bytes implies
                   wrpm@.state[i].outstanding_write.is_none() by {
            assert(wrpm@.state[i] == self.view(wrpm).state[i - self.start()]);
        }
        wrpm.get_pm_region_ref().read_and_deserialize::<S>(absolute_addr)
    }

    pub exec fn write_relative<Perm, PMRegion>(
        self: &Self,
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        relative_addr: u64,
        bytes: &[u8],
        Tracked(perm): Tracked<&Perm>,
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old::<&mut _>(wrpm), perm),
            relative_addr + bytes@.len() <= self.view(old::<&mut _>(wrpm)).len(),
            self.view(old::<&mut _>(wrpm)).no_outstanding_writes_in_range(relative_addr as int,
                                                                        relative_addr + bytes.len()),
            forall |i: int| relative_addr <= i < relative_addr + bytes@.len() ==> self.is_writable_relative_addr(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm) == self.view(old::<&mut _>(wrpm)).write(relative_addr as int, bytes@),
    {
        let ghost subregion_view = self.view(wrpm).write(relative_addr as int, bytes@);
        assert(forall |addr| #![trigger self.is_writable_absolute_addr_fn()(addr)]
                   !self.is_writable_absolute_addr_fn()(addr) ==> !self.is_writable_relative_addr(addr - self.start()));
        assert forall |i| #![trigger wrpm@.state[i]]
                   relative_addr + self.start_ <= i < relative_addr + self.start_ + bytes@.len() implies
                   wrpm@.state[i].outstanding_write.is_none() by {
            assert(wrpm@.state[i] == self.view(wrpm).state[i - self.start()]);
        }
        assert forall |crash_state| wrpm@.write(relative_addr + self.start_, bytes@).can_crash_as(crash_state)
                   implies perm.check_permission(crash_state) by {
            let alt_region_view = wrpm@.write(relative_addr + self.start_, bytes@);
            assert(alt_region_view.len() == wrpm@.len());
            assert forall |addr: int| {
                       ||| 0 <= addr < self.start()
                       ||| self.start() + self.len() <= addr < alt_region_view.len()
                       ||| self.start() <= addr < self.end() && !self.is_writable_absolute_addr_fn()(addr)
                   } implies self.initial_region_view().state[addr] == #[trigger] alt_region_view.state[addr] by {
                assert(!(relative_addr + self.start_ <= addr < relative_addr + self.start_ + bytes@.len()));
                assert(self.initial_region_view().state[addr] == wrpm@.state[addr]);
            }
        }
        wrpm.write(relative_addr + self.start_, bytes, Tracked(perm));
        assert(self.view(wrpm) =~= subregion_view);
    }

    pub exec fn write_absolute<Perm, PMRegion>(
        self: &Self,
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        absolute_addr: u64,
        bytes: &[u8],
        Tracked(perm): Tracked<&Perm>,
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old::<&mut _>(wrpm), perm),
            self.start() <= absolute_addr,
            absolute_addr + bytes@.len() <= self.len(),
            self.view(old::<&mut _>(wrpm)).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + bytes@.len() - self.start()
            ),
            forall |i: int| absolute_addr <= i < absolute_addr + bytes@.len() ==>
                #[trigger] self.is_writable_absolute_addr_fn()(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm) == self.view(old::<&mut _>(wrpm)).write(absolute_addr - self.start(), bytes@),
    {
        let ghost subregion_view = self.view(wrpm).write(absolute_addr - self.start(), bytes@);
        assert forall |i| #![trigger wrpm@.state[i]]
                   absolute_addr <= i < absolute_addr + bytes@.len() implies
                   wrpm@.state[i].outstanding_write.is_none() by {
            assert(wrpm@.state[i] == self.view(wrpm).state[i - self.start()]);
        }
        wrpm.write(absolute_addr, bytes, Tracked(perm));
        assert(self.view(wrpm) =~= subregion_view);
    }

    pub exec fn serialize_and_write_relative<S, Perm, PMRegion>(
        self: &Self,
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        relative_addr: u64,
        to_write: &S,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            S: Serializable + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old::<&mut _>(wrpm), perm),
            relative_addr + S::spec_serialized_len() <= self.view(old::<&mut _>(wrpm)).len(),
            self.view(old::<&mut _>(wrpm)).no_outstanding_writes_in_range(relative_addr as int,
                                                                        relative_addr + S::spec_serialized_len()),
            forall |i: int| relative_addr <= i < relative_addr + S::spec_serialized_len() ==>
                self.is_writable_relative_addr(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm) == self.view(old::<&mut _>(wrpm)).write(relative_addr as int, to_write.spec_serialize()),
    {
        let ghost bytes = to_write.spec_serialize();
        assert(bytes.len() == S::spec_serialized_len()) by {
            S::lemma_auto_serialized_len();
        }
        let ghost subregion_view = self.view(wrpm).write(relative_addr as int, bytes);
        assert(forall |addr| #![trigger self.is_writable_absolute_addr_fn()(addr)]
                   !self.is_writable_absolute_addr_fn()(addr) ==> !self.is_writable_relative_addr(addr - self.start()));
        assert forall |i| #![trigger wrpm@.state[i]]
                   relative_addr + self.start_ <= i < relative_addr + self.start_ + S::spec_serialized_len() implies
                   wrpm@.state[i].outstanding_write.is_none() by {
            assert(wrpm@.state[i] == self.view(wrpm).state[i - self.start()]);
        }
        assert forall |crash_state| wrpm@.write(relative_addr + self.start_, bytes).can_crash_as(crash_state)
                   implies perm.check_permission(crash_state) by {
            let alt_region_view = wrpm@.write(relative_addr + self.start_, bytes);
            assert(alt_region_view.len() == wrpm@.len());
            assert forall |addr: int| {
                       ||| 0 <= addr < self.start()
                       ||| self.start() + self.len() <= addr < alt_region_view.len()
                       ||| self.start() <= addr < self.end() && !self.is_writable_absolute_addr_fn()(addr)
                   } implies self.initial_region_view().state[addr] == #[trigger] alt_region_view.state[addr] by {
                assert(!(relative_addr + self.start_ <= addr < relative_addr + self.start_ + S::spec_serialized_len()));
                assert(self.initial_region_view().state[addr] == wrpm@.state[addr]);
            }
        }
        wrpm.serialize_and_write(relative_addr + self.start_, to_write, Tracked(perm));
        assert(self.view(wrpm) =~= subregion_view);
    }

    pub exec fn serialize_and_write_absolute<S, Perm, PMRegion>(
        self: &Self,
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        absolute_addr: u64,
        to_write: &S,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            S: Serializable + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old::<&mut _>(wrpm), perm),
            self.start() <= absolute_addr,
            absolute_addr + S::spec_serialized_len() <= self.len(),
            self.view(old::<&mut _>(wrpm)).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + S::spec_serialized_len() - self.start()
            ),
            forall |i: int| absolute_addr <= i < absolute_addr + S::spec_serialized_len() ==>
                #[trigger] self.is_writable_absolute_addr_fn()(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm) == self.view(old::<&mut _>(wrpm)).write(absolute_addr - self.start(),
                                                                  to_write.spec_serialize()),
    {
        let ghost bytes = to_write.spec_serialize();
        assert(bytes.len() == S::spec_serialized_len()) by {
            S::lemma_auto_serialized_len();
        }
        let ghost subregion_view = self.view(wrpm).write(absolute_addr - self.start(), bytes);
        assert forall |i| #![trigger wrpm@.state[i]]
                   absolute_addr <= i < absolute_addr + S::spec_serialized_len() implies
                   wrpm@.state[i].outstanding_write.is_none() by {
            assert(wrpm@.state[i] == self.view(wrpm).state[i - self.start()]);
        }
        wrpm.serialize_and_write(absolute_addr, to_write, Tracked(perm));
        assert(self.view(wrpm) =~= subregion_view);
    }

    pub proof fn lemma_reveal_opaque_inv<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: &Perm
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(wrpm, perm),
        ensures
            wrpm.inv(),
            wrpm.constants() == self.constants(),
            wrpm@.len() == self.initial_region_view().len(),
            views_differ_only_where_subregion_allows(self.initial_region_view(), wrpm@, self.start(), self.len(),
                                                     self.is_writable_absolute_addr_fn()),
            self.view(wrpm) == get_subregion_view(wrpm@, self.start(), self.len()),
            forall |addr: int| 0 <= addr < self.len() ==>
                #[trigger] self.view(wrpm).state[addr] == wrpm@.state[addr + self.start()],
    {
    }
}


pub struct PersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<int>,
}

impl PersistentMemorySubregion
{
    pub exec fn new<PMRegion: PersistentMemoryRegion>(
        pm: &PMRegion,
        start: u64,
        Ghost(len): Ghost<int>,
    ) -> (result: Self)
        requires
            pm.inv(),
            start + len <= pm@.len() <= u64::MAX,
        ensures
            result.start() == start,
            result.len() == len,
            result.view(pm) == get_subregion_view(pm@, start as int, len),
    {
        let result = Self{
            start_: start,
            len_: Ghost(len),
        };
        result
    }

    pub closed spec fn start(self) -> int
    {
        self.start_ as int
    }

    pub closed spec fn len(self) -> int
    {
        self.len_@
    }

    pub open spec fn end(self) -> int
    {
        self.start() + self.len()
    }

    pub closed spec fn view<PMRegion: PersistentMemoryRegion>(
        self,
        pm: &PMRegion,
    ) -> PersistentMemoryRegionView
    {
        get_subregion_view(pm@, self.start(), self.len())
    }

    pub open spec fn inv<PMRegion: PersistentMemoryRegion>(
        self,
        pm: &PMRegion,
    ) -> bool
    {
        &&& pm.inv()
        &&& pm@.len() <= u64::MAX
        &&& self.view(pm).len() == self.len()
        &&& self.start() + self.len() <= pm@.len()
    }

    pub exec fn read_relative<PMRegion: PersistentMemoryRegion>(
        self: &Self,
        pm: &PMRegion,
        relative_addr: u64,
        num_bytes: u64,
    ) -> (bytes: Vec<u8>)
        requires
            self.inv(pm),
            relative_addr + num_bytes <= self.len(),
            self.view(pm).no_outstanding_writes_in_range(relative_addr as int, relative_addr + num_bytes),
        ensures
            ({
                let true_bytes = self.view(pm).committed().subrange(relative_addr as int, relative_addr + num_bytes);
                // If the persistent memory region is impervious
                // to corruption, read returns the last bytes
                // written. Otherwise, it returns a
                // possibly-corrupted version of those bytes.
                if pm.constants().impervious_to_corruption {
                    bytes@ == true_bytes
                }
                else {
                    // The addresses in `maybe_corrupted` reflect the fact
                    // that we're reading from a subregion at a certain
                    // start.
                    let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| relative_addr + self.start() + i);
                    maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                }
            })
    {
        let ghost true_bytes1 = self.view(pm).committed().subrange(relative_addr as int, relative_addr + num_bytes);
        let ghost true_bytes2 = pm@.committed().subrange(self.start() + relative_addr,
                                                           self.start() + relative_addr + num_bytes);
        assert(true_bytes1 =~= true_bytes2);
        assert forall |i| #![trigger pm@.state[i]]
                   relative_addr + self.start_ <= i < relative_addr + self.start_ + num_bytes implies
                   pm@.state[i].outstanding_write.is_none() by {
            assert(pm@.state[i] == self.view(pm).state[i - self.start()]);
        }
        pm.read(relative_addr + self.start_, num_bytes)
    }

    pub exec fn read_absolute<PMRegion: PersistentMemoryRegion>(
        self: &Self,
        pm: &PMRegion,
        absolute_addr: u64,
        num_bytes: u64,
    ) -> (bytes: Vec<u8>)
        requires
            self.inv(pm),
            self.start() <= absolute_addr,
            absolute_addr + num_bytes <= self.end(),
            self.view(pm).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + num_bytes - self.start(),
            ),
        ensures
            ({
                let true_bytes = self.view(pm).committed().subrange(
                    absolute_addr - self.start(),
                    absolute_addr + num_bytes - self.start()
                );
                // If the persistent memory region is impervious
                // to corruption, read returns the last bytes
                // written. Otherwise, it returns a
                // possibly-corrupted version of those bytes.
                if pm.constants().impervious_to_corruption {
                    bytes@ == true_bytes
                }
                else {
                    // The addresses in `maybe_corrupted` reflect the fact
                    // that we're reading from a subregion at a certain
                    // start.
                    let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| absolute_addr + i);
                    maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                }
            })
    {
        let ghost true_bytes1 = self.view(pm).committed().subrange(
            absolute_addr - self.start(),
            absolute_addr + num_bytes - self.start(),
        );
        let ghost true_bytes2 = pm@.committed().subrange(
            absolute_addr as int,
            absolute_addr + num_bytes
        );
        assert(true_bytes1 =~= true_bytes2);
        assert forall |i| #![trigger pm@.state[i]]
                   absolute_addr <= i < absolute_addr + num_bytes implies
                   pm@.state[i].outstanding_write.is_none() by {
            assert(pm@.state[i] == self.view(pm).state[i - self.start()]);
        }
        pm.read(absolute_addr, num_bytes)
    }
 
    pub exec fn read_and_deserialize_relative<'a, S, PMRegion: PersistentMemoryRegion>(
        self: &Self,
        pm: &'a PMRegion,
        relative_addr: u64,
    ) -> (output: &'a S)
        where
            S: Serializable + Sized,
        requires
            self.inv(pm),
            relative_addr + S::spec_serialized_len() <= self.len(),
            self.view(pm).no_outstanding_writes_in_range(
                relative_addr as int,
                relative_addr + S::spec_serialized_len(),
            ),
        ensures
        ({
            let true_bytes = self.view(pm).committed().subrange(
                relative_addr as int,
                relative_addr + S::spec_serialized_len(),
            );
            let true_val = S::spec_deserialize(true_bytes);
            if pm.constants().impervious_to_corruption {
                output == true_val
            } else {
                maybe_corrupted_serialized(*output, true_val, relative_addr + self.start())
            }
        })
    {
        let absolute_addr = relative_addr + self.start_;
        let ghost num_bytes = S::spec_serialized_len();
        let ghost true_bytes1 = self.view(pm).committed().subrange(
            relative_addr as int,
            relative_addr + num_bytes,
        );
        let ghost true_bytes2 = pm@.committed().subrange(
            absolute_addr as int,
            absolute_addr + num_bytes
        );
        assert(true_bytes1 =~= true_bytes2);
        assert forall |i| #![trigger pm@.state[i]]
                   absolute_addr <= i < absolute_addr + num_bytes implies
                   pm@.state[i].outstanding_write.is_none() by {
            assert(pm@.state[i] == self.view(pm).state[i - self.start()]);
        }
        pm.read_and_deserialize::<S>(absolute_addr)
    }
 
    pub exec fn read_and_deserialize_absolute<'a, S, PMRegion: PersistentMemoryRegion>(
        self: &Self,
        pm: &'a PMRegion,
        absolute_addr: u64,
    ) -> (output: &'a S)
        where
            S: Serializable + Sized,
        requires
            self.inv(pm),
            self.start() <= absolute_addr,
            absolute_addr + S::spec_serialized_len() <= self.end(),
            self.view(pm).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + S::spec_serialized_len() - self.start(),
            ),
        ensures
        ({
            let true_bytes = self.view(pm).committed().subrange(
                absolute_addr - self.start(),
                absolute_addr + S::spec_serialized_len() - self.start()
            );
            let true_val = S::spec_deserialize(true_bytes);
            if pm.constants().impervious_to_corruption {
                output == true_val
            } else {
                maybe_corrupted_serialized(*output, true_val, absolute_addr as int)
            }
        })
    {
        let ghost num_bytes = S::spec_serialized_len();
        let ghost true_bytes1 = self.view(pm).committed().subrange(
            absolute_addr - self.start(),
            absolute_addr + num_bytes - self.start(),
        );
        let ghost true_bytes2 = pm@.committed().subrange(
            absolute_addr as int,
            absolute_addr + num_bytes
        );
        assert(true_bytes1 =~= true_bytes2);
        assert forall |i| #![trigger pm@.state[i]]
                   absolute_addr <= i < absolute_addr + num_bytes implies
                   pm@.state[i].outstanding_write.is_none() by {
            assert(pm@.state[i] == self.view(pm).state[i - self.start()]);
        }
        pm.read_and_deserialize::<S>(absolute_addr)
    }
}

}
