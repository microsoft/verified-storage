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

pub open spec fn replace_subregion_of_region_view(
    region: PersistentMemoryRegionView,
    subregion: PersistentMemoryRegionView,
    start: u64,
) -> PersistentMemoryRegionView
    recommends
        start + subregion.len() <= region.len(),
{
    PersistentMemoryRegionView{
        state:
            Seq::<PersistentMemoryByte>::new(
                region.len(),
                |i: int| if start <= i < start + subregion.len() { subregion.state[i - start] }
                       else { region.state[i] },
            )
    }
}

pub open spec fn get_subregion_view(
    region: PersistentMemoryRegionView,
    start: u64,
    len: u64,
) -> PersistentMemoryRegionView
    recommends
        start + len <= region.len(),
{
    PersistentMemoryRegionView{ state: region.state.subrange(start as int, start + len) }
}

pub proof fn lemma_replace_with_own_subregion_is_identity(
    region: PersistentMemoryRegionView,
    start: u64,
    len: u64,
)
    requires
        start + len <= region.len(),
    ensures
        region == replace_subregion_of_region_view(region, get_subregion_view(region, start, len), start)
{
    assert(region =~= replace_subregion_of_region_view(region, get_subregion_view(region, start, len), start));
}

pub open spec fn views_differ_only_where_subregion_allows(
    v1: PersistentMemoryRegionView,
    v2: PersistentMemoryRegionView,
    start: u64,
    len: u64,
    is_writable_absolute_addr: spec_fn(int) -> bool
) -> bool
{
    forall |addr: int| {
       ||| 0 <= addr < start
       ||| start + len <= addr < v1.len()
       ||| start <= addr < start + len && !is_writable_absolute_addr(addr)
    } ==> v1.state[addr] == #[trigger] v2.state[addr]
}

pub struct PersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<u64>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_writable_absolute_addr_: Ghost<spec_fn(int) -> bool>,
}

impl PersistentMemorySubregion
{
    pub exec fn new<Perm, PMRegion>(
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        Tracked(perm): Tracked<&Perm>,
        start: u64,
        Ghost(len): Ghost<u64>,
        Ghost(is_writable_absolute_addr): Ghost<spec_fn(int) -> bool>,
    ) -> (result: Self)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            wrpm.inv(),
            start + len <= wrpm@.len() <= u64::MAX,
            forall |alt_region_view: PersistentMemoryRegionView, crash_state: Seq<u8>| {
                &&& #[trigger] alt_region_view.can_crash_as(crash_state)
                &&& wrpm@.len() == alt_region_view.len()
                &&& views_differ_only_where_subregion_allows(wrpm@, alt_region_view, start, len,
                                                           is_writable_absolute_addr)
            } ==> perm.check_permission(crash_state),
        ensures
            result.inv(wrpm, perm),
            result.constants() == wrpm.constants(),
            result.start() == start,
            result.len() == len,
            result.initial_region_view() == wrpm@,
            result.is_writable_absolute_addr() == is_writable_absolute_addr,
            result.view(wrpm) == result.initial_subregion_view(),
            result.view(wrpm) == get_subregion_view(wrpm@, start, len),
    {
        let result = Self{
            start_: start,
            len_: Ghost(len),
            constants_: Ghost(wrpm.constants()),
            initial_region_view_: Ghost(wrpm@),
            is_writable_absolute_addr_: Ghost(is_writable_absolute_addr),
        };
        result
    }

    pub closed spec fn constants(self) -> PersistentMemoryConstants
    {
        self.constants_@
    }

    pub closed spec fn start(self) -> u64
    {
        self.start_
    }

    pub closed spec fn len(self) -> u64
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

    pub closed spec fn is_writable_absolute_addr(self) -> spec_fn(int) -> bool
    {
        self.is_writable_absolute_addr_@
    }

    pub open spec fn is_writable_relative_addr(self, addr: int) -> bool
    {
        self.is_writable_absolute_addr()(addr + self.start())
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
        &&& views_differ_only_where_subregion_allows(self.initial_region_view(), wrpm@, self.start(), self.len(),
                                                   self.is_writable_absolute_addr())
        &&& forall |alt_region_view: PersistentMemoryRegionView, crash_state: Seq<u8>| {
              &&& #[trigger] alt_region_view.can_crash_as(crash_state)
              &&& self.initial_region_view().len() == alt_region_view.len()
              &&& views_differ_only_where_subregion_allows(self.initial_region_view(), alt_region_view, self.start(),
                                                         self.len(), self.is_writable_absolute_addr())
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
            self.inv(&*old(wrpm), perm),
            relative_addr + bytes@.len() <= self.view(&*old(wrpm)).len(),
            self.view(&*old(wrpm)).no_outstanding_writes_in_range(relative_addr as int, relative_addr + bytes.len()),
            forall |i: int| relative_addr <= i < relative_addr + bytes@.len() ==> self.is_writable_relative_addr(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm) == self.view(&*old(wrpm)).write(relative_addr as int, bytes@),
    {
        let ghost subregion_view = self.view(wrpm).write(relative_addr as int, bytes@);
        assert(forall |addr| #![trigger self.is_writable_absolute_addr()(addr)]
                   !self.is_writable_absolute_addr()(addr) ==> !self.is_writable_relative_addr(addr - self.start()));
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
                       ||| self.start() <= addr < self.end() && !self.is_writable_absolute_addr()(addr)
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
            self.inv(&*old(wrpm), perm),
            self.start() <= absolute_addr,
            absolute_addr + bytes@.len() <= self.len(),
            self.view(&*old(wrpm)).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + bytes@.len() - self.start()
            ),
            forall |i: int| absolute_addr <= i < absolute_addr + bytes@.len() ==>
                #[trigger] self.is_writable_absolute_addr()(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm) == self.view(&*old(wrpm)).write(absolute_addr - self.start(), bytes@),
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
                                                     self.is_writable_absolute_addr()),
            self.view(wrpm) == get_subregion_view(wrpm@, self.start(), self.len()),
            forall |addr: int| 0 <= addr < self.len() ==>
                #[trigger] self.view(wrpm).state[addr] == wrpm@.state[addr + self.start()],
    {
    }
}


}
