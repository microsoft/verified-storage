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
    offset: u64,
) -> PersistentMemoryRegionView
    recommends
        offset + subregion.len() <= region.len(),
{
    PersistentMemoryRegionView{
        state:
            Seq::<PersistentMemoryByte>::new(
                region.len(),
                |i: int| if offset <= i < offset + subregion.len() { subregion.state[i - offset] }
                       else { region.state[i] },
            )
    }
}

pub open spec fn get_subregion_view(
    region: PersistentMemoryRegionView,
    offset: u64,
    len: u64,
) -> PersistentMemoryRegionView
    recommends
        offset + len <= region.len(),
{
    PersistentMemoryRegionView{ state: region.state.subrange(offset as int, offset + len) }
}

pub proof fn lemma_replace_with_own_subregion_is_identity(
    region: PersistentMemoryRegionView,
    offset: u64,
    len: u64,
)
    requires
        offset + len <= region.len(),
    ensures
        region == replace_subregion_of_region_view(region, get_subregion_view(region, offset, len), offset)
{
    assert(region =~= replace_subregion_of_region_view(region, get_subregion_view(region, offset, len), offset));
}

pub open spec fn region_views_differ_only_at_addresses(
    region1: PersistentMemoryRegionView,
    region2: PersistentMemoryRegionView,
    addrs: Set<int>,
) -> bool
{
    &&& region1.len() == region2.len()
    &&& forall |i: int| 0 <= i < region1.len() && region1.state[i] != region2.state[i] ==> #[trigger] addrs.contains(i)
}

pub struct PersistentMemorySubregion
{
    offset_: u64,
    len_: Ghost<u64>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_view_allowable_: Ghost<spec_fn(v: PersistentMemoryRegionView) -> bool>,
}

impl PersistentMemorySubregion
{
    pub exec fn new<Perm, PMRegion>(
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        Tracked(perm): Tracked<&Perm>,
        offset: u64,
        Ghost(len): Ghost<u64>,
        Ghost(is_view_allowable): Ghost<spec_fn(s: PersistentMemoryRegionView) -> bool>,
    ) -> (result: Self)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            wrpm.inv(),
            offset + len <= wrpm@.len() <= u64::MAX,
            (is_view_allowable)(get_subregion_view(wrpm@, offset, len)),
            forall |subregion_view: PersistentMemoryRegionView, s: Seq<u8>| {
                &&& subregion_view.len() == len
                &&& #[trigger] (is_view_allowable)(subregion_view)
                &&& replace_subregion_of_region_view(wrpm@, subregion_view, offset).can_crash_as(s)
            } ==> #[trigger] perm.check_permission(s),
        ensures
            result.inv(wrpm, perm),
            result.constants() == wrpm.constants(),
            result.offset() == offset,
            result.len() == len,
            result.initial_region_view() == wrpm@,
            forall |v| result.is_view_allowable(v) <==> (is_view_allowable)(v),
            result.view(wrpm) == get_subregion_view(wrpm@, offset, len),
            result.initial_subregion_view() == get_subregion_view(wrpm@, offset, len),
    {
        proof { lemma_replace_with_own_subregion_is_identity(wrpm@, offset, len); }
        Self{
            offset_: offset,
            len_: Ghost(len),
            constants_: Ghost(wrpm.constants()),
            initial_region_view_: Ghost(wrpm@),
            is_view_allowable_: Ghost(is_view_allowable),
        }
    }

    pub closed spec fn constants(self) -> PersistentMemoryConstants
    {
        self.constants_@
    }

    pub closed spec fn offset(self) -> u64
    {
        self.offset_
    }

    pub closed spec fn len(self) -> u64
    {
        self.len_@
    }

    pub closed spec fn initial_region_view(self) -> PersistentMemoryRegionView
    {
        self.initial_region_view_@
    }

    pub closed spec fn is_view_allowable(self, v: PersistentMemoryRegionView) -> bool
    {
        (self.is_view_allowable_@)(v)
    }

    pub closed spec fn initial_subregion_view(self) -> PersistentMemoryRegionView
    {
        get_subregion_view(self.initial_region_view(), self.offset(), self.len())
    }

    pub closed spec fn view<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>
    ) -> PersistentMemoryRegionView
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
    {
        get_subregion_view(wrpm@, self.offset(), self.len())
    }

    pub closed spec fn inv<Perm, PMRegion>(
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
        &&& self.offset() + self.len() <= wrpm@.len()
        &&& wrpm@ == replace_subregion_of_region_view(self.initial_region_view(), self.view(wrpm), self.offset())
        &&& self.is_view_allowable(self.view(wrpm))
        &&& forall |subregion_view: PersistentMemoryRegionView, s: Seq<u8>| {
               &&& subregion_view.len() == self.len()
               &&& #[trigger] self.is_view_allowable(subregion_view)
               &&& replace_subregion_of_region_view(self.initial_region_view(), subregion_view,
                                                  self.offset()).can_crash_as(s)
           } ==> #[trigger] perm.check_permission(s)
    }

    pub exec fn read<Perm, PMRegion>(
        self: &Self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        addr: u64,
        num_bytes: u64,
        Tracked(perm): Tracked<&Perm>,
    ) -> (bytes: Vec<u8>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(wrpm, perm),
            addr + num_bytes <= self.view(wrpm).len(),
            self.view(wrpm).no_outstanding_writes_in_range(addr as int, addr + num_bytes),
        ensures
            ({
                let true_bytes = self.view(wrpm).committed().subrange(addr as int, addr + num_bytes);
                // The addresses in `maybe_corrupted` reflect the fact
                // that we're reading from a subregion at a certain
                // offset.
                let addrs = Seq::<int>::new(num_bytes as nat, |i: int| i + addr + self.offset());
                // If the persistent memory region is impervious
                // to corruption, read returns the last bytes
                // written. Otherwise, it returns a
                // possibly-corrupted version of those bytes.
                if wrpm.constants().impervious_to_corruption {
                    bytes@ == true_bytes
                }
                else {
                    maybe_corrupted(bytes@, true_bytes, addrs)
                }
            })
    {
        let ghost true_bytes1 = self.view(wrpm).committed().subrange(addr as int, addr + num_bytes);
        let ghost true_bytes2 = wrpm@.committed().subrange(addr + self.offset(), addr + self.offset() + num_bytes);
        assert(true_bytes1 =~= true_bytes2);
        wrpm.get_pm_region_ref().read(addr + self.offset_, num_bytes)
    }

    pub exec fn write<Perm, PMRegion>(
        self: &Self,
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        addr: u64,
        bytes: &[u8],
        Tracked(perm): Tracked<&Perm>,
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(&*old(wrpm), perm),
            addr + bytes@.len() <= self.view(&*old(wrpm)).len(),
            self.view(&*old(wrpm)).no_outstanding_writes_in_range(addr as int, addr + bytes.len()),
            self.is_view_allowable(self.view(&*old(wrpm)).write(addr as int, bytes@)),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm) == self.view(&*old(wrpm)).write(addr as int, bytes@),
    {
        let ghost subregion_view = self.view(wrpm).write(addr as int, bytes@);
        assert(wrpm@.write(addr + self.offset(), bytes@) =~=
               replace_subregion_of_region_view(self.initial_region_view(), subregion_view, self.offset()));
        assert forall |s| wrpm@.write(addr + self.offset(), bytes@).can_crash_as(s) implies perm.check_permission(s) by {
            assert(self.is_view_allowable(subregion_view));
            assert(perm.check_permission(s));
        }
        wrpm.write(addr + self.offset_, bytes, Tracked(perm));
        assert(self.view(wrpm) =~= subregion_view);
    }

    pub proof fn lemma_implications_of_inv<Perm, PMRegion>(
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
            self.is_view_allowable(self.view(wrpm)),
            wrpm@ == replace_subregion_of_region_view(self.initial_region_view(), self.view(wrpm), self.offset()),
            self.initial_subregion_view() == get_subregion_view(self.initial_region_view(), self.offset(), self.len()),
    {
    }
}


}
