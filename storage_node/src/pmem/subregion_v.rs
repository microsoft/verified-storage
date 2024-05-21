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

pub open spec fn replace_subregion_in_view_helper(
    region: Seq<PersistentMemoryByte>,
    subregion: Seq<PersistentMemoryByte>,
    offset: u64,
) -> Seq<PersistentMemoryByte>
    recommends
        offset + subregion.len() <= region.len(),
{
    Seq::<PersistentMemoryByte>::new(
        region.len(),
        |i: int| if offset <= i < offset + subregion.len() { subregion[i - offset] } else { region[i] },
    )
}

pub open spec fn replace_subregion_in_view(
    region: PersistentMemoryRegionView,
    subregion: PersistentMemoryRegionView,
    offset: u64,
) -> PersistentMemoryRegionView
    recommends
        offset + subregion.len() <= region.len(),
{
    PersistentMemoryRegionView{ state: replace_subregion_in_view_helper(region.state, subregion.state, offset) }
}

pub open spec fn extract_subregion_view(
    region: PersistentMemoryRegionView,
    offset: u64,
    subregion_size: u64,
) -> PersistentMemoryRegionView
    recommends
        offset + subregion_size <= region.len(),
{
    PersistentMemoryRegionView{ state: region.state.subrange(offset as int, offset + subregion_size) }
}

pub proof fn lemma_extract_subregion_view_then_replace_is_idempotent(
    region: PersistentMemoryRegionView,
    offset: u64,
    subregion_size: u64,
)
    requires
        offset + subregion_size <= region.len(),
    ensures
        region == replace_subregion_in_view(region, extract_subregion_view(region, offset, subregion_size), offset)
{
    assert(region =~=
           replace_subregion_in_view(region, extract_subregion_view(region, offset, subregion_size), offset));
}

pub struct PersistentMemorySubregion
{
    constants: PersistentMemoryConstants,
    offset: u64,
    subregion_size: u64,
    initial_region_state: PersistentMemoryRegionView,
    is_subregion_state_allowable: spec_fn(v: PersistentMemoryRegionView) -> bool,
}

impl PersistentMemorySubregion
{
    pub proof fn new<Perm, PMRegion>(
        wrpm: WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: Perm,
        offset: u64,
        subregion_size: u64,
        is_subregion_state_allowable: spec_fn(s: PersistentMemoryRegionView) -> bool,
    ) -> (result: Self)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            wrpm.inv(),
            offset + subregion_size <= wrpm@.len(),
            wrpm@.len() < u64::MAX,
            (is_subregion_state_allowable)(extract_subregion_view(wrpm@, offset, subregion_size)),
            forall |subregion_view: PersistentMemoryRegionView, s: Seq<u8>| {
               &&& subregion_view.len() == subregion_size
               &&& #[trigger] (is_subregion_state_allowable)(subregion_view)
               &&& replace_subregion_in_view(wrpm@, subregion_view, offset).can_crash_as(s)
            } ==> #[trigger] perm.check_permission(s),
        ensures
            result.inv(wrpm, perm),
            result.wrpm_constants() == wrpm.constants(),
            result.subregion_offset() == offset,
            result.len() == subregion_size,
            result.initial_region_view() == wrpm@,
            forall |v| result.is_subregion_view_allowable(v) <==> (is_subregion_state_allowable)(v),
    {
        lemma_extract_subregion_view_then_replace_is_idempotent(wrpm@, offset, subregion_size);
        Self{
            constants: wrpm.constants(),
            offset,
            subregion_size,
            initial_region_state: wrpm@,
            is_subregion_state_allowable,
        }
    }

    pub closed spec fn wrpm_constants(self) -> PersistentMemoryConstants
    {
        self.constants
    }

    pub closed spec fn subregion_offset(self) -> u64
    {
        self.offset
    }

    pub closed spec fn len(self) -> u64
    {
        self.subregion_size
    }

    pub closed spec fn initial_region_view(self) -> PersistentMemoryRegionView
    {
        self.initial_region_state
    }

    pub closed spec fn is_subregion_view_allowable(self, v: PersistentMemoryRegionView) -> bool
    {
        (self.is_subregion_state_allowable)(v)
    }

    pub closed spec fn subregion_view<Perm, PMRegion>(
        self,
        wrpm: WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>
    ) -> PersistentMemoryRegionView
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
    {
        extract_subregion_view(wrpm@, self.offset, self.subregion_size)
    }

    pub closed spec fn initial_subregion_view(self) -> PersistentMemoryRegionView
    {
        extract_subregion_view(self.initial_region_state, self.offset, self.subregion_size)
    }

    pub closed spec fn inv<Perm, PMRegion>(
        self,
        wrpm: WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: Perm
    ) -> bool
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
    {
        &&& wrpm.inv()
        &&& wrpm.constants() == self.constants
        &&& wrpm@.len() == self.initial_region_state.len()
        &&& self.initial_region_state.len() < u64::MAX
        &&& self.offset + self.subregion_size <= wrpm@.len()
        &&& forall |subregion_view: PersistentMemoryRegionView, s: Seq<u8>| {
               &&& subregion_view.len() == self.subregion_size
               &&& #[trigger] (self.is_subregion_state_allowable)(subregion_view)
               &&& replace_subregion_in_view(self.initial_region_state, subregion_view, self.offset).can_crash_as(s)
           } ==> #[trigger] perm.check_permission(s)
        &&& (self.is_subregion_state_allowable)(self.subregion_view(wrpm))
        &&& wrpm@ == replace_subregion_in_view(self.initial_region_state, self.subregion_view(wrpm), self.offset)
    }

    pub exec fn read<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        addr: u64,
        num_bytes: u64,
        perm: Tracked<&Perm>,
    ) -> (bytes: Vec<u8>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(*wrpm, *(perm@)),
            addr + num_bytes <= self.subregion_view(*wrpm).len(),
            self.subregion_view(*wrpm).no_outstanding_writes_in_range(addr as int, addr + num_bytes),
        ensures
            ({
                let true_bytes = self.subregion_view(*wrpm).committed().subrange(addr as int, addr + num_bytes);
                // The addresses in `maybe_corrupted` reflect the fact
                // that we're reading from a subregion at a certain
                // offset.
                let addrs = Seq::<int>::new(num_bytes as nat, |i: int| i + addr + self.subregion_offset());
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
        let ghost true_bytes1 = self.subregion_view(*wrpm).committed().subrange(addr as int, addr + num_bytes);
        let ghost true_bytes2 = wrpm@.committed().subrange(addr + self.offset, addr + self.offset + num_bytes);
        assert(true_bytes1 =~= true_bytes2);
        wrpm.get_pm_region_ref().read(addr + self.offset, num_bytes)
    }

    pub exec fn write<Perm, PMRegion>(
        self,
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        addr: u64,
        bytes: &[u8],
        perm: Tracked<&Perm>,
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(*old(wrpm), *(perm@)),
            addr + bytes@.len() <= self.subregion_view(*old(wrpm)).len(),
            self.subregion_view(*old(wrpm)).no_outstanding_writes_in_range(addr as int, addr + bytes.len()),
            self.is_subregion_view_allowable(self.subregion_view(*old(wrpm)).write(addr as int, bytes@)),
        ensures
            self.inv(*wrpm, *(perm@)),
            self.subregion_view(*wrpm) == self.subregion_view(*old(wrpm)).write(addr as int, bytes@),
    {
        let ghost subregion_view = self.subregion_view(*wrpm).write(addr as int, bytes@);
        assert(wrpm@.write(addr + self.offset, bytes@) =~=
               replace_subregion_in_view(self.initial_region_state, subregion_view, self.offset));
        assert forall |s| wrpm@.write(addr + self.offset, bytes@).can_crash_as(s) implies perm@.check_permission(s) by {
            assert((self.is_subregion_state_allowable)(subregion_view));
            assert(perm@.check_permission(s));
        }
        wrpm.write(addr + self.offset, bytes, perm);
        assert(self.subregion_view(*wrpm) =~= subregion_view);
    }

    pub proof fn lemma_implications_of_inv<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: Tracked<&Perm>
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(*wrpm, *(perm@)),
        ensures
            wrpm.inv(),
            wrpm.constants() == self.wrpm_constants(),
            wrpm@.len() == self.initial_region_view().len(),
            self.is_subregion_view_allowable(self.subregion_view(*wrpm)),
            wrpm@ == replace_subregion_in_view(self.initial_region_view(), self.subregion_view(*wrpm),
                                               self.subregion_offset()),
    {
    }
}


}
