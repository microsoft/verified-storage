use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::power_t::*;
use crate::pmem::crc_t::*;
use vstd::arithmetic::div_mod::*;
use vstd::bytes::*;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;

verus! {

broadcast use pmcopy_axioms;

pub open spec fn get_subregion_view(
    region: PersistentMemoryRegionView,
    start: nat,
    len: nat,
) -> PersistentMemoryRegionView
    recommends
        start + len <= region.len(),
{
    PersistentMemoryRegionView{
        read_state: region.read_state.subrange(start as int, (start + len) as int),
        durable_state: region.durable_state.subrange(start as int, (start + len) as int),
    }
}

pub open spec fn address_modifiable_by_subregion(
    addr: int,
    start: nat,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool
) -> bool
{
    &&& start <= addr < start + len
    &&& is_writable_absolute_addr_fn(addr)
}

pub open spec fn memories_differ_only_where_subregion_allows(
    mem1: Seq<u8>,
    mem2: Seq<u8>,                                                         
    start: nat,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool
) -> bool
{
    &&& mem1.len() == mem2.len()
    &&& start + len <= mem1.len()
    &&& forall |addr: int| #![trigger mem1[addr]] #![trigger mem2[addr]]
        0 <= addr < mem2.len() && mem1[addr] != mem2[addr] ==>
            address_modifiable_by_subregion(addr, start, len, is_writable_absolute_addr_fn)
}

pub open spec fn views_differ_only_where_subregion_allows(
    v1: PersistentMemoryRegionView,
    v2: PersistentMemoryRegionView,
    start: nat,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool
) -> bool
{
    &&& memories_differ_only_where_subregion_allows(v1.read_state, v2.read_state, start, len,
                                                  is_writable_absolute_addr_fn)
    &&& memories_differ_only_where_subregion_allows(v1.durable_state, v2.durable_state, start, len,
                                                  is_writable_absolute_addr_fn)
}

pub proof fn lemma_state_resulting_from_partial_write_within_subregion_differs_only_where_subregion_allows(
    new_state: Seq<u8>,
    old_state: Seq<u8>,
    write_addr: int,
    bytes: Seq<u8>,
    start: nat,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool,
)
    requires
        0 <= write_addr,
        write_addr + bytes.len() <= old_state.len(),
        start + len <= old_state.len(),
        forall|addr: int| write_addr <= addr < write_addr + bytes.len() ==>
            address_modifiable_by_subregion(addr, start, len, is_writable_absolute_addr_fn),
        can_result_from_partial_write(new_state, old_state, write_addr, bytes),
    ensures
        memories_differ_only_where_subregion_allows(old_state, new_state, start, len, is_writable_absolute_addr_fn),
{
    assert forall|addr: int| 0 <= addr < new_state.len() && old_state[addr] != #[trigger] new_state[addr] implies
        address_modifiable_by_subregion(addr, start, len, is_writable_absolute_addr_fn) by {
        assert(chunk_trigger(addr / const_persistence_chunk_size()));
    }
}

pub proof fn lemma_view_resulting_from_write_has_subregion_view_resulting_from_write(
    v2: PersistentMemoryRegionView,
    v1: PersistentMemoryRegionView,
    write_addr: int,
    bytes: Seq<u8>,
    start: nat,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool,
)
    requires
        v1.valid(),
        v2.valid(),
        v1.len() == v2.len(),
        0 <= write_addr,
        write_addr + bytes.len() <= v1.len(),
        v2.can_result_from_write(v1, write_addr, bytes),
        start + len <= v1.len(),
        start % (const_persistence_chunk_size() as nat) == 0,
        forall|addr: int| write_addr <= addr < write_addr + bytes.len() ==>
            address_modifiable_by_subregion(addr, start, len, is_writable_absolute_addr_fn),
    ensures
        ({
            let sv2 = get_subregion_view(v2, start, len);
            let sv1 = get_subregion_view(v1, start, len);
            sv2.can_result_from_write(sv1, write_addr - start, bytes)
        }),
{
    let sv1 = get_subregion_view(v1, start, len);
    let sv2 = get_subregion_view(v2, start, len);
    assert(sv2.read_state =~= update_bytes(sv1.read_state, write_addr - start, bytes));
    assert forall|chunk| #[trigger] chunk_trigger(chunk) implies {
        ||| chunk_corresponds(sv2.durable_state, sv1.durable_state, chunk)
        ||| chunk_corresponds(sv2.durable_state, update_bytes(sv1.durable_state, write_addr - start, bytes), chunk)
    } by {
        let absolute_chunk = chunk + start / (const_persistence_chunk_size() as nat);
        assert(absolute_chunk * const_persistence_chunk_size() == chunk * const_persistence_chunk_size() + start) by {
            assert(start / (const_persistence_chunk_size() as nat) * const_persistence_chunk_size() == start) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(start as int, const_persistence_chunk_size());
            }
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                const_persistence_chunk_size(), chunk, start as int / const_persistence_chunk_size()
            );
        }
        assert(chunk_trigger(absolute_chunk));
        if chunk_corresponds(v2.durable_state, v1.durable_state, absolute_chunk) {
            assert(chunk_corresponds(sv2.durable_state, sv1.durable_state, chunk)) by {
                assert forall |addr: int| {
                    &&& 0 <= addr < sv1.durable_state.len()
                    &&& addr_in_chunk(chunk, addr)
                } implies #[trigger] sv2.durable_state[addr] == sv1.durable_state[addr] by {
                    assert(chunk_trigger(addr / const_persistence_chunk_size()));
                }
            }
        }
        else {
            assert(chunk_corresponds(sv2.durable_state, update_bytes(sv1.durable_state, write_addr - start, bytes),
                                     chunk)) by {
                assert forall |addr: int| {
                    &&& 0 <= addr < sv2.durable_state.len()
                    &&& addr_in_chunk(chunk, addr)
                } implies #[trigger] sv2.durable_state[addr] ==
                          update_bytes(sv1.durable_state, write_addr - start, bytes)[addr] by {
                    assert(chunk_trigger(addr / const_persistence_chunk_size()));
                }
            }
        }
    }
}

pub open spec fn condition_stable_to_subregion_modifications(
    condition: spec_fn(Seq<u8>) -> bool,
    region_len: nat,
    start: nat,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool,
) -> bool
{
    forall|s1: Seq<u8>, s2: Seq<u8>| {
        &&& condition(s1)
        &&& s1.len() == s2.len() == region_len
        &&& memories_differ_only_where_subregion_allows(s1, s2, start, len, is_writable_absolute_addr_fn)
    } ==> condition(s2)
}

pub open spec fn condition_sufficient_to_create_powerpm_subregion<Perm>(
    region_view: PersistentMemoryRegionView,
    perm: &Perm,
    start: u64,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool,
    condition: spec_fn(Seq<u8>) -> bool,
) -> bool
    where
        Perm: CheckPermission<Seq<u8>>,
{
    &&& start + len <= region_view.len() <= u64::MAX
    &&& condition(region_view.durable_state)
    &&& forall|crash_state| condition(crash_state) ==> perm.permits(crash_state)
    &&& condition_stable_to_subregion_modifications(condition, region_view.len(), start as nat, len,
                                                  is_writable_absolute_addr_fn)
}

pub proof fn lemma_condition_sufficient_to_create_powerpm_subregion<Perm>(
    region_view: PersistentMemoryRegionView,
    perm: &Perm,
    start: u64,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool,
    condition: spec_fn(Seq<u8>) -> bool,
)
    where
        Perm: CheckPermission<Seq<u8>>,
    requires
        region_view.valid(),
        condition_sufficient_to_create_powerpm_subregion(region_view, perm, start, len, is_writable_absolute_addr_fn,
                                                      condition),
    ensures
        forall |alt_crash_state: Seq<u8>|
            memories_differ_only_where_subregion_allows(region_view.durable_state, alt_crash_state,
                                                        start as nat, len, is_writable_absolute_addr_fn)
        ==> #[trigger] perm.permits(alt_crash_state),
{
    assert forall |alt_crash_state: Seq<u8>|
        memories_differ_only_where_subregion_allows(region_view.durable_state, alt_crash_state, start as nat, len,
                                                    is_writable_absolute_addr_fn)
    implies #[trigger] perm.permits(alt_crash_state) by {
        assert(condition(region_view.durable_state));
        assert(alt_crash_state.len() == region_view.durable_state.len());
        assert(region_view.durable_state.len() == region_view.len());
        assert(memories_differ_only_where_subregion_allows(region_view.durable_state, alt_crash_state,
                                                           start as nat, len, is_writable_absolute_addr_fn));
        assert(condition(alt_crash_state));
    }
}

pub proof fn lemma_bytes_match_in_equal_subregions(
    v1: PersistentMemoryRegionView,
    v2: PersistentMemoryRegionView,
    start: nat,
    len: nat,
)
    requires
        v1.valid(),
        v2.valid(),
        v1.len() == v2.len(),
        v1.len() >= start + len,
        get_subregion_view(v1, start, len) == get_subregion_view(v2, start, len),
    ensures 
        forall |addr: int| #![trigger v2.read_state[addr]] #![trigger v2.durable_state[addr]]
            start <= addr < start + len ==> {
                &&& v1.read_state[addr] == v2.read_state[addr]
                &&& v1.durable_state[addr] == v2.durable_state[addr]
            }
{
    assert forall |addr: int| #![trigger v2.read_state[addr]] #![trigger v2.durable_state[addr]]
        start <= addr < start + len implies {
            &&& v1.read_state[addr] == v2.read_state[addr]
            &&& v1.durable_state[addr] == v2.durable_state[addr]
        } by {
        let subregion1 = get_subregion_view(v1, start, len);
        let subregion2 = get_subregion_view(v2, start, len);
        assert(subregion1.read_state[addr - start] == subregion2.read_state[addr - start]);
        assert(subregion1.durable_state[addr - start] == subregion2.durable_state[addr - start]);
    }
}

pub struct PoWERPersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<nat>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_writable_absolute_addr_fn_: Ghost<spec_fn(int) -> bool>,
}

impl PoWERPersistentMemorySubregion
{
    pub exec fn new<Perm, PMRegion>(
        powerpm: &PoWERPersistentMemoryRegion<PMRegion>,
        Tracked(perm): Tracked<&Perm>,
        start: u64,
        Ghost(len): Ghost<nat>,
        Ghost(is_writable_absolute_addr_fn): Ghost<spec_fn(int) -> bool>,
    ) -> (result: Self)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            powerpm.inv(),
            powerpm@.valid(),
            (start as nat) % (const_persistence_chunk_size() as nat) == 0,
            start + len <= powerpm@.len() <= u64::MAX,
            perm.id() == powerpm.id(),
            forall |alt_crash_state: Seq<u8>|
                memories_differ_only_where_subregion_allows(powerpm@.durable_state, alt_crash_state,
                                                            start as nat, len, is_writable_absolute_addr_fn)
            ==> #[trigger] perm.permits(alt_crash_state),
        ensures
            result.inv(powerpm, perm),
            result.constants() == powerpm.constants(),
            result.start() == start,
            result.len() == len,
            result.initial_region_view() == powerpm@,
            result.is_writable_absolute_addr_fn() == is_writable_absolute_addr_fn,
            result.view(powerpm) == result.initial_subregion_view(),
            result.view(powerpm) == get_subregion_view(powerpm@, start as nat, len),
    {
        let result = Self{
            start_: start,
            len_: Ghost(len),
            constants_: Ghost(powerpm.constants()),
            initial_region_view_: Ghost(powerpm@),
            is_writable_absolute_addr_fn_: Ghost(is_writable_absolute_addr_fn),
        };
        result
    }

    pub exec fn new_with_condition<Perm, PMRegion>(
        powerpm: &PoWERPersistentMemoryRegion<PMRegion>,
        Tracked(perm): Tracked<&Perm>,
        start: u64,
        Ghost(len): Ghost<nat>,
        Ghost(is_writable_absolute_addr_fn): Ghost<spec_fn(int) -> bool>,
        Ghost(condition): Ghost<spec_fn(Seq<u8>) -> bool>,
    ) -> (result: Self)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            powerpm.inv(),
            powerpm@.valid(),
            (start as nat) % (const_persistence_chunk_size() as nat) == 0,
            perm.id() == powerpm.id(),
            condition_sufficient_to_create_powerpm_subregion(powerpm@, perm, start, len, is_writable_absolute_addr_fn,
                                                          condition),
        ensures
            result.inv(powerpm, perm),
            result.constants() == powerpm.constants(),
            result.start() == start,
            result.len() == len,
            result.initial_region_view() == powerpm@,
            result.is_writable_absolute_addr_fn() == is_writable_absolute_addr_fn,
            result.view(powerpm) == result.initial_subregion_view(),
            result.view(powerpm) == get_subregion_view(powerpm@, start as nat, len),
    {
        proof {
            lemma_condition_sufficient_to_create_powerpm_subregion(powerpm@, perm, start, len, is_writable_absolute_addr_fn,
                                                                condition);
        }
        let result = Self{
            start_: start,
            len_: Ghost(len),
            constants_: Ghost(powerpm.constants()),
            initial_region_view_: Ghost(powerpm@),
            is_writable_absolute_addr_fn_: Ghost(is_writable_absolute_addr_fn),
        };
        result
    }

    pub closed spec fn constants(self) -> PersistentMemoryConstants
    {
        self.constants_@
    }

    pub closed spec fn start(self) -> nat
    {
        self.start_ as nat
    }

    pub closed spec fn len(self) -> nat
    {
        self.len_@
    }

    pub open spec fn end(self) -> nat
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

    pub open spec fn view<PMRegion>(
        self,
        powerpm: &PoWERPersistentMemoryRegion<PMRegion>
    ) -> PersistentMemoryRegionView
        where
            PMRegion: PersistentMemoryRegion,
    {
        get_subregion_view(powerpm@, self.start(), self.len())
    }

    pub closed spec fn opaque_relation_with_powerpm<PMRegion>(
        self,
        powerpm: &PoWERPersistentMemoryRegion<PMRegion>,
    ) -> bool
        where
            PMRegion: PersistentMemoryRegion,
    {
        &&& powerpm.inv()
        &&& powerpm.constants() == self.constants()
        &&& powerpm@.valid()
        &&& powerpm@.len() == self.initial_region_view().len()
        &&& self.start() + self.len() <= powerpm@.len()
        &&& self.view(powerpm).len() == self.len()
        &&& self.start() % (const_persistence_chunk_size() as nat) == 0
        &&& views_differ_only_where_subregion_allows(self.initial_region_view(), powerpm@, self.start(),
                                                   self.len(), self.is_writable_absolute_addr_fn())
    }

    pub closed spec fn opaque_relation_with_perm<Perm>(self, perm: &Perm) -> bool
        where
            Perm: CheckPermission<Seq<u8>>,
    {
        forall |alt_crash_state: Seq<u8>|
            memories_differ_only_where_subregion_allows(self.initial_region_view().durable_state, alt_crash_state,
                                                        self.start(), self.len(), self.is_writable_absolute_addr_fn())
        ==> #[trigger] perm.permits(alt_crash_state)
    }

    pub open spec fn inv<Perm, PMRegion>(
        self,
        powerpm: &PoWERPersistentMemoryRegion<PMRegion>,
        perm: &Perm
    ) -> bool
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
    {
        &&& self.view(powerpm).valid()
        &&& self.view(powerpm).len() == self.len()
        &&& self.initial_region_view().len() <= u64::MAX
        &&& self.opaque_relation_with_powerpm(powerpm)
        &&& self.opaque_relation_with_perm(perm)
        &&& perm.id() == powerpm.id()
    }

    pub proof fn lemma_state_resulting_from_partial_write_differs_only_where_this_allows(
        self,
        new_state: Seq<u8>,
        old_state: Seq<u8>,
        write_addr: int,
        bytes: Seq<u8>,
    )
        requires
            0 <= write_addr,
            write_addr + bytes.len() <= old_state.len(),
            self.start() + self.len() <= old_state.len(),
            forall|addr: int| write_addr <= addr < write_addr + bytes.len() ==>
                address_modifiable_by_subregion(addr, self.start(), self.len(), self.is_writable_absolute_addr_fn()),
            can_result_from_partial_write(new_state, old_state, write_addr, bytes),
        ensures
            memories_differ_only_where_subregion_allows(old_state, new_state, self.start(), self.len(),
                                                        self.is_writable_absolute_addr_fn()),
    {
        lemma_state_resulting_from_partial_write_within_subregion_differs_only_where_subregion_allows(
            new_state, old_state, write_addr, bytes, self.start(), self.len(), self.is_writable_absolute_addr_fn()
        );
    }

    pub proof fn lemma_state_resulting_from_partial_write_differs_only_where_this_allows_always(self)
        ensures
            forall|new_state: Seq<u8>, old_state: Seq<u8>, write_addr: int, bytes: Seq<u8>| {
                &&& 0 <= write_addr
                &&& write_addr + bytes.len() <= old_state.len()
                &&& self.start() + self.len() <= old_state.len()
                &&& forall|addr: int| write_addr <= addr < write_addr + bytes.len() ==>
                    address_modifiable_by_subregion(addr, self.start(), self.len(), self.is_writable_absolute_addr_fn())
                &&& can_result_from_partial_write(new_state, old_state, write_addr, bytes)
            } ==> memories_differ_only_where_subregion_allows(old_state, new_state, self.start(), self.len(),
                                                             self.is_writable_absolute_addr_fn()),
    {
        assert forall|new_state: Seq<u8>, old_state: Seq<u8>, write_addr: int, bytes: Seq<u8>| {
                &&& 0 <= write_addr
                &&& write_addr + bytes.len() <= old_state.len()
                &&& self.start() + self.len() <= old_state.len()
                &&& forall|addr: int| write_addr <= addr < write_addr + bytes.len() ==>
                    address_modifiable_by_subregion(addr, self.start(), self.len(), self.is_writable_absolute_addr_fn())
                &&& can_result_from_partial_write(new_state, old_state, write_addr, bytes)
            } implies memories_differ_only_where_subregion_allows(old_state, new_state, self.start(), self.len(),
                                                                  self.is_writable_absolute_addr_fn()) by {
            self.lemma_state_resulting_from_partial_write_differs_only_where_this_allows(
                new_state, old_state, write_addr, bytes
            );
        }
    }

    pub proof fn lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write(
        self,
        v2: PersistentMemoryRegionView,
        v1: PersistentMemoryRegionView,
        write_addr: int,
        bytes: Seq<u8>,
    )
        requires
            v1.valid(),
            v2.valid(),
            v1.len() == v2.len(),
            0 <= write_addr,
            write_addr + bytes.len() <= v1.len(),
            v2.can_result_from_write(v1, write_addr, bytes),
            self.start() + self.len() <= v1.len(),
            self.start() % (const_persistence_chunk_size() as nat) == 0,
            forall|addr: int| write_addr <= addr < write_addr + bytes.len() ==>
                address_modifiable_by_subregion(addr, self.start(), self.len(), self.is_writable_absolute_addr_fn()),
        ensures
            ({
                let sv1 = get_subregion_view(v1, self.start(), self.len());
                let sv2 = get_subregion_view(v2, self.start(), self.len());
                sv2.can_result_from_write(sv1, write_addr - self.start(), bytes)
            }),
    {
        lemma_view_resulting_from_write_has_subregion_view_resulting_from_write(v2, v1, write_addr, bytes,
                                                                                self.start(), self.len(),
                                                                                self.is_writable_absolute_addr_fn());
    }

    pub proof fn lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write_always(self)
        ensures
            forall|v2: PersistentMemoryRegionView, v1: PersistentMemoryRegionView, write_addr: int, bytes: Seq<u8>| {
                &&& v1.valid()
                &&& v2.valid()
                &&& v1.len() == v2.len()
                &&& 0 <= write_addr
                &&& write_addr + bytes.len() <= v1.len()
                &&& #[trigger] v2.can_result_from_write(v1, write_addr, bytes)
                &&& self.start() + self.len() <= v1.len()
                &&& self.start() % (const_persistence_chunk_size() as nat) == 0
                &&& forall|addr: int| write_addr <= addr < write_addr + bytes.len() ==>
                    address_modifiable_by_subregion(addr, self.start(), self.len(), self.is_writable_absolute_addr_fn())
            } ==> {
                let sv1 = get_subregion_view(v1, self.start(), self.len());
                let sv2 = get_subregion_view(v2, self.start(), self.len());
                sv2.can_result_from_write(sv1, write_addr - self.start(), bytes)
            },
    {
        assert forall|v2: PersistentMemoryRegionView, v1: PersistentMemoryRegionView, write_addr: int, bytes: Seq<u8>| {
            &&& v1.valid()
            &&& v2.valid()
            &&& v1.len() == v2.len()
            &&& 0 <= write_addr
            &&& write_addr + bytes.len() <= v1.len()
            &&& #[trigger] v2.can_result_from_write(v1, write_addr, bytes)
            &&& self.start() + self.len() <= v1.len()
            &&& self.start() % (const_persistence_chunk_size() as nat) == 0
            &&& forall|addr: int| write_addr <= addr < write_addr + bytes.len() ==>
                address_modifiable_by_subregion(addr, self.start(), self.len(), self.is_writable_absolute_addr_fn())
        } implies {
            let sv1 = get_subregion_view(v1, self.start(), self.len());
            let sv2 = get_subregion_view(v2, self.start(), self.len());
            sv2.can_result_from_write(sv1, write_addr - self.start(), bytes)
        } by {
            self.lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write(
                v2, v1, write_addr, bytes
            ); 
        }
    }

    pub exec fn read_relative_unaligned<Perm, PMRegion>(
        self: &Self,
        powerpm: &PoWERPersistentMemoryRegion<PMRegion>,
        relative_addr: u64,
        num_bytes: u64,
        Tracked(perm): Tracked<&Perm>,
    ) ->(result: Result<Vec<u8>, PmemError>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(powerpm, perm),
            relative_addr + num_bytes <= self.end(),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes =
                        self.view(powerpm).read_state.subrange(relative_addr as int, relative_addr + num_bytes);
                    // The address in `bytes_read_from_storage`
                    // reflects the fact that we're reading from a
                    // subregion at a certain start.
                    let absolute_addr = relative_addr + self.start();
                    bytes_read_from_storage(bytes@, true_bytes, absolute_addr,
                                            powerpm.constants())
                },
                Err(_) => false,
            }
    {
        self.read_absolute_unaligned::<Perm, _>(powerpm, relative_addr + self.start_, num_bytes, Tracked(perm))
    }

    pub exec fn read_absolute_unaligned<Perm, PMRegion>(
        self: &Self,
        powerpm: &PoWERPersistentMemoryRegion<PMRegion>,
        absolute_addr: u64,
        num_bytes: u64,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<Vec<u8>, PmemError>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(powerpm, perm),
            self.start() <= absolute_addr,
            absolute_addr + num_bytes <= self.end(),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(powerpm).read_state.subrange(
                        absolute_addr - self.start(),
                        absolute_addr + num_bytes - self.start()
                    );
                    bytes_read_from_storage(bytes@, true_bytes, absolute_addr as int,
                                            powerpm.constants())
                },
                Err(_) => false,
            }
    {
        let ghost true_bytes1 = self.view(powerpm).read_state.subrange(
            absolute_addr - self.start(),
            absolute_addr + num_bytes - self.start(),
        );
        let ghost true_bytes2 = powerpm@.read_state.subrange(
            absolute_addr as int,
            absolute_addr + num_bytes
        );
        assert(true_bytes1 =~= true_bytes2);
        powerpm.get_pm_region_ref().read_unaligned(absolute_addr, num_bytes)
    }

    pub exec fn read_relative_aligned<'a, S, Perm, PMRegion>(
        self: &Self,
        powerpm: &'a PoWERPersistentMemoryRegion<PMRegion>,
        relative_addr: u64,
        Ghost(true_val): Ghost<S>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(powerpm, perm),
            relative_addr + S::spec_size_of() <= self.end(),
            self.view(powerpm).read_state.subrange(relative_addr as int, relative_addr + S::spec_size_of()) == true_val.spec_to_bytes(),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(powerpm).read_state.subrange(
                        relative_addr as int,
                        relative_addr + S::spec_size_of(),
                    );
                    let absolute_addr = relative_addr + self.start();
                    bytes_read_from_storage(bytes@, true_bytes, absolute_addr,
                                            powerpm.constants())
                },
                Err(_) => false,
            }
    {
        self.read_absolute_aligned::<_, Perm, _>(powerpm, relative_addr + self.start_, Ghost(true_val), Tracked(perm))
    }

    pub exec fn read_absolute_aligned<'a, S, Perm, PMRegion>(
        self: &Self,
        powerpm: &'a PoWERPersistentMemoryRegion<PMRegion>,
        absolute_addr: u64,
        Ghost(true_val): Ghost<S>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(powerpm, perm),
            self.start() <= absolute_addr,
            absolute_addr + S::spec_size_of() <= self.end(),
            self.view(powerpm).read_state.subrange(absolute_addr - self.start(),
                                                absolute_addr + S::spec_size_of() - self.start()) ==
                true_val.spec_to_bytes(),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = true_val.spec_to_bytes();
                    bytes_read_from_storage(bytes@, true_bytes, absolute_addr as int,
                                            powerpm.constants())
                },
                Err(_) => false,
            }
    {
        let ghost true_bytes1 = self.view(powerpm).read_state.subrange(
            absolute_addr - self.start(),
            absolute_addr + S::spec_size_of() - self.start(),
        );
        let ghost true_bytes2 = powerpm@.read_state.subrange(
            absolute_addr as int,
            absolute_addr + S::spec_size_of()
        );
        assert(true_bytes1 =~= true_bytes2);

        powerpm.get_pm_region_ref().read_aligned::<S>(absolute_addr)
    }


    pub exec fn write_relative<Perm, PMRegion>(
        self: &Self,
        powerpm: &mut PoWERPersistentMemoryRegion<PMRegion>,
        relative_addr: u64,
        bytes: &[u8],
        Tracked(perm): Tracked<&Perm>,
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(&*old(powerpm), perm),
            relative_addr + bytes@.len() <= self.view(&*old(powerpm)).len(),
            forall |i: int| relative_addr <= i < relative_addr + bytes@.len() ==> self.is_writable_relative_addr(i),
        ensures
            self.inv(powerpm, perm),
            self.view(powerpm).can_result_from_write(self.view(&*old(powerpm)), relative_addr as int, bytes@),
    {
        assert(forall |addr| #![trigger self.is_writable_absolute_addr_fn()(addr)]
                   !self.is_writable_absolute_addr_fn()(addr) ==> !self.is_writable_relative_addr(addr - self.start()));
        proof {
            self.lemma_state_resulting_from_partial_write_differs_only_where_this_allows_always();
            self.lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write_always();
        }
        powerpm.write::<Perm>(relative_addr + self.start_, bytes, Tracked(perm));
    }

    pub exec fn write_absolute<Perm, PMRegion>(
        self: &Self,
        powerpm: &mut PoWERPersistentMemoryRegion<PMRegion>,
        absolute_addr: u64,
        bytes: &[u8],
        Tracked(perm): Tracked<&Perm>,
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(&*old(powerpm), perm),
            self.start() <= absolute_addr,
            absolute_addr + bytes@.len() <= self.end(),
            forall |i: int| absolute_addr <= i < absolute_addr + bytes@.len() ==>
                #[trigger] self.is_writable_absolute_addr_fn()(i),
        ensures
            self.inv(powerpm, perm),
            self.view(powerpm).can_result_from_write(self.view(&*old(powerpm)), absolute_addr - self.start(), bytes@),
    {
        proof {
            self.lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write_always();
            self.lemma_state_resulting_from_partial_write_differs_only_where_this_allows_always();
        }
        powerpm.write::<Perm>(absolute_addr, bytes, Tracked(perm));
    }

    pub exec fn serialize_and_write_relative<S, Perm, PMRegion>(
        self: &Self,
        powerpm: &mut PoWERPersistentMemoryRegion<PMRegion>,
        relative_addr: u64,
        to_write: &S,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            S: PmCopy + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(&*old(powerpm), perm),
            relative_addr + S::spec_size_of() <= self.view(&*old(powerpm)).len(),
            forall |i: int| relative_addr <= i < relative_addr + S::spec_size_of() ==>
                self.is_writable_relative_addr(i),
        ensures
            self.inv(powerpm, perm),
            self.view(powerpm).can_result_from_write(self.view(&*old(powerpm)), relative_addr as int,
                                                  to_write.spec_to_bytes()),
            powerpm@.read_state.subrange(relative_addr + self.start(),
                                      relative_addr + self.start() + S::spec_size_of()) == to_write.spec_to_bytes(),
    {
        let ghost bytes = to_write.spec_to_bytes();
        assert(bytes.len() == S::spec_size_of());
        assert(forall |addr| #![trigger self.is_writable_absolute_addr_fn()(addr)]
                   !self.is_writable_absolute_addr_fn()(addr) ==> !self.is_writable_relative_addr(addr - self.start()));
        proof {
            self.lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write_always();
            self.lemma_state_resulting_from_partial_write_differs_only_where_this_allows_always();
            broadcast use lemma_update_then_subrange_is_updated_bytes;
        }
        powerpm.serialize_and_write::<Perm, _>(relative_addr + self.start_, to_write, Tracked(perm));
    }

    pub exec fn serialize_and_write_absolute<S, Perm, PMRegion>(
        self: &Self,
        powerpm: &mut PoWERPersistentMemoryRegion<PMRegion>,
        absolute_addr: u64,
        to_write: &S,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            S: PmCopy + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(&*old(powerpm), perm),
            self.start() <= absolute_addr,
            absolute_addr + S::spec_size_of() <= self.end(),
            forall |i: int| absolute_addr <= i < absolute_addr + S::spec_size_of() ==>
                #[trigger] self.is_writable_absolute_addr_fn()(i),
        ensures
            self.inv(powerpm, perm),
            self.view(powerpm).can_result_from_write(self.view(&*old(powerpm)), absolute_addr - self.start(),
                                                  to_write.spec_to_bytes()),
            powerpm@.read_state.subrange(absolute_addr as int, absolute_addr + S::spec_size_of()) ==
                to_write.spec_to_bytes(),
    {
        let ghost bytes = to_write.spec_to_bytes();
        proof {
            self.lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write_always();
            self.lemma_state_resulting_from_partial_write_differs_only_where_this_allows_always();
            broadcast use lemma_update_then_subrange_is_updated_bytes;
        }
        powerpm.serialize_and_write::<Perm, _>(absolute_addr, to_write, Tracked(perm));
    }

    pub proof fn lemma_reveal_opaque_inv<Perm, PMRegion>(
        self,
        powerpm: &PoWERPersistentMemoryRegion<PMRegion>,
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.opaque_relation_with_powerpm(powerpm),
        ensures
            powerpm.inv(),
            powerpm.constants() == self.constants(),
            powerpm@.len() == self.initial_region_view().len(),
            views_differ_only_where_subregion_allows(self.initial_region_view(), powerpm@, self.start(), self.len(),
                                                     self.is_writable_absolute_addr_fn()),
            self.view(powerpm) == get_subregion_view(powerpm@, self.start(), self.len()),
            forall |addr: int| 0 <= addr < powerpm@.len() && !(self.start() <= addr < self.start() + self.len()) ==>
                #[trigger] powerpm@.read_state[addr] == self.initial_region_view().read_state[addr],
            forall |addr: int| 0 <= addr < powerpm@.len() && !(self.start() <= addr < self.start() + self.len()) ==>
                #[trigger] powerpm@.durable_state[addr] == self.initial_region_view().durable_state[addr],
            forall |addr: int| 0 <= addr < self.len() ==>
                #[trigger] self.view(powerpm).read_state[addr] == powerpm@.read_state[addr + self.start()],
            forall |addr: int| 0 <= addr < self.len() ==>
                #[trigger] self.view(powerpm).durable_state[addr] == powerpm@.durable_state[addr + self.start()],
    {
    }
}


pub struct PersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<nat>,
}

impl PersistentMemorySubregion
{
    pub exec fn new<PMRegion: PersistentMemoryRegion>(
        pm: &PMRegion,
        start: u64,
        Ghost(len): Ghost<nat>,
    ) -> (result: Self)
        requires
            pm.inv(),
            pm@.valid(),
            (start as nat) % (const_persistence_chunk_size() as nat) == 0,
            start + len <= pm@.len() <= u64::MAX,
        ensures
            result.inv(pm),
            result.start() == start,
            result.len() == len,
            result.view(pm) == get_subregion_view(pm@, start as nat, len),
    {
        let result = Self{
            start_: start,
            len_: Ghost(len),
        };
        result
    }

    pub closed spec fn start(self) -> nat
    {
        self.start_ as nat
    }

    pub closed spec fn len(self) -> nat
    {
        self.len_@
    }

    pub open spec fn end(self) -> nat
    {
        self.start() + self.len()
    }

    pub open spec fn view<PMRegion: PersistentMemoryRegion>(
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

    // Bytes are maybe corrupted relative to this subregion if they are maybe corrupted wrt absolute
    // addrs calculated from this subregion's start addr
    pub open spec fn maybe_corrupted_relative(self, bytes: Seq<u8>, true_bytes: Seq<u8>, relative_addrs: Seq<int>, pmc: PersistentMemoryConstants) -> bool 
    {
        let absolute_addrs = Seq::new(relative_addrs.len(), |i: int| self.start() + relative_addrs[i]);
        pmc.maybe_corrupted(bytes, true_bytes, absolute_addrs)
    }

    pub exec fn read_relative_unaligned<'a, PMRegion>(
        self: &Self,
        pm: &'a PMRegion,
        relative_addr: u64,
        num_bytes: u64,
    ) ->(result: Result<Vec<u8>, PmemError>)
        where
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(pm),
            relative_addr + num_bytes <= self.end(),
        ensures
            pm.constants().valid(),
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).read_state.subrange(relative_addr as int, relative_addr + num_bytes);
                    // If the persistent memory region is impervious
                    // to corruption, read returns the last bytes
                    // written. Otherwise, it returns a
                    // possibly-corrupted version of those bytes.
                    //
                    // The addresses in `maybe_corrupted` reflect the fact
                    // that we're reading from a subregion at a certain
                    // start.
                    let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| relative_addr + self.start() + i);
                    pm.constants().maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                },
                Err(_) => false,
            }
    {
        self.read_absolute_unaligned(pm, relative_addr + self.start_, num_bytes)
    }

    pub exec fn read_absolute_unaligned<'a, PMRegion>(
        self: &Self,
        pm: &'a PMRegion,
        absolute_addr: u64,
        num_bytes: u64,
    ) -> (result: Result<Vec<u8>, PmemError>)
        where
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(pm),
            self.start() <= absolute_addr,
            absolute_addr + num_bytes <= self.end(),
        ensures
            pm.constants().valid(),
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).read_state.subrange(
                        absolute_addr - self.start(),
                        absolute_addr + num_bytes - self.start()
                    );
                    // If the persistent memory region is impervious
                    // to corruption, read returns the last bytes
                    // written. Otherwise, it returns a
                    // possibly-corrupted version of those bytes.
                    //
                    // The addresses in `maybe_corrupted` reflect the fact
                    // that we're reading from a subregion at a certain
                    // start.
                    let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| absolute_addr + i);
                    pm.constants().maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                },
                Err(_) => false,
            }
    {
        let ghost true_bytes1 = self.view(pm).read_state.subrange(
            absolute_addr - self.start(),
            absolute_addr + num_bytes - self.start(),
        );
        let ghost true_bytes2 = pm@.read_state.subrange(
            absolute_addr as int,
            absolute_addr + num_bytes
        );
        assert(true_bytes1 =~= true_bytes2);
        pm.read_unaligned(absolute_addr, num_bytes)
    }

    pub exec fn read_relative_aligned<'a, S, PMRegion>(
        self: &Self,
        pm: &'a PMRegion,
        relative_addr: u64,
    ) -> (result: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(pm),
            relative_addr + S::spec_size_of() <= self.end(),
            S::bytes_parseable(extract_bytes(self.view(pm).read_state, relative_addr as nat, S::spec_size_of())),
        ensures
            pm.constants().valid(),
            match result {
                Ok(bytes) => {
                    // let true_bytes = self.view(pm).read_state.subrange(
                    //     relative_addr as int,
                    //     relative_addr + S::spec_size_of(),
                    // );
                    let true_bytes = extract_bytes(
                        self.view(pm).read_state,
                        relative_addr as nat,
                        S::spec_size_of(),
                    );
                    let absolute_addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| relative_addr + self.start() + i);
                    pm.constants().maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                },
                Err(_) => false,
            }
    {
        self.read_absolute_aligned(pm, relative_addr + self.start_)
    }

    pub exec fn read_absolute_aligned<'a, S, PMRegion>(
        self: &Self,
        pm: &'a PMRegion,
        absolute_addr: u64,
    ) -> (result: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(pm),
            self.start() <= absolute_addr,
            absolute_addr + S::spec_size_of() <= self.end(),
            S::bytes_parseable(
                self.view(pm).read_state.subrange(absolute_addr - self.start(),
                                                   absolute_addr + S::spec_size_of() - self.start())
            ),
        ensures
            pm.constants().valid(),
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).read_state.subrange(
                        absolute_addr - self.start(),
                        absolute_addr + S::spec_size_of() - self.start()
                    );
                    let absolute_addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| absolute_addr + i);
                    pm.constants().maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                },
                Err(_) => false,
            }
    {
        let ghost true_bytes1 = self.view(pm).read_state.subrange(
            absolute_addr - self.start(),
            absolute_addr + S::spec_size_of() - self.start(),
        );
        let ghost true_bytes2 = pm@.read_state.subrange(
            absolute_addr as int,
            absolute_addr + S::spec_size_of()
        );
        assert(true_bytes1 =~= true_bytes2);

        pm.read_aligned::<S>(absolute_addr)
    }
}

/// A `WritablePersistentMemorySubregion` is useful when you have full
/// access to write anything anywhere in a persistent-memory region,
/// but want to reason about what happens when you only read and write
/// within a certain subregion.

pub struct WritablePersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<nat>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_writable_absolute_addr_fn_: Ghost<spec_fn(int) -> bool>,
}

impl WritablePersistentMemorySubregion
{
    pub exec fn new<PMRegion: PersistentMemoryRegion>(
        pm: &PMRegion,
        start: u64,
        Ghost(len): Ghost<nat>,
        Ghost(is_writable_absolute_addr_fn): Ghost<spec_fn(int) -> bool>,
    ) -> (result: Self)
        requires
            pm.inv(),
            pm@.valid(),
            (start as nat) % (const_persistence_chunk_size() as nat) == 0,
            start + len <= pm@.len() <= u64::MAX,
        ensures
            result.inv(pm),
            result.constants() == pm.constants(),
            result.start() == start,
            result.len() == len,
            result.initial_region_view() == pm@,
            result.is_writable_absolute_addr_fn() == is_writable_absolute_addr_fn,
            result.view(pm) == result.initial_subregion_view(),
            result.view(pm) == get_subregion_view(pm@, start as nat, len),
    {
        let result = Self{
            start_: start,
            len_: Ghost(len),
            constants_: Ghost(pm.constants()),
            initial_region_view_: Ghost(pm@),
            is_writable_absolute_addr_fn_: Ghost(is_writable_absolute_addr_fn),
        };
        result
    }

    pub closed spec fn constants(self) -> PersistentMemoryConstants
    {
        self.constants_@
    }

    pub closed spec fn start(self) -> nat
    {
        self.start_ as nat
    }

    pub closed spec fn len(self) -> nat
    {
        self.len_@
    }

    pub open spec fn end(self) -> nat
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

    pub open spec fn view<PMRegion: PersistentMemoryRegion>(
        self,
        pm: &PMRegion,
    ) -> PersistentMemoryRegionView
    {
        get_subregion_view(pm@, self.start(), self.len())
    }

    pub closed spec fn opaque_inv<PMRegion: PersistentMemoryRegion>(
        self,
        pm: &PMRegion,
    ) -> bool
    {
        &&& pm.inv()
        &&& pm.constants() == self.constants()
        &&& pm@.valid()
        &&& pm@.len() == self.initial_region_view().len()
        &&& self.initial_region_view().len() <= u64::MAX
        &&& self.start() + self.len() <= pm@.len()
        &&& self.view(pm).len() == self.len()
        &&& self.start() % (const_persistence_chunk_size() as nat) == 0
        &&& views_differ_only_where_subregion_allows(self.initial_region_view(), pm@, self.start(),
                                                   self.len(), self.is_writable_absolute_addr_fn())
    }

    pub open spec fn inv<PMRegion: PersistentMemoryRegion>(
        self,
        pm: &PMRegion,
    ) -> bool
    {
        &&& self.view(pm).len() == self.len()
        &&& self.opaque_inv(pm)
    }

    pub proof fn lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write(
        self,
        v2: PersistentMemoryRegionView,
        v1: PersistentMemoryRegionView,
        write_addr: int,
        bytes: Seq<u8>,
    )
        requires
            v1.valid(),
            v2.valid(),
            v1.len() == v2.len(),
            0 <= write_addr,
            write_addr + bytes.len() <= v1.len(),
            v2.can_result_from_write(v1, write_addr, bytes),
            self.start() + self.len() <= v1.len(),
            self.start() % (const_persistence_chunk_size() as nat) == 0,
            forall|addr: int| write_addr <= addr < write_addr + bytes.len() ==>
                address_modifiable_by_subregion(addr, self.start(), self.len(), self.is_writable_absolute_addr_fn()),
        ensures
            ({
                let sv1 = get_subregion_view(v1, self.start(), self.len());
                let sv2 = get_subregion_view(v2, self.start(), self.len());
                sv2.can_result_from_write(sv1, write_addr - self.start(), bytes)
            }),
    {
        lemma_view_resulting_from_write_has_subregion_view_resulting_from_write(v2, v1, write_addr, bytes,
                                                                                self.start(), self.len(),
                                                                                self.is_writable_absolute_addr_fn());
    }

    pub proof fn lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write_always(self)
        ensures
            forall|v2: PersistentMemoryRegionView, v1: PersistentMemoryRegionView, write_addr: int, bytes: Seq<u8>| {
                &&& v1.valid()
                &&& v2.valid()
                &&& v1.len() == v2.len()
                &&& 0 <= write_addr
                &&& write_addr + bytes.len() <= v1.len()
                &&& #[trigger] v2.can_result_from_write(v1, write_addr, bytes)
                &&& self.start() + self.len() <= v1.len()
                &&& self.start() % (const_persistence_chunk_size() as nat) == 0
                &&& forall|addr: int| write_addr <= addr < write_addr + bytes.len() ==>
                    address_modifiable_by_subregion(addr, self.start(), self.len(), self.is_writable_absolute_addr_fn())
            } ==> {
                let sv1 = get_subregion_view(v1, self.start(), self.len());
                let sv2 = get_subregion_view(v2, self.start(), self.len());
                sv2.can_result_from_write(sv1, write_addr - self.start(), bytes)
            },
    {
        assert forall|v2: PersistentMemoryRegionView, v1: PersistentMemoryRegionView, write_addr: int, bytes: Seq<u8>| {
            &&& v1.valid()
            &&& v2.valid()
            &&& v1.len() == v2.len()
            &&& 0 <= write_addr
            &&& write_addr + bytes.len() <= v1.len()
            &&& #[trigger] v2.can_result_from_write(v1, write_addr, bytes)
            &&& self.start() + self.len() <= v1.len()
            &&& self.start() % (const_persistence_chunk_size() as nat) == 0
            &&& forall|addr: int| write_addr <= addr < write_addr + bytes.len() ==>
                address_modifiable_by_subregion(addr, self.start(), self.len(), self.is_writable_absolute_addr_fn())
        } implies {
            let sv1 = get_subregion_view(v1, self.start(), self.len());
            let sv2 = get_subregion_view(v2, self.start(), self.len());
            sv2.can_result_from_write(sv1, write_addr - self.start(), bytes)
        } by {
            self.lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write(
                v2, v1, write_addr, bytes
            ); 
        }
    }

    pub proof fn lemma_state_resulting_from_partial_write_differs_only_where_this_allows(
        self,
        new_state: Seq<u8>,
        old_state: Seq<u8>,
        write_addr: int,
        bytes: Seq<u8>,
    )
        requires
            0 <= write_addr,
            write_addr + bytes.len() <= old_state.len(),
            self.start() + self.len() <= old_state.len(),
            forall|addr: int| write_addr <= addr < write_addr + bytes.len() ==>
                address_modifiable_by_subregion(addr, self.start(), self.len(), self.is_writable_absolute_addr_fn()),
            can_result_from_partial_write(new_state, old_state, write_addr, bytes),
        ensures
            memories_differ_only_where_subregion_allows(old_state, new_state, self.start(), self.len(),
                                                        self.is_writable_absolute_addr_fn()),
    {
        lemma_state_resulting_from_partial_write_within_subregion_differs_only_where_subregion_allows(
            new_state, old_state, write_addr, bytes, self.start(), self.len(), self.is_writable_absolute_addr_fn()
        );
    }

    pub proof fn lemma_state_resulting_from_partial_write_differs_only_where_this_allows_always(self)
        ensures
            forall|new_state: Seq<u8>, old_state: Seq<u8>, write_addr: int, bytes: Seq<u8>| {
                &&& 0 <= write_addr
                &&& write_addr + bytes.len() <= old_state.len()
                &&& self.start() + self.len() <= old_state.len()
                &&& forall|addr: int| write_addr <= addr < write_addr + bytes.len() ==>
                    address_modifiable_by_subregion(addr, self.start(), self.len(), self.is_writable_absolute_addr_fn())
                &&& can_result_from_partial_write(new_state, old_state, write_addr, bytes)
            } ==> memories_differ_only_where_subregion_allows(old_state, new_state, self.start(), self.len(),
                                                             self.is_writable_absolute_addr_fn()),
    {
        assert forall|new_state: Seq<u8>, old_state: Seq<u8>, write_addr: int, bytes: Seq<u8>| {
                &&& 0 <= write_addr
                &&& write_addr + bytes.len() <= old_state.len()
                &&& self.start() + self.len() <= old_state.len()
                &&& forall|addr: int| write_addr <= addr < write_addr + bytes.len() ==>
                    address_modifiable_by_subregion(addr, self.start(), self.len(), self.is_writable_absolute_addr_fn())
                &&& can_result_from_partial_write(new_state, old_state, write_addr, bytes)
            } implies memories_differ_only_where_subregion_allows(old_state, new_state, self.start(), self.len(),
                                                                  self.is_writable_absolute_addr_fn()) by {
            self.lemma_state_resulting_from_partial_write_differs_only_where_this_allows(
                new_state, old_state, write_addr, bytes
            );
        }
    }

    pub exec fn read_relative_unaligned<PMRegion: PersistentMemoryRegion>(
        self: &Self,
        pm: &PMRegion,
        relative_addr: u64,
        num_bytes: u64,
    ) ->(result: Result<Vec<u8>, PmemError>)
        requires
            self.inv(pm),
            relative_addr + num_bytes <= self.end(),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).read_state.subrange(relative_addr as int, relative_addr + num_bytes);
                    // If the persistent memory region is impervious
                    // to corruption, read returns the last bytes
                    // written. Otherwise, it returns a
                    // possibly-corrupted version of those bytes.
                    //
                    // The addresses in `maybe_corrupted` reflect the fact
                    // that we're reading from a subregion at a certain
                    // start.
                    let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| relative_addr + self.start() + i);
                    pm.constants().maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                },
                Err(_) => false,
            }
    {
        self.read_absolute_unaligned(pm, relative_addr + self.start_, num_bytes)
    }

    pub exec fn read_absolute_unaligned<PMRegion: PersistentMemoryRegion>(
        self: &Self,
        pm: &PMRegion,
        absolute_addr: u64,
        num_bytes: u64,
    ) -> (result: Result<Vec<u8>, PmemError>)
        requires
            self.inv(pm),
            self.start() <= absolute_addr,
            absolute_addr + num_bytes <= self.end(),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).read_state.subrange(
                        absolute_addr - self.start(),
                        absolute_addr + num_bytes - self.start()
                    );
                    // If the persistent memory region is impervious
                    // to corruption, read returns the last bytes
                    // written. Otherwise, it returns a
                    // possibly-corrupted version of those bytes.
                    //
                    // The addresses in `maybe_corrupted` reflect the fact
                    // that we're reading from a subregion at a certain
                    // start.
                    let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| absolute_addr + i);
                    pm.constants().maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                },
                Err(_) => false,
            }
    {
        let ghost true_bytes1 = self.view(pm).read_state.subrange(
            absolute_addr - self.start(),
            absolute_addr + num_bytes - self.start(),
        );
        let ghost true_bytes2 = pm@.read_state.subrange(
            absolute_addr as int,
            absolute_addr + num_bytes
        );
        assert(true_bytes1 =~= true_bytes2);
        pm.read_unaligned(absolute_addr, num_bytes)
    }

    pub exec fn read_relative_aligned<'a, S, PMRegion>(
        self: &Self,
        pm: &'a PMRegion,
        relative_addr: u64,
    ) -> (result: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(pm),
            relative_addr < relative_addr + S::spec_size_of() <= self.end(),
            <S as PmCopyHelper>::bytes_parseable(
                self.view(pm).read_state.subrange(relative_addr as int, relative_addr + S::spec_size_of())
            ),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).read_state.subrange(
                        relative_addr as int,
                        relative_addr + S::spec_size_of(),
                    );
                    let absolute_addrs = Seq::<int>::new(S::spec_size_of() as nat,
                                                       |i: int| relative_addr + self.start() + i);
                    self.constants().maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                },
                Err(_) => false,
            }
    {
        self.read_absolute_aligned(pm, relative_addr + self.start_)
    }

    pub exec fn read_absolute_aligned<'a, S, PMRegion>(
        self: &Self,
        pm: &'a PMRegion,
        absolute_addr: u64,
    ) -> (result: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(pm),
            self.start() <= absolute_addr,
            absolute_addr < absolute_addr + S::spec_size_of() <= self.end(),
            <S as PmCopyHelper>::bytes_parseable(
                self.view(pm).read_state.subrange(absolute_addr - self.start(),
                                                   absolute_addr + S::spec_size_of() - self.start())
            ),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).read_state.subrange(
                        absolute_addr - self.start(),
                        absolute_addr + S::spec_size_of() - self.start()
                    );
                    let absolute_addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| absolute_addr + i);
                    self.constants().maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                },
                Err(_) => false,
            }
    {
        let ghost true_bytes1 = self.view(pm).read_state.subrange(
            absolute_addr - self.start(),
            absolute_addr + S::spec_size_of() - self.start(),
        );
        let ghost true_bytes2 = pm@.read_state.subrange(
            absolute_addr as int,
            absolute_addr + S::spec_size_of()
        );
        assert(true_bytes1 =~= true_bytes2);

        pm.read_aligned::<S>(absolute_addr)
    }

    pub exec fn write_relative<PMRegion: PersistentMemoryRegion>(
        self: &Self,
        pm: &mut PMRegion,
        relative_addr: u64,
        bytes: &[u8],
    )
        requires
            self.inv(&*old(pm)),
            relative_addr + bytes@.len() <= self.view(&*old(pm)).len(),
            forall |i: int| relative_addr <= i < relative_addr + bytes@.len() ==> self.is_writable_relative_addr(i),
        ensures
            self.inv(pm),
            self.view(pm).can_result_from_write(self.view(&*old(pm)), relative_addr as int, bytes@),
    {
        assert(forall |addr| #![trigger self.is_writable_absolute_addr_fn()(addr)]
                   !self.is_writable_absolute_addr_fn()(addr) ==> !self.is_writable_relative_addr(addr - self.start()));
        pm.write(relative_addr + self.start_, bytes);
        proof {
            self.lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write_always();
            self.lemma_state_resulting_from_partial_write_differs_only_where_this_allows_always();
        }
    }

    pub exec fn write_absolute<PMRegion: PersistentMemoryRegion>(
        self: &Self,
        pm: &mut PMRegion,
        absolute_addr: u64,
        bytes: &[u8],
    )
        requires
            self.inv(&*old(pm)),
            self.start() <= absolute_addr,
            absolute_addr + bytes@.len() <= self.end(),
            forall |i: int| absolute_addr <= i < absolute_addr + bytes@.len() ==>
                #[trigger] self.is_writable_absolute_addr_fn()(i),
        ensures
            self.inv(pm),
            self.view(pm).can_result_from_write(self.view(&*old(pm)), absolute_addr - self.start(), bytes@),
    {
        pm.write(absolute_addr, bytes);
        proof {
            self.lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write_always();
            self.lemma_state_resulting_from_partial_write_differs_only_where_this_allows_always();
        }
    }

    pub exec fn serialize_and_write_relative<S, PMRegion>(
        self: &Self,
        pm: &mut PMRegion,
        relative_addr: u64,
        to_write: &S,
    )
        where
            S: PmCopy + Sized,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(&*old(pm)),
            relative_addr + S::spec_size_of() <= self.view(&*old(pm)).len(),
            forall |i: int| relative_addr <= i < relative_addr + S::spec_size_of() ==>
                self.is_writable_relative_addr(i),
        ensures
            pm@.len() == old(pm)@.len(),
            self.inv(pm),
            self.view(pm).can_result_from_write(self.view(&*old(pm)), relative_addr as int,
                                                to_write.spec_to_bytes()),
            pm@.read_state.subrange(relative_addr + self.start(),
                                    relative_addr + self.start() + S::spec_size_of()) == to_write.spec_to_bytes(),
    {
        let ghost bytes = to_write.spec_to_bytes();
        assert(bytes.len() == S::spec_size_of());
        assert(forall |addr| #![trigger self.is_writable_absolute_addr_fn()(addr)]
                   !self.is_writable_absolute_addr_fn()(addr) ==> !self.is_writable_relative_addr(addr - self.start()));
        pm.serialize_and_write(relative_addr + self.start_, to_write);
        proof {
            self.lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write_always();
            self.lemma_state_resulting_from_partial_write_differs_only_where_this_allows_always();
            broadcast use lemma_update_then_subrange_is_updated_bytes;
        }
    }

    pub exec fn serialize_and_write_absolute<S, PMRegion>(
        self: &Self,
        pm: &mut PMRegion,
        absolute_addr: u64,
        to_write: &S,
    )
        where
            S: PmCopy + Sized,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(&*old(pm)),
            self.start() <= absolute_addr,
            absolute_addr + S::spec_size_of() <= self.end(),
            forall |i: int| absolute_addr <= i < absolute_addr + S::spec_size_of() ==>
                #[trigger] self.is_writable_absolute_addr_fn()(i),
        ensures
            self.inv(pm),
            self.view(pm).can_result_from_write(self.view(&*old(pm)), absolute_addr - self.start(),
                                                to_write.spec_to_bytes()),
            pm@.read_state.subrange(absolute_addr as int, absolute_addr + S::spec_size_of()) == to_write.spec_to_bytes(),
    {
        let ghost bytes = to_write.spec_to_bytes();
        pm.serialize_and_write(absolute_addr, to_write);
        proof {
            self.lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write_always();
            self.lemma_state_resulting_from_partial_write_differs_only_where_this_allows_always();
            broadcast use lemma_update_then_subrange_is_updated_bytes;
        }
    }

    pub proof fn lemma_reveal_opaque_inv<PMRegion: PersistentMemoryRegion>(
        self,
        pm: &PMRegion,
    )
        requires
            self.inv(pm),
        ensures
            pm.inv(),
            pm.constants() == self.constants(),
            pm@.len() == self.initial_region_view().len(),
            views_differ_only_where_subregion_allows(self.initial_region_view(), pm@, self.start(), self.len(),
                                                     self.is_writable_absolute_addr_fn()),
            self.view(pm) == get_subregion_view(pm@, self.start(), self.len()),
            forall |addr: int| 0 <= addr < self.len() ==>
                #[trigger] self.view(pm).read_state[addr] == pm@.read_state[addr + self.start()],
            forall |addr: int| 0 <= addr < self.len() ==>
                #[trigger] self.view(pm).durable_state[addr] == pm@.durable_state[addr + self.start()],
    {
    }
}

pub proof fn lemma_subregion_commutes_with_flush(v: PersistentMemoryRegionView, start: nat, len: nat)
    requires
        v.len() >= start + len,
    ensures
        get_subregion_view(v, start, len).read_state == extract_bytes(v.read_state, start, len)
{
    assert(get_subregion_view(v, start, len).read_state =~= extract_bytes(v.read_state, start, len));
}

pub exec fn check_crc_for_two_reads_in_subregion<PM>(
    data1_c: &[u8],
    data2_c: &[u8],
    crc_c: &[u8],
    subregion: &PersistentMemorySubregion,
    pm_region: &PM,
    Ghost(relative_data_addr1): Ghost<int>,
    Ghost(relative_data_addr2): Ghost<int>,
    Ghost(relative_crc_addr): Ghost<int>,
) -> (b: bool)
    where 
        PM: PersistentMemoryRegion
    requires
        pm_region.constants().valid(),
        0 <= relative_data_addr1,
        0 <= relative_data_addr2,
        0 <= relative_crc_addr,
        relative_data_addr1 + data1_c@.len() <= subregion.len(),
        relative_data_addr2 + data2_c@.len() <= subregion.len(),
        relative_crc_addr + crc_c@.len() <= subregion.len(),
        subregion.start() + subregion.len() <= pm_region@.len(),
        ({
            ||| relative_data_addr1 + data1_c@.len() <= relative_data_addr2 <= subregion.len()
            ||| relative_data_addr2 + data2_c@.len() <= relative_data_addr1 <= subregion.len()
        }),
        crc_c@.len() == u64::spec_size_of(),
        ({
            let true_data_bytes1 =
                subregion.view(pm_region).read_state.subrange(relative_data_addr1 as int,
                                                              relative_data_addr1 + data1_c@.len());
            let true_data_bytes2 =
                subregion.view(pm_region).read_state.subrange(relative_data_addr2 as int,
                                                              relative_data_addr2 + data2_c@.len());
            let true_crc_bytes = spec_crc_bytes(true_data_bytes1 + true_data_bytes2);
            &&& bytes_read_from_storage(data1_c@, true_data_bytes1, relative_data_addr1 + subregion.start(),
                                      pm_region.constants())
            &&& bytes_read_from_storage(data2_c@, true_data_bytes2, relative_data_addr2 + subregion.start(),
                                      pm_region.constants())
            &&& bytes_read_from_storage(crc_c@, true_crc_bytes, relative_crc_addr + subregion.start(),
                                      pm_region.constants())
        }),
        ({
            let absolute_data1_addrs = Seq::new(data1_c@.len(), |i: int| i + relative_data_addr1 + subregion.start());
            let absolute_data2_addrs = Seq::new(data2_c@.len(), |i: int| i + relative_data_addr2 + subregion.start());
            let absolute_crc_addrs = Seq::new(u64::spec_size_of(), |i: int| i + relative_crc_addr + subregion.start());
            (absolute_data1_addrs + absolute_data2_addrs + absolute_crc_addrs).no_duplicates()
        }),
    ensures
        ({
            let true_data_bytes1 =
                subregion.view(pm_region).read_state.subrange(relative_data_addr1 as int,
                                                              relative_data_addr1 + data1_c@.len());
            let true_data_bytes2 =
                subregion.view(pm_region).read_state.subrange(relative_data_addr2 as int,
                                                              relative_data_addr2 + data2_c@.len());
            let true_crc_bytes = spec_crc_bytes(true_data_bytes1 + true_data_bytes2);
            if b {
                &&& data1_c@ == true_data_bytes1
                &&& data2_c@ == true_data_bytes2
                &&& crc_c@ == true_crc_bytes
            }
            else {
                !pm_region.constants().impervious_to_corruption()
            }
        }),
{
    // calculate the CRC using a digest including both data1_c and data2_c
    let mut digest = CrcDigest::new();
    digest.write_bytes(data1_c);
    digest.write_bytes(data2_c);
    proof {
        assert(digest.bytes_in_digest() =~= data1_c@ + data2_c@);
    }
    let computed_crc = digest.sum64();

    assert(computed_crc == spec_crc_u64(data1_c@ + data2_c@));

    // Check whether the CRCs match. This is done in an external body function so that we can convert the maybe-corrupted
    // CRC to a u64 for comparison to the computed CRC.
    let crcs_match = compare_crcs(crc_c, computed_crc);

    proof {
        let true_data_bytes1 =
            subregion.view(pm_region).read_state.subrange(relative_data_addr1 as int,
                                                          relative_data_addr1 + data1_c@.len());
        let true_data_bytes2 =
            subregion.view(pm_region).read_state.subrange(relative_data_addr2 as int,
                                                          relative_data_addr2 + data2_c@.len());
        let true_crc_bytes = spec_crc_bytes(true_data_bytes1 + true_data_bytes2);

        let data_c = data1_c@ + data2_c@;
        let true_data = true_data_bytes1 + true_data_bytes2;
        let absolute_data_addrs1 = Seq::new(data1_c@.len(),
                                            |i: int| i + relative_data_addr1 + subregion.start());
        let absolute_data_addrs2 = Seq::new(data2_c@.len(),
                                            |i: int| i + relative_data_addr2 + subregion.start());
        let absolute_crc_addrs = Seq::new(u64::spec_size_of(),
                                          |i: int| i + relative_crc_addr + subregion.start());

        if pm_region.constants().impervious_to_corruption() {
            pm_region.constants().maybe_corrupted_zero_addrs(data_c, true_data, absolute_data_addrs1 + absolute_data_addrs2);
            pm_region.constants().maybe_corrupted_zero(crc_c@, true_crc_bytes);
            assert(extract_bytes(data_c, 0, data1_c@.len()) == data1_c@);
            assert(extract_bytes(data_c, data1_c@.len(), data2_c@.len()) == data2_c@);
            assert(data1_c@ == true_data_bytes1);
            assert(data2_c@ == true_data_bytes2);
        }

        if {
            &&& !pm_region.constants().impervious_to_corruption()
            &&& crcs_match
        } {
            pm_region.constants().maybe_corrupted_crc(data_c, true_data, absolute_data_addrs1 + absolute_data_addrs2,
                                                      crc_c@, true_crc_bytes, absolute_crc_addrs);
            assert(extract_bytes(data_c, 0, data1_c@.len()) == data1_c@);
            assert(extract_bytes(data_c, data1_c@.len(), data2_c@.len()) == data2_c@);
            assert(data1_c@ == true_data_bytes1);
            assert(data2_c@ == true_data_bytes2);
        }
    }
    crcs_match
}

// TODO DOCUMENTATION
pub fn check_cdb_in_subregion<PM>(
    cdb_c: MaybeCorruptedBytes<u64>,
    subregion: &PersistentMemorySubregion,
    pm_region: &PM,
    Ghost(pmc): Ghost<PersistentMemoryConstants>,
    Ghost(relative_cdb_addrs): Ghost<Seq<int>>,
) -> (result: Option<bool>)
    where 
        PM: PersistentMemoryRegion,
    requires
        pmc.valid(),
        forall |i: int| 0 <= i < relative_cdb_addrs.len() ==> relative_cdb_addrs[i] <= subregion.view(pm_region).len(),
        relative_cdb_addrs.no_duplicates(),
        ({
            let true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| subregion.view(pm_region).read_state[relative_cdb_addrs[i]]);
            let true_cdb = u64::spec_from_bytes(true_cdb_bytes);
            &&& u64::bytes_parseable(true_cdb_bytes)
            &&& true_cdb == CDB_FALSE || true_cdb == CDB_TRUE
            &&& subregion.maybe_corrupted_relative(cdb_c@, true_cdb_bytes, relative_cdb_addrs, pmc)
        })
    ensures
        ({
            let true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| subregion.view(pm_region).read_state[relative_cdb_addrs[i]]);
            let true_cdb = u64::spec_from_bytes(true_cdb_bytes);
            match result {
                Some(b) => if b { true_cdb == CDB_TRUE }
                           else { true_cdb == CDB_FALSE },
                None => !pmc.impervious_to_corruption(),
            }
        })
{
    let ghost true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| subregion.view(pm_region).read_state[relative_cdb_addrs[i]]);
    let ghost absolute_cdb_addrs = Seq::new(relative_cdb_addrs.len(), |i: int| subregion.start() + relative_cdb_addrs[i]);
    proof {
        // We may need to invoke the lemma `maybe_corrupted_cdb` to justify
        // concluding that, if we read `CDB_FALSE` or `CDB_TRUE`, it can't
        // have been corrupted.
        if pmc.impervious_to_corruption() {
            pmc.maybe_corrupted_zero(cdb_c@, true_cdb_bytes);
        }
        if !pmc.impervious_to_corruption() && (cdb_c@ == CDB_FALSE.spec_to_bytes() || cdb_c@ == CDB_TRUE.spec_to_bytes()) {
            pmc.maybe_corrupted_cdb(cdb_c@, true_cdb_bytes, absolute_cdb_addrs);
        }  
    }
    
    let cdb_val = cdb_c.extract_cdb(Ghost(true_cdb_bytes), Ghost(absolute_cdb_addrs), Ghost(pmc));
    assert(cdb_val.spec_to_bytes() == cdb_c@);

    // If the read encoded CDB is one of the expected ones, translate
    // it into a boolean; otherwise, indicate corruption.

    if *cdb_val == CDB_FALSE {
        Some(false)
    }
    else if *cdb_val == CDB_TRUE {
        Some(true)
    }
    else {
        proof {
            // This part of the proof can be flaky -- invoking this axiom helps stabilize it
            // by helping Z3 prove that the real CDB is neither valid value, which implies we are 
            // not impervious to corruption
           axiom_to_from_bytes::<u64>(*cdb_val);
        }
        None
    }
}

}
