use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::wrpm_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_hoist_over_denominator};
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

pub proof fn lemma_memories_differ_only_where_subregion_allows_is_commutative(
    mem1: Seq<u8>,
    mem2: Seq<u8>,
    start: nat,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool
)
    ensures
         memories_differ_only_where_subregion_allows(mem1, mem2, start, len, is_writable_absolute_addr_fn)
         <==> memories_differ_only_where_subregion_allows(mem2, mem1, start, len, is_writable_absolute_addr_fn)
{
}

pub proof fn lemma_memories_differ_only_where_subregion_allows_is_commutative_always()
    ensures
        forall|mem1: Seq<u8>, mem2: Seq<u8>, start: nat, len: nat, is_writable_absolute_addr_fn: spec_fn(int) -> bool|
            memories_differ_only_where_subregion_allows(mem1, mem2, start, len, is_writable_absolute_addr_fn)
            <==> memories_differ_only_where_subregion_allows(mem2, mem1, start, len, is_writable_absolute_addr_fn)
{
    assert forall|mem1: Seq<u8>, mem2: Seq<u8>, start: nat, len: nat, is_writable_absolute_addr_fn: spec_fn(int) -> bool|
            memories_differ_only_where_subregion_allows(mem1, mem2, start, len, is_writable_absolute_addr_fn)
            <==> memories_differ_only_where_subregion_allows(mem2, mem1, start, len, is_writable_absolute_addr_fn) by {
        lemma_memories_differ_only_where_subregion_allows_is_commutative(mem1, mem2, start, len,
                                                                         is_writable_absolute_addr_fn);
    }
}

pub proof fn lemma_memories_differ_only_where_subregion_allows_is_transitive(
    mem1: Seq<u8>,
    mem2: Seq<u8>,
    mem3: Seq<u8>,
    start: nat,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool
)
    ensures
        ({
            &&& memories_differ_only_where_subregion_allows(mem2, mem1, start, len, is_writable_absolute_addr_fn)
            &&& memories_differ_only_where_subregion_allows(mem3, mem2, start, len, is_writable_absolute_addr_fn)
        } ==> memories_differ_only_where_subregion_allows(mem3, mem1, start, len, is_writable_absolute_addr_fn))
{
}

pub proof fn lemma_memories_differ_only_where_subregion_allows_is_transitive_always()
    ensures
        forall|mem1: Seq<u8>, mem2: Seq<u8>, mem3: Seq<u8>, start: nat, len: nat,
          is_writable_absolute_addr_fn: spec_fn(int) -> bool| {
            &&& #[trigger] memories_differ_only_where_subregion_allows(mem2, mem1, start, len,
                                                                     is_writable_absolute_addr_fn)
            &&& #[trigger] memories_differ_only_where_subregion_allows(mem3, mem2, start, len,
                                                                     is_writable_absolute_addr_fn)
        } ==> memories_differ_only_where_subregion_allows(mem3, mem1, start, len, is_writable_absolute_addr_fn)
{
    assert forall|mem1: Seq<u8>, mem2: Seq<u8>, mem3: Seq<u8>, start: nat, len: nat,
             is_writable_absolute_addr_fn: spec_fn(int) -> bool| {
            &&& #[trigger] memories_differ_only_where_subregion_allows(mem2, mem1, start, len,
                                                                     is_writable_absolute_addr_fn)
            &&& #[trigger] memories_differ_only_where_subregion_allows(mem3, mem2, start, len,
                                                                     is_writable_absolute_addr_fn)
        } implies memories_differ_only_where_subregion_allows(mem3, mem1, start, len, is_writable_absolute_addr_fn) by {
        lemma_memories_differ_only_where_subregion_allows_is_transitive(mem1, mem2, mem3, start, len,
                                                                        is_writable_absolute_addr_fn);
    }
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

pub open spec fn condition_sufficient_to_create_wrpm_subregion<Perm>(
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
    &&& forall|crash_state| condition(crash_state) ==> perm.check_permission(crash_state)
    &&& condition_stable_to_subregion_modifications(condition, region_view.len(), start as nat, len,
                                                  is_writable_absolute_addr_fn)
}

pub proof fn lemma_condition_sufficient_to_create_wrpm_subregion<Perm>(
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
        condition_sufficient_to_create_wrpm_subregion(region_view, perm, start, len, is_writable_absolute_addr_fn,
                                                      condition),
    ensures
        forall |alt_crash_state: Seq<u8>|
            memories_differ_only_where_subregion_allows(region_view.durable_state, alt_crash_state,
                                                        start as nat, len, is_writable_absolute_addr_fn)
        ==> #[trigger] perm.check_permission(alt_crash_state),
{
    assert forall |alt_crash_state: Seq<u8>|
        memories_differ_only_where_subregion_allows(region_view.durable_state, alt_crash_state, start as nat, len,
                                                    is_writable_absolute_addr_fn)
    implies #[trigger] perm.check_permission(alt_crash_state) by {
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

pub struct WriteRestrictedPersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<nat>,
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
        Ghost(len): Ghost<nat>,
        Ghost(is_writable_absolute_addr_fn): Ghost<spec_fn(int) -> bool>,
    ) -> (result: Self)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            wrpm.inv(),
            wrpm@.valid(),
            (start as nat) % (const_persistence_chunk_size() as nat) == 0,
            start + len <= wrpm@.len() <= u64::MAX,
            forall |alt_crash_state: Seq<u8>|
                memories_differ_only_where_subregion_allows(wrpm@.durable_state, alt_crash_state,
                                                            start as nat, len, is_writable_absolute_addr_fn)
            ==> #[trigger] perm.check_permission(alt_crash_state),
        ensures
            result.inv(wrpm, perm),
            result.constants() == wrpm.constants(),
            result.start() == start,
            result.len() == len,
            result.initial_region_view() == wrpm@,
            result.is_writable_absolute_addr_fn() == is_writable_absolute_addr_fn,
            result.view(wrpm) == result.initial_subregion_view(),
            result.view(wrpm) == get_subregion_view(wrpm@, start as nat, len),
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

    pub exec fn new_with_condition<Perm, PMRegion>(
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
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
            wrpm.inv(),
            wrpm@.valid(),
            (start as nat) % (const_persistence_chunk_size() as nat) == 0,
            condition_sufficient_to_create_wrpm_subregion(wrpm@, perm, start, len, is_writable_absolute_addr_fn,
                                                          condition),
        ensures
            result.inv(wrpm, perm),
            result.constants() == wrpm.constants(),
            result.start() == start,
            result.len() == len,
            result.initial_region_view() == wrpm@,
            result.is_writable_absolute_addr_fn() == is_writable_absolute_addr_fn,
            result.view(wrpm) == result.initial_subregion_view(),
            result.view(wrpm) == get_subregion_view(wrpm@, start as nat, len),
    {
        proof {
            lemma_condition_sufficient_to_create_wrpm_subregion(wrpm@, perm, start, len, is_writable_absolute_addr_fn,
                                                                condition);
        }
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

    pub open spec fn view<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>
    ) -> PersistentMemoryRegionView
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
    {
        get_subregion_view(wrpm@, self.start(), self.len())
    }

    pub closed spec fn opaque_relation_with_wrpm<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
    ) -> bool
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
    {
        &&& wrpm.inv()
        &&& wrpm.constants() == self.constants()
        &&& wrpm@.valid()
        &&& wrpm@.len() == self.initial_region_view().len()
        &&& self.start() + self.len() <= wrpm@.len()
        &&& self.view(wrpm).len() == self.len()
        &&& self.start() % (const_persistence_chunk_size() as nat) == 0
        &&& views_differ_only_where_subregion_allows(self.initial_region_view(), wrpm@, self.start(),
                                                   self.len(), self.is_writable_absolute_addr_fn())
    }

    pub closed spec fn opaque_relation_with_perm<Perm>(self, perm: &Perm) -> bool
        where
            Perm: CheckPermission<Seq<u8>>,
    {
        forall |alt_crash_state: Seq<u8>|
            memories_differ_only_where_subregion_allows(self.initial_region_view().durable_state, alt_crash_state,
                                                        self.start(), self.len(), self.is_writable_absolute_addr_fn())
        ==> #[trigger] perm.check_permission(alt_crash_state)
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
        &&& self.view(wrpm).valid()
        &&& self.view(wrpm).len() == self.len()
        &&& self.initial_region_view().len() <= u64::MAX
        &&& self.opaque_relation_with_wrpm(wrpm)
        &&& self.opaque_relation_with_perm(perm)
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
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        relative_addr: u64,
        num_bytes: u64,
        Tracked(perm): Tracked<&Perm>,
    ) ->(result: Result<Vec<u8>, PmemError>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(wrpm, perm),
            relative_addr + num_bytes <= self.len(),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes =
                        self.view(wrpm).read_state.subrange(relative_addr as int, relative_addr + num_bytes);
                    // The address in `bytes_read_from_storage`
                    // reflects the fact that we're reading from a
                    // subregion at a certain start.
                    let absolute_addr = relative_addr + self.start();
                    bytes_read_from_storage(bytes@, true_bytes, absolute_addr,
                                            wrpm.constants().impervious_to_corruption())
                },
                Err(_) => false,
            }
    {
        self.read_absolute_unaligned(wrpm, relative_addr + self.start_, num_bytes, Tracked(perm))
    }

    pub exec fn read_absolute_unaligned<Perm, PMRegion>(
        self: &Self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        absolute_addr: u64,
        num_bytes: u64,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<Vec<u8>, PmemError>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(wrpm, perm),
            self.start() <= absolute_addr,
            absolute_addr + num_bytes <= self.end(),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(wrpm).read_state.subrange(
                        absolute_addr - self.start(),
                        absolute_addr + num_bytes - self.start()
                    );
                    bytes_read_from_storage(bytes@, true_bytes, absolute_addr as int,
                                            wrpm.constants().impervious_to_corruption())
                },
                Err(_) => false,
            }
    {
        let ghost true_bytes1 = self.view(wrpm).read_state.subrange(
            absolute_addr - self.start(),
            absolute_addr + num_bytes - self.start(),
        );
        let ghost true_bytes2 = wrpm@.read_state.subrange(
            absolute_addr as int,
            absolute_addr + num_bytes
        );
        assert(true_bytes1 =~= true_bytes2);
        wrpm.get_pm_region_ref().read_unaligned(absolute_addr, num_bytes)
    }

    pub exec fn read_relative_aligned<'a, S, Perm, PMRegion>(
        self: &Self,
        wrpm: &'a WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        relative_addr: u64,
        Ghost(true_val): Ghost<S>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(wrpm, perm),
            relative_addr + S::spec_size_of() <= self.len(),
            self.view(wrpm).read_state.subrange(relative_addr as int, relative_addr + S::spec_size_of()) == true_val.spec_to_bytes(),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(wrpm).read_state.subrange(
                        relative_addr as int,
                        relative_addr + S::spec_size_of(),
                    );
                    let absolute_addr = relative_addr + self.start();
                    bytes_read_from_storage(bytes@, true_bytes, absolute_addr,
                                            wrpm.constants().impervious_to_corruption())
                },
                Err(_) => false,
            }
    {
        self.read_absolute_aligned(wrpm, relative_addr + self.start_, Ghost(true_val), Tracked(perm))
    }

    pub exec fn read_absolute_aligned<'a, S, Perm, PMRegion>(
        self: &Self,
        wrpm: &'a WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        absolute_addr: u64,
        Ghost(true_val): Ghost<S>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(wrpm, perm),
            self.start() <= absolute_addr,
            absolute_addr + S::spec_size_of() <= self.end(),
            self.view(wrpm).read_state.subrange(absolute_addr - self.start(),
                                                absolute_addr + S::spec_size_of() - self.start()) ==
                true_val.spec_to_bytes(),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = true_val.spec_to_bytes();
                    bytes_read_from_storage(bytes@, true_bytes, absolute_addr as int,
                                            wrpm.constants().impervious_to_corruption())
                },
                Err(_) => false,
            }
    {
        let ghost true_bytes1 = self.view(wrpm).read_state.subrange(
            absolute_addr - self.start(),
            absolute_addr + S::spec_size_of() - self.start(),
        );
        let ghost true_bytes2 = wrpm@.read_state.subrange(
            absolute_addr as int,
            absolute_addr + S::spec_size_of()
        );
        assert(true_bytes1 =~= true_bytes2);

        wrpm.get_pm_region_ref().read_aligned::<S>(absolute_addr)
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
            forall |i: int| relative_addr <= i < relative_addr + bytes@.len() ==> self.is_writable_relative_addr(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm).can_result_from_write(self.view(old::<&mut _>(wrpm)), relative_addr as int, bytes@),
    {
        assert(forall |addr| #![trigger self.is_writable_absolute_addr_fn()(addr)]
                   !self.is_writable_absolute_addr_fn()(addr) ==> !self.is_writable_relative_addr(addr - self.start()));
        proof {
            self.lemma_state_resulting_from_partial_write_differs_only_where_this_allows_always();
            self.lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write_always();
        }
        wrpm.write(relative_addr + self.start_, bytes, Tracked(perm));
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
            forall |i: int| absolute_addr <= i < absolute_addr + bytes@.len() ==>
                #[trigger] self.is_writable_absolute_addr_fn()(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm).can_result_from_write(self.view(old::<&mut _>(wrpm)), absolute_addr - self.start(), bytes@),
    {
        proof {
            self.lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write_always();
            self.lemma_state_resulting_from_partial_write_differs_only_where_this_allows_always();
        }
        wrpm.write(absolute_addr, bytes, Tracked(perm));
    }

    pub exec fn serialize_and_write_relative<S, Perm, PMRegion>(
        self: &Self,
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        relative_addr: u64,
        to_write: &S,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            S: PmCopy + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old::<&mut _>(wrpm), perm),
            relative_addr + S::spec_size_of() <= self.view(old::<&mut _>(wrpm)).len(),
            forall |i: int| relative_addr <= i < relative_addr + S::spec_size_of() ==>
                self.is_writable_relative_addr(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm).can_result_from_write(self.view(old::<&mut _>(wrpm)), relative_addr as int,
                                                  to_write.spec_to_bytes()),
            wrpm@.read_state.subrange(relative_addr + self.start(),
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
        wrpm.serialize_and_write(relative_addr + self.start_, to_write, Tracked(perm));
    }

    pub exec fn serialize_and_write_absolute<S, Perm, PMRegion>(
        self: &Self,
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        absolute_addr: u64,
        to_write: &S,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            S: PmCopy + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old::<&mut _>(wrpm), perm),
            self.start() <= absolute_addr,
            absolute_addr + S::spec_size_of() <= self.len(),
            forall |i: int| absolute_addr <= i < absolute_addr + S::spec_size_of() ==>
                #[trigger] self.is_writable_absolute_addr_fn()(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm).can_result_from_write(self.view(old::<&mut _>(wrpm)), absolute_addr - self.start(),
                                                  to_write.spec_to_bytes()),
            wrpm@.read_state.subrange(absolute_addr as int, absolute_addr + S::spec_size_of()) ==
                to_write.spec_to_bytes(),
    {
        let ghost bytes = to_write.spec_to_bytes();
        proof {
            self.lemma_view_resulting_from_write_has_this_subregion_view_resulting_from_write_always();
            self.lemma_state_resulting_from_partial_write_differs_only_where_this_allows_always();
            broadcast use lemma_update_then_subrange_is_updated_bytes;
        }
        wrpm.serialize_and_write(absolute_addr, to_write, Tracked(perm));
    }

    pub proof fn lemma_reveal_opaque_inv<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.opaque_relation_with_wrpm(wrpm),
        ensures
            wrpm.inv(),
            wrpm.constants() == self.constants(),
            wrpm@.len() == self.initial_region_view().len(),
            views_differ_only_where_subregion_allows(self.initial_region_view(), wrpm@, self.start(), self.len(),
                                                     self.is_writable_absolute_addr_fn()),
            self.view(wrpm) == get_subregion_view(wrpm@, self.start(), self.len()),
            forall |addr: int| 0 <= addr < wrpm@.len() && !(self.start() <= addr < self.start() + self.len()) ==>
                #[trigger] wrpm@.read_state[addr] == self.initial_region_view().read_state[addr],
            forall |addr: int| 0 <= addr < wrpm@.len() && !(self.start() <= addr < self.start() + self.len()) ==>
                #[trigger] wrpm@.durable_state[addr] == self.initial_region_view().durable_state[addr],
            forall |addr: int| 0 <= addr < self.len() ==>
                #[trigger] self.view(wrpm).read_state[addr] == wrpm@.read_state[addr + self.start()],
            forall |addr: int| 0 <= addr < self.len() ==>
                #[trigger] self.view(wrpm).durable_state[addr] == wrpm@.durable_state[addr + self.start()],
    {
    }

    pub proof fn lemma_if_committed_subview_unchanged_then_committed_view_unchanged<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.opaque_relation_with_wrpm(wrpm),
            self.view(wrpm).read_state == self.initial_subregion_view().read_state,
        ensures
            wrpm@.read_state == self.initial_region_view().read_state,
    {
        let s1 = wrpm@.read_state;
        let s2 = self.initial_region_view().read_state;
        assert forall|addr: int| 0 <= addr < wrpm@.len() implies
                   #[trigger] s1[addr] == s2[addr] by {
            if self.start() <= addr < self.end() {
                assert(s1[addr] == self.view(wrpm).read_state[addr - self.start()]);
                assert(s2[addr] == self.initial_subregion_view().read_state[addr - self.start()]);
            }
            else {
                assert(wrpm@.read_state[addr] == self.initial_region_view().read_state[addr]);
            }
        }
        assert(s1 =~= s2);
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
    pub open spec fn maybe_corrupted_relative(self, bytes: Seq<u8>, true_bytes: Seq<u8>, relative_addrs: Seq<int>) -> bool 
    {
        let absolute_addrs = Seq::new(relative_addrs.len(), |i: int| self.start() + relative_addrs[i]);
        maybe_corrupted(bytes, true_bytes, absolute_addrs)
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
            relative_addr + num_bytes <= self.len(),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).read_state.subrange(relative_addr as int, relative_addr + num_bytes);
                    // If the persistent memory region is impervious
                    // to corruption, read returns the last bytes
                    // written. Otherwise, it returns a
                    // possibly-corrupted version of those bytes.
                    if pm.constants().impervious_to_corruption() {
                        bytes@ == true_bytes
                    }
                    else {
                        // The addresses in `maybe_corrupted` reflect the fact
                        // that we're reading from a subregion at a certain
                        // start.
                        let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| relative_addr + self.start() + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
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
                    if pm.constants().impervious_to_corruption() {
                        bytes@ == true_bytes
                    }
                    else {
                        // The addresses in `maybe_corrupted` reflect the fact
                        // that we're reading from a subregion at a certain
                        // start.
                        let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| absolute_addr + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
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
            relative_addr + S::spec_size_of() <= self.len(),
            S::bytes_parseable(extract_bytes(self.view(pm).read_state, relative_addr as nat, S::spec_size_of())),
        ensures
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
                    if pm.constants().impervious_to_corruption() {
                        bytes@ == true_bytes
                    } else {
                        let absolute_addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| relative_addr + self.start() + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
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
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).read_state.subrange(
                        absolute_addr - self.start(),
                        absolute_addr + S::spec_size_of() - self.start()
                    );
                    if pm.constants().impervious_to_corruption() {
                        bytes@ == true_bytes
                    } else {
                        let absolute_addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| absolute_addr + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
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
            relative_addr + num_bytes <= self.len(),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).read_state.subrange(relative_addr as int, relative_addr + num_bytes);
                    // If the persistent memory region is impervious
                    // to corruption, read returns the last bytes
                    // written. Otherwise, it returns a
                    // possibly-corrupted version of those bytes.
                    if pm.constants().impervious_to_corruption() {
                        bytes@ == true_bytes
                    }
                    else {
                        // The addresses in `maybe_corrupted` reflect the fact
                        // that we're reading from a subregion at a certain
                        // start.
                        let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| relative_addr + self.start() + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
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
                    if pm.constants().impervious_to_corruption() {
                        bytes@ == true_bytes
                    }
                    else {
                        // The addresses in `maybe_corrupted` reflect the fact
                        // that we're reading from a subregion at a certain
                        // start.
                        let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| absolute_addr + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
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
            relative_addr < relative_addr + S::spec_size_of() <= self.len(),
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
                    if self.constants().impervious_to_corruption() {
                        bytes@ == true_bytes
                    } else {
                        let absolute_addrs = Seq::<int>::new(S::spec_size_of() as nat,
                                                           |i: int| relative_addr + self.start() + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
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
                    if self.constants().impervious_to_corruption() {
                        bytes@ == true_bytes
                    } else {
                        let absolute_addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| absolute_addr + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
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
            self.inv(old::<&mut _>(pm)),
            relative_addr + bytes@.len() <= self.view(old::<&mut _>(pm)).len(),
            forall |i: int| relative_addr <= i < relative_addr + bytes@.len() ==> self.is_writable_relative_addr(i),
        ensures
            self.inv(pm),
            self.view(pm).can_result_from_write(self.view(old::<&mut _>(pm)), relative_addr as int, bytes@),
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
            self.inv(old::<&mut _>(pm)),
            self.start() <= absolute_addr,
            absolute_addr + bytes@.len() <= self.len(),
            forall |i: int| absolute_addr <= i < absolute_addr + bytes@.len() ==>
                #[trigger] self.is_writable_absolute_addr_fn()(i),
        ensures
            self.inv(pm),
            self.view(pm).can_result_from_write(self.view(old::<&mut _>(pm)), absolute_addr - self.start(), bytes@),
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
            self.inv(old::<&mut _>(pm)),
            relative_addr + S::spec_size_of() <= self.view(old::<&mut _>(pm)).len(),
            forall |i: int| relative_addr <= i < relative_addr + S::spec_size_of() ==>
                self.is_writable_relative_addr(i),
        ensures
            pm@.len() == old(pm)@.len(),
            self.inv(pm),
            self.view(pm).can_result_from_write(self.view(old::<&mut _>(pm)), relative_addr as int,
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
            self.inv(old::<&mut _>(pm)),
            self.start() <= absolute_addr,
            absolute_addr + S::spec_size_of() <= self.len(),
            forall |i: int| absolute_addr <= i < absolute_addr + S::spec_size_of() ==>
                #[trigger] self.is_writable_absolute_addr_fn()(i),
        ensures
            self.inv(pm),
            self.view(pm).can_result_from_write(self.view(old::<&mut _>(pm)), absolute_addr - self.start(),
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

}
