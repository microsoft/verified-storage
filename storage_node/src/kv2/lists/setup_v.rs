#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::align_v::*;
use crate::common::overflow_v::CheckedU64;
use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use deps_hack::PmCopy;
use std::collections::HashSet;
use std::hash::Hash;
use super::{ListTable, ListTableSnapshot, ListTableStaticMetadata};
use super::recover_v::*;
use super::spec_v::*;
use super::super::impl_t::*;
use super::super::spec_t::*;

verus! {

impl<Perm, PM, L> ListTable<Perm, PM, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PM: PersistentMemoryRegion,
    L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub exec fn space_needed_for_setup(ps: &SetupParameters, min_start: &CheckedU64) -> (result: CheckedU64)
        requires
            ps.valid(),
        ensures
            result@ == Self::spec_space_needed_for_setup(*ps, min_start@),
    {
        broadcast use pmcopy_axioms;
    
        let row_next_crc_start = CheckedU64::new(size_of::<u64>() as u64);
        let row_element_start = row_next_crc_start.add(size_of::<u64>() as u64);
        let row_element_crc_start = row_element_start.add(size_of::<L>() as u64);
        let row_size = row_element_crc_start.add(size_of::<u64>() as u64);
        let num_rows = CheckedU64::new(ps.max_list_elements);
        let table_size = num_rows.mul_checked(&row_size);
        let initial_space = if min_start.is_overflowed() { 0 } else {
            get_space_needed_for_alignment_usize(min_start.unwrap(), size_of::<u64>()) as u64
        };
        CheckedU64::new(initial_space).add_checked(&table_size)
    }
    
    exec fn setup_given_metadata(
        pm: &mut PM,
        sm: &ListTableStaticMetadata,
    )
        requires
            old(pm).inv(),
            old(pm)@.valid(),
            sm.valid::<L>(),
            sm.table.end <= old(pm)@.len(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            pm@.valid(),
            pm@.len() == old(pm)@.len(),
            Self::recover(pm@.read_state, Set::<u64>::empty(), *sm) == Some(ListTableSnapshot::<L>::init()),
            seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.table.start as int, sm.table.end as int),
    {
        let ghost mapping = ListRecoveryMapping::<L>::new_empty(sm.table);
        let ghost list_addrs = Set::<u64>::empty();

        proof {
            assert(mapping.corresponds(pm@.read_state, list_addrs, *sm));
            assert(mapping.as_snapshot() =~= ListTableSnapshot::<L>::init());
            mapping.lemma_corresponds_implies_equals_new(pm@.read_state, list_addrs, *sm);
        }

        assert(Self::recover(pm@.read_state, Set::<u64>::empty(), *sm) == Some(ListTableSnapshot::<L>::init()));
    }

    pub exec fn setup(
        pm: &mut PM,
        ps: &SetupParameters,
        min_start: u64,
        max_end: u64,
    ) -> (result: Result<ListTableStaticMetadata, KvError>)
        requires
            old(pm).inv(),
            old(pm)@.valid(),
            ps.valid(),
            0 < min_start <= max_end <= old(pm)@.len(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            pm@.valid(),
            pm@.len() == old(pm)@.len(),
            match result {
                Ok(sm) => {
                    &&& Self::recover(pm@.read_state, Set::<u64>::empty(), sm) == Some(ListTableSnapshot::<L>::init())
                    &&& seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.start() as int, sm.end() as int)
                    &&& sm.valid::<L>()
                    &&& min_start <= sm.start() <= sm.end() <= max_end
                    &&& sm.end() - min_start == Self::spec_space_needed_for_setup(*ps, min_start as nat)
                    &&& sm.num_rows() == ps.max_list_elements
                },
                Err(KvError::OutOfSpace) =>
                    max_end - min_start < Self::spec_space_needed_for_setup(*ps, min_start as nat),
                _ => false,
            },
    {
        broadcast use pmcopy_axioms;
    
        let element_size = size_of::<L>();
        assert(element_size == L::spec_size_of()) by {
            broadcast use pmcopy_axioms;
        }
    
        let start = CheckedU64::new(min_start).align(size_of::<u64>());
        let row_next_crc_start = CheckedU64::new(size_of::<u64>() as u64);
        let row_element_start = row_next_crc_start.add(size_of::<u64>() as u64);
        let row_element_crc_start = row_element_start.add(size_of::<L>() as u64);
        let row_size = row_element_crc_start.add(size_of::<u64>() as u64);
        let num_rows = CheckedU64::new(ps.max_list_elements);
        let table_size = num_rows.mul_checked(&row_size);
        let end = start.add_checked(&table_size);
    
        assert(end@ - min_start == Self::spec_space_needed_for_setup(*ps, min_start as nat));
        assert(table_size@ >= row_size@) by {
            vstd::arithmetic::mul::lemma_mul_ordering(ps.max_list_elements as int, row_size@ as int);
        }
    
        if end.is_overflowed() {
            return Err(KvError::OutOfSpace);
        }
        
        if end.unwrap() > max_end {
            return Err(KvError::OutOfSpace);
        }
    
        let table = TableMetadata::new(
            start.unwrap(),
            end.unwrap(),
            ps.max_list_elements,
            row_size.unwrap(),
        );
        let sm = ListTableStaticMetadata {
            table,
            element_size: element_size as u64,
            row_next_start: 0,
            row_element_start: row_element_start.unwrap(),
            row_element_crc_start: row_element_crc_start.unwrap(),
        };
    
        Self::setup_given_metadata(pm, &sm);
        Ok(sm)
    }
}

}

