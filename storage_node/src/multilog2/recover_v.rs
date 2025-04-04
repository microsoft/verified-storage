#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;
use super::spec_t::*;

verus! {

pub const ABSOLUTE_POS_OF_VERSION_METADATA: u64 = 0;

// This GUID was generated randomly and is meant to describe the
// multilog module, even if it has future versions.

pub const MULTILOG_PROGRAM_GUID: u128 = 0x3fd80d2c7ae1494b97a6012875a8d673;

// The current version number, and the only one whose contents
// this program can read, is the following:

pub const MULTILOG_PROGRAM_VERSION_NUMBER: u64 = 1;

// The maximum number of logs supported, limited by the number of
// bits in the mask.

pub const MAX_NUM_LOGS: u64 = 64;

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub(super) struct MultilogVersionMetadata {
    pub program_guid: u128,
    pub version_number: u64,
    pub static_metadata_addr: u64,
}

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub(super) struct SingleLogConstants {
    pub log_area_start: u64,
    pub log_area_end: u64,
}

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub(super) struct SingleLogDynamicMetadata {
    pub length: u64,
    pub head: u128,
}

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub(super) struct MultilogStaticMetadata {
    pub id: u128,
    pub num_logs: u64,
    pub mask_cdb_addr: u64,
    pub mask0_addr: u64,
    pub mask0_crc_addr: u64,
    pub mask1_addr: u64,
    pub mask1_crc_addr: u64,
    pub log_metadata_table: TableMetadata,
    pub log_metadata_row_constants_addr: u64,
    pub log_metadata_row_constants_crc_addr: u64,
    pub log_metadata_row_dynamic_metadata0_addr: u64,
    pub log_metadata_row_dynamic_metadata0_crc_addr: u64,
    pub log_metadata_row_dynamic_metadata1_addr: u64,   
    pub log_metadata_row_dynamic_metadata1_crc_addr: u64,
}

pub(super) open spec fn validate_version_metadata(vm: MultilogVersionMetadata) -> bool
{
    &&& vm.program_guid == MULTILOG_PROGRAM_GUID
    &&& vm.version_number == MULTILOG_PROGRAM_VERSION_NUMBER
    &&& vm.static_metadata_addr >= MultilogVersionMetadata::spec_size_of() + u64::spec_size_of()
}

pub(super) open spec fn recover_version_metatata(s: Seq<u8>) -> Option<MultilogVersionMetadata>
{
    if s.len() < MultilogVersionMetadata::spec_size_of() + u64::spec_size_of() {
        None
    }
    else {
        match recover_object::<MultilogVersionMetadata>(s, 0, MultilogVersionMetadata::spec_size_of() as int) {
            None => None,
            Some(vm) =>
                if validate_version_metadata(vm) {
                    Some(vm)
                }
                else {
                    None
                },
        }
    }
}

pub(super) open spec fn validate_static_metadata(sm: MultilogStaticMetadata) -> bool
{
    &&& sm.num_logs <= MAX_NUM_LOGS    
    &&& sm.mask_cdb_addr >= MultilogStaticMetadata::spec_size_of() + u64::spec_size_of()
    &&& sm.mask0_addr >= sm.mask_cdb_addr + u64::spec_size_of()
    &&& sm.mask0_crc_addr >= sm.mask0_addr + u64::spec_size_of()
    &&& sm.mask1_addr >= sm.mask0_crc_addr + u64::spec_size_of()
    &&& sm.mask1_crc_addr >= sm.mask1_addr + u64::spec_size_of()
    &&& sm.log_metadata_table.start >= sm.mask1_crc_addr + u64::spec_size_of()
    &&& sm.log_metadata_table.valid()
    &&& sm.log_metadata_table.num_rows == sm.num_logs
    &&& sm.log_metadata_row_constants_crc_addr >= sm.log_metadata_row_constants_addr + SingleLogConstants::spec_size_of()
    &&& sm.log_metadata_row_dynamic_metadata0_addr >= sm.log_metadata_row_constants_crc_addr + u64::spec_size_of()
    &&& sm.log_metadata_row_dynamic_metadata0_crc_addr >= sm.log_metadata_row_dynamic_metadata0_addr + SingleLogDynamicMetadata::spec_size_of()
    &&& sm.log_metadata_row_dynamic_metadata1_addr >= sm.log_metadata_row_dynamic_metadata0_crc_addr + u64::spec_size_of()
    &&& sm.log_metadata_row_dynamic_metadata1_crc_addr >= sm.log_metadata_row_dynamic_metadata1_addr + SingleLogDynamicMetadata::spec_size_of()
    &&& sm.log_metadata_table.row_size >= sm.log_metadata_row_dynamic_metadata1_crc_addr + u64::spec_size_of()
}

pub(super) open spec fn recover_static_metadata(s: Seq<u8>, vm: MultilogVersionMetadata) -> Option<MultilogStaticMetadata>
{
    if s.len() < vm.static_metadata_addr + MultilogStaticMetadata::spec_size_of() {
        None
    }
    else {
        match recover_object::<MultilogStaticMetadata>(s, vm.static_metadata_addr as int, vm.static_metadata_addr + MultilogStaticMetadata::spec_size_of()) {
            None => None,
            Some(sm) => {
                if !validate_static_metadata(sm) {
                    None
                }
                else {
                    Some(sm)
                }
            },
        }
    }
}

pub(super) open spec fn recover_single_log_constants(s: Seq<u8>, which_log: int, sm: MultilogStaticMetadata) -> Option<SingleLogConstants>
{
    let row_addr = sm.log_metadata_table.spec_row_index_to_addr(which_log);
    let constants_addr = row_addr + sm.log_metadata_row_constants_addr;
    let constants_crc_addr = row_addr + sm.log_metadata_row_constants_crc_addr;
    match recover_object::<SingleLogConstants>(s, constants_addr, constants_crc_addr) {
        None => None,
        Some(c) =>
            if c.log_area_end <= c.log_area_start {
                None
            }
            else {
                Some(c)
            },
    }
}

pub(super) open spec fn recover_single_log_dynamic_metadata(s: Seq<u8>, which_log: int, sm: MultilogStaticMetadata, which_dynamic_metadata: int) -> Option<SingleLogDynamicMetadata>
{
    let row_addr = sm.log_metadata_table.spec_row_index_to_addr(which_log);
    let dynamic_metadata_addr =
         if which_dynamic_metadata == 0 {
            row_addr + sm.log_metadata_row_dynamic_metadata0_addr
        }
        else {
            row_addr + sm.log_metadata_row_dynamic_metadata1_addr
        };
    let dynamic_metadata_crc_addr =
         if which_dynamic_metadata == 0 {
            row_addr + sm.log_metadata_row_dynamic_metadata0_crc_addr
        }
        else {
            row_addr + sm.log_metadata_row_dynamic_metadata1_crc_addr
        };
    recover_object::<SingleLogDynamicMetadata>(s, dynamic_metadata_addr, dynamic_metadata_crc_addr)
}

pub(super) open spec fn recover_mask_cdb(s: Seq<u8>, sm: MultilogStaticMetadata) -> Option<bool>
{
    recover_cdb(s, sm.mask_cdb_addr as int)
}

pub(super) open spec fn recover_mask(s: Seq<u8>, sm: MultilogStaticMetadata) -> Option<u64>
{
    match recover_mask_cdb(s, sm) {
        None => None,
        Some(false) => recover_object::<u64>(s, sm.mask0_addr as int, sm.mask0_crc_addr as int),
        Some(true) => recover_object::<u64>(s, sm.mask1_addr as int, sm.mask1_crc_addr as int),
    }
}

pub open spec fn relative_log_pos_to_addr(
    pos_relative_to_head: int,
    head_addr: int,
    log_area_start: int,
    log_area_end: int,
) -> int
{
    let addr_without_wrapping = head_addr + pos_relative_to_head;
    if addr_without_wrapping >= log_area_end {
        addr_without_wrapping - log_area_end + log_area_start
    }
    else {
        addr_without_wrapping
    }
}

pub open spec fn extract_log(s: Seq<u8>, log_area_start: int, log_area_end: int, head: int, log_length: int) -> Seq<u8>
{
    let log_area_len = log_area_end - log_area_start;
    let head_addr = log_area_start + (head % log_area_len);
    Seq::<u8>::new(log_length as nat,
                |pos_relative_to_head: int|
                   s[log_area_start +
                     relative_log_pos_to_addr(pos_relative_to_head, head_addr, log_area_start, log_area_end)])
}

pub(super) open spec fn recover_single_log_given_metadata(
    s: Seq<u8>,
    c: SingleLogConstants,
    d: SingleLogDynamicMetadata,
) -> Option<AtomicLogState>
{
    if {
        &&& c.log_area_start < c.log_area_end
        &&& d.length <= c.log_area_end - c.log_area_start
        &&& c.log_area_end <= s.len()
    } {
        let log = extract_log(s, c.log_area_start as int, c.log_area_end as int, d.head as int, d.length as int);
        Some(AtomicLogState{ head: d.head as int, log })
    }
    else {
        None
    }
}

pub(super) open spec fn recover_single_log_capacity(s: Seq<u8>, which_log: int, sm: MultilogStaticMetadata) -> Option<u64>
{
    match recover_single_log_constants(s, which_log, sm) {
        None => None,
        Some(c) => Some((c.log_area_end - c.log_area_start) as u64),
    }
}

pub(super) open spec fn recover_single_log(s: Seq<u8>, which_log: int, sm: MultilogStaticMetadata, mask: u64) -> Option<AtomicLogState>
{
    let which_dynamic_metadata = if mask & (1u64 << which_log as u64) != 0 { 1 } else { 0 };
    match recover_single_log_constants(s, which_log, sm) {
        None => None,
        Some(c) =>
            match recover_single_log_dynamic_metadata(s, which_log, sm, which_dynamic_metadata) {
                None => None,
                Some(d) => recover_single_log_given_metadata(s, c, d),
            },
    }
}

pub(super) open spec fn recover_log_capacities(s: Seq<u8>, sm: MultilogStaticMetadata) -> Option<Seq<u64>>
{
    seq_option_to_option_seq::<u64>(
        Seq::<Option<u64>>::new(sm.num_logs as nat,
                              |which_log: int| recover_single_log_capacity(s, which_log, sm)))
}

pub(super) open spec fn recover_multilog(s: Seq<u8>, sm: MultilogStaticMetadata, mask: u64) -> Option<AtomicMultilogState>
{
    let logs = seq_option_to_option_seq::<AtomicLogState>(
        Seq::<Option<AtomicLogState>>::new(sm.num_logs as nat,
                                        |which_log: int| recover_single_log(s, which_log, sm, mask)));
    match logs {
        None => None,
        Some(logs) => Some(AtomicMultilogState{ logs }),
    }
}

pub(super) open spec fn recover_state(s: Seq<u8>) -> Option<RecoveredMultilogState>
{
    match recover_version_metatata(s) {
        None => None,
        Some(vm) =>
            match recover_static_metadata(s, vm) {
                None => None,
                Some(sm) =>
                    match recover_mask(s, sm) {
                        None => None,
                        Some(mask) =>
                            match (recover_log_capacities(s, sm), recover_multilog(s, sm, mask)) {
                                (Some(capacities), Some(state)) => {
                                    let c = MultilogConstants{ id: sm.id, capacities };
                                    Some(RecoveredMultilogState{ c, state })
                                },
                                _ => None,
                            },
                    },
            },
    }
}

}
