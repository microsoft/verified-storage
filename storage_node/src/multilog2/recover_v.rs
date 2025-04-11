#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use super::spec_t::*;
use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;

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
pub const MAX_NUM_LOGS: usize = 64;

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

#[verifier::ext_equal]
pub(super) struct MultilogRecoveryMapping {
    pub vm: MultilogVersionMetadata,
    pub sm: MultilogStaticMetadata,
    pub mask_cdb: bool,
    pub mask: u64,
    pub all_log_constants: Seq<SingleLogConstants>,
    pub all_log_dynamic_metadata: Seq<SingleLogDynamicMetadata>,
    pub c: MultilogConstants,
    pub state: AtomicMultilogState,
}

pub(super) open spec fn recover_version_metadata(s: Seq<u8>) -> Option<MultilogVersionMetadata> {
    recover_object::<MultilogVersionMetadata>(s, 0, MultilogVersionMetadata::spec_size_of() as int)
}

pub(super) open spec fn validate_version_metadata(vm: MultilogVersionMetadata) -> bool {
    &&& vm.program_guid == MULTILOG_PROGRAM_GUID
    &&& vm.version_number == MULTILOG_PROGRAM_VERSION_NUMBER
}

pub(super) open spec fn recover_static_metadata(s: Seq<u8>, vm: MultilogVersionMetadata) -> Option<
    MultilogStaticMetadata,
> {
    recover_object::<MultilogStaticMetadata>(
        s,
        vm.static_metadata_addr as int,
        vm.static_metadata_addr + MultilogStaticMetadata::spec_size_of(),
    )
}

pub(super) open spec fn validate_static_metadata(
    sm: MultilogStaticMetadata,
    vm: MultilogVersionMetadata,
) -> bool {
    &&& 0 < sm.num_logs <= MAX_NUM_LOGS
    &&& sm.log_metadata_table.valid()
    &&& sm.log_metadata_table.num_rows == sm.num_logs
    &&& sm.log_metadata_row_constants_crc_addr >= sm.log_metadata_row_constants_addr
        + SingleLogConstants::spec_size_of()
    &&& sm.log_metadata_row_dynamic_metadata0_addr >= sm.log_metadata_row_constants_crc_addr
        + u64::spec_size_of()
    &&& sm.log_metadata_row_dynamic_metadata0_crc_addr >= sm.log_metadata_row_dynamic_metadata0_addr
        + SingleLogDynamicMetadata::spec_size_of()
    &&& sm.log_metadata_row_dynamic_metadata1_addr >= sm.log_metadata_row_dynamic_metadata0_crc_addr
        + u64::spec_size_of()
    &&& sm.log_metadata_row_dynamic_metadata1_crc_addr >= sm.log_metadata_row_dynamic_metadata1_addr
        + SingleLogDynamicMetadata::spec_size_of()
    &&& sm.log_metadata_table.row_size >= sm.log_metadata_row_dynamic_metadata1_crc_addr
        + u64::spec_size_of()
}

pub(super) open spec fn recover_single_log_constants(
    s: Seq<u8>,
    which_log: int,
    sm: MultilogStaticMetadata,
) -> Option<SingleLogConstants> {
    let row_addr = sm.log_metadata_table.spec_row_index_to_addr(which_log);
    let constants_addr = row_addr + sm.log_metadata_row_constants_addr;
    let constants_crc_addr = row_addr + sm.log_metadata_row_constants_crc_addr;
    recover_object::<SingleLogConstants>(s, constants_addr, constants_crc_addr)
}

pub(super) open spec fn recover_single_log_dynamic_metadata_given_version(
    s: Seq<u8>,
    which_log: int,
    sm: MultilogStaticMetadata,
    which_dynamic_metadata: bool,
) -> Option<SingleLogDynamicMetadata> {
    let row_addr = sm.log_metadata_table.spec_row_index_to_addr(which_log);
    let dynamic_metadata_addr = if which_dynamic_metadata {
        row_addr + sm.log_metadata_row_dynamic_metadata1_addr
    } else {
        row_addr + sm.log_metadata_row_dynamic_metadata0_addr
    };
    let dynamic_metadata_crc_addr = if which_dynamic_metadata {
        row_addr + sm.log_metadata_row_dynamic_metadata1_crc_addr
    } else {
        row_addr + sm.log_metadata_row_dynamic_metadata0_crc_addr
    };
    recover_object::<SingleLogDynamicMetadata>(s, dynamic_metadata_addr, dynamic_metadata_crc_addr)
}

pub(super) open spec fn mask_bit_set(mask: u64, which_bit: u64) -> bool
{
    mask & (1u64 << which_bit) != 0
}

pub(super) open spec fn recover_single_log_dynamic_metadata_given_mask(
    s: Seq<u8>,
    which_log: int,
    sm: MultilogStaticMetadata,
    mask: u64,
) -> Option<SingleLogDynamicMetadata> {
    recover_single_log_dynamic_metadata_given_version(s, which_log, sm, mask_bit_set(mask, which_log as u64))
}

pub(super) open spec fn recover_mask_cdb(s: Seq<u8>, sm: MultilogStaticMetadata) -> Option<bool> {
    recover_cdb(s, sm.mask_cdb_addr as int)
}

pub(super) open spec fn recover_mask_given_cdb(
    s: Seq<u8>,
    sm: MultilogStaticMetadata,
    cdb: bool,
) -> Option<u64> {
    if cdb {
        recover_object::<u64>(s, sm.mask1_addr as int, sm.mask1_crc_addr as int)
    } else {
        recover_object::<u64>(s, sm.mask0_addr as int, sm.mask0_crc_addr as int)
    }
}

pub open spec fn relative_log_pos_to_addr(
    pos_relative_to_head: int,
    head_addr: int,
    log_area_start: int,
    log_area_end: int,
) -> int {
    let addr_without_wrapping = head_addr + pos_relative_to_head;
    if addr_without_wrapping >= log_area_end {
        addr_without_wrapping - log_area_end + log_area_start
    } else {
        addr_without_wrapping
    }
}

pub(super) open spec fn recover_state(s: Seq<u8>) -> Option<RecoveredMultilogState> {
    match MultilogRecoveryMapping::new(s) {
        Some(rm) => Some(rm@),
        None => None,
    }
}

impl View for MultilogRecoveryMapping {
    type V = RecoveredMultilogState;

    open(super) spec fn view(&self) -> RecoveredMultilogState {
        RecoveredMultilogState { c: self.c, state: self.state }
    }
}

impl MultilogRecoveryMapping {
    pub(super) open spec fn new(s: Seq<u8>) -> Option<Self> {
        if exists|rm: MultilogRecoveryMapping| rm.corresponds(s) {
            let rm = choose|rm: MultilogRecoveryMapping| rm.corresponds(s);
            Some(rm)
        } else {
            None
        }
    }

    pub(super) open spec fn parts_dont_overlap(self) -> bool {
        &&& self.vm.static_metadata_addr >= MultilogVersionMetadata::spec_size_of()
            + u64::spec_size_of()
        &&& self.sm.mask_cdb_addr >= self.vm.static_metadata_addr
            + MultilogStaticMetadata::spec_size_of() + u64::spec_size_of()
        &&& self.sm.mask0_addr >= self.sm.mask_cdb_addr + u64::spec_size_of()
        &&& self.sm.mask0_crc_addr >= self.sm.mask0_addr + u64::spec_size_of()
        &&& self.sm.mask1_addr >= self.sm.mask0_crc_addr + u64::spec_size_of()
        &&& self.sm.mask1_crc_addr >= self.sm.mask1_addr + u64::spec_size_of()
        &&& self.sm.log_metadata_table.start >= self.sm.mask1_crc_addr + u64::spec_size_of()
        &&& self.sm.log_metadata_table.end >= self.sm.log_metadata_table.start
        &&& self.all_log_constants[0].log_area_start >= self.sm.log_metadata_table.end
        &&& forall|i: int, j: int|
            0 <= i < j < self.sm.num_logs ==> #[trigger] self.all_log_constants[i].log_area_end
                <= #[trigger] self.all_log_constants[j].log_area_start
    }

    pub(super) open spec fn constants_correspond(self) -> bool {
        &&& self.c.id == self.sm.id
        &&& self.c.capacities.len() == self.sm.num_logs
        &&& forall|i: int|
            #![trigger self.c.capacities[i]]
            #![trigger self.all_log_constants[i]]
            0 <= i < self.sm.num_logs ==> {
                &&& self.c.capacities[i] == self.all_log_constants[i].log_area_end
                    - self.all_log_constants[i].log_area_start
                &&& self.c.capacities[i] > 0
            }
    }

    pub(super) open spec fn state_corresponds_to_dynamic_metadata(self) -> bool {
        forall|which_log: int|
            #![trigger self.all_log_dynamic_metadata[which_log]]
            #![trigger self.state.logs[which_log]]
            0 <= which_log < self.sm.num_logs ==> {
                let log_constants = self.all_log_constants[which_log];
                let log_area_len = log_constants.log_area_end - log_constants.log_area_start;
                let log_dynamic_metadata = self.all_log_dynamic_metadata[which_log];
                let head = self.state.logs[which_log].head;
                let log = self.state.logs[which_log].log;
                &&& head == log_dynamic_metadata.head
                &&& log.len() == log_dynamic_metadata.length
                &&& log.len() <= log_area_len
            }
    }

    pub(super) open spec fn storage_state_corresponds(self, s: Seq<u8>) -> bool {
        forall|which_log: int, pos: int|
            #![trigger self.state.logs[which_log].log[pos]]
            0 <= which_log < self.sm.num_logs ==> {
                let log_constants = self.all_log_constants[which_log];
                let log_area_start = log_constants.log_area_start;
                let log_area_end = log_constants.log_area_end;
                let log_area_len = log_area_end - log_area_start;
                let head = self.state.logs[which_log].head;
                let head_addr = log_area_start + (head % log_area_len);
                let log = self.state.logs[which_log].log;
                0 <= pos < log.len() ==> log[pos] == s[relative_log_pos_to_addr(
                    pos,
                    head_addr,
                    log_area_start as int,
                    log_area_end as int,
                )]
            }
    }

    pub(super) open spec fn valid(self) -> bool {
        &&& self.parts_dont_overlap()
        &&& validate_version_metadata(self.vm)
        &&& validate_static_metadata(self.sm, self.vm)
        &&& self.sm.num_logs == self.all_log_constants.len() == self.all_log_dynamic_metadata.len()
            == self.state.logs.len()
        &&& self.constants_correspond()
        &&& self.state_corresponds_to_dynamic_metadata()
    }

    pub(super) open spec fn corresponds(self, s: Seq<u8>) -> bool {
        &&& self.valid()
        &&& self.all_log_constants.last().log_area_end <= s.len()
        &&& recover_version_metadata(s) == Some(self.vm)
        &&& recover_static_metadata(s, self.vm) == Some(self.sm)
        &&& recover_mask_cdb(s, self.sm) == Some(self.mask_cdb)
        &&& recover_mask_given_cdb(s, self.sm, self.mask_cdb) == Some(self.mask)
        &&& forall|i: int|
            0 <= i < self.sm.num_logs ==> recover_single_log_constants(s, i, self.sm) == Some(
                #[trigger] self.all_log_constants[i],
            )
        &&& forall|i: int|
            0 <= i < self.sm.num_logs ==> recover_single_log_dynamic_metadata_given_mask(
                s,
                i,
                self.sm,
                self.mask,
            ) == Some(#[trigger] self.all_log_dynamic_metadata[i])
        &&& self.storage_state_corresponds(s)
    }

    pub(super) proof fn lemma_uniqueness(self, other: Self, s: Seq<u8>)
        requires
            self.corresponds(s),
            other.corresponds(s),
        ensures
            self == other,
    {
        assert(self.all_log_constants =~= other.all_log_constants);
        assert(self.all_log_dynamic_metadata =~= other.all_log_dynamic_metadata);
        assert(self.c =~= other.c);
        assert(self.state =~= other.state) by {
            assert forall|i: int| 0 <= i < self.sm.num_logs implies self.state.logs[i]
                == other.state.logs[i] by {
                assert(self.all_log_constants[i] == other.all_log_constants[i]);
                assert(self.all_log_dynamic_metadata[i] == other.all_log_dynamic_metadata[i]);
                assert(self.state.logs[i] =~= other.state.logs[i]);
            }
        }
        assert(self =~= other);
    }

    pub(super) proof fn lemma_corresponds_implies_equals_new(self, s: Seq<u8>)
        requires
            self.corresponds(s),
        ensures
            Self::new(s) == Some(self),
    {
        self.lemma_uniqueness(Self::new(s).unwrap(), s);
    }
}

} // verus!
