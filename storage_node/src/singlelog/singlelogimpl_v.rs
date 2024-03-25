use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use crate::pmem::serializedpmemspec_t::*;
use crate::singlelog::layout_v::*;
use crate::singlelog::singlelogimpl_t::*;
use crate::singlelog::singlelogspec_t::*;

verus! {
    pub struct LogInfo {
        pub log_area_len: u64,
        pub head: u128,
        pub head_log_area_offset: u64,
        pub log_length: u64,
        pub log_plus_pending_length: u64,
    }

    pub struct UntrustedLogImpl<
        CDBRegion: SerializedPmRegion<u64>,
        SRegion: SerializedPmRegion<S>,
        HRegion: SerializedPmRegion<H>,
        DRegion: SerializedPmRegion<D>,
        S: Sized + Serializable + SuperBlock,
        H: Sized + Serializable + Headers,
        D: Sized + Serializable + LogContents,
        Perm: CheckPermission<LogMemState>,
    > {
        cdb: bool,
        info: LogInfo,
        superblock_region: WriteRestrictedSerializedPmRegion<Perm, SRegion, S, LogMemState>,
        cdb_region: WriteRestrictedSerializedPmRegion<Perm, CDBRegion, u64, LogMemState>,
        metadata_region: WriteRestrictedSerializedPmRegion<Perm, HRegion, H, LogMemState>,
        data_region: WriteRestrictedSerializedPmRegion<Perm, DRegion, D, LogMemState>,
        log_id: u128,
        state: Ghost<AbstractLogState>,
        _phantom: Ghost<Option<(H, D, S)>> // TODO: use PhantomData
    }

    impl<
        CDBRegion: SerializedPmRegion<u64>,
        SRegion: SerializedPmRegion<S>,
        HRegion: SerializedPmRegion<H>,
        DRegion: SerializedPmRegion<D>,
        S: Sized + Serializable + SuperBlock,
        H: Sized + Serializable + Headers,
        D: Sized + Serializable + LogContents,
        Perm: CheckPermission<LogMemState>,
    > UntrustedLogImpl<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm>
    {
        pub closed spec fn view(self) -> AbstractLogState
        {
            self.state@
        }

        pub closed spec fn inv(self) -> bool
        {
            // TODO: impl
            false
        }

        pub closed spec fn recover(cdb_mem: Seq<u8>, sb_mem: Seq<u8>, h_mem: Seq<u8>, d_mem: Seq<u8>) -> Option<AbstractLogState>
        {
            // 0. parse superblock
            let super_block = S::parse_sb(sb_mem);
            // 1. parse CDB and determine if it is a legal value
            let cdb = parse_cdb(cdb_mem);
            if cdb != CDB_TRUE && cdb != CDB_FALSE {
                None
            } else {
                // 2. obtain header based on CDB
                let header = H::parse_header_with_cdb(cdb, h_mem);
                match header {
                    Some(header) => {
                        // 3. obtain logical head and tail from header and translate it
                        // into physical head and tail in d_mem
                        let logical_head = H::get_logical_log_head(header);
                        let logical_tail = H::get_logical_log_tail(header);
                        let physical_log_size = super_block.get_log_size();

                        let physical_head = logical_head % physical_log_size;
                        let physical_tail = logical_tail % physical_log_size;

                        // obtain the live bytes in the log's data region
                        let log_contents = if physical_head <= physical_tail {
                            // log does not wrap
                            d_mem.subrange(physical_head as int, physical_tail as int)
                        } else {
                            // log wraps
                            d_mem.subrange(physical_tail as int, physical_log_size as int) + d_mem.subrange(0, physical_head as int)
                        };
                        Some(AbstractLogState {
                            head: logical_head as int,
                            log: log_contents,
                            // pending: Seq::<u8>::empty(),
                            capacity: physical_log_size as int
                        })
                    }
                    None => None
                }
            }
        }

        // pub closed spec fn recover_to_intermediate_state(
        //     cdb_mem: Seq<u8>,
        //     sb_mem: Seq<u8>,
        //     h_mem: Seq<u8>,
        //     d_mem: Seq<u8>
        // ) -> Option<IntermediateAbstractLogState>
        // {
        //     // 0. parse superblock
        //     let super_block = S::parse_sb(sb_mem);
        //     // 1. parse CDB and determine if it is a legal value
        //     let cdb = parse_cdb(cdb_mem);
        //     if cdb != CDB_TRUE && cdb != CDB_FALSE {
        //         None
        //     } else {
        //         // 2. obtain header based on CDB
        //         let header = H::parse_header_with_cdb(cdb, h_mem);
        //         match header {
        //             Some(header) => {
        //                 // 3. obtain logical head and tail from header and translate it
        //                 // into physical head and tail in d_mem
        //                 let logical_head = H::get_logical_log_head(header);
        //                 let logical_tail = H::get_logical_log_tail(header);
        //                 let physical_log_size = super_block.get_log_size();

        //                 let physical_head = logical_head % physical_log_size;
        //                 let physical_tail = logical_tail % physical_log_size;

        //                 // obtain the live bytes in the log's data region
        //                 let log_contents = if physical_head <= physical_tail {
        //                     // log does not wrap
        //                     d_mem.subrange(physical_head as int, physical_tail as int)
        //                 } else {
        //                     // log wraps
        //                     d_mem.subrange(physical_tail as int, physical_log_size as int) + d_mem.subrange(0, physical_head as int)
        //                 };
        //                 Some(IntermediateAbstractLogState {
        //                     capacity: physical_log_size as int,
        //                     cdb,
        //                     header: AbstractHeader {
        //                         logical_head: logical_head as int,
        //                         logical_tail: logical_tail as int,
        //                     },
        //                     log_contents: AbstractLogContents {
        //                         bytes: log_contents,
        //                         pending: Seq::empty(),
        //                     }
        //                 })
        //             }
        //             None => None
        //         }
        //     }
        // }

        pub exec fn setup(
            cdb_region: &mut CDBRegion,
            sb_region: &mut SRegion,
            h_region: &mut HRegion,
            d_region: &mut DRegion,
            log_id: u128
        ) -> (result: Result<(), LogErr>)
            where
                CDBRegion: SerializedPmRegion<u64>,
                SRegion: SerializedPmRegion<S>,
                HRegion: SerializedPmRegion<H>,
                DRegion: SerializedPmRegion<D>,
                S: Sized + Serializable + SuperBlock,
                H: Sized + Serializable + Headers,
                D: Sized + Serializable + LogContents,
            requires
                old(cdb_region).inv(),
                old(sb_region).inv(),
                old(h_region).inv(),
                old(d_region).inv(),

                // size requirements
                old(cdb_region)@.len() >= u64::spec_serialized_len()
            ensures
                cdb_region.inv(),
                sb_region.inv(),
                h_region.inv(),
                d_region.inv(),

                cdb_region@.no_outstanding_writes(),
                sb_region@.no_outstanding_writes(),
                h_region@.no_outstanding_writes(),
                d_region@.no_outstanding_writes(),

                match result {
                    Ok(()) => {
                        let state = AbstractLogState::initialize(d_region@.len() as int);
                        &&& Self::recover(
                                cdb_region@.view_as_pm_region_view().committed(),
                                sb_region@.view_as_pm_region_view().committed(),
                                h_region@.view_as_pm_region_view().committed(),
                                d_region@.view_as_pm_region_view().committed()
                            ) == Some(state)
                        &&& Self::recover(
                                cdb_region@.view_as_pm_region_view().flush().committed(),
                                sb_region@.view_as_pm_region_view().flush().committed(),
                                h_region@.view_as_pm_region_view().flush().committed(),
                                d_region@.view_as_pm_region_view().flush().committed()
                            ) == Some(state)
                        &&& can_only_crash_as_state::<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm>(
                                cdb_region@,
                                sb_region@,
                                h_region@,
                                d_region@,
                                state
                            )
                    }
                    Err(_) => true // TODO
                }


        {
            assume(false);
            Ok(())
        }

        // TODO: start

        pub exec fn append(&mut self, new_entries: &[S], Tracked(perm): Tracked<&TrustedPermission<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm>>) -> (result: Result<u128, LogErr>)
            requires
                old(self).inv(),
            ensures
                self.inv(),
                match result {
                    Ok(offset) => {
                        let old_state = old(self)@;
                        let new_state = self@;
                        &&& offset == old_state.head + old_state.log.len() + new_entries@.len()
                    }
                    Err(_) => true // TODO
                }
        {
            Err(LogErr::NotImplemented)
        }

    }
}
