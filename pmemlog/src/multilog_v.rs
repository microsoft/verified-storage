use crate::infinitelog_t::*;
use crate::main_t::can_only_crash_as_state;
use crate::multilog_t;
use crate::math::*;
use crate::pmemspec_t::*;
use crate::logimpl_v;
use crate::sccf::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::set::*;
use vstd::slice::*;

verus! {

    pub const incorruptible_bool_pos: u64 = 0;
    pub const const_crc_offset: u64 = 8;
    pub const header_log_num_offset: u64 = 16; 
    pub const header_prefix_size: u64 = 8 * 3; // 3 u64s - IB, const crc, number of logs

    // offset of CRC and # of logs within each header
    // each of these values is stored once. # logs is checked
    // by the CRC
    pub const multilog_header_crc_offset: u64 = 0;
    pub const multilog_header_metadata_offset: u64 = 8;

    pub const header1_offset: u64 = header_prefix_size;
    // header1 size is not known at compile time so we can't have a constant
    // offset for header2

    // offset of per-log metadata within per-log structures
    pub const multilog_header_head_offset: u64 = 0;
    pub const multilog_header_tail_offset: u64 = 8;
    pub const multilog_header_log_size_offset: u64 = 16;

    // does not include crc or log num
    pub const multilog_header_size: u64 = 24;

    // TODO: use something more secure (CRC or SHA hash of 0 and 1) 
    pub const header1_val: u64 = 0;
    pub const header2_val: u64 = 1;

    pub const crc_size: u64 = 8;

    pub enum InfiniteMultiLogErr {
        None,
        InsufficientSpaceForSetup { pm_index: usize, required_space: u64 },
        InsufficientSpaceForAppend { pm_index: usize, available_space: u64 },
        CRCMismatch,
        CantReadBeforeHead { head: u64 },
        CantReadPastTail { tail: u64 },
        CantAdvanceHeadPositionBeforeHead { pm_index: usize, head: u64 },
        CantAdvanceHeadPositionBeyondTail { pm_index: usize, tail: u64 },
        InvalidIndex { pm_index: usize },
        InvalidLength { index: usize, log_num: usize }
    }

    pub struct MultiLogHeaderView {
        pub const_crc_bytes: Seq<u8>,
        pub log_num_bytes: Seq<u8>,
        pub header1: MultiLogPersistentHeader,
        pub header2: MultiLogPersistentHeader,
    }

    pub open spec fn spec_header_version_size(log_num: int) -> int 
    {
        crc_size + (multilog_header_size * log_num)
    }
    
    #[verifier::ext_equal]
    pub struct MultiLogAbstractInfiniteLogState {
        pub states: Seq<AbstractInfiniteLogState>
    }

    #[verifier::ext_equal]
    impl MultiLogAbstractInfiniteLogState {
        pub open spec fn len(self) -> nat {
            self.states.len()
        }

        pub open spec fn spec_index(self, i: int) -> AbstractInfiniteLogState {
            self.states[i]
        }

        pub open spec fn initialize(capacities: Seq<u64>) -> Self {
            Self {
                states: Seq::<AbstractInfiniteLogState>::new(capacities.len(),
                    |i| AbstractInfiniteLogState::initialize(capacities[i] as int))
            }
        }

        pub open spec fn append(self, index: int, bytes_to_append: Seq<u8>) -> Self {
            Self {
                states: Seq::<AbstractInfiniteLogState>::new(self.states.len(), 
                    |i| if i == index {
                        self.states[i].append(bytes_to_append)
                    } else {
                        self.states[i]
                    }
                )
            }
        }

        pub open spec fn advance_head(self, index: int, new_head: int) -> Self {
            Self {
                states: Seq::<AbstractInfiniteLogState>::new(self.states.len(),
                    |i| if index == i {
                        self.states[i].advance_head(new_head)
                    } else {
                        self.states[i]
                    }
                )
            }
        }
    }

    #[verifier::ext_equal]
    pub struct MultiLogPersistentHeader {
        pub crc: u64,
        pub metadata: Seq<logimpl_v::PersistentHeaderMetadata>,
    }

    pub proof fn lemma_if_no_outstanding_writes_then_can_only_crash_as_committed(multilog: MultiLogPersistentMemoryView)
        requires 
            multilog.no_outstanding_writes()
        ensures 
            forall |crash_pm| multilog.can_crash_as(crash_pm) ==> crash_pm == multilog.committed()
    {
        assert forall |crash_pm| multilog.can_crash_as(crash_pm) implies crash_pm == multilog.committed() by {
            lemma_effect_of_crash(multilog, crash_pm);
            assert(multilog.len() == crash_pm.len());
            assert(forall |i| 0 <= i < multilog.len() ==> {
                &&& multilog.committed()[i].len() == crash_pm[i].len()
                &&& #[trigger] crash_pm[i] =~= multilog.committed()[i]
            });
            assert(crash_pm =~= multilog.committed());
        }
    }

    pub proof fn lemma_can_crash_as_committed_and_all_flushed(multilog: MultiLogPersistentMemoryView)
        ensures
            multilog.can_crash_as(multilog.committed()),
            multilog.can_crash_as(multilog.flush_committed())
    {}

    pub proof fn lemma_ib_unchanged(old_multilog: MultiLogPersistentMemoryView, new_multilog: MultiLogPersistentMemoryView)
        requires 
            old_multilog.committed()[0].subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8) == 
                new_multilog.committed()[0].subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8),
        ensures 
            ({
                let (old_ib, _) = multilog_to_views(old_multilog.committed()[0]);
                let (new_ib, _) = multilog_to_views(new_multilog.committed()[0]);
                old_ib == new_ib
            })
    {}

    pub proof fn lemma_const_crc_unchanged(old_multilog: MultiLogPersistentMemoryView, new_multilog: MultiLogPersistentMemoryView)
        requires 
            old_multilog.committed()[0].subrange(const_crc_offset as int, const_crc_offset + crc_size) == 
                new_multilog.committed()[0].subrange(const_crc_offset as int, const_crc_offset + crc_size)
        ensures 
            ({
                let (_, old_headers) = multilog_to_views(old_multilog.committed()[0]);
                let (_, new_headers) = multilog_to_views(new_multilog.committed()[0]);
                old_headers.const_crc_bytes =~= new_headers.const_crc_bytes
            })
    {}

    pub proof fn lemma_same_header(header_bytes1: Seq<u8>, header_bytes2: Seq<u8>, log_num: int)
        requires 
            header_bytes1 == header_bytes2,
            header_bytes1.len() == spec_header_version_size(log_num)
        ensures 
            spec_convert_to_header(header_bytes1, log_num) =~= spec_convert_to_header(header_bytes2, log_num),
    {}

    pub open spec fn spec_convert_to_header(bytes: Seq<u8>, log_num: int) -> MultiLogPersistentHeader
        recommends 
            bytes.len() == spec_header_version_size(log_num as int),
    {
        spec_bytes_to_header(
            bytes.subrange(multilog_header_crc_offset as int, multilog_header_crc_offset + crc_size),
            bytes.subrange(multilog_header_metadata_offset as int, multilog_header_metadata_offset + spec_header_version_size(log_num as int)),
            log_num
        )
    }

    pub open spec fn spec_bytes_to_header(crc_bytes: Seq<u8>, metadata_bytes: Seq<u8>, log_num: int) -> MultiLogPersistentHeader
        recommends 
            log_num >= 0
    {
        let header_crc = spec_u64_from_le_bytes(crc_bytes);
        let header_metadata = Seq::<logimpl_v::PersistentHeaderMetadata>::new(log_num as nat,
            |i: int| spec_bytes_to_metadata(metadata_bytes.subrange(i * multilog_header_size, i * multilog_header_size + multilog_header_size)));
        MultiLogPersistentHeader { crc: header_crc, metadata: header_metadata }
    }

    pub proof fn lemma_header_bytes_match(header_region: Seq<u8>, headers: MultiLogHeaderView)
        requires 
            ({
                let (_, h) = multilog_to_views(header_region);
                headers =~= h
            }),
        ensures 
            ({
                let (_, h) = multilog_to_views(header_region);
                let log_num = spec_u64_from_le_bytes(h.log_num_bytes);
                spec_convert_to_header(
                    header_region.subrange(header1_offset as int, header1_offset + spec_header_version_size(log_num as int)), 
                    log_num as int
                ) =~= headers.header1    
            })
    {}

    /// This function takes the header region and produces a view of the multilog's metadata
    pub open spec fn multilog_to_views(header_region: Seq<u8>) -> (u64, MultiLogHeaderView)
    {
        let incorruptible_bool = spec_u64_from_le_bytes(header_region.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8));
        let const_crc_bytes = header_region.subrange(const_crc_offset as int, const_crc_offset + crc_size);
        let log_num_bytes = header_region.subrange(header_log_num_offset as int, header_log_num_offset + 8);
        let log_num = spec_u64_from_le_bytes(log_num_bytes);

        let header1 = spec_convert_to_header(
            header_region.subrange(header1_offset as int, header1_offset + spec_header_version_size(log_num as int)), 
            log_num as int
        );

        let header2_offset = header1_offset + spec_header_version_size(log_num as int);
        let header2 = spec_convert_to_header(
            header_region.subrange(header2_offset as int, header2_offset + spec_header_version_size(log_num as int)), 
            log_num as int
        );

        (
            incorruptible_bool,
            MultiLogHeaderView {
                const_crc_bytes,
                log_num_bytes,
                header1,
                header2,
            }
        )
    }

    pub proof fn lemma_same_live_header_view(old_multilog: Seq<Seq<u8>>, new_multilog: Seq<Seq<u8>>, header2_offset: int)
        requires 
            old_multilog.len() == new_multilog.len(),
            ({
                let (old_ib, old_headers) = multilog_to_views(old_multilog[0]);
                let (new_ib, new_headers) = multilog_to_views(new_multilog[0]);
                let old_log_num = spec_u64_from_le_bytes(old_headers.log_num_bytes);
                let new_log_num = spec_u64_from_le_bytes(new_headers.log_num_bytes);
                &&& old_ib == header1_val || old_ib == header2_val
                &&& old_ib == new_ib
                &&& old_log_num == new_log_num
                &&& old_ib == header1_val ==> {
                    old_headers.header1 == new_headers.header1
                }
                &&& old_ib == header2_val ==> {
                    old_headers.header2 == new_headers.header2
                }
            })
        ensures 
            ({
                let old_live_header = spec_get_live_header(old_multilog);
                let new_live_header = spec_get_live_header(new_multilog);
                old_live_header == new_live_header
            })
    {
        let (old_ib, old_headers) = multilog_to_views(old_multilog[0]);
        let (new_ib, new_headers) = multilog_to_views(new_multilog[0]);
        let old_live_header = spec_get_live_header(old_multilog);
        let new_live_header = spec_get_live_header(new_multilog);
        if old_ib == header1_val {
            assert(old_live_header =~= old_headers.header1);
            assert(new_live_header =~= new_headers.header1);
            assert(old_live_header == new_live_header);
        } else {
            assert(old_ib == header2_val);
            assert(old_live_header =~= old_headers.header2);
            assert(new_live_header =~= new_headers.header2);
            assert(old_live_header == new_live_header);
        }
    }

    pub proof fn lemma_view_abstract_state_head(multilog: Seq<Seq<u8>>)
        requires 
            UntrustedMultiLogImpl::convert_multilog_to_log_state(multilog).is_Some()
        ensures 
            ({
                let live_header = spec_get_live_header(multilog);
                let state = UntrustedMultiLogImpl::convert_multilog_to_log_state(multilog).unwrap();
                forall |i: int| #![auto] 0 <= i < live_header.metadata.len() ==> live_header.metadata[i].head == state[i].head
            })
    {}

    pub proof fn lemma_log_num_metadata_len(multilog: MultiLogPersistentMemoryView)
        requires 
            UntrustedMultiLogImpl::convert_multilog_to_log_state(multilog.committed()).is_Some(),
        ensures 
            ({
                let (_, headers) = multilog_to_views(multilog.committed()[0]);
                let live_header = spec_get_live_header(multilog.committed());
                spec_u64_from_le_bytes(headers.log_num_bytes) == live_header.metadata.len()
            })
    {
        let (_, headers) = multilog_to_views(multilog.committed()[0]);
        let live_header = spec_get_live_header(multilog.committed());
        let log_num = spec_u64_from_le_bytes(headers.log_num_bytes);
        assert(UntrustedMultiLogImpl::multilog_state_is_valid(multilog.committed()));
        assert(log_num == multilog.len() - 1);
        assert(multilog.len() - 1 == live_header.metadata.len());
    }

    pub proof fn lemma_states_equal(old_state: MultiLogAbstractInfiniteLogState, new_state: MultiLogAbstractInfiniteLogState)
        requires 
            old_state.len() == new_state.len(),
            forall |i: int| #![auto] 0 <= i < old_state.len() ==> old_state.states[i] == new_state.states[i],
        ensures 
            old_state =~= new_state 
    {}

    pub proof fn lemma_header_crc_correct(header_bytes: Seq<u8>, crc_bytes: Seq<u8>, metadata_bytes: Seq<u8>, log_num: int) 
        requires
            crc_bytes.len() == crc_size,
            crc_bytes =~= logimpl_v::spec_crc_bytes(metadata_bytes),
            header_bytes =~= crc_bytes + metadata_bytes,
            header_bytes.len() == spec_header_version_size(log_num),
            header_bytes.subrange(multilog_header_crc_offset as int, multilog_header_crc_offset + crc_size) =~= crc_bytes,
            header_bytes.subrange(multilog_header_metadata_offset as int, spec_header_version_size(log_num) as int) =~= metadata_bytes,
        ensures 
            header_bytes.subrange(multilog_header_crc_offset as int, multilog_header_crc_offset + crc_size) =~=
                logimpl_v::spec_crc_bytes(header_bytes.subrange(multilog_header_metadata_offset as int, spec_header_version_size(log_num) as int))
    {}

    pub open spec fn spec_addr_logical_to_physical(addr: int, log_size: int) -> int {
        addr % log_size
    }

    pub open spec fn spec_get_live_header(pm: Seq<Seq<u8>>) -> MultiLogPersistentHeader 
    {
        let (ib, headers) = multilog_to_views(pm[0]);
        if ib == header1_val {
            headers.header1
        } else {
            headers.header2
        }
    }

    pub open spec fn permissions_depend_only_on_recovery_view<P: CheckPermission<Seq<Seq<u8>>>>(perm: &P) -> bool
    {
        forall |s1: Seq<Seq<u8>>, s2: Seq<Seq<u8>>| multilog_t::recovery_view()(s1) == multilog_t::recovery_view()(s2) ==> perm.check_permission(s1) == perm.check_permission(s2)
    }

    pub proof fn lemma_same_permissions<P: CheckPermission<Seq<Seq<u8>>>>(pm1: Seq<Seq<u8>>, pm2: Seq<Seq<u8>>, perm: &P)
        requires 
            multilog_t::recovery_view()(pm1) =~= multilog_t::recovery_view()(pm2),
            perm.check_permission(pm1),
            permissions_depend_only_on_recovery_view(perm)
        ensures 
            perm.check_permission(pm2)
    {}  

    pub open spec fn spec_constants_unchanged(old_multilog: MultiLogPersistentMemory, new_multilog: MultiLogPersistentMemory) -> bool 
    {
        let (old_ib, old_headers) = multilog_to_views(old_multilog@.committed()[0]);
        let (new_ib, new_headers) = multilog_to_views(new_multilog@.committed()[0]);
        &&& old_ib == new_ib 
        &&& old_headers == new_headers
    }

    pub open spec fn spec_bytes_to_metadata(header_seq: Seq<u8>) -> logimpl_v::PersistentHeaderMetadata 
        recommends 
            header_seq.len() == multilog_header_size
    {
        let head = spec_u64_from_le_bytes(header_seq.subrange(multilog_header_head_offset as int, multilog_header_head_offset + 8));
        let tail = spec_u64_from_le_bytes(header_seq.subrange(multilog_header_tail_offset as int, multilog_header_tail_offset + 8));
        let log_size = spec_u64_from_le_bytes(header_seq.subrange(multilog_header_log_size_offset as int, multilog_header_log_size_offset + 8));
        logimpl_v::PersistentHeaderMetadata {
            head,
            tail,
            log_size
        }
    }

    exec fn metadata_to_bytes(metadata: &logimpl_v::PersistentHeaderMetadata) -> (out: Vec<u8>)
        ensures 
            metadata == spec_bytes_to_metadata(out@),
            out@.len() == multilog_header_size,
    {
        let mut bytes: Vec<u8> = Vec::new();
        let ghost old_bytes = bytes@;

        let mut head_bytes = u64_to_le_bytes(metadata.head);
        let ghost old_head_bytes = head_bytes@;
        let mut tail_bytes = u64_to_le_bytes(metadata.tail);
        let ghost old_tail_bytes = tail_bytes@;
        let mut log_size_bytes = u64_to_le_bytes(metadata.log_size);
        let ghost old_log_size_bytes = log_size_bytes@;

        bytes.append(&mut head_bytes);
        bytes.append(&mut tail_bytes);
        bytes.append(&mut log_size_bytes);

        proof {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(old_bytes == Seq::<u8>::empty());
            assert(old_head_bytes =~= bytes@.subrange(multilog_header_head_offset as int, multilog_header_head_offset + 8));
            assert(old_tail_bytes =~= bytes@.subrange(multilog_header_tail_offset as int, multilog_header_tail_offset + 8));
            assert(old_log_size_bytes =~= bytes@.subrange(multilog_header_log_size_offset as int, multilog_header_log_size_offset + 8));
        }
        bytes
    }

    pub proof fn lemma_effect_of_crash(multilog: MultiLogPersistentMemoryView, crash_pm: Seq<Seq<u8>>)
        requires
            multilog.can_crash_as(crash_pm)
        ensures
            crash_pm.len() == multilog.len(),
            forall |i, j| 0 <= i < multilog.len() && 0 <= j < multilog[i].len() ==> {
                ||| #[trigger] crash_pm[i][j] == multilog.committed()[i][j]
                ||| crash_pm[i][j] == multilog.flush().committed()[i][j]
            }
    {
        assert forall |i, j| 0 <= i < multilog.len() && 0 <= j < multilog[i].len() implies {
            ||| #[trigger] crash_pm[i][j] == multilog.committed()[i][j]
            ||| crash_pm[i][j] == multilog.flush().committed()[i][j]
        } by {
            logimpl_v::lemma_effect_of_crash(multilog[i], crash_pm[i]);
        }
    }

    pub struct UntrustedMultiLogImpl {
        pub incorruptible_bool: u64,
        pub log_num: u64,
        pub header2_offset: u64,
        pub header_crc: u64,
        pub log_metadata: Vec<logimpl_v::PersistentHeaderMetadata>,
    }

    impl UntrustedMultiLogImpl {   

        pub proof fn lemma_inactive_header_update_view(&self, old_multilog: MultiLogPersistentMemoryView, bytes: Seq<u8>, header_pos: int, 
                                                        abstract_state: MultiLogAbstractInfiniteLogState, crash_pm: Seq<Seq<u8>>)
            requires
                old_multilog.no_outstanding_writes(),
                UntrustedMultiLogImpl::convert_multilog_to_log_state(old_multilog.flush_committed()) == Some(abstract_state),
                self.consistent_with_multilog(old_multilog),
                header_pos == header1_offset || header_pos == self.header2_offset,
                ({
                    // the new bytes must be written to the inactive header
                    let (old_ib, old_headers) = multilog_to_views(old_multilog.flush_committed()[0]);
                    let log_num = spec_u64_from_le_bytes(old_headers.log_num_bytes);
                    &&& old_ib == header1_val ==> header_pos == self.header2_offset 
                    &&& old_ib == header2_val ==> header_pos == header1_offset
                    &&& bytes.len() == spec_header_version_size(log_num as int)
                }),
                old_multilog.write(0, header_pos, bytes).can_crash_as(crash_pm),
                crash_pm.len() == old_multilog.len(),
                forall |i: int| #![auto] 0 <= i < crash_pm.len() ==> crash_pm[i].len() == old_multilog[i].len(),
            ensures 
                ({
                    let (old_ib, old_headers) = multilog_to_views(old_multilog.flush_committed()[0]);
                    let (new_ib, new_headers) = multilog_to_views(crash_pm[0]);
                    &&& old_ib == new_ib 
                    &&& old_headers.log_num_bytes =~= new_headers.log_num_bytes 
                    &&& old_headers.const_crc_bytes =~= new_headers.const_crc_bytes
                    &&& header_pos == header1_offset ==> 
                        old_headers.header2 == new_headers.header2
                    &&& header_pos == self.header2_offset ==>
                        old_headers.header1 == new_headers.header1 
                    &&& UntrustedMultiLogImpl::convert_multilog_to_log_state(crash_pm) == Some(abstract_state)
                })
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            let (old_ib, old_headers) = multilog_to_views(old_multilog.flush_committed()[0]);
            let (new_ib, new_headers) = multilog_to_views(crash_pm[0]);
            let log_num = spec_u64_from_le_bytes(old_headers.log_num_bytes);

            lemma_effect_of_crash(old_multilog.write(0, header_pos, bytes), crash_pm);
            assert(old_multilog.flush_committed()[0].subrange(0, header_prefix_size as int) =~= crash_pm[0].subrange(0, header_prefix_size as int));
            logimpl_v::lemma_subrange_equality_implies_subsubrange_equality(
                old_multilog.flush_committed()[0],
                crash_pm[0], 
                0,
                header_prefix_size as int
            );
            if header_pos == header1_offset {
                assert(old_multilog.flush_committed()[0].subrange(self.header2_offset as int, self.header2_offset + spec_header_version_size(log_num as int)) =~= 
                    crash_pm[0].subrange(self.header2_offset as int, self.header2_offset + spec_header_version_size(log_num as int)));
                logimpl_v::lemma_subrange_equality_implies_subsubrange_equality(
                    old_multilog.flush_committed()[0],
                    crash_pm[0], 
                    self.header2_offset as int,
                    self.header2_offset + spec_header_version_size(log_num as int)
                );
                assert(old_headers.header2 =~= new_headers.header2);
            } else {
                assert(old_multilog.flush_committed()[0].subrange(header1_offset as int, header1_offset + spec_header_version_size(log_num as int)) =~= 
                    crash_pm[0].subrange(header1_offset as int, header1_offset + spec_header_version_size(log_num as int)));
                logimpl_v::lemma_subrange_equality_implies_subsubrange_equality(
                    old_multilog.flush_committed()[0],
                    crash_pm[0], 
                    header1_offset as int,
                    header1_offset + spec_header_version_size(log_num as int)
                );
                assert(old_headers.header1 =~= new_headers.header1);
            }

            let crash_state = UntrustedMultiLogImpl::convert_multilog_to_log_state(crash_pm).unwrap();
            lemma_same_live_header_view(old_multilog.flush_committed(), crash_pm, self.header2_offset as int);
            lemma_view_abstract_state_head(crash_pm);
            Self::lemma_same_visible_state(old_multilog.flush_committed(), crash_pm);
        }

        pub proof fn lemma_log_view_unchanged(&self, old_multilog: MultiLogPersistentMemoryView, index: int, addr: int, bytes: Seq<u8>) 
            requires 
                index >= 0,
                0 <= addr < old_multilog[index].len(),
                old_multilog.no_outstanding_writes_in_range(index, addr, addr + bytes.len()),
                ({
                    let (old_ib, old_headers) = multilog_to_views(old_multilog.flush_committed()[0]);
                    let log_num = spec_u64_from_le_bytes(old_headers.log_num_bytes);
                    ||| index != 0 
                    ||| ({  &&& index == 0 
                            &&& old_multilog.flush_committed()[0].len() >= Self::minimum_header_region_size(log_num as int) 
                            &&& self.header2_offset < self.header2_offset + spec_header_version_size(log_num as int) <= old_multilog[index].len()
                            &&& old_ib == header1_val || old_ib == header2_val
                            &&& old_ib == header1_val ==> {
                                    self.header2_offset <= addr < addr + bytes.len() <= old_multilog.flush_committed()[0].len()
                                }
                            &&& old_ib == header2_val ==> {
                                ||| self.header2_offset < self.header2_offset + spec_header_version_size(log_num as int) < addr
                                ||| header_prefix_size <= addr < addr + bytes.len() <= self.header2_offset < self.header2_offset + spec_header_version_size(log_num as int)
                            }      
                            &&& old_multilog.no_outstanding_writes_in_range(index as int, incorruptible_bool_pos as int, header_prefix_size as int)  
                    })
                }),
                UntrustedMultiLogImpl::convert_multilog_to_log_state(old_multilog.flush_committed()).is_Some(),
                self.consistent_with_multilog(old_multilog),
            ensures 
                ({
                    let new_multilog = old_multilog.write(index, addr, bytes).flush();
                    UntrustedMultiLogImpl::convert_multilog_to_log_state(old_multilog.flush_committed()) =~= UntrustedMultiLogImpl::convert_multilog_to_log_state(new_multilog.flush_committed())
                })
        {   
            if index != 0 {
                assume(false); // TODO
            } else {
                assert(index == 0);
                let new_multilog = old_multilog.write(index, addr, bytes).flush();

                let (old_ib, old_headers) = multilog_to_views(old_multilog.flush_committed()[index]);
                let (new_ib, new_headers) = multilog_to_views(new_multilog.flush_committed()[index]);
                let old_live_header = spec_get_live_header(old_multilog.flush_committed());
                let new_live_header = spec_get_live_header(new_multilog.flush_committed());
                let old_state = UntrustedMultiLogImpl::convert_multilog_to_log_state(old_multilog.flush_committed()).unwrap();
                let new_state = UntrustedMultiLogImpl::convert_multilog_to_log_state(new_multilog.flush_committed()).unwrap();
                let log_num = spec_u64_from_le_bytes(old_headers.log_num_bytes);

                lemma_auto_spec_u64_to_from_le_bytes();
                assert(old_multilog.flush_committed()[0].subrange(0, header_prefix_size as int) =~= new_multilog.flush_committed()[0].subrange(0, header_prefix_size as int));
                logimpl_v::lemma_subrange_equality_implies_subsubrange_equality(
                    old_multilog.flush_committed()[0],
                    new_multilog.flush_committed()[0], 
                    0,
                    header_prefix_size as int
                );
                
                // the bytes associated with the header version we didn't change are the same
                if old_ib == header1_val {
                    assert(old_multilog.flush_committed()[0].subrange(header1_offset as int, header1_offset + spec_header_version_size(log_num as int)) =~= 
                        new_multilog.flush_committed()[0].subrange(header1_offset as int, header1_offset + spec_header_version_size(log_num as int)));
                    logimpl_v::lemma_subrange_equality_implies_subsubrange_equality(
                        old_multilog.flush_committed()[0],
                        new_multilog.flush_committed()[0], 
                        header1_offset as int,
                        header1_offset + spec_header_version_size(log_num as int)
                    );
                } else if old_ib == header2_val {
                    assert(old_multilog.flush_committed()[0].subrange(self.header2_offset as int, self.header2_offset + spec_header_version_size(log_num as int)) =~= 
                        new_multilog.flush_committed()[0].subrange(self.header2_offset as int, self.header2_offset + spec_header_version_size(log_num as int)));
                    logimpl_v::lemma_subrange_equality_implies_subsubrange_equality(
                        old_multilog.flush_committed()[0],
                        new_multilog.flush_committed()[0], 
                        self.header2_offset as int,
                        self.header2_offset + spec_header_version_size(log_num as int)
                    );
                } else {
                    assert(false);
                }

                lemma_same_live_header_view(old_multilog.flush_committed(), new_multilog.flush_committed(), self.header2_offset as int);
                lemma_view_abstract_state_head(new_multilog.flush_committed());    
                Self::lemma_same_visible_state(old_multilog.flush_committed(), new_multilog.flush_committed());            
                assert(old_state =~= new_state);
            }
        }

        pub proof fn lemma_same_visible_state(old_multilog: Seq<Seq<u8>>, new_multilog: Seq<Seq<u8>>)
            requires 
                ({
                    let (old_ib, old_headers) = multilog_to_views(old_multilog[0]);
                    let (new_ib, new_headers) = multilog_to_views(new_multilog[0]);
                    &&& old_ib == new_ib 
                    &&& old_headers.log_num_bytes =~= new_headers.log_num_bytes 
                    &&& old_headers.const_crc_bytes =~= new_headers.const_crc_bytes 
                    &&& old_ib == header1_val ==> old_headers.header1 =~= new_headers.header1
                    &&& old_ib == header2_val ==> old_headers.header2 =~= new_headers.header2
                    &&& forall |i: int| #![auto] 0 <= i < old_multilog.len() - 1 ==>
                            Self::spec_get_live_bytes(i, old_multilog) =~= Self::spec_get_live_bytes(i, new_multilog)
                }),
                UntrustedMultiLogImpl::convert_multilog_to_log_state(old_multilog).is_Some(),
                UntrustedMultiLogImpl::convert_multilog_to_log_state(new_multilog).is_Some()
            ensures 
                UntrustedMultiLogImpl::convert_multilog_to_log_state(old_multilog) =~= 
                    UntrustedMultiLogImpl::convert_multilog_to_log_state(new_multilog)
        {
            let old_state = UntrustedMultiLogImpl::convert_multilog_to_log_state(old_multilog).unwrap();
            let new_state = UntrustedMultiLogImpl::convert_multilog_to_log_state(new_multilog).unwrap();
            lemma_states_equal(old_state, new_state);
        }

        pub proof fn lemma_header_updated(
            self,
            old_multilog: MultiLogPersistentMemoryView, 
            new_multilog: MultiLogPersistentMemoryView,
            header_pos: int,
            new_header_bytes: Seq<u8>
        )
            requires 
                self.consistent_with_multilog(old_multilog),
                UntrustedMultiLogImpl::convert_multilog_to_log_state(old_multilog.flush_committed()).is_Some(),
                ({
                    let (old_ib, headers) = multilog_to_views(old_multilog.flush_committed()[0]);
                    let log_num = spec_u64_from_le_bytes(headers.log_num_bytes);
                    &&& new_header_bytes.len() == spec_header_version_size(log_num as int)
                    &&& old_ib == header1_val || old_ib == header2_val
                    &&& old_ib == header1_val ==> header_pos == self.header2_offset 
                    &&& old_ib == header2_val ==> header_pos == header1_offset
                }),
                new_header_bytes.subrange(multilog_header_crc_offset as int, multilog_header_crc_offset + crc_size) =~=
                    logimpl_v::spec_crc_bytes(new_header_bytes.subrange(multilog_header_crc_offset + crc_size, new_header_bytes.len() as int)),
                header_pos == header1_offset || header_pos == self.header2_offset,
                new_multilog == old_multilog.write(0, header_pos, new_header_bytes).flush()
            ensures 
                self.consistent_with_multilog(new_multilog),
                // new_multilog.impervious_to_corruption() == old_multilog.impervious_to_corruption(),
                match (UntrustedMultiLogImpl::convert_multilog_to_log_state(new_multilog.flush_committed()),
                        UntrustedMultiLogImpl::convert_multilog_to_log_state(old_multilog.flush_committed())) {
                            (Some(old_log_state), Some(new_log_state)) => old_log_state =~= new_log_state,
                            _ => false
                        },
                ({
                    let (new_ib, new_headers) = multilog_to_views(new_multilog.flush_committed()[0]);
                    let (old_ib, old_headers) = multilog_to_views(old_multilog.flush_committed()[0]);
                    let new_header = spec_convert_to_header(new_header_bytes, spec_u64_from_le_bytes(old_headers.log_num_bytes) as int);
                    &&& old_ib == new_ib 
                    &&& old_headers.const_crc_bytes =~= new_headers.const_crc_bytes 
                    &&& old_headers.log_num_bytes =~= new_headers.log_num_bytes
                    &&& old_ib == header1_val ==> {
                        // current header is header1, so we update header2
                        &&& old_headers.header1 == new_headers.header1
                        &&& new_headers.header2 == new_header
                    }
                    &&& old_ib == header2_val ==> {
                        // current header is header2, so we update header1
                        &&& new_headers.header1 == new_header
                        &&& old_headers.header2 == new_headers.header2
                    }
                })
        {
            lemma_auto_spec_u64_to_from_le_bytes();                
            let (old_ib, old_headers) = multilog_to_views(old_multilog.flush_committed()[0]);
            let (new_ib, new_headers) = multilog_to_views(new_multilog.flush_committed()[0]);
            let log_num = spec_u64_from_le_bytes(old_headers.log_num_bytes);
            let new_header = spec_convert_to_header(new_header_bytes, log_num as int);
            
            assert(old_multilog.flush_committed()[0].subrange(0, header_prefix_size as int) =~= new_multilog.flush_committed()[0].subrange(0, header_prefix_size as int));
            logimpl_v::lemma_subrange_equality_implies_subsubrange_equality(
                old_multilog.flush_committed()[0],
                new_multilog.flush_committed()[0], 
                0,
                header_prefix_size as int
            );
    
            let live_header = spec_get_live_header(new_multilog.flush_committed());
            if old_ib == header1_val {
                assert(new_multilog.flush_committed()[0].subrange(self.header2_offset as int, self.header2_offset + spec_header_version_size(log_num as int)) =~= new_header_bytes);
                assert(new_multilog.flush_committed()[0].subrange(header1_offset as int, header1_offset + spec_header_version_size(log_num as int)) =~= 
                    old_multilog.flush_committed()[0].subrange(header1_offset as int, header1_offset + spec_header_version_size(log_num as int)));
                logimpl_v::lemma_subrange_equality_implies_subsubrange_equality(
                    new_multilog.flush_committed()[0], 
                    old_multilog.flush_committed()[0], 
                    header1_offset as int, 
                    header1_offset + spec_header_version_size(log_num as int)
                );  
            }
            else if old_ib == header2_val {
                assert(new_multilog.flush_committed()[0].subrange(header1_offset as int, header1_offset + spec_header_version_size(log_num as int)) =~= new_header_bytes);
                assert(new_multilog.flush_committed()[0].subrange(self.header2_offset as int, self.header2_offset + spec_header_version_size(log_num as int)) =~= 
                    old_multilog.flush_committed()[0].subrange(self.header2_offset as int, self.header2_offset + spec_header_version_size(log_num as int)));
                logimpl_v::lemma_subrange_equality_implies_subsubrange_equality(
                    new_multilog.flush_committed()[0], 
                    old_multilog.flush_committed()[0], 
                    self.header2_offset as int, 
                    self.header2_offset + spec_header_version_size(log_num as int)
                );
            } else {
                assert(false);
            }
            self.lemma_log_view_unchanged(old_multilog, 0, header_pos as int, new_header_bytes);
            assert(old_ib == header1_val ==> new_headers.header2 == new_header);
            assert(old_ib == header2_val ==> new_headers.header1 == new_header);
        }

        pub exec fn addr_logical_to_physical(addr: u64, log_size: u64) -> (out: u64)
            requires
                addr <= u64::MAX,
                log_size > 0,
            ensures
                out == spec_addr_logical_to_physical(addr as int, log_size as int)
        {
            (addr % log_size)
        }

        pub open spec fn minimum_header_region_size(num_logs: int) -> int 
        {
            (2 * spec_header_version_size(num_logs)) + header_prefix_size
        }

        pub open spec fn live_header_valid(live_header: MultiLogPersistentHeader, multilog: Seq<Seq<u8>>) -> bool
        {
            forall |i: int| #![trigger (live_header.metadata[i])] 0 <= i < live_header.metadata.len() ==> {
                let head = live_header.metadata[i].head as int;
                let tail = live_header.metadata[i].tail as int;
                let log_size = live_header.metadata[i].log_size as int;
                &&& log_size > 0 
                &&& tail - head < log_size 
                &&& head <= tail
                &&& log_size == multilog[i + 1].len()
            }
        }

        pub open spec fn multilog_state_is_valid(multilog: Seq<Seq<u8>>) -> bool
        {
            let header_region = multilog[0];
            let (ib, headers) = multilog_to_views(header_region);
            let live_header = spec_get_live_header(multilog);

            let log_num = spec_u64_from_le_bytes(headers.log_num_bytes);
            let header2_offset = header1_offset + spec_header_version_size(log_num as int);

            &&& header_region.len() >= Self::minimum_header_region_size(log_num as int) 
            &&& headers.const_crc_bytes == logimpl_v::spec_crc_bytes(headers.log_num_bytes)
            &&& ib == header1_val || ib == header2_val
            &&& ib == header1_val ==> {
                    &&& live_header.crc == spec_u64_from_le_bytes(logimpl_v::spec_crc_bytes(header_region.subrange(header1_offset + multilog_header_metadata_offset, header1_offset + spec_header_version_size(log_num as int))))
                    &&& header_region.subrange(header1_offset + multilog_header_crc_offset, header1_offset + multilog_header_crc_offset + crc_size) =~= 
                        logimpl_v::spec_crc_bytes(header_region.subrange(header1_offset + multilog_header_metadata_offset, header1_offset + spec_header_version_size(log_num as int)))
                } 
            &&& ib == header2_val ==> {
                    &&& live_header.crc == spec_u64_from_le_bytes(logimpl_v::spec_crc_bytes(header_region.subrange(header2_offset + multilog_header_metadata_offset, header2_offset + spec_header_version_size(log_num as int))))
                    &&& header_region.subrange(header2_offset + multilog_header_crc_offset, header2_offset + multilog_header_crc_offset + crc_size) =~= 
                        logimpl_v::spec_crc_bytes(header_region.subrange(header2_offset + multilog_header_metadata_offset, header2_offset + spec_header_version_size(log_num as int)))
            }
            &&& Self::live_header_valid(live_header, multilog)
            &&& log_num == multilog.len() - 1
            &&& 0 < log_num <= usize::MAX
        }

        /// Expects an index into the multilog, not an index into metadata
        pub open spec fn spec_get_live_bytes(index: int, multilog: Seq<Seq<u8>>) -> Seq<u8> 
        {
            // metadata[n] corresponds to multilog[n+1]
            let live_header = spec_get_live_header(multilog);
            let head = live_header.metadata[index].head as int;
            let tail = live_header.metadata[index].tail as int;
            let log_size = live_header.metadata[index].log_size as int;

            let physical_head = spec_addr_logical_to_physical(head, log_size);
            let physical_tail = spec_addr_logical_to_physical(tail, log_size);
            
            if physical_head < physical_tail {
                multilog[index + 1].subrange(physical_head, physical_tail)
            } else if physical_tail < physical_head {
                let range1 = multilog[index + 1].subrange(physical_head, log_size);
                let range2 = multilog[index + 1].subrange(0, physical_tail);
                range1 + range2 
            } else {
                Seq::empty()
            }
        }

        pub open spec fn convert_multilog_to_log_state(multilog: Seq<Seq<u8>>) -> Option<MultiLogAbstractInfiniteLogState>
        {
            if !Self::multilog_state_is_valid(multilog) {
                None 
            } else {
                let header_region = multilog[0];
                let (ib, headers) = multilog_to_views(header_region);
                let live_header = spec_get_live_header(multilog);
                Some(
                    MultiLogAbstractInfiniteLogState {
                        states: Seq::<AbstractInfiniteLogState>::new((multilog.len() - 1) as nat,
                            |i: int| {
                                let head = live_header.metadata[i].head as int;
                                let log_size = live_header.metadata[i].log_size as int;
                                let abstract_log = Self::spec_get_live_bytes(i, multilog);
                                AbstractInfiniteLogState { head: head, log: abstract_log, capacity: log_size - 1 }
                            }
                        )
                    }
                )
            }
        }

        pub open spec fn consistent_with_multilog(self, pms: MultiLogPersistentMemoryView) -> bool {
            let header_region = pms.regions[0].flush_committed();
            let (ib, headers) = multilog_to_views(header_region);
            let log_num = spec_u64_from_le_bytes(headers.log_num_bytes);
            &&& pms.no_outstanding_writes()
            &&& match UntrustedMultiLogImpl::convert_multilog_to_log_state(pms.flush_committed()) {
                Some(multilog) => {
                    let header_pos = if ib == header1_val {
                        header1_offset
                    } else {
                        self.header2_offset
                    };
                    let live_header = spec_get_live_header(pms.flush_committed());
                    &&& self.incorruptible_bool == header1_val || self.incorruptible_bool == header2_val 
                    &&& self.incorruptible_bool == ib
                    &&& logimpl_v::spec_crc_bytes(header_region.subrange(header_pos + multilog_header_metadata_offset, header_pos + spec_header_version_size(log_num as int))) =~= 
                            header_region.subrange(multilog_header_crc_offset as int, multilog_header_crc_offset + crc_size)
                    &&& self.header_crc == spec_u64_from_le_bytes(headers.const_crc_bytes)
                    &&& self.log_num == spec_u64_from_le_bytes(headers.log_num_bytes)
                    &&& self.log_num == self.log_metadata@.len()
                    &&& self.log_num == live_header.metadata.len()
                    &&& self.log_num == pms.len() - 1
                    &&& self.log_metadata.len() == live_header.metadata.len()
                    &&& forall |i: int| 0 <= i < live_header.metadata.len() ==> {
                            let head = #[trigger] live_header.metadata[i].head;
                            let tail = #[trigger] live_header.metadata[i].tail;
                            let log_size = #[trigger] live_header.metadata[i].log_size;

                            &&& self.header_crc == spec_u64_from_le_bytes(headers.const_crc_bytes)
                            &&& self.log_metadata@[i] == live_header.metadata[i]
                            &&& multilog[i].head + multilog[i].log.len() == live_header.metadata[i].tail
                            &&& log_size == pms.committed()[i + 1].len()
                            &&& log_size > 0
                        }
                    &&& self.header2_offset == header1_offset + spec_header_version_size(log_num as int)
                }
                None => false
            }
        }

        exec fn update_header<P: CheckPermission<Seq<Seq<u8>>>> (
            &mut self,
            multilog: &mut MultiLogWriteRestrictedPersistentMemory<P>,
            Tracked(perm): Tracked<&P>,
            new_header_bytes: &Vec<u8>,
        )
            requires 
                permissions_depend_only_on_recovery_view(perm),
                old(self).consistent_with_multilog(old(multilog)@),
                UntrustedMultiLogImpl::convert_multilog_to_log_state(old(multilog)@.flush_committed()).is_Some(),
                ({
                    let (_, headers) = multilog_to_views(old(multilog)@.flush_committed()[0]);
                    let log_num = spec_u64_from_le_bytes(headers.log_num_bytes);
                    new_header_bytes@.len() == spec_header_version_size(log_num as int)
                }),
                new_header_bytes@.subrange(multilog_header_crc_offset as int, multilog_header_crc_offset + crc_size) =~=
                    logimpl_v::spec_crc_bytes(new_header_bytes@.subrange(multilog_header_crc_offset + crc_size, new_header_bytes@.len() as int)),
                old(multilog)@.no_outstanding_writes(),
                perm.check_permission(old(multilog)@.flush_committed()),
            ensures 
                self.consistent_with_multilog(multilog@),
                multilog.impervious_to_corruption() == old(multilog).impervious_to_corruption(),
                match (UntrustedMultiLogImpl::convert_multilog_to_log_state(multilog@.flush_committed()),
                        UntrustedMultiLogImpl::convert_multilog_to_log_state(old(multilog)@.flush_committed())) {
                            (Some(old_log_state), Some(new_log_state)) => old_log_state =~= new_log_state,
                            _ => false
                        },
                ({
                    let (new_ib, new_headers) = multilog_to_views(multilog@.flush_committed()[0]);
                    let (old_ib, old_headers) = multilog_to_views(old(multilog)@.flush_committed()[0]);
                    let new_header = spec_convert_to_header(new_header_bytes@, spec_u64_from_le_bytes(old_headers.log_num_bytes) as int);
                    &&& old_ib == new_ib 
                    &&& old_headers.const_crc_bytes =~= new_headers.const_crc_bytes 
                    &&& old_headers.log_num_bytes =~= new_headers.log_num_bytes
                    &&& old_ib == header1_val ==> {
                        // current header is header1, so we update header2
                        &&& old_headers.header1 == new_headers.header1
                        &&& new_headers.header2 == new_header
                    }
                    &&& old_ib == header2_val ==> {
                        // current header is header2, so we update header1
                        &&& new_headers.header1 == new_header
                        &&& old_headers.header2 == new_headers.header2
                    }
                })
        {
            // write to the header that is NOT pointed to by the IB
            let header_pos = if self.incorruptible_bool == header1_val {
                self.header2_offset
            } else {
                header1_offset 
            };
            
            proof {
                let abstract_state = UntrustedMultiLogImpl::convert_multilog_to_log_state(multilog@.flush_committed()).unwrap()[0];
                assert forall |crash_pm|
                    #[trigger] multilog@.write(0, header_pos as int, new_header_bytes@).can_crash_as(crash_pm) implies perm.check_permission(crash_pm)
                by { 
                    let state = UntrustedMultiLogImpl::convert_multilog_to_log_state(multilog@.flush_committed()).unwrap();
                    self.lemma_inactive_header_update_view(multilog@, new_header_bytes@, header_pos as int, state, crash_pm);
                }
            }
            multilog.write(0, header_pos, new_header_bytes.as_slice(), Tracked(perm));
            multilog.flush();

            proof {
                self.lemma_header_updated(old(multilog)@, multilog@, header_pos as int, new_header_bytes@);
            }
            
        }

        pub exec fn untrusted_setup(regions: &mut MultiLogPersistentMemory) -> (result: Result<Vec<u64>, InfiniteMultiLogErr>)
            ensures 
                match result {
                    Ok(capacities) => {
                        &&& capacities@.len() == regions@.len()
                        &&& UntrustedMultiLogImpl::convert_multilog_to_log_state(regions@.committed()) == 
                                Some(MultiLogAbstractInfiniteLogState::initialize(capacities@))
                        &&& capacities[0] == Self::minimum_header_region_size(regions@.len() - 1)
                    },
                    Err(InfiniteMultiLogErr::InsufficientSpaceForSetup { pm_index, required_space }) => 
                        regions@[pm_index as int].len() < required_space,
                    _ => false
                }
        {
            assume(false);
            Err(InfiniteMultiLogErr::None)
        }

        pub exec fn untrusted_start<P>(
            wrpms: &mut MultiLogWriteRestrictedPersistentMemory<P>, 
            Tracked(perm): Tracked<&P>,
            state: Ghost<MultiLogAbstractInfiniteLogState>
        ) -> (result: Result<UntrustedMultiLogImpl, InfiniteMultiLogErr>)
            where 
                P: CheckPermission<Seq<Seq<u8>>>,
            requires 
                multilog_t::can_only_crash_as_state(old(wrpms)@, state@),
                // The restriction on writing persistent memory during initialization is
                // that it can't change the interpretation of that memory's contents.
                forall |pm_states| #[trigger] perm.check_permission(pm_states) <==> 
                    UntrustedMultiLogImpl::convert_multilog_to_log_state(pm_states) == Some(state@)
            ensures 
                old(wrpms).impervious_to_corruption() == wrpms.impervious_to_corruption(),
                forall |s| multilog_t::can_only_crash_as_state(old(wrpms)@, s) ==> s == state,
                match result {
                    Ok(log_impl) => {
                        &&& log_impl.consistent_with_multilog(wrpms@)
                        &&& log_impl.log_metadata@.len() == wrpms.spec_get_pms().regions.len() - 1
                        &&& multilog_t::can_only_crash_as_state(wrpms@, state@)
                    }
                    Err(InfiniteMultiLogErr::CRCMismatch) => !old(wrpms).impervious_to_corruption(),
                    Err(InfiniteMultiLogErr::InsufficientSpaceForSetup { pm_index, required_space }) => {
                        &&& 0 <= pm_index < wrpms@.len() ==> wrpms@[pm_index as int].len() < required_space
                        &&& !(0 <= pm_index < wrpms@.len()) ==> false
                    }
                    _ => false
                }
        {
            assume(false);
            Err(InfiniteMultiLogErr::None)
        }

        pub exec fn untrusted_append<P>(
            &mut self,
            wrpms: &mut MultiLogWriteRestrictedPersistentMemory<P>,
            index: usize,
            bytes_to_append: &Vec<u8>,
            Tracked(perm): Tracked<&P>
        ) -> (result: Result<u64, InfiniteMultiLogErr>)
            where 
                P: CheckPermission<Seq<Seq<u8>>>,
            requires
                old(self).consistent_with_multilog(old(wrpms)@),
                UntrustedMultiLogImpl::convert_multilog_to_log_state(old(wrpms)@.flush_committed()).is_Some(),
                ({
                    let old_log_states = UntrustedMultiLogImpl::convert_multilog_to_log_state(old(wrpms)@.flush_committed());
                    forall |pm_states| #[trigger] perm.check_permission(pm_states) <==> {
                        let log_states = UntrustedMultiLogImpl::convert_multilog_to_log_state(pm_states);
                        match (log_states, log_states) {
                            (Some(log_states), Some(crash_log_states)) => {
                                ||| crash_log_states == log_states
                                ||| crash_log_states == log_states.append(index as int, bytes_to_append@)
                            }
                            _ => false,
                        }
                    }
                })
            ensures 
                wrpms.impervious_to_corruption() == old(wrpms).impervious_to_corruption(),
                self.untrusted_append_postcond(result, old(wrpms).spec_get_pms(), wrpms.spec_get_pms(), index as int, bytes_to_append@)
        {
            assume(false);
            Err(InfiniteMultiLogErr::None)
        }

        pub open spec fn untrusted_append_postcond(
            &self, 
            result: Result<u64, InfiniteMultiLogErr>,
            old_multilog: MultiLogPersistentMemory,
            new_multilog: MultiLogPersistentMemory,
            index: int,
            bytes_appended: Seq<u8>,
        ) -> bool {
            let old_log_states = UntrustedMultiLogImpl::convert_multilog_to_log_state(old_multilog@.committed());
            let new_log_states = UntrustedMultiLogImpl::convert_multilog_to_log_state(new_multilog@.committed());
            &&& self.consistent_with_multilog(new_multilog@)
            &&& match (result, old_log_states, new_log_states) {
                (Ok(offset), Some(old_log_states), Some(new_log_states)) => {
                    &&& offset == old_log_states[index].head + old_log_states[index].log.len()
                    &&& new_log_states == old_log_states.append(index, bytes_appended)
                }
                (Err(InfiniteMultiLogErr::InsufficientSpaceForAppend { pm_index, available_space }), Some(old_log_states), Some(new_log_states)) => {
                    let pm_index = pm_index as int;
                    &&& new_log_states == old_log_states 
                    &&& available_space < bytes_appended.len()
                    &&& ({
                            ||| available_space == old_log_states[pm_index].capacity - old_log_states[pm_index].log.len()
                            ||| available_space == u64::MAX - old_log_states[pm_index].head - old_log_states[pm_index].log.len()
                        })
                }
                (_, _, _) => false,
            }
        }

        pub exec fn untrusted_advance_head<P>(
            &mut self,
            wrpms: &mut MultiLogWriteRestrictedPersistentMemory<P>,
            index: usize,
            new_head: u64,
            Tracked(perm): Tracked<&P>,
            state: Ghost<MultiLogAbstractInfiniteLogState>
        ) -> (result: Result<(), InfiniteMultiLogErr>)
            where
                P: CheckPermission<Seq<Seq<u8>>>,
            requires
                old(self).consistent_with_multilog(old(wrpms)@),
                forall |s| #[trigger] old(wrpms)@.can_crash_as(s) ==>
                    UntrustedMultiLogImpl::convert_multilog_to_log_state(s) == Some(state@),
                forall |pm_states| #[trigger] perm.check_permission(pm_states) <==> {
                    let log_state = UntrustedMultiLogImpl::convert_multilog_to_log_state(pm_states);
                    ||| log_state == Some(state@)
                    ||| log_state == Some(state@.advance_head(index as int, new_head as int))
                }
            ensures 
                self.consistent_with_multilog(wrpms@),
                wrpms.impervious_to_corruption() == old(wrpms).impervious_to_corruption(),
                wrpms@.can_crash_as(wrpms@.committed()),
                ({
                    let old_log_states = UntrustedMultiLogImpl::convert_multilog_to_log_state(old(wrpms)@.flush_committed());
                    let new_log_states = UntrustedMultiLogImpl::convert_multilog_to_log_state(wrpms@.flush_committed());
                    match (result, old_log_states, new_log_states) {
                        (Ok(_), Some(old_log_states), Some(new_log_states)) => {true}
                        (Err(InfiniteMultiLogErr::CantAdvanceHeadPositionBeforeHead{ pm_index, head }), Some(old_log_states), Some(new_log_states)) => {
                            &&& old_log_states =~= new_log_states 
                            &&& head == old_log_states[pm_index as int].head
                            &&& new_head < head 
                        }
                        (Err(InfiniteMultiLogErr::CantAdvanceHeadPositionBeyondTail{ pm_index, tail }), Some(old_log_states), Some(new_log_states)) => {
                            &&& old_log_states =~= new_log_states 
                            &&& tail == old_log_states[pm_index as int].head + old_log_states[pm_index as int].log.len()
                            &&& new_head > tail
                        },
                        (Err(InfiniteMultiLogErr::InvalidLength{ index, log_num }), Some(old_log_states), Some(new_log_states)) => {
                            &&& old_log_states =~= new_log_states
                            &&& log_num <= index
                        },
                        (_, _, _) => false
                    }
                })
        {
            proof {
                lemma_if_no_outstanding_writes_then_can_only_crash_as_committed(wrpms@);
                lemma_can_crash_as_committed_and_all_flushed(wrpms@);
                assert (UntrustedMultiLogImpl::convert_multilog_to_log_state(wrpms@.flush_committed()) == Some(state@));
            }

            if index >= self.log_metadata.len() {
                assert(UntrustedMultiLogImpl::convert_multilog_to_log_state(old(wrpms)@.flush_committed()) =~= UntrustedMultiLogImpl::convert_multilog_to_log_state(wrpms@.flush_committed()));
                return Err(InfiniteMultiLogErr::InvalidLength { index, log_num: self.log_metadata.len() });
            }

            let mut new_metadata_vec: Vec<u8> = Vec::with_capacity(self.log_metadata.len());

            let mut i = 0;
            while i < self.log_metadata.len()
                invariant 
                    // TODO: put in a spec function since some of this is shared with the postcond of the function
                    wrpms.impervious_to_corruption() == old(wrpms).impervious_to_corruption(),
                    self.consistent_with_multilog(wrpms@),
                    UntrustedMultiLogImpl::convert_multilog_to_log_state(old(wrpms)@.flush_committed()) =~= 
                        UntrustedMultiLogImpl::convert_multilog_to_log_state(wrpms@.flush_committed()),
                    new_metadata_vec@.len() == i * multilog_header_size,
                    i <= self.log_metadata.len(),
            {
                if i == index {
                    let log_size = self.log_metadata[i].log_size;
                    let head = self.log_metadata[i].head;
                    let tail = self.log_metadata[i].tail;

                    if new_head < head {
                        assert(UntrustedMultiLogImpl::convert_multilog_to_log_state(old(wrpms)@.flush_committed()) =~= UntrustedMultiLogImpl::convert_multilog_to_log_state(wrpms@.flush_committed()));
                        return Err(InfiniteMultiLogErr::CantAdvanceHeadPositionBeforeHead{ pm_index: index, head });
                    }
                    if new_head > tail {
                        assert(UntrustedMultiLogImpl::convert_multilog_to_log_state(old(wrpms)@.flush_committed()) =~= UntrustedMultiLogImpl::convert_multilog_to_log_state(wrpms@.flush_committed()));
                        return Err(InfiniteMultiLogErr::CantAdvanceHeadPositionBeyondTail { pm_index: index, tail });
                    }

                    let new_header = logimpl_v::PersistentHeaderMetadata {
                        head: new_head,
                        tail,
                        log_size,
                    };

                    let mut bytes = metadata_to_bytes(&new_header);
                    new_metadata_vec.append(&mut bytes);
                } else {
                    let mut bytes = metadata_to_bytes(&self.log_metadata[i]);
                    new_metadata_vec.append(&mut bytes);
                }
         
                i += 1;
            }
            assert(new_metadata_vec@.len() == self.log_metadata@.len() * multilog_header_size);

            // now that we have fully updated header bytes, calculate CRC
            // NOTE: it would be more efficient to write them to PM as we go and calculate the CRC directly
            // on persistent data, but we don't have a way to do that that doesn't involve saving the 
            // vector or reading it back into regular memory.
            
            let crc_bytes = logimpl_v::bytes_crc(&new_metadata_vec);
            let ghost old_crc_bytes = crc_bytes@;
            let ghost old_metadata_bytes = new_metadata_vec@;
            let mut header_bytes = crc_bytes;
            header_bytes.append(&mut new_metadata_vec);

            proof { 
                let (_, headers) = multilog_to_views(wrpms@.flush_committed()[0]);
                let log_num = spec_u64_from_le_bytes(headers.log_num_bytes);
                assert(permissions_depend_only_on_recovery_view(perm));
                assert(header_bytes@ =~= old_crc_bytes + old_metadata_bytes);
                lemma_header_crc_correct(header_bytes@, old_crc_bytes, old_metadata_bytes, log_num as int);
            }
            
            self.update_header(wrpms, Tracked(perm), &header_bytes);
            assume(false);
            Err(InfiniteMultiLogErr::None)
        }

        pub exec fn untrusted_read(
            &self,
            multilog: &MultiLogPersistentMemory,
            index: usize,
            pos: u64,
            len: u64,
            state: Ghost<MultiLogAbstractInfiniteLogState>
        ) -> (result: Result<(Vec<u8>, Ghost<Seq<int>>), InfiniteMultiLogErr>)
            requires
                self.consistent_with_multilog(multilog@),
                forall |pm_states| #[trigger] multilog@.can_crash_as(pm_states) ==>
                    UntrustedMultiLogImpl::convert_multilog_to_log_state(pm_states) == Some(state@),
            ensures
                ({
                    let head = state@[index as int].head;
                    let log = state@[index as int].log;
                    match result {
                        Ok((bytes, addrs)) => {
                            &&& pos >= head
                            &&& pos + len <= head + log.len()
                            &&& maybe_corrupted(bytes@, log.subrange(pos - head, pos + len - head), addrs@)
                            &&& multilog.impervious_to_corruption() ==>
                                    bytes@ == log.subrange(pos - head, pos + len - head)
                        },
                        Err(InfiniteMultiLogErr::CantReadBeforeHead{ head: head_pos }) => {
                            &&& pos < head
                            &&& head_pos == head
                        },
                        Err(InfiniteMultiLogErr::CantReadPastTail{ tail }) => {
                            &&& pos + len > head + log.len()
                            &&& tail == head + log.len()
                        },
                        Err(InfiniteMultiLogErr::InvalidIndex { pm_index }) => {
                            &&& pm_index == index 
                            &&& pm_index >= self.log_metadata@.len()
                        }
                        _ => false
                    }
                })
        {   
            proof {
                lemma_if_no_outstanding_writes_then_can_only_crash_as_committed(multilog@);
                lemma_can_crash_as_committed_and_all_flushed(multilog@);
                assert(UntrustedMultiLogImpl::convert_multilog_to_log_state(multilog@.committed()) == Some(state@));
            }

            if index >= self.log_metadata.len() {
                return Err(InfiniteMultiLogErr::InvalidIndex { pm_index: index });
            }

            let log_size = self.log_metadata[index].log_size;
            let head = self.log_metadata[index].head;
            let tail = self.log_metadata[index].tail;
            let metadata_index = index; // index argument is an index into the multilog; metadata_index indexes into metadata structures and log states
            let index = index + 1;
            
            proof {
                let (ib, headers) = multilog_to_views(multilog@.committed()[0]);
                let live_header = spec_get_live_header(multilog@.committed());
                assert(self.log_metadata.len() == live_header.metadata.len());
                assert(head == live_header.metadata[metadata_index as int].head);
                assert(tail == live_header.metadata[metadata_index as int].tail);
                assert(log_size == live_header.metadata[metadata_index as int].log_size);
            }

            let physical_pos = Self::addr_logical_to_physical(pos, log_size);

            if pos < head {
                Err(InfiniteMultiLogErr::CantReadBeforeHead{ head })
            } else if pos > u64::MAX - len {
                Err(InfiniteMultiLogErr::CantReadPastTail{ tail })
            } else if pos + len > tail {
                Err(InfiniteMultiLogErr::CantReadPastTail{ tail })
            } else {
                proof {
                    // we get a type error if we calculate physical head and tail in non-ghost code and use them here,
                    // so we need to calculate them here for the proof and again later for execution
                    let physical_head = spec_addr_logical_to_physical(head as int, log_size as int);
                    let physical_tail = spec_addr_logical_to_physical(tail as int, log_size as int);
                    if physical_head == physical_tail {
                        lemma_mod_equal(head as int, tail as int, log_size as int);
                        assert(len == 0);
                    } else if physical_head < physical_tail {
                        // read cannot wrap around 
                        lemma_mod_between(log_size as int, head as int, tail as int, pos as int);
                        lemma_mod_difference_equal(head as int, pos as int, log_size as int);
                    } else {
                        // read may wrap around 
                        lemma_mod_not_between(log_size as int, head as int, tail as int, pos as int);
                        if physical_pos <= physical_tail {
                            lemma_mod_wrapped_len(head as int, pos as int, log_size as int);
                        } else {
                            lemma_mod_difference_equal(head as int, pos as int, log_size as int);
                        }
                    }
                }

                let physical_head = Self::addr_logical_to_physical(head, log_size);
                let physical_tail = Self::addr_logical_to_physical(tail, log_size);
                let ghost log = Self::convert_multilog_to_log_state(multilog@.committed()).unwrap()[metadata_index as int];

                let buffer = if physical_head == physical_tail {
                    assert(pos - head == pos + len - head);
                    assert (Seq::<u8>::empty() =~= log.log.subrange(pos - head, pos + len - head));
                    (Vec::new(), Ghost(Seq::empty()))
                } else if physical_pos >= physical_head && physical_pos >= log_size - len {
                    let r1_len = log_size - physical_pos;
                    let r2_len = len - r1_len;

                    let (mut r1, r1_addrs) = multilog.read(index, physical_pos, r1_len);
                    let (mut r2, r2_addrs) = multilog.read(index, 0, r2_len);
                    r1.append(&mut r2);

                    assert (multilog@.committed()[index as int].subrange(physical_pos as int, physical_pos + r1_len) + multilog@.committed()[index as int].subrange(0, r2_len as int)
                                    =~= log.log.subrange(pos - head, pos + len - head));

                    (r1, Ghost(r1_addrs@ + r2_addrs@))
                } else {
                    assert(multilog@.committed()[index as int].subrange(physical_pos as int, physical_pos + len) =~= log.log.subrange(pos - head, pos + len - head));
                    multilog.read(index, physical_pos, len)
                };
                
                Ok(buffer)
            }
        }

        pub exec fn untrusted_get_head_and_tail(
            &self,
            multilog: &MultiLogPersistentMemory,
            index: usize
        ) -> (result: Result<(u64, u64, u64), InfiniteMultiLogErr>)
            requires 
                self.consistent_with_multilog(multilog@),
                UntrustedMultiLogImpl::convert_multilog_to_log_state(multilog@.flush_committed()).is_Some(),
                0 <= index < self.log_metadata.len(),
                ({
                    let (_, headers) = multilog_to_views(multilog@.flush_committed()[0]);
                    let log_num = spec_u64_from_le_bytes(headers.log_num_bytes);
                    &&& log_num == multilog@.committed().len() - 1
                    &&& log_num == self.log_metadata@.len()
                }),
            ensures 
                match result {
                    Ok((result_head, result_tail, result_capacity)) => 
                        match UntrustedMultiLogImpl::convert_multilog_to_log_state(multilog@.flush_committed()).unwrap()[index as int] {
                            AbstractInfiniteLogState{head, log, capacity} => {
                                &&& result_head == head 
                                &&& result_tail == head + log.len()
                                &&& result_capacity == capacity
                            }
                        }
                    Err(_) => false
                }
        {
            let metadata = &self.log_metadata[index];
            proof {
                let live_header = spec_get_live_header(multilog@.flush_committed());
                assert(metadata.log_size == live_header.metadata[index as int].log_size);
            }
            Ok((metadata.head, metadata.tail, metadata.log_size - 1))
        }  
    }
    
} // verus!