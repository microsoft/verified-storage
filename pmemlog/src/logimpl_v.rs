use crate::infinitelog_t::*;
use crate::main_t::*;
use crate::math::*;
use crate::pmemspec_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::set::*;
use vstd::slice::*;
use core::convert::TryInto;
use std::f32::consts::E;
use std::fmt::Write;
use crate::sccf::CheckPermission;

verus! {

    // new structure:
    // bytes 0-7: incorruptible boolean
    // bytes 8-39: header 1
    // bytes 40-71: header 2

    // header structure:
    // 0-7: header CRC
    // 8-15: logical head
    // 16-23: logical tail
    // 24-31: log size

    pub const incorruptible_bool_pos: u64 = 0;
    pub const header1_pos: u64 = 8;
    pub const header2_pos: u64 = 40;

    // offsets of fields within the header structure
    pub const header_crc_offset: u64 = 0;
    pub const header_head_offset: u64 = 8;
    pub const header_tail_offset: u64 = 16;
    pub const header_log_size_offset: u64 = 24;

    // TODO: use something more secure (CRC or SHA hash of 0 and 1) 
    pub const header1_val: u64 = 0;
    pub const header2_val: u64 = 1;

    pub const header_size: u64 = 32;

    pub const crc_size: u64 = 8; 

    // TODO: axiom should check that we are using a header that is expected to be valid?
    // TODO: use all Seq<u8>s rather than u64s for crcs
    #[verifier(external_body)]
    pub proof fn axiom_bytes_uncorrupted(x_c: Seq<u8>, x: Seq<u8>, x_addrs: Seq<int>,
                                        y_c: Seq<u8>, y: Seq<u8>, y_addrs: Seq<int>)
        requires 
            maybe_corrupted(x_c, x, x_addrs),
            maybe_corrupted(y_c, y, y_addrs),
            y =~= spec_crc_bytes(x),
            y_c =~= spec_crc_bytes(x_c),
            all_elements_unique(x_addrs),
            all_elements_unique(y_addrs),
        ensures
            x == x_c
    {}

    #[verifier(external_body)]
    pub proof fn axiom_incorruptible_bool(spec_ib: u64, ib_c: u64)
        requires 
            ({
                &&& maybe_corrupted_u64(ib_c, spec_ib, Seq::<int>::new(8, |i: int| incorruptible_bool_pos + i))
                &&& ib_c == header1_val || ib_c == header2_val
                &&& spec_ib == header1_val || spec_ib == header2_val // maintained by pm_invariant
            })
        ensures 
            ib_c == spec_ib
    {}

    pub open spec fn spec_modulo(x: int, y: int) -> (out: int)
    {
        x % y
    }

    pub exec fn modulo(x: u64, y: u64) -> (out: u64)
        requires 0 < y
        ensures out == spec_modulo(x as int, y as int)

    {
        x % y
    }

    pub open spec fn pm_to_views(pm: Seq<u8>) -> (u64, HeaderView, Seq<u8>) 
    {
        let incorruptible_bool = spec_u64_from_le_bytes(pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8));
        // read the CRC, then read the rest of the metadata, then combine them
        let crc1 = spec_u64_from_le_bytes(pm.subrange(header1_pos + header_crc_offset, header1_pos + header_crc_offset + 8));
        let crc2 = spec_u64_from_le_bytes(pm.subrange(header2_pos + header_crc_offset, header2_pos + header_crc_offset + 8));

        let header1_metadata = spec_bytes_to_metadata(pm.subrange(header1_pos + header_head_offset, header1_pos + header_size));
        let header2_metadata = spec_bytes_to_metadata(pm.subrange(header2_pos + header_head_offset, header2_pos + header_size));
        let header_view = HeaderView {
            header1: PersistentHeader {
                crc: crc1,
                metadata: header1_metadata,
            },
            header2: PersistentHeader {
                crc: crc2,
                metadata: header2_metadata,
            }
        };
        let data_view = pm.subrange(contents_offset as int, pm.len() as int);
        (
            incorruptible_bool,
            header_view,
            data_view
        )
    }

    pub open spec fn spec_get_live_header(pm: Seq<u8>) -> PersistentHeader 
    {
        let (ib, headers, _) = pm_to_views(pm);
        if ib == header1_val {
            headers.header1
        } else {
            headers.header2
        }
    }

    pub open spec fn permissions_depend_only_on_recovery_view<P: CheckPermission<Seq<u8>>>(perm: &P) -> bool
    {
        forall |s1, s2| recovery_view()(s1) == recovery_view()(s2) ==> perm.check_permission(s1) == perm.check_permission(s2)
    }

    pub proof fn lemma_same_permissions<P: CheckPermission<Seq<u8>>>(pm1: Seq<u8>, pm2: Seq<u8>, perm: &P)
        requires 
            recovery_view()(pm1) =~= recovery_view()(pm2),
            perm.check_permission(pm1),
            permissions_depend_only_on_recovery_view(perm)
        ensures 
            perm.check_permission(pm2)
    {}     

    pub proof fn lemma_header_match(pm: Seq<u8>, header_pos: int, header: PersistentHeader) 
        requires 
            pm.len() > contents_offset,
            header_pos == header1_pos || header_pos == header2_pos,
            spec_bytes_to_header(pm.subrange(header_pos as int, header_pos + header_size)) == header,
        ensures 
            ({
                let (_, headers, _) = pm_to_views(pm);
                &&& header_pos == header1_pos ==>
                        headers.header1 == header
                &&& header_pos == header2_pos ==>
                        headers.header2 == header
            })
    {
        assert(pm.subrange(header_pos as int, header_pos + header_size) =~=
                pm.subrange(header_pos + header_crc_offset, header_pos + header_crc_offset + 8) +
                pm.subrange(header_pos + header_head_offset, header_pos + header_size)
            );
        lemma_bytes_combine_into_header(
            pm.subrange(header_pos + header_crc_offset, header_pos + header_crc_offset + 8), 
            pm.subrange(header_pos + header_head_offset, header_pos + header_size), 
            header
        );
    }

    pub proof fn lemma_bytes_combine_into_header(crc_bytes: Seq<u8>, metadata_bytes: Seq<u8>, header: PersistentHeader)
        requires 
            crc_bytes.len() == 8,
            metadata_bytes.len() == header_size - 8,
            spec_bytes_to_header((crc_bytes + metadata_bytes)) == header,
        ensures 
            ({
                let combined_header = PersistentHeader { crc: spec_u64_from_le_bytes(crc_bytes), metadata: spec_bytes_to_metadata(metadata_bytes) };
                header == combined_header
            })
    {
        let crc_val = spec_u64_from_le_bytes(crc_bytes);
        let metadata = spec_bytes_to_metadata(metadata_bytes);
        lemma_seq_addition(crc_bytes, metadata_bytes);

        let combined_header = spec_bytes_to_header((crc_bytes + metadata_bytes));
        assert(combined_header.crc == crc_val);
        assert(metadata == spec_bytes_to_metadata((crc_bytes + metadata_bytes).subrange(header_head_offset as int, header_size as int)));
        assert(combined_header.metadata == metadata);
    }

    pub proof fn lemma_header_split_into_bytes(crc_bytes: Seq<u8>, metadata_bytes: Seq<u8>, header_bytes: Seq<u8>)
        requires 
            crc_bytes.len() == 8,
            metadata_bytes.len() == header_size - 8,
            header_bytes.len() == header_size,
            ({
                let header = PersistentHeader { crc: spec_u64_from_le_bytes(crc_bytes), metadata: spec_bytes_to_metadata(metadata_bytes) };
                spec_bytes_to_header(header_bytes) == header
            }),
        ensures
            crc_bytes + metadata_bytes =~= header_bytes
    {
        lemma_auto_spec_u64_to_from_le_bytes();
        let header = PersistentHeader { crc: spec_u64_from_le_bytes(crc_bytes), metadata: spec_bytes_to_metadata(metadata_bytes) };
        assert(header.crc == spec_u64_from_le_bytes(crc_bytes));
        assert(header_bytes.subrange(header_crc_offset as int, header_crc_offset + 8) =~= spec_u64_to_le_bytes(header.crc));
        assert(crc_bytes =~= spec_u64_to_le_bytes(header.crc));

        assert(header.metadata == spec_bytes_to_metadata(metadata_bytes));
        assert(header.metadata == spec_bytes_to_metadata(header_bytes.subrange(header_head_offset as int, header_size as int)));
        lemma_metadata_bytes_eq(metadata_bytes, header_bytes.subrange(header_head_offset as int, header_size as int), header.metadata);
        assert(header_bytes.subrange(header_head_offset as int, header_size as int) =~= metadata_bytes);
        
    }

    pub proof fn lemma_seq_addition(bytes1: Seq<u8>, bytes2: Seq<u8>)
        ensures 
            ({
                let i = bytes1.len() as int;
                let j = bytes2.len() as int;
                &&& (bytes1 + bytes2).subrange(0, i) =~= bytes1
                &&& (bytes1 + bytes2).subrange(i, i + j) =~= bytes2
            })
    {
        assert(forall |i: int| #![auto] 0 <= i < bytes1.len() ==> (bytes1 + bytes2)[i] == bytes1[i]);
        assert(forall |i: int| #![auto] 0 <= i < bytes2.len() ==> (bytes1 + bytes2)[bytes1.len() + i] == bytes2[i]);
    }

    #[verifier::ext_equal]
    pub struct PersistentHeader {
        pub crc: u64,
        pub metadata: PersistentHeaderMetadata,
    }

    #[verifier::ext_equal]
    pub struct PersistentHeaderMetadata {
        pub head: u64,
        pub tail: u64,
        pub log_size: u64,
    }


    // maybe make the CRC a sequence of bytes in the structure
    pub closed spec fn spec_crc_bytes(header_bytes: Seq<u8>) -> Seq<u8>;

    #[verifier::external_body]
    pub exec fn bytes_crc(header_bytes: &Vec<u8>) -> (out: Vec<u8>)
        ensures
            spec_crc_bytes(header_bytes@) =~= out@,
            out@.len() == 8
    {
        unimplemented!();
    }

    #[verifier::ext_equal]
    pub struct HeaderView {
        pub header1: PersistentHeader,
        pub header2: PersistentHeader,
    }

    // only go in one direction in ghost code - bytes -> structures
    // exec code is required to go structures -> bytes sometimes

    exec fn bytes_to_header(bytes: &[u8]) -> (out: PersistentHeader)
        requires 
            bytes@.len() == header_size
        ensures 
            out == spec_bytes_to_header(bytes@)
    {
        let crc_bytes = slice_subrange(bytes, header_crc_offset as usize, (header_crc_offset + 8) as usize);
        let metadata_bytes = slice_subrange(bytes, header_head_offset as usize, header_size as usize);

        PersistentHeader {
            crc: u64_from_le_bytes(crc_bytes),
            metadata: bytes_to_metadata(metadata_bytes),
        } 
    }

    exec fn header_to_bytes(header: &PersistentHeader) -> (out: Vec<u8>)
        ensures 
            // header == spec_words_to_header(spec_bytes_to_words(out@)),
            header == spec_bytes_to_header(out@),
            spec_u64_from_le_bytes(out@.subrange(header_crc_offset as int, header_crc_offset + 8)) == header.crc, 
            spec_bytes_to_metadata(out@.subrange(header_head_offset as int, header_size as int)) == header.metadata,
            out@.len() == header_size
    {
        proof { lemma_auto_spec_u64_to_from_le_bytes(); }

        let mut metadata_bytes = metadata_to_bytes(&header.metadata);
        let mut crc_bytes = u64_to_le_bytes(header.crc);
        let ghost old_metadata_bytes = metadata_bytes@;
        let ghost old_crc_bytes = crc_bytes@;
        crc_bytes.append(&mut metadata_bytes);
        proof {
            lemma_auto_spec_u64_to_from_le_bytes(); 
            assert(old_crc_bytes =~= crc_bytes@.subrange(header_crc_offset as int, header_crc_offset + 8));
            assert(old_metadata_bytes =~= crc_bytes@.subrange(header_head_offset as int, header_size as int));
        }
        crc_bytes
    }

    exec fn bytes_to_metadata(bytes: &[u8]) -> (out: PersistentHeaderMetadata)
        requires 
            bytes@.len() == header_size - 8
        ensures 
            out == spec_bytes_to_metadata(bytes@)
    {
        let head_bytes = slice_subrange(bytes, (header_head_offset - 8) as usize, (header_head_offset - 8 + 8) as usize);
        let tail_bytes = slice_subrange(bytes, (header_tail_offset - 8) as usize, (header_tail_offset - 8+ 8) as usize);
        let log_size_bytes = slice_subrange(bytes, (header_log_size_offset - 8) as usize, (header_log_size_offset - 8 + 8) as usize);

        PersistentHeaderMetadata { 
            head: u64_from_le_bytes(head_bytes), 
            tail: u64_from_le_bytes(tail_bytes), 
            log_size: u64_from_le_bytes(log_size_bytes),
        }
    }

    exec fn metadata_to_bytes(metadata: &PersistentHeaderMetadata) -> (out: Vec<u8>)
        ensures 
            metadata == spec_bytes_to_metadata(out@),
            out@.len() == header_size - 8,
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
            assert(old_head_bytes =~= bytes@.subrange(header_head_offset - 8, header_head_offset - 8 + 8));
            assert(old_tail_bytes =~= bytes@.subrange(header_tail_offset - 8, header_tail_offset - 8 + 8));
            assert(old_log_size_bytes =~= bytes@.subrange(header_log_size_offset - 8, header_log_size_offset - 8 + 8));
        }
        bytes
    }

    exec fn crc_and_metadata_bytes_to_header(crc_bytes: &[u8], header_bytes: &[u8]) -> (out: PersistentHeader)
        requires 
            crc_bytes@.len() == 8,
            header_bytes@.len() == header_size - 8
        ensures 
            out.crc == spec_u64_from_le_bytes(crc_bytes@),
            out.metadata == spec_bytes_to_metadata(header_bytes@)
    {
        let head_bytes = slice_subrange(header_bytes, (header_head_offset - 8) as usize, (header_head_offset + 8 - 8) as usize);
        let tail_bytes = slice_subrange(header_bytes, (header_tail_offset - 8) as usize, (header_tail_offset + 8 - 8) as usize);
        let log_size_bytes = slice_subrange(header_bytes, (header_log_size_offset - 8) as usize, (header_log_size_offset + 8 - 8) as usize);
    
        PersistentHeader {
            crc: u64_from_le_bytes(crc_bytes),
            metadata: PersistentHeaderMetadata {
                head: u64_from_le_bytes(head_bytes),
                tail: u64_from_le_bytes(tail_bytes),
                log_size: u64_from_le_bytes(log_size_bytes)
            } 
        }
    }

    pub open spec(checked) fn spec_bytes_to_metadata(header_seq: Seq<u8>) -> PersistentHeaderMetadata 
        recommends 
            header_seq.len() == 3*8
    {
        let head = spec_u64_from_le_bytes(header_seq.subrange(header_head_offset - 8, header_head_offset - 8 + 8));
        let tail = spec_u64_from_le_bytes(header_seq.subrange(header_tail_offset - 8, header_tail_offset - 8 + 8));
        let log_size = spec_u64_from_le_bytes(header_seq.subrange(header_log_size_offset - 8, header_log_size_offset - 8 + 8));
        PersistentHeaderMetadata {
            head,
            tail,
            log_size
        }
    }

    // TODO: refactor? seems overly long
    pub proof fn lemma_metadata_bytes_eq(bytes1: Seq<u8>, bytes2: Seq<u8>, metadata: PersistentHeaderMetadata)
        requires 
            bytes1.len() == header_size - 8,
            bytes2.len() == header_size - 8,
            metadata == spec_bytes_to_metadata(bytes1),
            metadata == spec_bytes_to_metadata(bytes2),
        ensures
            bytes1 =~= bytes2 
    {
        let metadata1 = spec_bytes_to_metadata(bytes1);
        let metadata2 = spec_bytes_to_metadata(bytes2);

        // TODO: could write a lemma that triggers on from instead of to - might help here
        lemma_auto_spec_u64_to_from_le_bytes();
        assert(spec_u64_to_le_bytes(metadata1.head) == spec_u64_to_le_bytes(metadata2.head));
        assert(metadata1.head == spec_u64_from_le_bytes(bytes1.subrange(header_head_offset - 8, header_head_offset - 8 + 8)));
        assert(metadata2.head == spec_u64_from_le_bytes(bytes2.subrange(header_head_offset - 8, header_head_offset - 8 + 8)));
        assert(bytes1.subrange(header_head_offset - 8, header_head_offset - 8 + 8) =~= bytes2.subrange(header_head_offset - 8, header_head_offset - 8 + 8));

        assert(spec_u64_to_le_bytes(metadata1.tail) == spec_u64_to_le_bytes(metadata2.tail));
        assert(metadata1.tail == spec_u64_from_le_bytes(bytes1.subrange(header_tail_offset - 8, header_tail_offset - 8 + 8)));
        assert(metadata2.tail == spec_u64_from_le_bytes(bytes2.subrange(header_tail_offset - 8, header_tail_offset - 8 + 8)));
        assert(bytes1.subrange(header_tail_offset - 8, header_tail_offset - 8 + 8) =~= bytes2.subrange(header_tail_offset - 8, header_tail_offset - 8 + 8));

        assert(spec_u64_to_le_bytes(metadata1.log_size) == spec_u64_to_le_bytes(metadata2.log_size));
        assert(metadata1.log_size == spec_u64_from_le_bytes(bytes1.subrange(header_log_size_offset - 8, header_log_size_offset - 8 + 8)));
        assert(metadata2.log_size == spec_u64_from_le_bytes(bytes2.subrange(header_log_size_offset - 8, header_log_size_offset - 8 + 8)));
        assert(bytes1.subrange(header_log_size_offset - 8, header_log_size_offset - 8 + 8) =~= bytes2.subrange(header_log_size_offset - 8, header_log_size_offset - 8 + 8));

        assert(bytes1 =~= bytes1.subrange(header_head_offset - 8, header_head_offset - 8 + 8) + 
                            bytes1.subrange(header_tail_offset - 8, header_tail_offset - 8 + 8) +
                            bytes1.subrange(header_log_size_offset - 8, header_log_size_offset - 8 + 8));
    }

    pub open spec(checked) fn spec_bytes_to_header(header_seq: Seq<u8>) -> PersistentHeader
        recommends 
            header_seq.len() == header_size 
    {
        let crc_val = spec_u64_from_le_bytes(header_seq.subrange(header_crc_offset as int, header_crc_offset +8));
        let metadata = spec_bytes_to_metadata(header_seq.subrange(header_head_offset as int, header_size as int));
        PersistentHeader {
            crc: crc_val,
            metadata
        }
    }

    pub proof fn lemma_data_write_is_safe<P>(pm: Seq<u8>, bytes: Seq<u8>, write_addr: int, perm: &P) 
        where 
            P: CheckPermission<Seq<u8>>,
        requires 
            UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm).is_Some(),
            pm.len() > contents_offset,
            contents_offset <= write_addr < pm.len(),
            perm.check_permission(pm),
            permissions_depend_only_on_recovery_view(perm),
            ({
                // write must be a valid write and not overlap the live log
                let live_header = spec_get_live_header(pm);
                let physical_head = spec_addr_logical_to_physical(live_header.metadata.head as int, live_header.metadata.log_size as int);
                let physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);
                &&& physical_head <= physical_tail ==> {
                    &&& write_addr + bytes.len() <= live_header.metadata.log_size + contents_offset
                    &&& write_addr < physical_head ==> write_addr + bytes.len() <= physical_head
                    &&& (physical_tail <= write_addr || write_addr < physical_head)
                }
                &&& physical_tail < physical_head ==> {
                    &&& physical_tail <= write_addr <= write_addr + bytes.len() < physical_head 
                }
            }),
        ensures 
            UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm).is_Some(),
            forall |chunks_flushed| {
                let new_pm = #[trigger] PersistentMemory::update_contents_to_reflect_partially_flushed_write(
                    pm, write_addr, bytes, chunks_flushed);
                perm.check_permission(new_pm)
            },
            ({
                let new_pm = PersistentMemory::update_contents_to_reflect_write(pm, write_addr, bytes);
                perm.check_permission(new_pm)
            }),
            update_data_view_postcond(pm, bytes, write_addr),
    {
        let new_pm = PersistentMemory::update_contents_to_reflect_write(pm, write_addr, bytes);
        lemma_append_data_update_view(pm, bytes, write_addr);
        lemma_same_log_state(pm, new_pm);

        assert forall |chunks_flushed| {
            let new_pm = #[trigger] PersistentMemory::update_contents_to_reflect_partially_flushed_write(
                pm, write_addr, bytes, chunks_flushed);
            perm.check_permission(new_pm)
        } by {
            let new_pm = PersistentMemory::update_contents_to_reflect_partially_flushed_write(
                pm, write_addr, bytes, chunks_flushed);
            lemma_append_data_update_view_crash(pm, bytes, write_addr, chunks_flushed);
            lemma_same_log_state(pm, new_pm);
            lemma_same_permissions(pm, new_pm, perm);
        }
    }

    pub open spec fn update_data_view_postcond(pm: Seq<u8>, new_bytes: Seq<u8>, write_addr: int) -> bool
    {
        let new_pm = PersistentMemory::update_contents_to_reflect_write(pm, write_addr, new_bytes);
        let (old_ib, old_headers, old_data) = pm_to_views(pm);
        let (new_ib, new_headers, new_data) = pm_to_views(new_pm);
        let live_header = spec_get_live_header(pm);
        let physical_head = spec_addr_logical_to_physical(live_header.metadata.head as int, live_header.metadata.log_size as int);
        let physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);
        &&& old_ib == new_ib
        &&& old_headers == new_headers 
        &&& new_data.len() == old_data.len()
        &&& new_data.subrange(write_addr - contents_offset, write_addr - contents_offset + new_bytes.len()) =~= new_bytes
        &&& new_data.subrange(0, write_addr - contents_offset) =~= old_data.subrange(0, write_addr - contents_offset)
        &&& new_data.subrange(write_addr - contents_offset + new_bytes.len(), new_data.len() as int) =~= 
                old_data.subrange(write_addr - contents_offset + new_bytes.len(), old_data.len() as int)
        &&& UntrustedLogImpl::convert_from_pm_contents_to_log_state2(new_pm).is_Some()

        &&& physical_head < physical_tail ==>
                new_data.subrange(physical_head - contents_offset, physical_tail - contents_offset) =~= old_data.subrange(physical_head - contents_offset, physical_tail - contents_offset)
        &&& physical_tail < physical_head ==> {
                &&& old_data.subrange(physical_head - contents_offset, live_header.metadata.log_size as int) =~= new_data.subrange(physical_head - contents_offset, live_header.metadata.log_size as int)
                &&& old_data.subrange(0, physical_tail - contents_offset) =~= new_data.subrange(0, physical_tail - contents_offset)
        }
    }

    pub proof fn lemma_append_data_update_view(pm: Seq<u8>, new_bytes: Seq<u8>, write_addr: int) 
        requires 
            UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm).is_Some(),
            pm.len() > contents_offset,
            contents_offset <= write_addr < pm.len(),
            ({
                // write must be a valid write and not overlap the live log
                let live_header = spec_get_live_header(pm);
                let physical_head = spec_addr_logical_to_physical(live_header.metadata.head as int, live_header.metadata.log_size as int);
                let physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);
                &&& physical_head <= physical_tail ==> {
                        &&& write_addr + new_bytes.len() <= live_header.metadata.log_size + contents_offset
                        &&& write_addr < physical_head ==> write_addr + new_bytes.len() <= physical_head
                        &&& (physical_tail <= write_addr || write_addr < physical_head)
                }
                &&& physical_tail < physical_head ==> {
                        &&& physical_tail <= write_addr <= write_addr + new_bytes.len() < physical_head 
                }
            }),
        ensures 
            UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm).is_Some(),
            update_data_view_postcond(pm, new_bytes, write_addr),
    {
        let live_header = spec_get_live_header(pm);
        let physical_head = spec_addr_logical_to_physical(live_header.metadata.head as int, live_header.metadata.log_size as int);
        let physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);
        let new_pm = PersistentMemory::update_contents_to_reflect_write(pm, write_addr, new_bytes);
        lemma_headers_unchanged(pm, new_pm);
        lemma_incorruptible_bool_unchanged(pm, new_pm);
        assert(live_header == spec_get_live_header(new_pm));
        assert(new_pm.subrange(0, write_addr) =~= pm.subrange(0, write_addr));
        assert(new_pm.subrange(write_addr + new_bytes.len(), new_pm.len() as int) =~= pm.subrange(write_addr + new_bytes.len(), pm.len() as int));
        lemma_subrange_equality_implies_subsubrange_equality(pm, new_pm, 0, write_addr);
        lemma_subrange_equality_implies_subsubrange_equality(pm, new_pm, write_addr + new_bytes.len(), new_pm.len() as int);
        if physical_head < physical_tail {
            assert(new_pm.subrange(physical_head as int, physical_tail as int) =~= pm.subrange(physical_head as int, physical_tail as int));
        } 
    }

    // TODO: combine with above
    pub proof fn lemma_append_data_update_view_crash(pm: Seq<u8>, new_bytes: Seq<u8>, write_addr: int, chunks_flushed: Set<int>) 
        requires 
            UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm).is_Some(),
            pm.len() > contents_offset,
            contents_offset <= write_addr < pm.len(),
            ({
                // write must be a valid write and not overlap the live log
                let live_header = spec_get_live_header(pm);
                let physical_head = spec_addr_logical_to_physical(live_header.metadata.head as int, live_header.metadata.log_size as int);
                let physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);
                &&& physical_head <= physical_tail ==> write_addr + new_bytes.len() <= live_header.metadata.log_size + contents_offset
                &&& physical_tail < physical_head ==> write_addr + new_bytes.len() < physical_head 
            })
        ensures 
            UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm).is_Some(),
            ({
                let new_pm = PersistentMemory::update_contents_to_reflect_partially_flushed_write(pm, write_addr, new_bytes, chunks_flushed);
                let (old_ib, old_headers, old_data) = pm_to_views(pm);
                let (new_ib, new_headers, new_data) = pm_to_views(new_pm);
                &&& old_ib == new_ib
                &&& old_headers == new_headers 
                &&& new_data.len() == old_data.len()
                &&& new_data.subrange(0, write_addr - contents_offset) =~= old_data.subrange(0, write_addr - contents_offset)
                &&& new_data.subrange(write_addr - contents_offset + new_bytes.len(), new_data.len() as int) =~= 
                        old_data.subrange(write_addr - contents_offset + new_bytes.len(), old_data.len() as int)
                &&& UntrustedLogImpl::convert_from_pm_contents_to_log_state2(new_pm).is_Some()
            })
    {
        let live_header = spec_get_live_header(pm);
        let physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);
        let new_pm = PersistentMemory::update_contents_to_reflect_partially_flushed_write(pm, write_addr, new_bytes, chunks_flushed);
        lemma_headers_unchanged(pm, new_pm);
        lemma_incorruptible_bool_unchanged(pm, new_pm);
        assert(new_pm.subrange(0, write_addr) =~= pm.subrange(0, write_addr));
        assert(new_pm.subrange(write_addr + new_bytes.len(), new_pm.len() as int) =~= pm.subrange(write_addr + new_bytes.len(), pm.len() as int));
        lemma_subrange_equality_implies_subsubrange_equality(pm, new_pm, 0, write_addr);
    }

    pub proof fn lemma_inactive_header_update_view(pm: Seq<u8>, new_header_bytes: Seq<u8>, header_pos: int)
        requires 
            UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm).is_Some(),
            header_pos == header1_pos || header_pos == header2_pos,
            ({
                // the new bytes must be written to the inactive header
                let (old_ib, old_headers, old_data) = pm_to_views(pm);
                &&& old_ib == header1_val ==> header_pos == header2_pos 
                &&& old_ib == header2_val ==> header_pos == header1_pos
            }),
            new_header_bytes.len() == header_size,
            pm.len() > contents_offset,
        ensures 
            ({
                let new_pm = PersistentMemory::update_contents_to_reflect_write(pm, header_pos, new_header_bytes);
                let (old_ib, old_headers, old_data) = pm_to_views(pm);
                let (new_ib, new_headers, new_data) = pm_to_views(new_pm);
                &&& old_ib == new_ib
                &&& old_data =~= old_data
                &&& header_pos == header1_pos ==> 
                    old_headers.header2 == new_headers.header2
                &&& header_pos == header2_pos ==>
                    old_headers.header1 == new_headers.header1
                &&& UntrustedLogImpl::convert_from_pm_contents_to_log_state2(new_pm).is_Some()
            })
    {
        let new_pm = PersistentMemory::update_contents_to_reflect_write(pm, header_pos, new_header_bytes);
        let (new_ib, new_headers, new_data) = pm_to_views(new_pm);
        assert(pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8) =~= new_pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8));
        if header_pos == header1_pos {
            // we wrote to header1, so header2 should have stayed the same
            assert(pm.subrange(header2_pos + header_crc_offset, header2_pos + header_crc_offset + 8) =~= 
                new_pm.subrange(header2_pos + header_crc_offset, header2_pos + header_crc_offset + 8));

            assert(pm.subrange(header2_pos + header_head_offset, header2_pos + header_size) =~= 
                new_pm.subrange(header2_pos + header_head_offset, header2_pos + header_size));
        } else {
            // we wrote to header2, so header1 should have stayed the same
            assert(pm.subrange(header1_pos + header_crc_offset, header1_pos + header_crc_offset + 8) =~= 
                new_pm.subrange(header1_pos + header_crc_offset, header1_pos + header_crc_offset + 8));

            assert(pm.subrange(header1_pos + header_head_offset, header1_pos + header_size) =~= 
                new_pm.subrange(header1_pos + header_head_offset, header1_pos + header_size));
        }
    }

    // TODO: combine with above
    pub proof fn lemma_inactive_header_update_view_crash(pm: Seq<u8>, new_header_bytes: Seq<u8>, header_pos: int, chunks_flushed: Set<int>)
        requires 
            UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm).is_Some(),
            header_pos == header1_pos || header_pos == header2_pos,
            ({
                // the new bytes must be written to the inactive header
                let (old_ib, old_headers, old_data) = pm_to_views(pm);
                &&& old_ib == header1_val ==> header_pos == header2_pos 
                &&& old_ib == header2_val ==> header_pos == header1_pos
            }),
            new_header_bytes.len() == header_size,
            pm.len() > contents_offset,
        ensures 
            ({
                let new_pm = PersistentMemory::update_contents_to_reflect_partially_flushed_write(
                    pm, header_pos, new_header_bytes, chunks_flushed);
                let (old_ib, old_headers, old_data) = pm_to_views(pm);
                let (new_ib, new_headers, new_data) = pm_to_views(new_pm);
                &&& old_ib == new_ib
                &&& old_data =~= old_data
                &&& header_pos == header1_pos ==> 
                    old_headers.header2 == new_headers.header2
                &&& header_pos == header2_pos ==>
                    old_headers.header1 == new_headers.header1
                &&& UntrustedLogImpl::convert_from_pm_contents_to_log_state2(new_pm).is_Some()
            })
    {
        let new_pm = PersistentMemory::update_contents_to_reflect_partially_flushed_write(
            pm, header_pos, new_header_bytes, chunks_flushed);
        assert(pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8) =~= new_pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8));
        if header_pos == header1_pos {
            // we wrote to header1, so header2 should have stayed the same
            assert(pm.subrange(header2_pos + header_crc_offset, header2_pos + header_crc_offset + 8) =~= 
                new_pm.subrange(header2_pos + header_crc_offset, header2_pos + header_crc_offset + 8));

            assert(pm.subrange(header2_pos + header_head_offset, header2_pos + header_size) =~= 
                new_pm.subrange(header2_pos + header_head_offset, header2_pos + header_size));
        } else {
            // we wrote to header2, so header1 should have stayed the same
            assert(pm.subrange(header1_pos + header_crc_offset, header1_pos + header_crc_offset + 8) =~= 
                new_pm.subrange(header1_pos + header_crc_offset, header1_pos + header_crc_offset + 8));

            assert(pm.subrange(header1_pos + header_head_offset, header1_pos + header_size) =~= 
                new_pm.subrange(header1_pos + header_head_offset, header1_pos + header_size));
        }
    }

    pub proof fn lemma_append_ib_update<P: CheckPermission<Seq<u8>>>(
        pm: Seq<u8>, 
        new_ib: u64, 
        bytes_to_append: Seq<u8>, 
        new_header_bytes: Seq<u8>, 
        perm: &P
    )
        requires 
            pm.len() > contents_offset,
            UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm).is_Some(),
            new_ib == header1_val || new_ib == header2_val,
            new_ib == header1_val ==> 
                pm.subrange(header1_pos as int, header1_pos + header_size) == new_header_bytes,
            new_ib == header2_val ==>
                pm.subrange(header2_pos as int, header2_pos + header_size) == new_header_bytes,
            new_header_bytes.subrange(header_crc_offset as int, header_crc_offset + 8) == 
                spec_crc_bytes(new_header_bytes.subrange(header_head_offset as int, header_size as int)),
            ({
                let new_header = spec_bytes_to_header(new_header_bytes);
                let live_header = spec_get_live_header(pm);
                &&& new_header.metadata.tail == live_header.metadata.tail + bytes_to_append.len()
                &&& new_header.metadata.head == live_header.metadata.head 
                &&& new_header.metadata.log_size == live_header.metadata.log_size
                &&& new_header.metadata.tail - new_header.metadata.head < new_header.metadata.log_size
            }),
            perm.check_permission(pm),
            permissions_depend_only_on_recovery_view(perm),
            ({
                let live_header = spec_get_live_header(pm);
                let physical_head = spec_addr_logical_to_physical(live_header.metadata.head as int, live_header.metadata.log_size as int);
                let physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);
                let contents_end = (live_header.metadata.log_size + contents_offset) as int;
                let append_size = bytes_to_append.len();
                let len1 = (contents_end - physical_tail);
                let len2 = bytes_to_append.len() - len1;

                &&& physical_tail + append_size >= contents_end ==> {
                    &&& pm.subrange(physical_tail, contents_end) =~= bytes_to_append.subrange(0, len1)
                    &&& pm.subrange(contents_offset as int, contents_offset + len2) =~= bytes_to_append.subrange(len1 as int, append_size as int)
                    &&& bytes_to_append =~= pm.subrange(physical_tail, contents_end) + pm.subrange(contents_offset as int, contents_offset + len2)
                }
                &&& physical_head <= physical_tail && physical_tail + append_size < contents_end ==> {
                    pm.subrange(physical_tail, physical_tail + append_size) =~= bytes_to_append
                }
                &&& physical_tail < physical_head ==> {
                    &&& physical_tail + append_size < physical_head
                    &&& pm.subrange(physical_tail, physical_tail + append_size) =~= bytes_to_append
                }
            }),
            ({
                let old_log_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm);
                forall |pm_state| #[trigger] perm.check_permission(pm_state) <==> {
                    let log_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm_state);
                    log_state == old_log_state || log_state == Some(old_log_state.unwrap().append(bytes_to_append))
                }
            }),
        ensures
            ({
                let ib_bytes = spec_u64_to_le_bytes(new_ib);
                let new_pm = PersistentMemory::update_contents_to_reflect_write(pm, incorruptible_bool_pos as int, ib_bytes);
                let old_log_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm);
                let new_log_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(new_pm);
                let new_live_header = spec_get_live_header(new_pm);
                let (new_pm_ib, _, _) = pm_to_views(new_pm);
                &&& match (old_log_state, new_log_state) {
                        (Some(old_log_state), Some(new_log_state)) => {
                            &&& new_log_state =~= old_log_state.append(bytes_to_append)
                            &&& perm.check_permission(new_pm)
                        }
                        _ => false,
                    }
                &&& new_live_header == spec_bytes_to_header(new_header_bytes)
                &&& new_ib == new_pm_ib
            }),
            forall |chunks_flushed| {
                let new_pm = #[trigger] PersistentMemory::update_contents_to_reflect_partially_flushed_write(
                    pm, incorruptible_bool_pos as int, spec_u64_to_le_bytes(new_ib), chunks_flushed);
                &&& perm.check_permission(new_pm)
            }
    {
        let ib_bytes = spec_u64_to_le_bytes(new_ib);
        let live_header = spec_get_live_header(pm);
        let append_size = bytes_to_append.len();
        let contents_end = live_header.metadata.log_size + contents_offset;
        let physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);

        lemma_auto_spec_u64_to_from_le_bytes();
        lemma_single_write_crash(pm, incorruptible_bool_pos as int, ib_bytes);
        assert(perm.check_permission(pm));

        let new_pm = PersistentMemory::update_contents_to_reflect_write(pm, incorruptible_bool_pos as int, ib_bytes);
        lemma_headers_unchanged(pm, new_pm); 
        assert(new_pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8) =~= ib_bytes);
    
        let new_header = spec_bytes_to_header(new_header_bytes);
        let (ib, headers, data) = pm_to_views(new_pm);
        let header_pos = if new_ib == header1_val {
            header1_pos
        } else {
            header2_pos
        };
        assert(new_pm.subrange(header_pos as int, header_pos + header_size) =~= new_header_bytes);
        lemma_header_match(new_pm, header_pos as int, new_header);
        lemma_header_correct(new_pm, new_header_bytes, header_pos as int);
        
        // prove that new pm has the append update
        let new_log_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(new_pm);
        let old_log_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm);

        match (new_log_state, old_log_state) {
            (Some(new_log_state), Some(old_log_state)) => {
                lemma_pm_state_header(new_pm);
                lemma_pm_state_header(pm);

                let old_header = spec_get_live_header(pm);
                let live_header = spec_get_live_header(new_pm);
                assert(live_header == new_header);
                
                assert(live_header.metadata.head == old_header.metadata.head);
                assert(live_header.metadata.tail == old_header.metadata.tail + bytes_to_append.len());

                let physical_head = spec_addr_logical_to_physical(live_header.metadata.head as int, live_header.metadata.log_size as int);
                let new_physical_tail = spec_addr_logical_to_physical(live_header.metadata.tail as int, live_header.metadata.log_size as int);
                let old_physical_tail = spec_addr_logical_to_physical(old_header.metadata.tail as int, old_header.metadata.log_size as int);
                assert(old_physical_tail == physical_tail);

                let (_, _, old_data) = pm_to_views(pm);
                let (_, _, new_data) = pm_to_views(pm);

                if physical_head <= old_physical_tail {
                    if old_physical_tail + append_size >= contents_end {
                        assert(new_log_state.log =~= new_data.subrange(physical_head - contents_offset, old_physical_tail - contents_offset) + 
                                                    new_data.subrange(old_physical_tail - contents_offset, contents_end - contents_offset) + 
                                                    new_data.subrange(0, new_physical_tail - contents_offset));
                        assert(new_log_state.log =~= old_data.subrange(physical_head - contents_offset, old_physical_tail - contents_offset) + 
                                                    new_data.subrange(old_physical_tail - contents_offset, contents_end - contents_offset) + 
                                                    new_data.subrange(0, new_physical_tail - contents_offset));
                        let len1 = (contents_end - old_physical_tail);
                        let len2 = bytes_to_append.len() - len1;
                        assert(bytes_to_append =~= new_data.subrange(old_physical_tail - contents_offset, contents_end - contents_offset) + 
                                                    new_data.subrange(0, new_physical_tail - contents_offset));
                        assert(new_log_state.log =~= old_data.subrange(physical_head - contents_offset, old_physical_tail - contents_offset) + bytes_to_append);
                    } else {
                        assert(old_data.subrange(0, old_physical_tail - contents_offset) =~= new_data.subrange(0, old_physical_tail - contents_offset));
                        assert(new_data.subrange(old_physical_tail - contents_offset, old_physical_tail - contents_offset + append_size) =~= bytes_to_append);
                    }
                } else { // physical_tail < physical_head 
                    assert(old_physical_tail + append_size < physical_head);
                }
                assert(new_log_state =~= old_log_state.append(bytes_to_append));
                assert(perm.check_permission(new_pm));
            }
            _ => assert(false),
        }
    }

    pub open spec fn live_data_view_eq(old_pm: Seq<u8>, new_pm: Seq<u8>) -> bool 
    {
        let (old_ib, old_headers, old_data) = pm_to_views(old_pm);
        let (new_ib, new_headers, new_data) = pm_to_views(new_pm);
        let old_live_header = spec_get_live_header(old_pm);
        let new_live_header = spec_get_live_header(new_pm);
        let physical_head = spec_addr_logical_to_physical(old_live_header.metadata.head as int, old_live_header.metadata.log_size as int);
        let physical_tail = spec_addr_logical_to_physical(old_live_header.metadata.tail as int, old_live_header.metadata.log_size as int);
        let log_size = old_live_header.metadata.log_size;
        let physical_data_head = physical_head - contents_offset;
        let physical_data_tail = physical_tail - contents_offset;

        &&& new_live_header == old_live_header 
        &&& physical_head < physical_tail ==> 
                old_data.subrange(physical_data_head, physical_data_tail) =~= new_data.subrange(physical_data_head, physical_data_tail)
        &&& physical_tail < physical_head ==> {
                &&& old_data.subrange(physical_data_head as int, log_size as int) =~= new_data.subrange(physical_data_head as int, log_size as int)
                &&& old_data.subrange(0, physical_data_tail as int) =~= new_data.subrange(0, physical_data_tail as int)
        }  
        &&& physical_tail == physical_head ==> 
                physical_data_head == physical_data_tail
    }

    pub proof fn lemma_same_log_state(old_pm: Seq<u8>, new_pm: Seq<u8>)
        requires 
            UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old_pm).is_Some(),
            UntrustedLogImpl::convert_from_pm_contents_to_log_state2(new_pm).is_Some(),
            live_data_view_eq(old_pm, new_pm),
            ({
                let (old_ib, old_headers, old_data) = pm_to_views(old_pm);
                let (new_ib, new_headers, new_data) = pm_to_views(new_pm);
                &&& old_ib == header1_val || old_ib == header2_val
                &&& old_ib == new_ib
                &&& old_ib == header1_val ==> {
                    &&& old_headers.header1 == new_headers.header1
                }
                &&& old_ib == header2_val ==> {
                    &&& old_headers.header2 == new_headers.header2
                }
            })
        ensures 
            UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old_pm) =~= 
                UntrustedLogImpl::convert_from_pm_contents_to_log_state2(new_pm)
    {
        let old_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old_pm);
        let new_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(new_pm);
        let (old_ib, old_headers, old_data) = pm_to_views(old_pm);
        let (new_ib, new_headers, new_data) = pm_to_views(new_pm);

        assert(old_state.is_Some());
        assert(new_state.is_Some());
        match (old_state, new_state) {
            (Some(old_state), Some(new_state)) => {
                let (old_live_header, new_live_header) = if old_ib == header1_val {
                    (old_headers.header1, new_headers.header1)
                } else {
                    (old_headers.header2, new_headers.header2)
                };

                assert(old_state.head == old_live_header.metadata.head);
                assert(new_state.head == new_live_header.metadata.head);
                assert(old_live_header.metadata.tail == new_live_header.metadata.tail);
                let physical_head = spec_addr_logical_to_physical(old_live_header.metadata.head as int, old_live_header.metadata.log_size as int);
                let physical_tail = spec_addr_logical_to_physical(old_live_header.metadata.tail as int, old_live_header.metadata.log_size as int);
                let contents_end = old_live_header.metadata.log_size + contents_offset;

                if physical_head < physical_tail {
                    assert(old_pm.subrange(physical_head, physical_tail) =~= old_data.subrange(physical_head - contents_offset, physical_tail - contents_offset));
                    assert(old_pm.subrange(physical_head, physical_tail) =~= new_pm.subrange(physical_head, physical_tail));
                } else if physical_tail < physical_head {
                    assert(old_pm.subrange(physical_head, contents_end) =~= old_data.subrange(physical_head - contents_offset, contents_end - contents_offset));
                    assert(old_pm.subrange(contents_offset as int, physical_tail) =~= old_data.subrange(contents_offset - contents_offset, physical_tail - contents_offset));
                    assert(old_pm.subrange(physical_head, contents_end) + old_pm.subrange(contents_offset as int, physical_tail) =~=
                        new_pm.subrange(physical_head, contents_end) + new_pm.subrange(contents_offset as int, physical_tail));
                } else {
                    assert(physical_head == physical_tail);
                    assert(old_state.log.len() == 0);
                    assert(new_state.log.len() == 0);
                }
            }   
            _ => assert(false),
        }
    }

    pub proof fn lemma_subrange_equality_implies_index_equality<T>(s1: Seq<T>, s2: Seq<T>, i: int, j: int)
        requires
            0 <= i <= j <= s1.len(),
            j <= s2.len(),
            s1.subrange(i, j) == s2.subrange(i, j)
        ensures
            forall |k| i <= k < j ==> s1[k] == s2[k]
    {
        assert forall |k| i <= k < j implies s1[k] == s2[k] by {
            // Trigger axiom_seq_subrange_index
            assert (s1[k] == s1.subrange(i, j)[k - i]);
            assert (s2[k] == s2.subrange(i, j)[k - i]);
        }
    }

    pub proof fn lemma_subrange_equality_implies_subsubrange_equality<T>(s1: Seq<T>, s2: Seq<T>, i: int, j: int)
        requires
            0 <= i <= j <= s1.len(),
            j <= s2.len(),
            s1.subrange(i, j) == s2.subrange(i, j)
        ensures
            forall |k, m| i <= k <= m <= j ==> s1.subrange(k, m) == s2.subrange(k, m)
    {
        lemma_subrange_equality_implies_index_equality(s1, s2, i, j);
        assert forall |k, m| i <= k <= m <= j implies s1.subrange(k, m) == s2.subrange(k, m) by {
            assert (s1.subrange(k, m) =~= s2.subrange(k, m));
        }
    }

    pub proof fn lemma_subrange_equality_implies_subsubrange_equality_forall<T>()
        ensures
            forall |s1: Seq<T>, s2: Seq<T>, i: int, j: int, k: int, m: int|
                {
                    &&& 0 <= i <= j <= s1.len()
                    &&& j <= s2.len()
                    &&& s1.subrange(i, j) == s2.subrange(i, j)
                    &&& i <= k <= m <= j
                }
                ==> s1.subrange(k, m) == s2.subrange(k, m)
    {
        assert forall |s1: Seq<T>, s2: Seq<T>, i: int, j: int, k: int, m: int|
                   {
                       &&& 0 <= i <= j <= s1.len()
                       &&& j <= s2.len()
                       &&& s1.subrange(i, j) == s2.subrange(i, j)
                       &&& i <= k <= m <= j
                   }
                   implies s1.subrange(k, m) == s2.subrange(k, m) by {
            lemma_subrange_equality_implies_subsubrange_equality(s1, s2, i, j);
        }
    }

    pub proof fn lemma_headers_unchanged(old_pm: Seq<u8>, new_pm: Seq<u8>) 
        requires
            old_pm.len() == new_pm.len(),
            old_pm.len() >= contents_offset,
            old_pm.subrange(header1_pos as int, header1_pos + header_size) =~= new_pm.subrange(header1_pos as int, header1_pos + header_size),
            old_pm.subrange(header2_pos as int, header2_pos + header_size) =~= new_pm.subrange(header2_pos as int, header2_pos + header_size),
        ensures 
            ({
                let (_, old_headers, _) = pm_to_views(old_pm);
                let (_, new_headers, _) = pm_to_views(new_pm);
                old_headers == new_headers 
            })
    {
        lemma_subrange_equality_implies_subsubrange_equality_forall::<u8>();
    }

    pub proof fn lemma_incorruptible_bool_unchanged(old_pm: Seq<u8>, new_pm: Seq<u8>)
        requires 
            old_pm.len() == new_pm.len(),
            old_pm.len() >= contents_offset,
            old_pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8) =~= new_pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8)
        ensures 
            ({
                let (old_ib, _, _) = pm_to_views(old_pm);
                let (new_ib, _, _) = pm_to_views(new_pm);
                old_ib == new_ib 
            })
    {}

    pub proof fn lemma_header_crc_correct(header_bytes: Seq<u8>, crc_bytes: Seq<u8>, metadata_bytes: Seq<u8>) 
        requires
            header_bytes.len() == header_size,
            crc_bytes.len() == 8,
            metadata_bytes.len() == header_size - 8,
            crc_bytes =~= spec_crc_bytes(metadata_bytes),
            header_bytes =~= crc_bytes + metadata_bytes 
        ensures 
            header_bytes.subrange(header_crc_offset as int, header_crc_offset + 8) =~= crc_bytes,
            header_bytes.subrange(header_head_offset as int, header_size as int) =~= metadata_bytes,
            header_bytes.subrange(header_crc_offset as int, header_crc_offset + 8) =~=
                spec_crc_bytes(header_bytes.subrange(header_head_offset as int, header_size as int))
    {
        assert(header_bytes.subrange(header_crc_offset as int, header_crc_offset + 8) =~= crc_bytes);
        assert(header_bytes.subrange(header_head_offset as int, header_size as int) =~= metadata_bytes);
    }

    pub proof fn lemma_header_correct(pm: Seq<u8>, header_bytes: Seq<u8>, header_pos: int)
        requires 
            pm.len() > contents_offset,
            header_bytes.len() == header_size,
            header_pos == header1_pos || header_pos == header2_pos,
            header_bytes.subrange(header_crc_offset as int, header_crc_offset + 8) =~= 
                spec_crc_bytes(header_bytes.subrange(header_head_offset as int, header_size as int)),
            pm.subrange(header_pos, header_pos + header_size) =~= header_bytes            
        ensures 
            pm.subrange(header_pos + header_crc_offset, header_pos + header_crc_offset + 8) =~= 
                header_bytes.subrange(header_crc_offset as int, header_crc_offset + 8),
            pm.subrange(header_pos + header_head_offset, header_pos + header_size) =~= 
                header_bytes.subrange(header_head_offset as int, header_size as int),
            pm.subrange(header_pos + header_crc_offset, header_pos + header_crc_offset + 8) =~= 
                spec_crc_bytes(pm.subrange(header_pos + header_head_offset, header_pos + header_size))
    {
        assert(pm.subrange(header_pos + header_crc_offset, header_pos + header_crc_offset + 8) =~= 
            header_bytes.subrange(header_crc_offset as int, header_crc_offset + 8));
        assert(pm.subrange(header_pos + header_head_offset, header_pos + header_size) =~= 
            header_bytes.subrange(header_head_offset as int, header_size as int));
    }
    
    pub proof fn lemma_u64_bytes_eq(val1: u64, val2: u64) 
        requires 
            val1 == val2
        ensures 
            spec_u64_to_le_bytes(val1) =~= spec_u64_to_le_bytes(val2)
    {}

    pub proof fn lemma_subrange_index(bytes: Seq<u8>, start: int, end: int)
        requires 
            0 <= start < end < bytes.len()
        ensures 
            forall |i: int| 0 <= i < (end - start) ==> bytes.subrange(start, end)[i] == bytes[start + i]
    {}  

    pub proof fn lemma_subrange_eq<T>(bytes1: Seq<T>, bytes2: Seq<T>)
        requires 
            bytes1 =~= bytes2
        ensures 
            forall |i: int, j: int| 0 <= i < j < bytes1.len() ==> bytes1.subrange(i, j) =~= bytes2.subrange(i, j)
    {}

    /// If our write is persistence_chunk_size-sized and -aligned, then there are only 2 possible
    /// resulting crash states, one with the write and one without.
    pub proof fn lemma_single_write_crash(pm: Seq<u8>, write_addr: int, bytes_to_write: Seq<u8>)
        requires
            bytes_to_write.len() == persistence_chunk_size,
            write_addr % persistence_chunk_size == 0, // currently seems to succeed without nonlinear arith
            0 <= write_addr < pm.len(),
            write_addr + bytes_to_write.len() <= pm.len()
        ensures
            ({
                forall |chunks_flushed: Set<int>| {
                    let new_crash_contents = #[trigger] PersistentMemory::update_contents_to_reflect_partially_flushed_write(
                                                            pm, write_addr, bytes_to_write, chunks_flushed);
                    let new_contents = PersistentMemory::update_contents_to_reflect_write(pm, write_addr, bytes_to_write);
                    new_crash_contents =~= pm || new_crash_contents =~= new_contents
                }
            })
    {}

    pub proof fn lemma_pm_state_header(pm: Seq<u8>)
        requires 
            UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm).is_Some(),
            ({
                let header = spec_get_live_header(pm);
                header.metadata.tail - header.metadata.head < header.metadata.log_size
            })
        ensures 
            ({
                let pm_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm);
                let header = spec_get_live_header(pm);
                match pm_state {
                    Some(pm_state) => {
                        &&& header.metadata.head == pm_state.head
                        &&& pm_state.log.len() == header.metadata.tail - header.metadata.head
                    }
                    None => false 
                }
            })
    {
        let pm_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm);
        let header = spec_get_live_header(pm);
        lemma_mod_range(header.metadata.head as int, header.metadata.log_size as int);
        lemma_mod_range(header.metadata.tail as int, header.metadata.log_size as int);
        let head = header.metadata.head as int;
        let tail = header.metadata.tail as int;
        let log_size = header.metadata.log_size as int;
        let physical_head = spec_addr_logical_to_physical(head, log_size);
        let physical_tail = spec_addr_logical_to_physical(tail, log_size);
        match pm_state {
            Some(pm_state) => {
                if physical_head < physical_tail {
                    // log does not wrap 
                    lemma_mod_difference_equal(head, tail, log_size);
                } else if physical_tail < physical_head {
                    // log wraps 
                    lemma_mod_wrapped_len(head, tail, log_size);
                } else {
                    // size is 0
                    lemma_mod_equal(head, tail, log_size);
                }
            }
            None => assert(false),
        }
    }

    pub open spec fn spec_addr_logical_to_physical(addr: int, log_size: int) -> int {
        (addr % log_size) + contents_offset
    }

    pub struct UntrustedLogImpl {
        pub incorruptible_bool: u64,
        // header fields are stored separately because of limitations
        // on deriving Copy/Clone for the header structures
        pub header_crc: u64,
        pub head: u64,
        pub tail: u64,
        pub log_size: u64,
    }

    // offset of actual log contents from the beginning of the device
    pub const contents_offset: u64 = header2_pos + header_log_size_offset + 8;

    impl UntrustedLogImpl {

        pub exec fn addr_logical_to_physical(addr: u64, log_size: u64) -> (out: u64)
            requires
                addr <= u64::MAX,
                log_size > 0,
                log_size + contents_offset <= u64::MAX,
            ensures
                out == spec_addr_logical_to_physical(addr as int, log_size as int)
        {
            (addr % log_size) + contents_offset
        }

        pub open spec fn log_state_is_valid2(pm: Seq<u8>) -> bool {
            let (ib, headers, data) = pm_to_views(pm);
            let live_header = if ib == header1_val {
                headers.header1 
            } else {
                headers.header2
            };

            let head = live_header.metadata.head as int;
            let tail = live_header.metadata.tail as int;
            let log_size = live_header.metadata.log_size as int;

            &&& ib == header1_val || ib == header2_val
            &&& crc_size == 8
            &&& log_size + contents_offset <= u64::MAX
            &&& log_size > 0
            &&& log_size + contents_offset == pm.len()
            &&& tail - head < log_size
            &&& ib == header1_val ==> {
                    &&& live_header.crc == spec_u64_from_le_bytes(spec_crc_bytes(pm.subrange(header1_pos + header_head_offset, header1_pos + header_size)))
                    &&& pm.subrange(header1_pos + header_crc_offset, header1_pos + header_crc_offset + 8) =~= spec_crc_bytes(pm.subrange(header1_pos + header_head_offset, header1_pos + header_size))
                }
            &&& ib == header2_val ==> {
                &&& live_header.crc == spec_u64_from_le_bytes(spec_crc_bytes(pm.subrange(header2_pos + header_head_offset, header2_pos + header_size)))
                &&& pm.subrange(header2_pos + header_crc_offset, header2_pos + header_crc_offset + 8) =~= spec_crc_bytes(pm.subrange(header2_pos + header_head_offset, header2_pos + header_size))
            }
            &&& head <= tail
        }

        pub open spec fn convert_from_pm_contents_to_log_state2(pm: Seq<u8>) -> Option<AbstractInfiniteLogState> 
        {
            let (ib, headers, data) = pm_to_views(pm);
            if !Self::log_state_is_valid2(pm) {
                None
            } else {
                let live_header = if ib == header1_val {
                    headers.header1 
                } else {
                    headers.header2
                };

                let head = live_header.metadata.head as int;
                let tail = live_header.metadata.tail as int;
                let log_size = live_header.metadata.log_size as int;
                let contents_end = log_size + contents_offset;
                let physical_head = spec_addr_logical_to_physical(head, log_size);
                let physical_tail = spec_addr_logical_to_physical(tail, log_size);
                
                let abstract_log = if physical_head < physical_tail {
                    pm.subrange(physical_head, physical_tail)
                } else if physical_tail < physical_head {
                    let range1 = pm.subrange(physical_head, contents_end);
                    let range2 = pm.subrange(contents_offset as int, physical_tail);
                    range1 + range2 
                } else {
                    Seq::empty()
                };

                Some(AbstractInfiniteLogState { head: head, log: abstract_log, capacity: log_size - 1 })
            }
        }

        pub open spec fn consistent_with_pm2(self, pm: Seq<u8>) -> bool 
        {
            let (ib, headers, data) = pm_to_views(pm);
            match UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm) {
                Some(inf_log) => {
                    let header_pos = if ib == header1_val {
                        header1_pos
                    } else {
                        header2_pos
                    };
                    let header = spec_get_live_header(pm);
                    let head = header.metadata.head;
                    let tail = header.metadata.tail;
                    let log_size = header.metadata.log_size;

                    &&& self.incorruptible_bool == header1_val || self.incorruptible_bool == header2_val
                    &&& ib == header1_val || ib == header2_val 
                    &&& spec_crc_bytes(pm.subrange(header_pos + header_head_offset, header_pos + header_size)) =~= 
                                pm.subrange(header_pos + header_crc_offset, header_pos + header_crc_offset + 8)
                    &&& log_size + contents_offset <= u64::MAX 
                    &&& log_size > 0 
                    &&& tail == head + inf_log.log.len()
                    &&& tail - head < log_size
                    &&& log_size + contents_offset == pm.len()
                    &&& self.header_crc == header.crc
                    &&& self.head == head 
                    &&& self.tail == tail 
                    &&& self.log_size == log_size 
                    &&& self.incorruptible_bool == ib   
                }
                None => false
            }
        }

        pub exec fn read_incorruptible_boolean(pm: &PersistentMemory) -> (result: Result<u64, InfiniteLogErr>)
            requires 
                UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm@).is_Some(),
                pm@.len() > contents_offset 
            ensures 
                match result {
                    Ok(ib) => {
                        let (spec_ib, _, _) = pm_to_views(pm@);
                        ib == spec_ib
                    }
                    Err(InfiniteLogErr::CRCMismatch) => !pm.impervious_to_corruption(),
                    _ => false,
                }
        {
            let (bytes, addrs) = pm.read(incorruptible_bool_pos, 8);
            let ib = u64_from_le_bytes(bytes.as_slice());
            if ib == header1_val || ib == header2_val {
                proof {
                    let (spec_ib, _, _) = pm_to_views(pm@);
                    lemma_auto_spec_u64_to_from_le_bytes();
                    axiom_incorruptible_bool(spec_ib, ib);
                }
                Ok(ib)
            } else {
                Err(InfiniteLogErr::CRCMismatch)
            }
        }

        exec fn update_header<P: CheckPermission<Seq<u8>>> (
            &mut self,
            wrpm: &mut WriteRestrictedPersistentMemory<P>,
            Tracked(perm): Tracked<&P>,
            new_header_bytes: &Vec<u8>
        )
            requires 
                permissions_depend_only_on_recovery_view(perm),
                contents_offset < old(wrpm)@.len(),
                old(self).consistent_with_pm2(old(wrpm)@),
                UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old(wrpm)@).is_Some(),
                new_header_bytes@.subrange(header_crc_offset as int, header_crc_offset + 8) =~= 
                    spec_crc_bytes(new_header_bytes@.subrange(header_head_offset as int, header_size as int)),
                new_header_bytes.len() == header_size,
                match UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old(wrpm)@) {
                    Some(log_state) => perm.check_permission(old(wrpm)@),
                    None => false
                }
            ensures 
                self.consistent_with_pm2(wrpm@),
                UntrustedLogImpl::convert_from_pm_contents_to_log_state2(wrpm@).is_Some(),
                wrpm.impervious_to_corruption() == old(wrpm).impervious_to_corruption(),
                match (UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old(wrpm)@), UntrustedLogImpl::convert_from_pm_contents_to_log_state2(wrpm@)) {
                    (Some(old_log_state), Some(new_log_state)) => old_log_state =~= new_log_state,
                    _ => false
                },
                ({
                    let (old_pm_ib, old_metadata, old_data) = pm_to_views(old(wrpm)@);
                    let (new_pm_ib, new_metadata, new_data) = pm_to_views(wrpm@);
                    let new_header = spec_bytes_to_header(new_header_bytes@);
                    &&& old_pm_ib == new_pm_ib 
                    &&& old_pm_ib == header1_val ==> {
                        &&& new_metadata.header1 == old_metadata.header1
                        &&& new_metadata.header2 == new_header
                        &&& wrpm@.subrange(header2_pos + header_crc_offset, header2_pos + header_crc_offset + 8) =~= 
                                spec_crc_bytes(wrpm@.subrange(header2_pos + header_head_offset, header2_pos + header_size))
                        &&& wrpm@.subrange(header2_pos as int, header2_pos + header_size) =~= new_header_bytes@
                    }
                    &&& old_pm_ib == header2_val ==> {
                        &&& new_metadata.header1 == new_header
                        &&& new_metadata.header2 == old_metadata.header2
                        &&& wrpm@.subrange(header1_pos + header_crc_offset, header1_pos + header_crc_offset + 8) =~= 
                                spec_crc_bytes(wrpm@.subrange(header1_pos + header_head_offset, header1_pos + header_size))
                        &&& wrpm@.subrange(header1_pos as int, header1_pos + header_size) =~= new_header_bytes@
                    }
                    &&& old_data =~= new_data
                }),
                
        {
            let ghost original_wrpm = wrpm@;

            // write to the header that is NOT pointed to by the IB
            let header_pos = if self.incorruptible_bool == header1_val {
                header2_pos 
            } else {
                header1_pos 
            };

            // TODO: we could probably roll all of this into a single lemma that contains all of the proofs
            proof {
                let new_pm = PersistentMemory::update_contents_to_reflect_write(wrpm@, header_pos as int, new_header_bytes@);
                lemma_inactive_header_update_view(wrpm@, new_header_bytes@, header_pos as int);
                lemma_same_log_state(wrpm@, new_pm);
                assert(UntrustedLogImpl::convert_from_pm_contents_to_log_state2(wrpm@) =~= UntrustedLogImpl::convert_from_pm_contents_to_log_state2(new_pm));
                
                // prove crash consistency
                assert forall |chunks_flushed| {
                    let new_pm = #[trigger] PersistentMemory::update_contents_to_reflect_partially_flushed_write(
                        wrpm@, header_pos as int, new_header_bytes@, chunks_flushed);
                    perm.check_permission(new_pm)
                } by {
                    let new_pm = PersistentMemory::update_contents_to_reflect_partially_flushed_write(
                        wrpm@, header_pos as int, new_header_bytes@, chunks_flushed);
                    lemma_inactive_header_update_view_crash(wrpm@, new_header_bytes@, header_pos as int, chunks_flushed);
                    lemma_same_log_state(wrpm@, new_pm);
                    assert(permissions_depend_only_on_recovery_view(perm));
                    lemma_same_permissions(wrpm@, new_pm, perm);
                }
            }
            wrpm.write(header_pos, new_header_bytes.as_slice(), Tracked(perm));
            proof {
                // TODO: clean up once ib update is done. put this all in a lemma
                assert(UntrustedLogImpl::convert_from_pm_contents_to_log_state2(wrpm@).is_Some());
                let (_, headers, _) = pm_to_views(wrpm@);
                assert(wrpm@.subrange(header_pos as int, header_pos + header_size) =~= new_header_bytes@);
                lemma_header_correct(wrpm@, new_header_bytes@, header_pos as int);

                // live header is unchanged 
                let live_header_pos = if header_pos == header1_pos {
                    header2_pos
                } else {
                    assert(header_pos == header2_pos);
                    header1_pos
                };

                // TODO: refactor into a lemma (ideally lemma_header_correct)
                assert(old(wrpm)@.subrange(live_header_pos as int, live_header_pos + header_size) =~= 
                        wrpm@.subrange(live_header_pos as int, live_header_pos + header_size));
                assert(old(wrpm)@.subrange(live_header_pos + header_crc_offset, live_header_pos + header_crc_offset + 8) =~= 
                    spec_crc_bytes(old(wrpm)@.subrange(live_header_pos + header_head_offset, live_header_pos + header_size)));
                assert(old(wrpm)@.subrange(live_header_pos + header_crc_offset, live_header_pos + header_crc_offset + 8) =~= 
                    wrpm@.subrange(live_header_pos + header_crc_offset, live_header_pos + header_crc_offset + 8));
                assert(old(wrpm)@.subrange(live_header_pos + header_head_offset, live_header_pos + header_size) =~= 
                    wrpm@.subrange(live_header_pos + header_head_offset, live_header_pos + header_size));

                assert(wrpm@.subrange(live_header_pos + header_crc_offset, live_header_pos + header_crc_offset + 8) =~= 
                    spec_crc_bytes(wrpm@.subrange(live_header_pos + header_head_offset, live_header_pos + header_size)));
            }
        }

        // Since untrusted_setup doesn't take a WriteRestrictedPersistentMemory, it is not guaranteed
        // to perform crash-safe updates.
        pub exec fn untrusted_setup(pm: &mut PersistentMemory) -> (result: Result<u64, InfiniteLogErr>)
            ensures
                match result {
                    Ok(capacity) => UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm@) ==
                                Some(AbstractInfiniteLogState::initialize(capacity as int)),
                    Err(InfiniteLogErr::InsufficientSpaceForSetup{ required_space }) => pm@.len() < required_space,
                    _ => false
                }
        {
            let device_size = pm.get_capacity();
            if device_size <= contents_offset {
                return Err(InfiniteLogErr::InsufficientSpaceForSetup { required_space: device_size + 1 });
            }

            let log_size = device_size - contents_offset;
            
            let log_header_metadata = PersistentHeaderMetadata {
                head: 0,
                tail: 0,
                log_size
            };
            let metadata_bytes = metadata_to_bytes(&log_header_metadata);
            let crc_bytes = bytes_crc(&metadata_bytes);
            let log_header = PersistentHeader {
                crc: u64_from_le_bytes(crc_bytes.as_slice()),
                metadata: log_header_metadata,
            };
            let header_bytes = header_to_bytes(&log_header);
            
            let initial_ib_bytes = u64_to_le_bytes(header1_val);
            pm.write(header1_pos, header_bytes.as_slice());
            pm.write(incorruptible_bool_pos, initial_ib_bytes.as_slice());

            proof {
                lemma_auto_spec_u64_to_from_le_bytes();
                assert(pm@.subrange(header1_pos as int, header1_pos + header_size) =~= header_bytes@);
                assert(pm@.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8) =~= initial_ib_bytes@);
                lemma_header_split_into_bytes(crc_bytes@, metadata_bytes@, header_bytes@);
                assert(pm@.subrange(header1_pos + header_head_offset, header1_pos + header_size) =~= metadata_bytes@);
                lemma_header_match(pm@, header1_pos as int, log_header);
                let log_state = Self::convert_from_pm_contents_to_log_state2(pm@);
                match log_state {
                    Some(log_state) => {
                        assert(log_state.head == 0);
                        assert(log_state.log == Seq::<u8>::empty());
                        assert(log_state.capacity == log_size - 1);
                    }
                    None => assert(false),
                }
            }

            Ok(log_size - 1)
        }

        pub exec fn untrusted_start<P>(wrpm: &mut WriteRestrictedPersistentMemory<P>, Tracked(perm): Tracked<&P>)
                                       -> (result: Result<UntrustedLogImpl, InfiniteLogErr>)
            where
                P: CheckPermission<Seq<u8>>,
            requires
                UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old(wrpm)@).is_Some(),
                header_crc_offset < header_crc_offset + crc_size <= header_head_offset < header_tail_offset < header_log_size_offset,
                // The restriction on writing persistent memory during initialization is
                // that it can't change the interpretation of that memory's contents.
                ({
                    forall |pm_state| #[trigger] perm.check_permission(pm_state) <==>
                        UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm_state) ==
                        UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old(wrpm)@)
                }),
            ensures
                UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old(wrpm)@) == UntrustedLogImpl::convert_from_pm_contents_to_log_state2(wrpm@),
                wrpm.impervious_to_corruption() == old(wrpm).impervious_to_corruption(),
                match result {
                    Ok(log_impl) => log_impl.consistent_with_pm2(wrpm@),
                    Err(InfiniteLogErr::CRCMismatch) => !old(wrpm).impervious_to_corruption(),
                    _ => false
                }
        {
            let pm = wrpm.get_pm_ref();
            let device_size = pm.get_capacity();
            assert (device_size >= contents_offset);

            let ib = match Self::read_incorruptible_boolean(pm) {
                Ok(ib) => ib,
                Err(e) => return Err(e)
            };

            let header_pos = if ib == header1_val {
                header1_pos
            } else {
                assert(ib == header2_val);
                header2_pos
            };
            let (mut crc_bytes, crc_addrs) = pm.read(header_pos + header_crc_offset, 8);
            let (mut header_bytes, header_addrs) = pm.read(header_pos + header_head_offset, header_size - header_head_offset);
            
            let header = if u64_from_le_bytes(bytes_crc(&header_bytes).as_slice()) == u64_from_le_bytes(crc_bytes.as_slice()) { 
                proof {
                    lemma_auto_spec_u64_to_from_le_bytes();
                    lemma_u64_bytes_eq(spec_u64_from_le_bytes(spec_crc_bytes(header_bytes@)), spec_u64_from_le_bytes(crc_bytes@));
                    axiom_bytes_uncorrupted(
                        header_bytes@,
                        pm@.subrange(header_pos + header_head_offset, header_pos + header_size),
                        header_addrs@,
                        crc_bytes@,
                        pm@.subrange(header_pos + header_crc_offset, header_pos + header_crc_offset + 8),
                        crc_addrs@
                    );
                }
                crc_and_metadata_bytes_to_header(crc_bytes.as_slice(), header_bytes.as_slice())
            } else {
                return Err(InfiniteLogErr::CRCMismatch);
            };

            let head = header.metadata.head;
            let tail = header.metadata.tail;
            let log_size = header.metadata.log_size;
            // check log validity now that we have its uncorrupted metadata
            if device_size != log_size + contents_offset ||
                head > tail ||
                tail - head >= log_size 
            {
                return Err(InfiniteLogErr::InvalidHeader { head: head, tail: tail, log_size: log_size });
            }

            let untrusted_log = UntrustedLogImpl {
                incorruptible_bool: ib,
                header_crc: u64_from_le_bytes(crc_bytes.as_slice()),
                head,
                tail,
                log_size
            };

            proof { lemma_pm_state_header(pm@); }
            Ok(untrusted_log)
        }

        pub exec fn untrusted_append<P>(
            &mut self,
            wrpm: &mut WriteRestrictedPersistentMemory<P>,
            bytes_to_append: &Vec<u8>,
            Tracked(perm): Tracked<&P>
        ) -> (result: Result<u64, InfiniteLogErr>)
            where
                P: CheckPermission<Seq<u8>>
            requires
                old(self).consistent_with_pm2(old(wrpm)@),
                UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old(wrpm)@).is_Some(),
                ({
                    let old_log_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old(wrpm)@);
                    forall |pm_state| #[trigger] perm.check_permission(pm_state) <==> {
                        let log_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm_state);
                        log_state == old_log_state || log_state == Some(old_log_state.unwrap().append(bytes_to_append@))
                    }
                }),
            ensures
                self.untrusted_append_postcond(result, old(wrpm)@, wrpm@, bytes_to_append@),
                wrpm.impervious_to_corruption() == old(wrpm).impervious_to_corruption()
        {
            assert(permissions_depend_only_on_recovery_view(perm));

            let pm = wrpm.get_pm_ref();
            let ghost original_pm = wrpm@;

            let physical_head = Self::addr_logical_to_physical(self.head, self.log_size);
            let physical_tail = Self::addr_logical_to_physical(self.tail, self.log_size);
            let contents_end = self.log_size + contents_offset;
            let append_size: u64 = bytes_to_append.len() as u64;
            let old_logical_tail = self.tail;

            if self.tail > u64::MAX - append_size {
                Err(InfiniteLogErr::InsufficientSpaceForAppend{ available_space: u64::MAX - self.tail })
            }
            else if append_size >= self.log_size - (self.tail - self.head) {
                Err(InfiniteLogErr::InsufficientSpaceForAppend{ available_space: self.log_size - 1 - (self.tail - self.head) })
            } else {
                let mut header_metadata =
                    PersistentHeaderMetadata { head: self.head, tail: self.tail, log_size: self.log_size };
                assert(header_metadata == spec_get_live_header(wrpm@).metadata);

                if physical_head <= physical_tail {
                    if physical_tail >= contents_end - append_size {
                        // wrap case
                        self.append_wrap(wrpm, bytes_to_append, &header_metadata, Tracked(perm));
                    } else {
                        // no wrap
                        self.append_no_wrap(wrpm, bytes_to_append, &header_metadata, Tracked(perm));
                    }
                } else { // physical_tail < physical_head
                    if physical_tail + append_size >= physical_head {
                        return Err(InfiniteLogErr::InsufficientSpaceForAppend { available_space: physical_head - physical_tail });
                    }
                    // no wrap
                    self.append_no_wrap(wrpm, bytes_to_append, &header_metadata, Tracked(perm));
                }

                let new_tail = self.tail + append_size;
                header_metadata.tail = new_tail;

                let mut metadata_bytes = metadata_to_bytes(&header_metadata);
                let new_crc_bytes = bytes_crc(&metadata_bytes);
                let new_crc_val = u64_from_le_bytes(new_crc_bytes.as_slice());
                let ghost old_metadata_bytes = metadata_bytes@;
                let mut new_header_bytes = new_crc_bytes;
                new_header_bytes.append(&mut metadata_bytes);
                
                proof { lemma_header_crc_correct(new_header_bytes@, new_crc_bytes@, old_metadata_bytes); }

                self.update_header(wrpm, Tracked(perm), &new_header_bytes);

                // update incorruptible boolean
                let old_ib = self.incorruptible_bool;
                let new_ib = if old_ib == header1_val {
                    header2_val 
                } else {
                    assert(old_ib == header2_val);
                    header1_val
                };
                let new_ib_bytes = u64_to_le_bytes(new_ib);

                proof {
                    lemma_append_ib_update(wrpm@, new_ib, bytes_to_append@, new_header_bytes@, perm);
                }

                wrpm.write(incorruptible_bool_pos, new_ib_bytes.as_slice(), Tracked(perm));
                self.incorruptible_bool = new_ib;
                self.tail = new_tail;
                self.header_crc = new_crc_val;

                Ok(old_logical_tail)
            }
        }

        pub open spec fn untrusted_append_postcond(&self, result: Result<u64, InfiniteLogErr>, old_pm: Seq<u8>, new_pm: Seq<u8>, bytes_appended: Seq<u8>) -> bool 
        {
            let old_log_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old_pm);
            let new_log_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(new_pm);
            &&& self.consistent_with_pm2(new_pm)    
            &&& match (result, old_log_state, new_log_state) {
                (Ok(offset), Some(old_log_state), Some(new_log_state)) => {
                    &&& offset as nat == old_log_state.log.len() + old_log_state.head
                    &&& new_log_state == old_log_state.append(bytes_appended)
                },
                (Err(InfiniteLogErr::InsufficientSpaceForAppend{ available_space }), _, _) => {
                    &&& new_log_state == old_log_state
                    &&& available_space < bytes_appended.len()
                    &&& {
                           let log = old_log_state.unwrap();
                           ||| available_space == log.capacity - log.log.len()
                           ||| available_space == u64::MAX - log.head - log.log.len()
                       }
                },
                (_, _, _) => false
            }
        }

        exec fn append_no_wrap<P>(
            &mut self,
            wrpm: &mut WriteRestrictedPersistentMemory<P>,
            bytes_to_append: &Vec<u8>,
            old_header: &PersistentHeaderMetadata,
            Tracked(perm): Tracked<&P>
        ) 
            where 
                P: CheckPermission<Seq<u8>>,
            requires 
                permissions_depend_only_on_recovery_view(perm),
                perm.check_permission(old(wrpm)@),
                old(self).consistent_with_pm2(old(wrpm)@),
                UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old(wrpm)@).is_Some(),
                old_header == spec_get_live_header(old(wrpm)@).metadata,
                // TODO: clean up
                ({
                    let physical_tail = spec_addr_logical_to_physical(old_header.tail as int, old_header.log_size as int);
                    physical_tail + bytes_to_append@.len() < old_header.log_size + contents_offset
                }),
                ({
                    let physical_head = spec_addr_logical_to_physical(old_header.head as int, old_header.log_size as int);
                    let physical_tail = spec_addr_logical_to_physical(old_header.tail as int, old_header.log_size as int);
                    let contents_end = old_header.log_size + contents_offset;
                    &&& physical_head <= physical_tail ==> physical_tail + bytes_to_append@.len() < contents_end
                    &&& physical_tail < physical_head ==> physical_tail <= physical_tail + bytes_to_append@.len() < physical_head 
                })
            ensures 
                self.consistent_with_pm2(wrpm@),
                UntrustedLogImpl::convert_from_pm_contents_to_log_state2(wrpm@).is_Some(),
                wrpm.impervious_to_corruption() == old(wrpm).impervious_to_corruption(),
                match (UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old(wrpm)@), UntrustedLogImpl::convert_from_pm_contents_to_log_state2(wrpm@)) {
                    (Some(old_log_state), Some(new_log_state)) => old_log_state =~= new_log_state,
                    _ => false
                },
                ({
                    let (old_ib, old_headers, old_data) = pm_to_views(old(wrpm)@);
                    let (new_ib, new_headers, new_data) = pm_to_views(wrpm@);
                    let physical_tail = spec_addr_logical_to_physical(old_header.tail as int, old_header.log_size as int);
                    &&& old_ib == new_ib 
                    &&& old_headers == new_headers
                    &&& new_data.subrange(physical_tail - contents_offset, physical_tail - contents_offset + bytes_to_append@.len() as int) =~= bytes_to_append@
                    &&& new_data.subrange(0, physical_tail - contents_offset) =~= old_data.subrange(0, physical_tail - contents_offset)
                    &&& new_data.subrange(physical_tail - contents_offset + bytes_to_append@.len(), new_data.len() as int) =~= 
                            old_data.subrange(physical_tail - contents_offset + bytes_to_append@.len(), old_data.len() as int)
                })
        {
            let physical_tail = Self::addr_logical_to_physical(old_header.tail, old_header.log_size);
            proof { lemma_data_write_is_safe(wrpm@, bytes_to_append@, physical_tail as int, perm); }
            wrpm.write(physical_tail, bytes_to_append.as_slice(), Tracked(perm));
            proof {
                assert(wrpm@.subrange(0, physical_tail as int) =~= old(wrpm)@.subrange(0, physical_tail as int));
                lemma_subrange_equality_implies_subsubrange_equality(wrpm@, old(wrpm)@, 0, physical_tail as int);
            }   
        }

        pub exec fn append_wrap<P>(
            &mut self,
            wrpm: &mut WriteRestrictedPersistentMemory<P>,
            bytes_to_append: &Vec<u8>,
            old_header: &PersistentHeaderMetadata,
            Tracked(perm): Tracked<&P>
        )
            where 
                P: CheckPermission<Seq<u8>>,
            requires 
                permissions_depend_only_on_recovery_view(perm),
                perm.check_permission(old(wrpm)@),
                old(self).consistent_with_pm2(old(wrpm)@),
                UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old(wrpm)@).is_Some(),
                old_header == spec_get_live_header(old(wrpm)@).metadata,
                ({
                    let physical_head = spec_addr_logical_to_physical(old_header.head as int, old_header.log_size as int);
                    let physical_tail = spec_addr_logical_to_physical(old_header.tail as int, old_header.log_size as int);
                    let contents_end = old_header.log_size + contents_offset;
                    &&& contents_offset < physical_head
                    &&& physical_tail + bytes_to_append@.len() >= contents_end
                    &&& physical_head <= physical_tail
                    &&& bytes_to_append@.len() <= old_header.log_size - (old_header.tail - old_header.head)
                }),
            ensures 
                self.consistent_with_pm2(wrpm@),
                UntrustedLogImpl::convert_from_pm_contents_to_log_state2(wrpm@).is_Some(),
                wrpm.impervious_to_corruption() == old(wrpm).impervious_to_corruption(),
                match (UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old(wrpm)@), UntrustedLogImpl::convert_from_pm_contents_to_log_state2(wrpm@)) {
                    (Some(old_log_state), Some(new_log_state)) => old_log_state =~= new_log_state,
                    _ => false
                },
                ({
                    let (old_ib, old_headers, old_data) = pm_to_views(old(wrpm)@);
                    let (new_ib, new_headers, new_data) = pm_to_views(wrpm@);
                    let contents_end = old_header.log_size + contents_offset;
                    let physical_tail = spec_addr_logical_to_physical(old_header.tail as int, old_header.log_size as int);
                    let len1 = (contents_end - physical_tail);
                    let len2 = bytes_to_append@.len() - len1;
                    &&& old_ib == new_ib 
                    &&& old_headers == new_headers
                    &&& new_data.subrange(physical_tail - contents_offset, contents_end - contents_offset) =~= bytes_to_append@.subrange(0, len1)
                    &&& new_data.subrange(0, len2 as int) =~= bytes_to_append@.subrange(len1 as int, bytes_to_append@.len() as int)
                    &&& new_data.subrange(len2 as int, physical_tail - contents_offset) =~= old_data.subrange(len2 as int, physical_tail - contents_offset)
                    &&& bytes_to_append@ =~= new_data.subrange(physical_tail - contents_offset, contents_end - contents_offset) + new_data.subrange(0, len2 as int)
                })
        {
            let physical_head = Self::addr_logical_to_physical(old_header.head, old_header.log_size);
            let physical_tail = Self::addr_logical_to_physical(old_header.tail, old_header.log_size);
            let contents_end = old_header.log_size + contents_offset;
            let append_size = bytes_to_append.len();

            let len1 = (contents_end - physical_tail) as usize;
            let len2 = bytes_to_append.len() - len1;
            let append_bytes_slice = bytes_to_append.as_slice();
            let bytes1 = slice_subrange(append_bytes_slice, 0, len1);
            let bytes2 = slice_subrange(append_bytes_slice, len1, append_size);

            proof { lemma_data_write_is_safe(wrpm@, bytes1@, physical_tail as int, perm); }
            wrpm.write(physical_tail, bytes1, Tracked(perm));

            proof { lemma_data_write_is_safe(wrpm@, bytes2@, contents_offset as int, perm); }
            wrpm.write(contents_offset, bytes2, Tracked(perm));

            proof {
                assert(wrpm@.subrange(0, contents_offset as int) =~= old(wrpm)@.subrange(0, contents_offset as int));
                lemma_subrange_equality_implies_subsubrange_equality(wrpm@, old(wrpm)@, 0, contents_offset as int);
            }
        }

        pub exec fn untrusted_advance_head<P>(
            &mut self,
            wrpm: &mut WriteRestrictedPersistentMemory<P>,
            new_head: u64,
            Tracked(perm): Tracked<&P>
        ) -> (result: Result<(), InfiniteLogErr>)
            where
                P: CheckPermission<Seq<u8>>,
            requires
                old(self).consistent_with_pm2(old(wrpm)@),
                UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old(wrpm)@).is_Some(),
                ({
                    let old_log_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old(wrpm)@);
                    forall |pm_state| #[trigger] perm.check_permission(pm_state) <==> {
                        let log_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm_state);
                        ||| log_state == old_log_state 
                        ||| log_state == Some(old_log_state.unwrap().advance_head(new_head as int))
                    }
                })
            ensures
                self.consistent_with_pm2(wrpm@),
                wrpm.impervious_to_corruption() == old(wrpm).impervious_to_corruption(),
                ({
                    let old_log_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old(wrpm)@);
                    let new_log_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(wrpm@);
                    match (result, old_log_state, new_log_state) {
                        (Ok(_), Some(old_log_state), Some(new_log_state)) => {
                            &&& old_log_state.head <= new_head <= old_log_state.head + old_log_state.log.len()
                            &&& new_log_state == old_log_state.advance_head(new_head as int)
                        },
                        (Err(InfiniteLogErr::CantAdvanceHeadPositionBeforeHead{ head }), Some(old_log_state), Some(new_log_state)) => {
                            &&& new_log_state == old_log_state
                            &&& head == old_log_state.head
                            &&& new_head < head
                        },
                        (Err(InfiniteLogErr::CantAdvanceHeadPositionBeyondTail{ tail }), Some(old_log_state), Some(new_log_state)) => {
                            &&& new_log_state == old_log_state
                            &&& tail == old_log_state.head + old_log_state.log.len()
                            &&& new_head > tail
                        },
                        (_, _, _) => false
                    }
                })
        {
            let pm = wrpm.get_pm_ref();
            let ghost original_pm = wrpm@;

            let live_header = PersistentHeader {
                crc: self.header_crc,
                metadata: PersistentHeaderMetadata { head: self.head, tail: self.tail, log_size: self.log_size }
            };

            if new_head < live_header.metadata.head {
                assert(self.header_crc == old(self).header_crc);
                return Err(InfiniteLogErr::CantAdvanceHeadPositionBeforeHead{ head: live_header.metadata.head });
            }

            if new_head > live_header.metadata.tail {
                assert(self.header_crc == old(self).header_crc);
                return Err(InfiniteLogErr::CantAdvanceHeadPositionBeyondTail{ tail: live_header.metadata.tail });
            }

            // copy the header and update it 
            let mut new_header = live_header;
            new_header.metadata.head = new_head;
            let mut metadata_bytes = metadata_to_bytes(&new_header.metadata);
            let new_crc_bytes = bytes_crc(&metadata_bytes);
            let new_crc_val = u64_from_le_bytes(new_crc_bytes.as_slice());
            let ghost old_metadata_bytes = metadata_bytes@;
            let mut new_header_bytes = new_crc_bytes;
            new_header_bytes.append(&mut metadata_bytes);
            
            proof { lemma_header_crc_correct(new_header_bytes@, new_crc_bytes@, old_metadata_bytes); }
            
            self.update_header(wrpm, Tracked(perm), &new_header_bytes);

            // TODO: put ib update in a lemma
            let old_ib = self.incorruptible_bool;
            let new_ib = if old_ib == header1_val {
                header2_val 
            } else {
                assert(old_ib == header2_val);
                header1_val
            };
            let new_ib_bytes = u64_to_le_bytes(new_ib);

            proof {
                lemma_auto_spec_u64_to_from_le_bytes();
                lemma_single_write_crash(wrpm@, incorruptible_bool_pos as int, new_ib_bytes@);
                assert(perm.check_permission(old(wrpm)@));
                let new_pm = PersistentMemory::update_contents_to_reflect_write(wrpm@, incorruptible_bool_pos as int, new_ib_bytes@);
                lemma_headers_unchanged(wrpm@, new_pm); 
                assert(new_pm.subrange(incorruptible_bool_pos as int, incorruptible_bool_pos + 8) =~= new_ib_bytes@);
                
                let new_header = spec_bytes_to_header(new_header_bytes@);
                let (ib, headers, data) = pm_to_views(new_pm);
                let header_pos = if new_ib == header1_val {
                    header1_pos
                } else {
                    header2_pos
                };
                assert(new_pm.subrange(header_pos as int, header_pos + header_size) =~= new_header_bytes@);
                lemma_header_match(new_pm, header_pos as int, new_header);
                lemma_header_correct(new_pm, new_header_bytes@, header_pos as int);
                
                // prove that new pm has the advance head update
                let new_log_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(new_pm);
                let old_log_state = UntrustedLogImpl::convert_from_pm_contents_to_log_state2(old(wrpm)@);
                match (new_log_state, old_log_state) {
                    (Some(new_log_state), Some(old_log_state)) => {
                        lemma_pm_state_header(new_pm);
                        lemma_pm_state_header(old(wrpm)@);
                        assert(new_log_state =~= old_log_state.advance_head(new_head as int));
                        assert(perm.check_permission(new_pm));
                    }
                    _ => assert(false),
                }                
            }

            wrpm.write(incorruptible_bool_pos, new_ib_bytes.as_slice(), Tracked(perm));
            self.incorruptible_bool = new_ib;
            self.head = new_head;
            self.header_crc = new_crc_val;

            Ok(())
        }

        pub exec fn untrusted_read(
            &self,
            pm: &PersistentMemory,
            pos: u64,
            len: u64
        ) -> (result: Result<(Vec<u8>, Ghost<Seq<int>>), InfiniteLogErr>)
            requires
                self.consistent_with_pm2(pm@),
                UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm@).is_Some(),
            ensures
                match UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm@).unwrap() {
                    AbstractInfiniteLogState{ head: head, log: log, .. } =>
                        match result {
                            Ok((bytes, addrs)) => {
                                &&& pos >= head
                                &&& pos + len <= head + log.len()
                                &&& maybe_corrupted(bytes@, log.subrange(pos - head, pos + len - head), addrs@)
                                &&& pm.impervious_to_corruption() ==>
                                       bytes@ == log.subrange(pos - head, pos + len - head)
                            },
                            Err(InfiniteLogErr::CantReadBeforeHead{ head: head_pos }) => {
                                &&& pos < head
                                &&& head_pos == head
                            },
                            Err(InfiniteLogErr::CantReadPastTail{ tail }) => {
                                &&& pos + len > head + log.len()
                                &&& tail == head + log.len()
                            },
                            _ => false
                        }
                }
        {
            let physical_pos = Self::addr_logical_to_physical(pos, self.log_size);
            let contents_end = self.log_size + contents_offset;
            if pos < self.head {
                Err(InfiniteLogErr::CantReadBeforeHead{ head: self.head })
            } else if pos > u64::MAX - len {
                Err(InfiniteLogErr::CantReadPastTail{ tail: self.tail })
            } else if pos + len > self.tail {
                Err(InfiniteLogErr::CantReadPastTail{ tail: self.tail })
            } else {
                proof {
                    // we get a type error if we calculate physical head and tail in non-ghost code and use them here,
                    // so we need to calculate them here for the proof and again later for execution
                    let physical_head = spec_addr_logical_to_physical(self.head as int, self.log_size as int);
                    let physical_tail = spec_addr_logical_to_physical(self.tail as int, self.log_size as int);
                    if physical_head == physical_tail {
                        lemma_mod_equal(self.head as int, self.tail as int, self.log_size as int);
                        assert(len == 0);
                    } else if physical_head < physical_tail {
                        // read cannot wrap around 
                        lemma_mod_between(self.log_size as int, self.head as int, self.tail as int, pos as int);
                        lemma_mod_difference_equal(self.head as int, pos as int, self.log_size as int);
                    } else {
                        // read may wrap around 
                        lemma_mod_not_between(self.log_size as int, self.head as int, self.tail as int, pos as int);
                        if physical_pos <= physical_tail {
                            lemma_mod_wrapped_len(self.head as int, pos as int, self.log_size as int);
                        } else {
                            lemma_mod_difference_equal(self.head as int, pos as int, self.log_size as int);
                        }
                    }
                }

                let physical_head = Self::addr_logical_to_physical(self.head, self.log_size);
                let physical_tail = Self::addr_logical_to_physical(self.tail, self.log_size);
                
                let ghost log = Self::convert_from_pm_contents_to_log_state2(pm@).unwrap();
                let buffer = if physical_head == physical_tail {
                    assert (Seq::<u8>::empty() =~= log.log.subrange(pos - log.head, pos + len - log.head));
                    (Vec::new(), Ghost(Seq::empty()))
                } else if physical_pos >= physical_head && physical_pos >= contents_end - len {
                    let r1_len = contents_end - physical_pos;
                    let r2_len = len - r1_len;

                    let (mut r1, r1_addrs) = pm.read(physical_pos, r1_len);
                    let (mut r2, r2_addrs) = pm.read(contents_offset, r2_len);

                    r1.append(&mut r2);
                    assert (pm@.subrange(physical_pos as int, physical_pos + r1_len)
                                + pm@.subrange(contents_offset as int, contents_offset + r2_len)
                                =~= log.log.subrange(pos - log.head, pos + len - log.head));
                    (r1, Ghost(r1_addrs@ + r2_addrs@))
                } else {
                    assert (pm@.subrange(physical_pos as int, physical_pos + len) =~=
                                log.log.subrange(pos - log.head, pos + len - log.head));
                    pm.read(physical_pos, len)
                };
                proof { lemma_pm_state_header(pm@); }
                Ok(buffer)
            }
        }

        pub exec fn untrusted_get_head_and_tail(
            &self,
            pm: &PersistentMemory
        ) -> (result: Result<(u64, u64, u64), InfiniteLogErr>)
            requires
                self.consistent_with_pm2(pm@),
                UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm@).is_Some()
            ensures
                match result {
                    Ok((result_head, result_tail, result_capacity)) =>
                        match UntrustedLogImpl::convert_from_pm_contents_to_log_state2(pm@).unwrap() {
                            AbstractInfiniteLogState{ head: head, log: log, capacity: capacity } => {
                                &&& result_head == head
                                &&& result_tail == head + log.len()
                                &&& result_capacity == capacity
                            }
                        },
                    Err(_) => false,
                }
        {
            proof { lemma_pm_state_header(pm@); }
            Ok((self.head, self.tail, self.log_size - 1))
        }
    }
}
