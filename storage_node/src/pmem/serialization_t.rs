use crate::pmem::pmemspec_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

use deps_hack::crc64fast::Digest;
use std::convert::TryInto;

verus! {
    // TODO: is this enough to prevent someone from creating an
    // S from different data and passing it off as one that was
    // read normally?
    pub open spec fn maybe_corrupted_serialized<S>(
        read_val: S,
        true_val: S,
        start_addr: int
    ) -> bool
        where
            S: Serializable + Sized
    {
        maybe_corrupted(
            read_val.spec_serialize(),
            true_val.spec_serialize(),
            Seq::<int>::new(S::spec_serialized_len() as nat, |i: int| i + start_addr)
        )
    }

    pub proof fn lemma_serialized_val_uncorrupted<S>(
        read_val: S,
        true_val: S,
        val_addr: int,
        read_crc: u64,
        true_crc: u64,
        crc_addr: int,
    )
        where
            S: Serializable + Sized
        requires
            // an impl of `Serializable can override the default impl, so
            // we have to require it here
            read_val.spec_crc() == spec_crc_u64(read_val.spec_serialize()),
            true_val.spec_crc() == spec_crc_u64(true_val.spec_serialize()),
            maybe_corrupted_serialized(read_val, true_val, val_addr),
            maybe_corrupted_serialized(read_crc, true_crc, crc_addr),
            read_crc == read_val.spec_crc(),
            true_crc == true_val.spec_crc(),
            crc_addr < crc_addr + CRC_SIZE <= val_addr || crc_addr >= val_addr + S::spec_serialized_len()
        ensures
            read_val == true_val
    {
        let read_val_bytes = read_val.spec_serialize();
        let true_val_bytes = true_val.spec_serialize();
        let read_crc_bytes = read_crc.spec_serialize();
        let true_crc_bytes = true_crc.spec_serialize();
        let val_addrs = Seq::<int>::new(S::spec_serialized_len() as nat, |i: int| i + val_addr);
        u64::lemma_auto_serialize_deserialize();
        assert(true_crc == true_val.spec_crc());
        assert(true_val.spec_crc() == spec_crc_u64(true_val_bytes));
        assert(true_crc == spec_crc_u64(true_val_bytes));

        axiom_bytes_uncorrupted(read_val_bytes, true_val_bytes, val_addrs,
                                read_crc, true_crc, crc_addr);
        assert(read_val_bytes == true_val_bytes);
        assert(S::spec_deserialize(read_val_bytes) == S::spec_deserialize(true_val_bytes));
        S::lemma_auto_serialize_deserialize();
        assert(S::spec_deserialize(read_val_bytes) == read_val);
        assert(S::spec_deserialize(true_val_bytes) == true_val);
    }

    // TODO: maybe use a specific type for the CDB?
    pub proof fn lemma_corruption_detecting_boolean_serialized(
        read_cdb: u64,
        true_cdb: u64,
        addr: int,
    )
        requires
            maybe_corrupted_serialized(read_cdb, true_cdb, addr),
            read_cdb == CDB_FALSE || read_cdb == CDB_TRUE,
            true_cdb == CDB_FALSE || true_cdb == CDB_TRUE,
        ensures
            read_cdb == true_cdb
    {
        let addrs = Seq::<int>::new(u64::spec_serialized_len() as nat, |i: int| i + addr);
        let read_cdb_bytes = read_cdb.spec_serialize();
        let true_cdb_bytes = true_cdb.spec_serialize();
        assert(maybe_corrupted(read_cdb_bytes, true_cdb_bytes, addrs));
        u64::lemma_auto_serialize_deserialize();
        axiom_corruption_detecting_boolean(read_cdb_bytes, true_cdb_bytes, addrs);
    }

    pub trait Serializable : Sized {
        spec fn spec_serialize(self) -> Seq<u8>;

        spec fn spec_deserialize(bytes: Seq<u8>) -> Self;

        open spec fn spec_crc(self) -> u64 {
            spec_crc_u64(self.spec_serialize())
        }

        proof fn lemma_auto_serialize_deserialize()
            ensures
                forall |s: Self| #![auto] s == Self::spec_deserialize(s.spec_serialize()),
        ;

        proof fn lemma_auto_deserialize_serialize()
            ensures
                forall |bytes: Seq<u8>| #![auto] bytes.len() == Self::spec_serialized_len() ==>
                    bytes == Self::spec_deserialize(bytes).spec_serialize()
        ;


        proof fn lemma_auto_serialized_len()
            ensures
                forall |s: Self| #![auto] s.spec_serialize().len() == Self::spec_serialized_len()
        ;

        // TODO: this should really be a constant, but verus doesn't
        // support associated constants right now
        spec fn spec_serialized_len() -> int;

        fn serialized_len() -> (out: u64)
            ensures
                out == Self::spec_serialized_len()
        ;
    }

    impl Serializable for u64 {
        closed spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self)
        }

        closed spec fn spec_deserialize(bytes: Seq<u8>) -> Self
        {
            spec_u64_from_le_bytes(bytes)
        }


        open spec fn spec_crc(self) -> u64 {
            spec_crc_u64(self.spec_serialize())
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(forall |s: Self| #![auto] s == Self::spec_deserialize(s.spec_serialize()));
        }

        proof fn lemma_auto_deserialize_serialize() {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(forall |bytes: Seq<u8>| #![auto] bytes.len() == Self::spec_serialized_len() ==>
                bytes =~= Self::spec_deserialize(bytes).spec_serialize());
        }

        proof fn lemma_auto_serialized_len()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(forall |s: Self| #![auto] s.spec_serialize().len() == 8);
            assert(Self::spec_serialized_len() == 8);
        }

        open spec fn spec_serialized_len() -> int
        {
            8
        }

        fn serialized_len() -> u64
        {
            8
        }
    }
}
